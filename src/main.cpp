// RecLite - grabador de pantalla ultraligero para Windows 7+ (sin GPU, sin .NET)
// Captura: GDI BitBlt | Audio: WASAPI (sistema + micro) | Codificación: x264 ultrafast vía ffmpeg.exe
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <shellapi.h>
#include <shlobj.h>
#include <mmsystem.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <stdio.h>

#define WM_TRAY (WM_APP + 1)
#define WM_DONE (WM_APP + 2)

enum { ID_REC = 1, ID_PAUSE, ID_OPEN, ID_EXIT, ID_SCALE = 100, ID_FPS = 110, ID_Q = 120,
       ID_SYS = 130, ID_MIC, ID_CUR, ID_CORES };

static const int kScale[] = {100, 75, 50};
static const WCHAR* kScaleN[] = {L"100 % (original)", L"75 %", L"50 % (el mas ligero)"};
static const int kFps[] = {20, 30, 60};
static const WCHAR* kQN[] = {L"Ligera (menos CPU)", L"Normal", L"Alta"};
static const WCHAR* kQArgs[] = {L"-preset ultrafast -crf 30", L"-preset ultrafast -crf 25", L"-preset superfast -crf 21"};

struct Settings { int scale, fps, q, sys, mic, cursor, cores; };
static Settings S;

static HWND g_hwnd;
static NOTIFYICONDATAW g_nid;
static WCHAR g_exeDir[MAX_PATH], g_ini[MAX_PATH], g_outDir[MAX_PATH], g_base[MAX_PATH];
static volatile LONG g_state = 0;            // 0 libre, 1 grabando, 2 pausa, 3 finalizando
static volatile bool g_stop = false, g_paused = false;
static LARGE_INTEGER g_freq;
static volatile LONGLONG g_t0 = 0, g_pausedTotal = 0, g_pauseStart = 0;
static int g_sx, g_sy, g_sw, g_sh, g_w, g_h, g_fps;
static bool g_cursor, g_useSys, g_useMic;
static HANDLE g_pipe = 0, g_ff = 0, g_ath = 0;

static LONGLONG qpc() { LARGE_INTEGER x; QueryPerformanceCounter(&x); return x.QuadPart; }

// ---------------------------------------------------------------- ajustes
static void loadSettings() {
    S.scale = GetPrivateProfileIntW(L"rec", L"scale", 0, g_ini);
    S.fps = GetPrivateProfileIntW(L"rec", L"fps", 1, g_ini);
    S.q = GetPrivateProfileIntW(L"rec", L"q", 1, g_ini);
    S.sys = GetPrivateProfileIntW(L"rec", L"sys", 1, g_ini);
    S.mic = GetPrivateProfileIntW(L"rec", L"mic", 0, g_ini);
    S.cursor = GetPrivateProfileIntW(L"rec", L"cursor", 0, g_ini);
    S.cores = GetPrivateProfileIntW(L"rec", L"cores", 1, g_ini);
    if (S.scale < 0 || S.scale > 2) S.scale = 0;
    if (S.fps < 0 || S.fps > 2) S.fps = 1;
    if (S.q < 0 || S.q > 2) S.q = 1;
}
static void saveOne(const WCHAR* k, int v) { WCHAR b[16]; _snwprintf(b, 16, L"%d", v); WritePrivateProfileStringW(L"rec", k, b, g_ini); }
static void saveSettings() {
    saveOne(L"scale", S.scale); saveOne(L"fps", S.fps); saveOne(L"q", S.q); saveOne(L"sys", S.sys);
    saveOne(L"mic", S.mic); saveOne(L"cursor", S.cursor); saveOne(L"cores", S.cores);
}

// ---------------------------------------------------------------- audio WASAPI
static const GUID kFloat = {0x00000003, 0x0000, 0x0010, {0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}};
struct AS {
    IAudioClient* ac; IAudioCaptureClient* cc; WAVEFORMATEX* fmt; HANDLE f;
    unsigned long long written; bool ok, isFloat; DWORD rate; WORD ch, bits; WCHAR path[MAX_PATH];
};
static AS g_sys, g_mic;

static bool aOpen(AS& s, bool loop, const WCHAR* path) {
    ZeroMemory(&s, sizeof s);
    IMMDeviceEnumerator* en = 0; IMMDevice* dev = 0;
    if (FAILED(CoCreateInstance(__uuidof(MMDeviceEnumerator), 0, CLSCTX_ALL, __uuidof(IMMDeviceEnumerator), (void**)&en))) return false;
    HRESULT hr = en->GetDefaultAudioEndpoint(loop ? eRender : eCapture, eConsole, &dev);
    en->Release();
    if (FAILED(hr)) return false;
    hr = dev->Activate(__uuidof(IAudioClient), CLSCTX_ALL, 0, (void**)&s.ac);
    dev->Release();
    if (FAILED(hr) || FAILED(s.ac->GetMixFormat(&s.fmt))) return false;
    s.isFloat = s.fmt->wFormatTag == WAVE_FORMAT_IEEE_FLOAT ||
        (s.fmt->wFormatTag == WAVE_FORMAT_EXTENSIBLE && IsEqualGUID(((WAVEFORMATEXTENSIBLE*)s.fmt)->SubFormat, kFloat));
    s.rate = s.fmt->nSamplesPerSec; s.ch = s.fmt->nChannels; s.bits = s.fmt->wBitsPerSample;
    if (!(s.isFloat && s.bits == 32) && s.bits != 16 && s.bits != 24 && s.bits != 32) return false;
    hr = s.ac->Initialize(AUDCLNT_SHAREMODE_SHARED, loop ? AUDCLNT_STREAMFLAGS_LOOPBACK : 0, 10000000, 0, s.fmt, 0);
    if (FAILED(hr) || FAILED(s.ac->GetService(__uuidof(IAudioCaptureClient), (void**)&s.cc))) return false;
    lstrcpyW(s.path, path);
    s.f = CreateFileW(path, GENERIC_WRITE, 0, 0, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, 0);
    if (s.f == INVALID_HANDLE_VALUE) return false;
    s.ac->Start();
    s.ok = true;
    return true;
}

static void zeros(HANDLE f, unsigned long long bytes) {
    static BYTE z[16384]; DWORD w;
    while (bytes) { DWORD c = bytes > sizeof z ? (DWORD)sizeof z : (DWORD)bytes; WriteFile(f, z, c, &w, 0); bytes -= c; }
}

// Vacía lo capturado. Si el dispositivo no entrega datos (silencio), rellena con ceros para no perder sincronía.
static void pump(AS& s, bool discard, long long expected) {
    UINT32 n = 0;
    while (SUCCEEDED(s.cc->GetNextPacketSize(&n)) && n) {
        BYTE* d; UINT32 fr; DWORD fl;
        if (FAILED(s.cc->GetBuffer(&d, &fr, &fl, 0, 0))) break;
        if (!discard) {
            unsigned long long bytes = (unsigned long long)fr * s.fmt->nBlockAlign; DWORD w;
            if (fl & AUDCLNT_BUFFERFLAGS_SILENT) zeros(s.f, bytes); else WriteFile(s.f, d, (DWORD)bytes, &w, 0);
            s.written += fr;
        }
        s.cc->ReleaseBuffer(fr);
    }
    if (!discard) {
        long long lack = expected - (long long)s.written;
        if (lack > (long long)s.rate / 50) { zeros(s.f, (unsigned long long)lack * s.fmt->nBlockAlign); s.written += lack; }
    }
}

static void aClose(AS& s) {
    if (s.ac) { s.ac->Stop(); }
    if (s.cc) s.cc->Release();
    if (s.ac) s.ac->Release();
    if (s.fmt) CoTaskMemFree(s.fmt);
    if (s.f && s.f != INVALID_HANDLE_VALUE) CloseHandle(s.f);
    s.cc = 0; s.ac = 0; s.fmt = 0; s.f = 0;
}

static DWORD WINAPI audioThread(LPVOID) {
    CoInitializeEx(0, COINIT_MULTITHREADED);
    WCHAR p[MAX_PATH];
    ZeroMemory(&g_sys, sizeof g_sys); ZeroMemory(&g_mic, sizeof g_mic);
    if (g_useSys) { _snwprintf(p, MAX_PATH, L"%ls.sys.raw", g_base); if (!aOpen(g_sys, true, p)) aClose(g_sys), g_sys.ok = false; }
    if (g_useMic) { _snwprintf(p, MAX_PATH, L"%ls.mic.raw", g_base); if (!aOpen(g_mic, false, p)) aClose(g_mic), g_mic.ok = false; }
    while (!g_stop) {
        Sleep(10);
        bool pz = g_paused;
        double sec = (double)(qpc() - g_t0 - g_pausedTotal) / (double)g_freq.QuadPart;
        if (g_sys.ok) pump(g_sys, pz, (long long)(sec * g_sys.rate));
        if (g_mic.ok) pump(g_mic, pz, (long long)(sec * g_mic.rate));
    }
    aClose(g_sys); aClose(g_mic);
    CoUninitialize();
    return 0;
}

// ---------------------------------------------------------------- ffmpeg
static HANDLE spawn(WCHAR* cmd, DWORD prio) {
    STARTUPINFOW si; ZeroMemory(&si, sizeof si); si.cb = sizeof si;
    si.dwFlags = STARTF_USESHOWWINDOW; si.wShowWindow = SW_HIDE;
    PROCESS_INFORMATION pi;
    if (!CreateProcessW(0, cmd, 0, 0, FALSE, prio | CREATE_NO_WINDOW, 0, g_exeDir, &si, &pi)) return 0;
    CloseHandle(pi.hThread);
    return pi.hProcess;
}

static const WCHAR* rawFmt(const AS& s) {
    if (s.isFloat) return L"f32le";
    return s.bits == 16 ? L"s16le" : (s.bits == 24 ? L"s24le" : L"s32le");
}

// Une video + audio(s) en un MP4 (el video se copia sin recodificar; solo el audio pasa a AAC)
static bool mux() {
    WCHAR v[MAX_PATH], sy[MAX_PATH], mi[MAX_PATH], out[MAX_PATH], cmd[4096], in[1536], ff[MAX_PATH];
    _snwprintf(v, MAX_PATH, L"%ls.v.mkv", g_base);
    _snwprintf(sy, MAX_PATH, L"%ls.sys.raw", g_base);
    _snwprintf(mi, MAX_PATH, L"%ls.mic.raw", g_base);
    _snwprintf(out, MAX_PATH, L"%ls.mp4", g_base);
    _snwprintf(ff, MAX_PATH, L"%ls\\ffmpeg.exe", g_exeDir);
    bool hs = g_sys.ok && g_sys.written > 0, hm = g_mic.ok && g_mic.written > 0;
    in[0] = 0; int n = 0; size_t len = 0;
    if (hs) { len += _snwprintf(in + len, 1536 - len, L" -f %ls -ar %lu -ac %d -i \"%ls\"", rawFmt(g_sys), g_sys.rate, (int)g_sys.ch, sy); n++; }
    if (hm) { len += _snwprintf(in + len, 1536 - len, L" -f %ls -ar %lu -ac %d -i \"%ls\"", rawFmt(g_mic), g_mic.rate, (int)g_mic.ch, mi); n++; }
    const WCHAR* fx = L"aformat=sample_rates=48000:channel_layouts=stereo";
    WCHAR opt[800];
    if (n == 0) _snwprintf(opt, 800, L"-map 0:v -c copy");
    else if (n == 1) _snwprintf(opt, 800, L"-map 0:v -map 1:a -af %ls -c:v copy -c:a aac -b:a 160k -shortest", fx);
    else _snwprintf(opt, 800, L"-filter_complex \"[1:a]%ls[a1];[2:a]%ls[a2];[a1][a2]amix=inputs=2:duration=longest,volume=2[a]\" -map 0:v -map \"[a]\" -c:v copy -c:a aac -b:a 160k -shortest", fx, fx);
    _snwprintf(cmd, 4096, L"\"%ls\" -hide_banner -loglevel error -i \"%ls\"%ls %ls -movflags +faststart -y \"%ls\"", ff, v, in, opt, out);
    HANDLE h = spawn(cmd, BELOW_NORMAL_PRIORITY_CLASS);
    if (!h) return false;
    WaitForSingleObject(h, 10 * 60 * 1000);
    DWORD code = 1; GetExitCodeProcess(h, &code); CloseHandle(h);
    if (code != 0) return false;
    DeleteFileW(v); DeleteFileW(sy); DeleteFileW(mi);
    return true;
}

// ---------------------------------------------------------------- video
static bool pwrite(HANDLE h, HANDLE ev, const void* p, DWORD n) {
    OVERLAPPED o; ZeroMemory(&o, sizeof o); o.hEvent = ev; ResetEvent(ev);
    DWORD w = 0;
    if (!WriteFile(h, p, n, &w, &o)) {
        if (GetLastError() != ERROR_IO_PENDING) return false;
        if (!GetOverlappedResult(h, &o, &w, TRUE)) return false;
    }
    return w == n;
}

static void drawCursor(HDC dc) {
    CURSORINFO ci; ci.cbSize = sizeof ci;
    if (!GetCursorInfo(&ci) || !(ci.flags & CURSOR_SHOWING)) return;
    ICONINFO ii;
    if (!GetIconInfo(ci.hCursor, &ii)) return;
    int x = (int)((ci.ptScreenPos.x - (int)ii.xHotspot - g_sx) * (long long)g_w / g_sw);
    int y = (int)((ci.ptScreenPos.y - (int)ii.yHotspot - g_sy) * (long long)g_h / g_sh);
    DrawIconEx(dc, x, y, ci.hCursor, 0, 0, 0, 0, DI_NORMAL);
    if (ii.hbmMask) DeleteObject(ii.hbmMask);
    if (ii.hbmColor) DeleteObject(ii.hbmColor);
}

static DWORD WINAPI videoThread(LPVOID) {
    bool ok = true;
    HANDLE ev = CreateEventW(0, TRUE, FALSE, 0);
    OVERLAPPED ov; ZeroMemory(&ov, sizeof ov); ov.hEvent = ev;
    BOOL c = ConnectNamedPipe(g_pipe, &ov);
    DWORD e = GetLastError();
    if (!c) {
        if (e == ERROR_IO_PENDING) {
            HANDLE hs[2] = {ev, g_ff};
            if (WaitForMultipleObjects(2, hs, FALSE, 15000) != WAIT_OBJECT_0) { CancelIo(g_pipe); ok = false; }
        } else if (e != ERROR_PIPE_CONNECTED) ok = false;
    }
    if (ok) {
        g_t0 = qpc(); g_pausedTotal = 0;
        g_ath = CreateThread(0, 0, audioThread, 0, 0, 0);
        HDC scr = GetDC(0), mem = CreateCompatibleDC(scr);
        BITMAPINFO bi; ZeroMemory(&bi, sizeof bi);
        bi.bmiHeader.biSize = sizeof bi.bmiHeader; bi.bmiHeader.biWidth = g_w; bi.bmiHeader.biHeight = -g_h;
        bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32; bi.bmiHeader.biCompression = BI_RGB;
        void* bits = 0;
        HBITMAP dib = CreateDIBSection(scr, &bi, DIB_RGB_COLORS, &bits, 0, 0);
        HGDIOBJ old = SelectObject(mem, dib);
        SetStretchBltMode(mem, COLORONCOLOR);
        DWORD bytes = (DWORD)g_w * g_h * 4;
        LONGLONG sent = 0;
        while (!g_stop) {
            if (g_paused) { Sleep(15); continue; }
            double el = (double)(qpc() - g_t0 - g_pausedTotal) / (double)g_freq.QuadPart;
            LONGLONG target = (LONGLONG)(el * g_fps) + 1;
            if (sent >= target) { Sleep(1); continue; }
            if (g_w == g_sw && g_h == g_sh) BitBlt(mem, 0, 0, g_w, g_h, scr, g_sx, g_sy, SRCCOPY);
            else StretchBlt(mem, 0, 0, g_w, g_h, scr, g_sx, g_sy, g_sw, g_sh, SRCCOPY);
            if (g_cursor) drawCursor(mem);
            el = (double)(qpc() - g_t0 - g_pausedTotal) / (double)g_freq.QuadPart;
            target = (LONGLONG)(el * g_fps) + 1;
            if (target - sent > g_fps) target = sent + g_fps;   // tope: 1 s de repetidos
            if (target <= sent) target = sent + 1;
            bool bad = false;
            while (sent < target && !g_stop) { if (!pwrite(g_pipe, ev, bits, bytes)) { bad = true; break; } sent++; }
            if (bad) break;
        }
        SelectObject(mem, old); DeleteObject(dib); DeleteDC(mem); ReleaseDC(0, scr);
    }
    g_stop = true;
    if (g_pipe) { CloseHandle(g_pipe); g_pipe = 0; }
    if (WaitForSingleObject(g_ff, 30000) != WAIT_OBJECT_0) TerminateProcess(g_ff, 1);
    CloseHandle(g_ff); g_ff = 0;
    if (g_ath) { WaitForSingleObject(g_ath, 8000); CloseHandle(g_ath); g_ath = 0; }
    CloseHandle(ev);
    bool saved = ok && mux();
    timeEndPeriod(1);
    g_state = 0;
    PostMessageW(g_hwnd, WM_DONE, saved ? 1 : 0, 0);
    return 0;
}

// ---------------------------------------------------------------- control
static void setTray(const WCHAR* tip, WORD icon, const WCHAR* balloon) {
    g_nid.uFlags = NIF_ICON | NIF_TIP | (balloon ? NIF_INFO : 0);
    g_nid.hIcon = LoadIconW(0, MAKEINTRESOURCEW(icon));
    lstrcpynW(g_nid.szTip, tip, 127);
    if (balloon) { lstrcpynW(g_nid.szInfo, balloon, 255); lstrcpyW(g_nid.szInfoTitle, L"RecLite"); g_nid.dwInfoFlags = NIIF_INFO; }
    Shell_NotifyIconW(NIM_MODIFY, &g_nid);
}
static void updateTray(const WCHAR* balloon = 0) {
    if (g_state == 1) setTray(L"RecLite - GRABANDO", (WORD)(ULONG_PTR)IDI_ERROR, balloon);
    else if (g_state == 2) setTray(L"RecLite - en pausa", (WORD)(ULONG_PTR)IDI_WARNING, balloon);
    else if (g_state == 3) setTray(L"RecLite - guardando...", (WORD)(ULONG_PTR)IDI_WARNING, balloon);
    else setTray(L"RecLite - listo (Ctrl+Alt+R)", (WORD)(ULONG_PTR)IDI_APPLICATION, balloon);
}

static void startRec() {
    if (g_state) return;
    WCHAR ff[MAX_PATH];
    _snwprintf(ff, MAX_PATH, L"%ls\\ffmpeg.exe", g_exeDir);
    if (GetFileAttributesW(ff) == INVALID_FILE_ATTRIBUTES) {
        MessageBoxW(0, L"Falta ffmpeg.exe en la misma carpeta que RecLite.exe", L"RecLite", MB_ICONERROR); return;
    }
    DWORD_PTR pm, sm; GetProcessAffinityMask(GetCurrentProcess(), &pm, &sm);
    SYSTEM_INFO si; GetSystemInfo(&si); int n = (int)si.dwNumberOfProcessors;
    if (S.cores && n >= 3) SetProcessAffinityMask(GetCurrentProcess(), ((DWORD_PTR)1 << (n - 1)) | ((DWORD_PTR)1 << (n - 2)));
    else SetProcessAffinityMask(GetCurrentProcess(), sm);

    g_sx = 0; g_sy = 0; g_sw = GetSystemMetrics(SM_CXSCREEN); g_sh = GetSystemMetrics(SM_CYSCREEN);
    int sc = kScale[S.scale];
    g_w = (g_sw * sc / 100) & ~1; g_h = (g_sh * sc / 100) & ~1; g_fps = kFps[S.fps];
    g_cursor = S.cursor != 0; g_useSys = S.sys != 0; g_useMic = S.mic != 0;
    SYSTEMTIME t; GetLocalTime(&t);
    _snwprintf(g_base, MAX_PATH, L"%ls\\REC_%04d%02d%02d_%02d%02d%02d", g_outDir, t.wYear, t.wMonth, t.wDay, t.wHour, t.wMinute, t.wSecond);

    WCHAR pn[64];
    _snwprintf(pn, 64, L"\\\\.\\pipe\\reclite_%lu", GetCurrentProcessId());
    g_pipe = CreateNamedPipeW(pn, PIPE_ACCESS_OUTBOUND | FILE_FLAG_OVERLAPPED, PIPE_TYPE_BYTE | PIPE_WAIT, 1, 8 << 20, 0, 0, 0);
    if (g_pipe == INVALID_HANDLE_VALUE) { g_pipe = 0; return; }
    WCHAR cmd[2048];
    _snwprintf(cmd, 2048, L"\"%ls\" -hide_banner -loglevel error -f rawvideo -pix_fmt bgra -video_size %dx%d -framerate %d -i %ls "
        L"-c:v libx264 %ls -threads 2 -bf 0 -pix_fmt yuv420p -sws_flags fast_bilinear -y \"%ls.v.mkv\"",
        ff, g_w, g_h, g_fps, pn, kQArgs[S.q], g_base);
    g_ff = spawn(cmd, BELOW_NORMAL_PRIORITY_CLASS);
    if (!g_ff) { CloseHandle(g_pipe); g_pipe = 0; MessageBoxW(0, L"No se pudo iniciar ffmpeg.exe", L"RecLite", MB_ICONERROR); return; }
    g_stop = false; g_paused = false; g_state = 1;
    timeBeginPeriod(1);
    CloseHandle(CreateThread(0, 0, videoThread, 0, 0, 0));
    Beep(900, 70);
    updateTray();
}

static void stopRec() {
    if (g_state != 1 && g_state != 2) return;
    g_state = 3; g_stop = true;
    Beep(500, 70);
    updateTray();
}
static void toggleRec() { if (g_state == 0) startRec(); else stopRec(); }
static void togglePause() {
    if (g_state == 1) { g_pauseStart = qpc(); g_paused = true; g_state = 2; }
    else if (g_state == 2) { g_pausedTotal += qpc() - g_pauseStart; g_paused = false; g_state = 1; }
    updateTray();
}

static void radio(HMENU parent, const WCHAR* title, int base, const WCHAR* const* names, const int* vals, int count, int cur) {
    HMENU m = CreatePopupMenu();
    for (int i = 0; i < count; i++) {
        WCHAR b[64];
        if (names) lstrcpynW(b, names[i], 64); else _snwprintf(b, 64, L"%d fps", vals[i]);
        AppendMenuW(m, MF_STRING | (i == cur ? MF_CHECKED : 0), base + i, b);
    }
    AppendMenuW(parent, MF_POPUP, (UINT_PTR)m, title);
}

static void showMenu() {
    HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING, ID_REC, g_state == 0 ? L"Iniciar grabacion\tCtrl+Alt+R" : L"Detener y guardar\tCtrl+Alt+R");
    AppendMenuW(m, MF_STRING | ((g_state == 1 || g_state == 2) ? 0 : MF_GRAYED), ID_PAUSE, g_state == 2 ? L"Reanudar\tCtrl+Alt+P" : L"Pausar\tCtrl+Alt+P");
    AppendMenuW(m, MF_SEPARATOR, 0, 0);
    radio(m, L"Escala del video", ID_SCALE, kScaleN, kScale, 3, S.scale);
    radio(m, L"FPS", ID_FPS, 0, kFps, 3, S.fps);
    radio(m, L"Calidad / consumo", ID_Q, kQN, 0, 3, S.q);
    AppendMenuW(m, MF_STRING | (S.sys ? MF_CHECKED : 0), ID_SYS, L"Audio del sistema (juego)");
    AppendMenuW(m, MF_STRING | (S.mic ? MF_CHECKED : 0), ID_MIC, L"Microfono");
    AppendMenuW(m, MF_STRING | (S.cursor ? MF_CHECKED : 0), ID_CUR, L"Grabar el cursor del mouse");
    AppendMenuW(m, MF_STRING | (S.cores ? MF_CHECKED : 0), ID_CORES, L"Usar solo los 2 ultimos nucleos (libera los otros al juego)");
    AppendMenuW(m, MF_SEPARATOR, 0, 0);
    AppendMenuW(m, MF_STRING, ID_OPEN, L"Abrir carpeta de videos");
    AppendMenuW(m, MF_STRING, ID_EXIT, L"Salir");
    POINT p; GetCursorPos(&p);
    SetForegroundWindow(g_hwnd);
    TrackPopupMenu(m, TPM_RIGHTBUTTON, p.x, p.y, 0, g_hwnd, 0);
    PostMessageW(g_hwnd, WM_NULL, 0, 0);
    DestroyMenu(m);
}

static void onCommand(int id) {
    if (id == ID_REC) toggleRec();
    else if (id == ID_PAUSE) togglePause();
    else if (id == ID_OPEN) ShellExecuteW(0, L"open", g_outDir, 0, 0, SW_SHOW);
    else if (id == ID_EXIT) { if (g_state == 1 || g_state == 2) stopRec(); DestroyWindow(g_hwnd); }
    else if (id >= ID_SCALE && id < ID_SCALE + 3) S.scale = id - ID_SCALE;
    else if (id >= ID_FPS && id < ID_FPS + 3) S.fps = id - ID_FPS;
    else if (id >= ID_Q && id < ID_Q + 3) S.q = id - ID_Q;
    else if (id == ID_SYS) S.sys = !S.sys;
    else if (id == ID_MIC) S.mic = !S.mic;
    else if (id == ID_CUR) S.cursor = !S.cursor;
    else if (id == ID_CORES) S.cores = !S.cores;
    saveSettings();
}

static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM w, LPARAM l) {
    switch (m) {
    case WM_TRAY:
        if (LOWORD(l) == WM_RBUTTONUP || LOWORD(l) == WM_CONTEXTMENU) showMenu();
        else if (LOWORD(l) == WM_LBUTTONUP) toggleRec();
        return 0;
    case WM_HOTKEY: if (w == 1) toggleRec(); else if (w == 2) togglePause(); return 0;
    case WM_COMMAND: onCommand(LOWORD(w)); return 0;
    case WM_DONE: updateTray(w ? L"Video guardado en Videos\\RecLite" : L"Error al guardar. Revisa la carpeta (archivos temporales)"); return 0;
    case WM_DESTROY:
        UnregisterHotKey(h, 1); UnregisterHotKey(h, 2);
        Shell_NotifyIconW(NIM_DELETE, &g_nid);
        PostQuitMessage(0); return 0;
    }
    return DefWindowProcW(h, m, w, l);
}

int WINAPI WinMain(HINSTANCE hi, HINSTANCE, LPSTR, int) {
    HANDLE mx = CreateMutexW(0, TRUE, L"RecLite_single_instance");
    if (GetLastError() == ERROR_ALREADY_EXISTS) return 0;
    SetProcessDPIAware();
    QueryPerformanceFrequency(&g_freq);
    SetPriorityClass(GetCurrentProcess(), BELOW_NORMAL_PRIORITY_CLASS);

    GetModuleFileNameW(0, g_exeDir, MAX_PATH);
    WCHAR* sl = wcsrchr(g_exeDir, L'\\'); if (sl) *sl = 0;
    _snwprintf(g_ini, MAX_PATH, L"%ls\\reclite.ini", g_exeDir);
    loadSettings();
    SHGetFolderPathW(0, CSIDL_MYVIDEO, 0, 0, g_outDir);
    lstrcatW(g_outDir, L"\\RecLite");
    CreateDirectoryW(g_outDir, 0);

    WNDCLASSW wc; ZeroMemory(&wc, sizeof wc);
    wc.lpfnWndProc = WndProc; wc.hInstance = hi; wc.lpszClassName = L"RecLiteWnd";
    RegisterClassW(&wc);
    g_hwnd = CreateWindowW(L"RecLiteWnd", L"RecLite", 0, 0, 0, 0, 0, 0, 0, hi, 0);

    ZeroMemory(&g_nid, sizeof g_nid);
    g_nid.cbSize = sizeof g_nid; g_nid.hWnd = g_hwnd; g_nid.uID = 1; g_nid.uCallbackMessage = WM_TRAY;
    g_nid.uFlags = NIF_ICON | NIF_MESSAGE | NIF_TIP;
    g_nid.hIcon = LoadIconW(0, IDI_APPLICATION);
    lstrcpyW(g_nid.szTip, L"RecLite - listo (Ctrl+Alt+R)");
    Shell_NotifyIconW(NIM_ADD, &g_nid);
    if (!RegisterHotKey(g_hwnd, 1, MOD_CONTROL | MOD_ALT, 'R') || !RegisterHotKey(g_hwnd, 2, MOD_CONTROL | MOD_ALT, 'P'))
        updateTray(L"No pude registrar los atajos; usa el menu del icono.");

    MSG msg;
    while (GetMessageW(&msg, 0, 0, 0)) { TranslateMessage(&msg); DispatchMessageW(&msg); }
    CloseHandle(mx);
    return 0;
}
