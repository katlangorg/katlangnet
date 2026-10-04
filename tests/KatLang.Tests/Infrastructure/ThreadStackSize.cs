using System.Runtime.InteropServices;

namespace KatLang.TestInfrastructure;

/// <summary>
/// The size of the current thread's stack as the operating system actually allocated it, which is
/// not always the size the thread requested: glibc keeps the stacks of exited threads and gives a
/// new thread any cached stack from the requested size up to four times it, so on Linux a thread
/// created with a 384 KiB stack can run on a 1 MiB one. A freshly allocated stack reports exactly
/// the requested size (glibc reports the usable size, which excludes the guard page it adds;
/// Windows reports the whole reservation, which is the requested size).
/// </summary>
internal static class ThreadStackSize
{
    /// <summary>
    /// The current thread's stack size in bytes, or <c>null</c> where it is not read: only Windows
    /// and glibc-based Linux, the platforms the tests run on, are.
    /// </summary>
    internal static long? OfCurrentThread()
    {
        if (OperatingSystem.IsWindows())
        {
            GetCurrentThreadStackLimits(out var low, out var high);
            return (long)(high - low);
        }

        if (!OperatingSystem.IsLinux())
            return null;

        // pthread_attr_t is 56 bytes on x86-64 glibc and 64 on arm64; the buffer covers both.
        var attributes = new byte[256];
        try
        {
            if (PthreadGetattrNp(PthreadSelf(), attributes) != 0)
                return null;
        }
        catch (DllNotFoundException)
        {
            return null;
        }

        try
        {
            return PthreadAttrGetstack(attributes, out _, out var size) == 0 ? (long)size : null;
        }
        finally
        {
            _ = PthreadAttrDestroy(attributes);
        }
    }

    [DllImport("kernel32.dll")]
    private static extern void GetCurrentThreadStackLimits(out nuint lowLimit, out nuint highLimit);

    [DllImport("libc.so.6", EntryPoint = "pthread_self")]
    private static extern nint PthreadSelf();

    [DllImport("libc.so.6", EntryPoint = "pthread_getattr_np")]
    private static extern int PthreadGetattrNp(nint thread, byte[] attributes);

    [DllImport("libc.so.6", EntryPoint = "pthread_attr_getstack")]
    private static extern int PthreadAttrGetstack(byte[] attributes, out nint stackAddress, out nuint stackSize);

    [DllImport("libc.so.6", EntryPoint = "pthread_attr_destroy")]
    private static extern int PthreadAttrDestroy(byte[] attributes);
}
