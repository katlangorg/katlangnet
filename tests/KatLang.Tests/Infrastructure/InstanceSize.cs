using System.Runtime.CompilerServices;

namespace KatLang.TestInfrastructure;

/// <summary>
/// Measures the heap bytes of one instance for exact allocation assertions, without running its constructor.
/// </summary>
internal static class InstanceSize
{
    public static long Of(Type type)
    {
        // GetUninitializedObject can rebuild a weak type cache after a GC. Create the template
        // outside the window. A shallow copy allocates one object of the same runtime type.
        var template = RuntimeHelpers.GetUninitializedObject(type);
        _ = ShallowCopy(template);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var copy = ShallowCopy(template);
        var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        GC.KeepAlive(copy);
        return bytes;
    }

    [UnsafeAccessor(UnsafeAccessorKind.Method, Name = "MemberwiseClone")]
    private static extern object ShallowCopy(object instance);
}
