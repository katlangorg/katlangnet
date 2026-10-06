using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>The front-end passes that elaborate a loaded module unit, in pipeline order.</summary>
internal enum ModuleUnitPass
{
    /// <summary>Name resolution (<see cref="ParameterDetector"/>): the import view to its detected declaration.</summary>
    Detection,

    /// <summary>Automatic parameter forwarding (<see cref="ImplicitArgumentResolver"/>): detected to resolved.</summary>
    Resolution,

    /// <summary>Exposure classification (<see cref="PropertyExposureResolver"/>): resolved to classified.</summary>
    Exposure,
}

/// <summary>
/// Q-32 I-U (decided 2026-10-06, with Q-31 H-P): ONE module declaration per canonical URL per compiled
/// program. Load elaboration splices one locationless import view per canonical URL (the loader's
/// per-document cache), and a loaded module is a hygienic unit rooted at the prelude, so its elaboration
/// is the same wherever it is reached: each front-end pass elaborates the view ONCE and every reach
/// receives that one declaration — one member binding, one callable identity, one open provider. A
/// program is elaborated in more than one OPERATION — the parse, then each deferred region's
/// materialization when evaluation selects it — so the units an error-free operation elaborated are
/// PUBLISHED here, and a later operation that splices the same view receives the same declaration
/// instead of re-elaborating it (a re-elaboration would mint new member properties, and with them new
/// bindings). An operation that reported an error publishes nothing: its result is never evaluated, and
/// a later operation elaborates — and reports — the module afresh. Never static: a registry belongs to
/// one loader, which belongs to one document.
/// </summary>
internal sealed class ModuleUnitRegistry
{
    private readonly Dictionary<Algorithm, Algorithm>[] _published =
    [
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
    ];

    /// <summary>A new operation's units, reading what earlier error-free operations published.</summary>
    internal ModuleUnits BeginOperation() => new(this);

    internal bool TryGet(ModuleUnitPass pass, Algorithm module, [NotNullWhen(true)] out Algorithm? elaborated)
        => _published[(int)pass].TryGetValue(module, out elaborated);

    internal void Publish(Dictionary<Algorithm, Algorithm>[] units)
    {
        for (var pass = 0; pass < units.Length; pass++)
        {
            foreach (var (module, elaborated) in units[pass])
                _published[pass].TryAdd(module, elaborated);
        }
    }
}

/// <summary>
/// The loaded module units of ONE front-end operation (see <see cref="ModuleUnitRegistry"/>): what each
/// pass elaborated, by the module declaration it received. Without a registry (a parse with no module
/// loader, a pass run on its own) the units live for the operation only.
/// </summary>
internal sealed class ModuleUnits(ModuleUnitRegistry? registry = null)
{
    private readonly Dictionary<Algorithm, Algorithm>[] _units =
    [
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
    ];

    /// <summary>The declaration <paramref name="pass"/> already elaborated <paramref name="module"/> to, in this operation or an earlier published one.</summary>
    internal bool TryGet(ModuleUnitPass pass, Algorithm module, [NotNullWhen(true)] out Algorithm? elaborated)
        => _units[(int)pass].TryGetValue(module, out elaborated)
            || (registry is not null && registry.TryGet(pass, module, out elaborated));

    internal void Add(ModuleUnitPass pass, Algorithm module, Algorithm elaborated)
        => _units[(int)pass].Add(module, elaborated);

    /// <summary>Publishes this operation's units to the program's registry: call only when the operation reported no error.</summary>
    internal void Publish() => registry?.Publish(_units);
}
