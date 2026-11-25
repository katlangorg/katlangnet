using KatLang.Evaluation;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// The C# observation of one host-parent case, on the neutral channel shared with the generated
/// Lean artifact plus the zero-argument property cache's PUBLISHED entries per binding name. The
/// entries are kept beside a failure too (KL-06): a failed run still shows every entry a successful
/// owner published before it, and the generated guards compare them on failing cases as well.
/// A successful run also carries the <c>kl-struct-v1</c> identity of its typed value
/// (<see cref="MetamorphicStructuralIdentity.Encode"/>, KL-07), which the generated guards compare
/// with the Lean exporter's text: unlike <see cref="Neutral"/>, it never writes two values alike.
/// </summary>
public sealed record HostParentObservation(
    string Neutral,
    SharedErrorPayload? ErrorPayload,
    CachePublications Publications,
    string? StructuralIdentity)
{
    public bool IsSuccess => Neutral.StartsWith("ok ", StringComparison.Ordinal);
    public IReadOnlyDictionary<string, int> PublishedByName => Publications.ByName;
    public int PublishedTotal => Publications.Total;
    public int Published(string name) => Publications.Published(name);
}

/// <summary>
/// Runs a host-parent case's ONE program graph through every C# evaluator route — the plain
/// evaluator, the counted evaluator, the observed counted run with the generic strategies and with
/// the optimizers enabled, and the genuinely suspending async twin — and requires them to agree
/// exactly on value, emitted count and error category/payload. Sync routes also compare published
/// entries per name; the async route compares the published total and rejects synchronous access
/// (<see cref="ZeroArgPublicationObserver"/>, the cache-recording routes shared with the other corpora).
/// The harness reports one observation only after these checks. A disagreement throws, naming the case: the corpus can never
/// pin one route's behaviour as "the C# observation".
/// </summary>
public static class HostParentDifferentialHarness
{
    public static HostParentObservation Observe(HostParentCase hostCase)
    {
        var id = hostCase.Id;
        var program = hostCase.Program;

        var plain = Evaluator.Run(program);
        var counted = Evaluator.RunCounted(program);

        // The cache-recording routes, shared with the other generated corpora (KL-06 pilots): they
        // must agree on the published entries before this harness compares them with plain/counted.
        var (generic, optimized, asynchronous, publications) =
            ZeroArgPublicationObserver.Observe("Host-parent differential", id, program);

        var routes = new (string Name, EvalResult<Evaluator.CountedResult> Result)[]
        {
            ("counted", counted), ("generic", generic), ("optimized", optimized), ("async", asynchronous),
        };
        foreach (var (name, result) in routes)
        {
            Require(id, result.IsError == plain.IsError, $"plain and {name} routes disagree on success");
            if (plain.IsError)
                DifferentialErrors.RequireAgreement(id, plain.Error, result.Error);
            else
            {
                Require(id, Result.ValueComparer.Equals(plain.Value, result.Value.Value),
                    $"plain value {SemanticExplorerHarness.Neutral(plain.Value)} vs {name} {SemanticExplorerHarness.Neutral(result.Value.Value)}");
                Require(id, result.Value.EmittedCount == counted.Value.EmittedCount, $"{name} emitted count differs");
            }
        }

        if (plain.IsError)
        {
            var observed = DifferentialErrors.Observe(plain.Error);
            return new($"err {observed.Category}", observed.Payload, publications, StructuralIdentity: null);
        }

        // KL-07: the identity of the TYPED value, encoded directly. Rebuilding it from the neutral
        // text would lose exactly the distinction it exists for (strings between unescaped quotes).
        return new($"ok raw={SemanticExplorerHarness.Neutral(counted.Value.Value)} n={counted.Value.EmittedCount}",
            null, publications, MetamorphicStructuralIdentity.Encode(counted.Value.Value));
    }

    private static void Require(string caseId, bool condition, string what)
    {
        if (!condition)
            throw new InvalidOperationException($"Host-parent differential route disagreement for '{caseId}': {what}.");
    }
}
