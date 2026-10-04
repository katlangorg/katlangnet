using System.Text;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace KatLang.Tests;

/// <summary>
/// The documentation hosts read states the owner's Q-09 decisions (October 2026) and none of the
/// claims they retired (X-34). Q-09a: host-stack headroom is not a semantic quantity — whether the
/// host-stack backstop stops a run depends on the route, genuine suspension, the thread and its
/// stack size, the build, the runtime and its JIT state, and the platform; KatLang promises the
/// error kind <see cref="EvalError.EvaluationStackExhausted"/>, never a recursion depth, and the
/// async twin can stop both shallower and deeper than the synchronous evaluator. Q-09b: limits
/// observe a run; they never choose how it runs.
///
/// <para>The checked file is the compiled <c>KatLang.xml</c> that ships beside the assembly (and in
/// the package), so a documentation edit that reintroduces a retired claim — a fixed
/// stack-calibration ratio, "the async twin always stops earlier", a budget that selects another
/// evaluator — fails this suite. Phrases are matched on the rendered text (a <c>cref</c> renders as
/// its simple name), case-insensitively.</para>
/// </summary>
public class LimitDocumentationContractTests
{
    private static readonly Lazy<IReadOnlyDictionary<string, string>> Members = new(LoadMembers);

    [Fact]
    public void MaxSupportedDepth_IsASemanticBound_NotAStackCalibration()
    {
        var doc = Member("F:KatLang.EvaluationLimits.MaxSupportedDepth");
        AssertContains(doc, "deterministic SEMANTIC bound");
        AssertContains(doc, "NOT a measure of host-stack capacity");
        AssertContains(doc, "promises that error kind, never a recursion depth");
        AssertNoStackCalibration(doc);
    }

    [Fact]
    public void MaxDepth_SeparatesTheBackstop_AndStatesBothRouteDirections()
    {
        var doc = Member("P:KatLang.EvaluationLimits.MaxDepth");
        AssertContains(doc, "host-stack backstop is separate from this limit");
        AssertContains(doc, "SHALLOWER");
        AssertContains(doc, "DEEPER");
        AssertContains(doc, "never depends on which limits are configured");
        AssertNoStackCalibration(doc);
    }

    [Fact]
    public void AsyncEntryPoints_StateBothRouteDirections_AndLimitIndependence()
    {
        // Every public async overload documented with the recursion-depth paragraph states both
        // directions; at least one must carry it.
        var evaluatorDocs = Members.Value
            .Where(entry => entry.Key.StartsWith("M:KatLang.Evaluator.RunAsync(", StringComparison.Ordinal)
                && entry.Value.Contains("Recursion depth on the async twin path", StringComparison.OrdinalIgnoreCase))
            .Select(entry => entry.Value)
            .ToList();
        Assert.NotEmpty(evaluatorDocs);
        var engineDoc = Member("M:KatLang.KatLangEngine.RunAsync(System.String,KatLang.RunOptions)");
        foreach (var doc in evaluatorDocs.Append(engineDoc))
        {
            AssertContains(doc, "shallower");
            AssertContains(doc, "deeper");
            AssertContains(doc, "never on which");
        }
    }

    [Fact]
    public void EvaluationStackExhausted_IsHostPolicy_NeverAConfiguredLimitEffect()
    {
        var doc = Member("T:KatLang.EvalError.EvaluationStackExhausted");
        AssertContains(doc, "never on which EvaluationLimits are configured");
        AssertContains(doc, "only this error kind is part of the language contract, never a depth");
    }

    [Fact]
    public void LimitDocs_StateThatLimitsObserveARun()
    {
        var type = Member("T:KatLang.EvaluationLimits");
        AssertContains(type, "Limits observe a run; they never choose how it runs.");
        AssertContains(type, "its budget accounting, which internal evaluation strategy runs, or whether it completes");
        AssertContains(type, "writing a limit's default value is the same as leaving it unset");

        var steps = Member("P:KatLang.EvaluationLimits.MaxSteps");
        AssertContains(steps, "Steps are LOGICAL work");
        AssertContains(steps, "charges exactly the same steps at the same points as the generic evaluator");

        var items = Member("P:KatLang.EvaluationLimits.MaxMaterializedItems");
        AssertContains(items, "Slots are counted LOGICALLY");

        var runOptions = Member("P:KatLang.RunOptions.EvaluationLimits");
        AssertContains(runOptions, "Limits observe a run; they never choose how it runs");
    }

    /// <summary>
    /// No documented member — public or internal — restates a retired claim in the present tense.
    /// Historical narrative (past tense, dated) stays legal; the patterns target the claims X-34
    /// removed and the selector Q-09b deleted.
    /// </summary>
    [Fact]
    public void NoShippedDoc_RestatesARetiredClaim()
    {
        string[] forbidden =
        [
            // "The async twin always fails/stops/exhausts earlier" (Q-09a: it can also go deeper).
            @"\balways\b[^.;]{0,80}\b(earlier|shallower|sooner)\b",
            @"\b(earlier|shallower|sooner)\b[^.;]{0,40}\balways\b",
            // One portable safety factor / a depth limit calibrated against the host stack
            // (X-34). Frame-size calibration of the structural walks (parser, loader, AST
            // preflight) is a different, still-valid host-safety design and stays legal.
            @"\bmeasured margin\b",
            @"calibrat\w*[^.;]{0,60}\b(depth ceiling|depth limit|depth envelope|MaxSupportedDepth|MaxDepth)\b",
            @"\b(MaxSupportedDepth|MaxDepth|depth ceiling|depth limit|depth envelope)\b[^.;]{0,60}\bcalibrat",
            // A configured budget selecting another evaluator (Q-09b).
            @"\b(budgets?|limits?)\b[^.;]{0,80}\b(selects?|forces?|disables?|switch(es)? off)\b[^.;]{0,60}\b(generic|fusion|planning|optimi[sz])",
            @"can change which internal evaluation strategy runs",
        ];
        var violations = (
            from entry in Members.Value
            from pattern in forbidden
            let match = Regex.Match(entry.Value, pattern, RegexOptions.IgnoreCase | RegexOptions.CultureInvariant)
            where match.Success
            select $"{entry.Key}: `{match.Value}`").ToList();
        Assert.True(violations.Count == 0, "Retired claims in the shipped documentation:\n" + string.Join("\n", violations));
    }

    private static void AssertNoStackCalibration(string doc)
    {
        Assert.DoesNotMatch(new Regex(@"calibrat", RegexOptions.IgnoreCase), doc);
        // A fixed ratio such as `1.7x` or `2.6x`, or a measured boundary pair such as `222 / 333`.
        Assert.DoesNotMatch(new Regex(@"\b\d+(\.\d+)?x\b"), doc);
        Assert.DoesNotMatch(new Regex(@"\b\d{2,}\s*/\s*\d{2,}\b"), doc);
    }

    private static void AssertContains(string doc, string phrase)
        => Assert.True(
            doc.Contains(phrase, StringComparison.OrdinalIgnoreCase),
            $"Expected the documentation to state \"{phrase}\":\n{doc}");

    private static string Member(string name)
        => Members.Value.TryGetValue(name, out var doc)
            ? doc
            : throw new Xunit.Sdk.XunitException($"No documentation for {name} in the shipped KatLang.xml.");

    private static IReadOnlyDictionary<string, string> LoadMembers()
    {
        var path = Path.ChangeExtension(typeof(EvaluationLimits).Assembly.Location, ".xml");
        if (!File.Exists(path))
            throw new Xunit.Sdk.XunitException($"The KatLang XML documentation must ship beside the assembly: {path}");

        return XDocument.Load(path).Root!.Element("members")!.Elements("member")
            .ToDictionary(member => (string)member.Attribute("name")!, Render, StringComparer.Ordinal);
    }

    /// <summary>Plain text of one member's documentation: a cross-reference renders as its simple name.</summary>
    private static string Render(XElement member)
    {
        var text = new StringBuilder();
        Append(member, text);
        return Regex.Replace(text.ToString(), @"\s+", " ").Trim();

        static void Append(XElement element, StringBuilder text)
        {
            foreach (var node in element.Nodes())
            {
                switch (node)
                {
                    case XText literal:
                        text.Append(literal.Value);
                        break;
                    case XElement { Name.LocalName: "see" or "seealso" } reference when reference.Value.Length > 0:
                        text.Append(reference.Value);
                        break;
                    case XElement { Name.LocalName: "see" or "seealso" } reference:
                        text.Append(SimpleName((string?)reference.Attribute("cref") ?? (string?)reference.Attribute("langword") ?? ""));
                        break;
                    case XElement { Name.LocalName: "paramref" or "typeparamref" } reference:
                        text.Append((string?)reference.Attribute("name"));
                        break;
                    case XElement child:
                        text.Append(' ');
                        Append(child, text);
                        text.Append(' ');
                        break;
                }
            }
        }
    }

    private static string SimpleName(string cref)
    {
        var name = cref.IndexOf(':') is var colon and >= 0 ? cref[(colon + 1)..] : cref;
        if (name.IndexOf('(') is var parenthesis and >= 0)
            name = name[..parenthesis];
        return name[(name.LastIndexOf('.') + 1)..];
    }
}
