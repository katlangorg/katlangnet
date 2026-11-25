using System.Text;
using System.Text.Json;

namespace KatLang.Tests.ExposureCensus;

/// <summary>
/// THE HEAD PROBE of the census's <c>check-head</c> mode: it evaluates every probe program of <c>head-programs.tsv</c>
/// against KatLang as of <see cref="Revision"/> and writes <c>head.out</c>, the input of
/// <see cref="ExposureCensusTests.HeadOutput"/>. The file is compiled into the test project, which pins it against
/// today's API and lets <c>ExposureCensusHarnessTests</c> run it in-process against <c>HeadOutput</c>, and it is
/// compiled AGAIN, unchanged, into a scratch console project against an export of <see cref="Revision"/>: the
/// <c>emit-head</c> mode writes that project (<see cref="WriteProject"/>) and <see cref="Steps"/> lists the commands.
/// It therefore uses only API that both revisions have, and nothing of the test project.
/// </summary>
internal static class CensusHeadProbe
{
    /// <summary>The revision the census compares with (the E-18 audit's HEAD).</summary>
    public const string Revision = "a4b545e8";

    /// <summary>The scratch project's file names inside its directory.</summary>
    public const string ProjectFileName = "HeadProbe.csproj";
    public const string EntryFileName = "Program.cs";

    internal static string InputLine(string id, string probe, string source, IReadOnlyList<KeyValuePair<string, string>>? modules)
    {
        var line = $"{id}\t{probe}\t{source.Replace("\n", "\\n")}";
        return modules is null ? line : line + "\t" + JsonSerializer.Serialize(modules.ToDictionary());
    }

    /// <summary>
    /// The protocol (<see cref="ExposureCensusTests.HeadOutput"/> reads it). Input: one program per line,
    /// <c>id \t probe \t source</c>, with an optional fourth field containing the fixture's URL-to-source map as JSON.
    /// A newline of the main source is written as the two characters <c>\n</c>. Output: tab-separated
    /// lines in input order,
    /// <list type="bullet">
    /// <item><c>id \t in5 \t META \t root.&lt;path&gt;: &lt;Exposure&gt;[name@depth,...]</c> for every non-exported declaration
    /// reachable through property values of an <c>in5</c> probe (an owner depth of <c>-1</c> marks a names-only
    /// requirement); a path met twice is skipped and counted, and the reader rejects a duplicate;</item>
    /// <item><c>id \t probe \t OUT \t outcome</c>, then <c>probe:async</c> (ordinary <c>Evaluator.RunAsync</c>) and
    /// <c>probe:forced</c> (<c>RunAsync</c> with an asynchronous host operation), the outcome being <c>OK &lt;neutral&gt;</c>,
    /// <c>FAIL &lt;error&gt;[:subject]</c> (the error under every context wrapper; the subject of a
    /// <c>LocalOnlyProperty</c>, <c>UnknownName</c> or <c>UnknownProperty</c>), <c>PARSE &lt;codes&gt;</c> (error
    /// diagnostics, on all three routes) or <c>EXCEPTION &lt;type&gt;</c>.</item>
    /// </list>
    /// </summary>
    public static async Task<(int Programs, int DuplicatePaths)> RunAsync(string programsPath, string outputPath)
    {
        var lines = File.ReadAllLines(programsPath);
        var outputs = new string[lines.Length];
        var duplicates = 0;
        var asyncRoute = HostOperations.Create(HostOperation.CreateAsync(
            "UnusedCensusRoute", static (_, _) => throw new InvalidOperationException("The census route marker must never run.")));

        await Parallel.ForEachAsync(Enumerable.Range(0, lines.Length),
            new ParallelOptions { MaxDegreeOfParallelism = Math.Max(1, Environment.ProcessorCount - 2) },
            async (i, _) =>
            {
                var parts = lines[i].Split('\t', 4);
                var (id, probe, source) = (parts[0], parts[1], parts[2].Replace("\\n", "\n"));
                var text = new StringBuilder();
                var parsed = parts.Length == 4 ? await ParseModules(source, parts[3]) : Parser.Parse(source);
                if (parsed.HasErrors)
                {
                    var codes = string.Join(",", parsed.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)
                        .Select(d => d.Code.ToString()).Distinct().Order(StringComparer.Ordinal));
                    foreach (var suffix in new[] { "", ":async", ":forced" })
                        text.Append($"{id}\t{probe}{suffix}\tOUT\tPARSE {codes}\n");
                    outputs[i] = text.ToString();
                    return;
                }

                var root = parsed.Root;
                if (probe == "in5")
                {
                    var seen = new HashSet<string>(StringComparer.Ordinal);
                    foreach (var (path, property) in Declarations(root, "root"))
                    {
                        if (property.Exposure == PropertyExposure.Exported) continue;
                        if (!seen.Add(path))
                        {
                            Interlocked.Increment(ref duplicates);
                            continue;
                        }
                        var requirements = property.CaptureRequirements is { } captures
                            ? captures.Select(r => $"{r.Name}@{r.OwnerDepth}")
                            : property.RequiredAncestorParameters.Select(name => $"{name}@-1");
                        text.Append($"{id}\t{probe}\tMETA\t{path}: {property.Exposure}[{string.Join(",", requirements)}]\n");
                    }
                }

                var expression = new Expr.AlgorithmExpr(root);
                text.Append($"{id}\t{probe}\tOUT\t{await Observe(() => Task.FromResult(Evaluator.Run(expression)))}\n");
                text.Append($"{id}\t{probe}:async\tOUT\t{await Observe(() => Evaluator.RunAsync(expression))}\n");
                text.Append($"{id}\t{probe}:forced\tOUT\t{await Observe(() => Evaluator.RunAsync(expression, asyncRoute, null, null, default))}\n");
                outputs[i] = text.ToString();
            });

        await File.WriteAllTextAsync(outputPath, string.Concat(outputs));
        return (lines.Length, duplicates);
    }

    private static Task<ParseResult> ParseModules(string source, string json)
    {
        var modules = JsonSerializer.Deserialize<Dictionary<string, string>>(json)
            ?? throw new InvalidDataException("Missing HEAD module fixture.");
        return Parser.ParseAsync(source, new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (url, _) => ValueTask.FromResult(modules[url]),
        });
    }

    private static async Task<string> Observe(Func<Task<EvalResult<Result>>> run)
    {
        try
        {
            var result = await run();
            if (!result.IsError) return "OK " + Neutral(result.Value);
            var inner = result.Error;
            while (inner is EvalError.WithContext context) inner = context.Inner;
            return "FAIL " + inner switch
            {
                EvalError.LocalOnlyProperty local => $"LocalOnlyProperty:{local.PropertyName}",
                EvalError.UnknownName unknown => $"UnknownName:{unknown.Name}",
                EvalError.UnknownProperty property => $"UnknownProperty:{property.PropertyName}",
                _ => inner.GetType().Name,
            };
        }
        catch (Exception exception)
        {
            return "EXCEPTION " + exception.GetType().Name;
        }
    }

    private static string Neutral(Result result) => result switch
    {
        Result.Atom a => KatLang.Rendering.ValueTextRenderer.FormatNumberInvariant(a.Value),
        Result.Str s => "'" + s.Value + "'",
        Result.Bool b => KatLang.Rendering.ValueTextRenderer.FormatBool(b.Value),
        Result.SequenceValue g => "S[" + string.Join(", ", g.Items.Select(Neutral)) + "]",
        Result.ListValue l => "L[" + string.Join(", ", l.Items.Select(Neutral)) + "]",
        _ => result.GetType().Name,
    };

    // Every declaration reachable through property values (user algorithms and aliases), with its dotted path.
    private static IEnumerable<(string Path, Property Property)> Declarations(Algorithm algorithm, string path)
    {
        IReadOnlyList<Property> properties = algorithm switch
        {
            Algorithm.User user => user.Properties,
            Algorithm.Alias alias => alias.Properties,
            _ => [],
        };
        foreach (var property in properties)
        {
            var at = $"{path}.{property.Name}";
            yield return (at, property);
            foreach (var nested in Declarations(property.Value, at))
                yield return nested;
        }
    }

    /// <summary>
    /// Writes the scratch console project into <paramref name="directory"/>: a project file that compiles THIS source
    /// file (<paramref name="probeSource"/>) against the KatLang project passed as <c>-p:KatLangHeadProject=…</c> (an
    /// export of <see cref="Revision"/>), named <c>KatLang.Benchmarks</c> for KatLang's existing
    /// <c>InternalsVisibleTo</c> (<c>Property.CaptureRequirements</c>), and its two-line entry point.
    /// </summary>
    public static void WriteProject(string directory, string probeSource)
    {
        if (!File.Exists(probeSource)) throw new FileNotFoundException("The head probe source is missing.", probeSource);
        Directory.CreateDirectory(directory);
        File.WriteAllText(Path.Combine(directory, ProjectFileName), $"""
            <Project Sdk="Microsoft.NET.Sdk">
              <!-- Generated by ExposureCensusTests (emit-head): the E-18 census HEAD probe. Build with
                   -p:KatLangHeadProject=PATH, the dotnet/src/KatLang/KatLang.csproj of an export of {Revision} (CensusHeadProbe.Steps). -->
              <PropertyGroup>
                <OutputType>Exe</OutputType>
                <TargetFramework>net11.0</TargetFramework>
                <Nullable>enable</Nullable>
                <ImplicitUsings>enable</ImplicitUsings>
                <AssemblyName>KatLang.Benchmarks</AssemblyName>
                <RootNamespace>HeadProbe</RootNamespace>
                <TreatWarningsAsErrors>false</TreatWarningsAsErrors>
              </PropertyGroup>
              <ItemGroup>
                <ProjectReference Include="$(KatLangHeadProject)" />
                <Compile Include="{probeSource}" Link="CensusHeadProbe.cs" />
              </ItemGroup>
              <Target Name="RequireKatLangHeadProject" BeforeTargets="Restore;CollectPackageReferences;ResolveProjectReferences;Build">
                <Error Condition="'$(KatLangHeadProject)' == '' Or !Exists('$(KatLangHeadProject)')"
                       Text="Pass -p:KatLangHeadProject=PATH, the dotnet/src/KatLang/KatLang.csproj of an export of {Revision}." />
              </Target>
            </Project>

            """);
        File.WriteAllText(Path.Combine(directory, EntryFileName), """
            // Generated by ExposureCensusTests (emit-head): usage HeadProbe <head-programs.tsv> <head.out>.
            if (args.Length != 2) { Console.Error.WriteLine("usage: HeadProbe <head-programs.tsv> <head.out>"); return 2; }
            var (programs, duplicates) = await KatLang.Tests.ExposureCensus.CensusHeadProbe.RunAsync(args[0], args[1]);
            Console.WriteLine($"programs {programs}; duplicate metadata paths skipped {duplicates}");
            return 0;

            """);
    }

    /// <summary>The commands that turn <c>emit-head</c>'s output into <c>head.out</c> (bash; <c>OUT</c> is the census output directory).</summary>
    public static IReadOnlyList<string> Steps(string outDirectory) =>
    [
        $"# 1. Export {Revision} (KatLang.csproj imports KatLangVersion.props and packs the root's LICENSE, README.md and NOTICE):",
        $"mkdir -p <scratch>/{Revision} && git archive {Revision} dotnet/src/KatLang KatLangVersion.props global.json LICENSE README.md NOTICE PATENTS | tar -x -C <scratch>/{Revision}",
        "# 2. Build the probe against the export (it links this repository's CensusHeadProbe.cs):",
        $"dotnet build \"{Path.Combine(outDirectory, "head-probe", ProjectFileName)}\" -p:KatLangHeadProject=<scratch>/{Revision}/dotnet/src/KatLang/KatLang.csproj -o <scratch>/head-probe-bin",
        "# 3. Run it over every probe program:",
        $"dotnet <scratch>/head-probe-bin/KatLang.Benchmarks.dll \"{Path.Combine(outDirectory, "head-programs.tsv")}\" \"{Path.Combine(outDirectory, "head.out")}\"",
        "# 4. Compare: KATLANG_EXPOSURE_CENSUS=check-head with the same KATLANG_EXPOSURE_CENSUS_OUT.",
    ];
}
