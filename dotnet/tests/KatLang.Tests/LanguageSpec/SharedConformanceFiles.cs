using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.Json.Serialization.Metadata;

namespace KatLang.Tests.LanguageSpec;

internal sealed class SharedConformanceFiles
{
    private sealed record Manifest(int SchemaVersion, string[] Categories, string[] Files);
    private static readonly JsonSerializerOptions Options = CreateOptions();
    private readonly string directory;
    private readonly Manifest manifest;
    public IReadOnlyList<string> Categories { get; }

    public SharedConformanceFiles(string directory)
    {
        this.directory = directory;
        manifest = Read<Manifest>(Path.Combine(directory, "cases.json"));
        if (manifest.SchemaVersion != 3)
            throw new InvalidDataException($"Unsupported conformance schema version {manifest.SchemaVersion}.");

        var available = Directory.GetFiles(Path.Combine(directory, "features"), "*.json", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(directory, path).Replace(Path.DirectorySeparatorChar, '/'))
            .ToHashSet(StringComparer.Ordinal);
        foreach (var file in manifest.Files)
            if (!available.Remove(file))
                throw new InvalidDataException($"Missing or repeated feature file in cases.json: '{file}'.");
        if (available.Count > 0 || manifest.Files.Length == 0)
            throw new InvalidDataException($"List every feature file once in cases.json. Unlisted: {string.Join(", ", available)}.");
        Categories = Array.AsReadOnly(manifest.Categories);
    }

    public IEnumerable<SpecCase> ReadCases()
    {
        foreach (var file in manifest.Files)
        {
            var cases = Read<SpecCase[]>(Path.Combine(directory, file));
            if (cases.Length == 0)
                throw new InvalidDataException($"Empty conformance feature file: {file}.");
            foreach (var item in cases)
                yield return item ?? throw new InvalidDataException($"Null conformance case in {file}.");
        }
    }

    private static T Read<T>(string path) where T : class
    {
        try
        {
            using var input = File.OpenRead(path);
            return JsonSerializer.Deserialize<T>(input, Options) ?? throw new JsonException("Expected a JSON document.");
        }
        catch (JsonException error)
        {
            throw new InvalidDataException($"{path}: {error.Message}", error);
        }
    }

    private static JsonSerializerOptions CreateOptions()
    {
        // Only authored fields belong in a case. In particular, a fixture cannot supply the derived Lean AST.
        var resolver = new DefaultJsonTypeInfoResolver();
        resolver.Modifiers.Add(info =>
        {
            if (info.Type == typeof(SpecCase))
                foreach (var property in info.Properties.Where(p => p.Set is null).ToArray())
                    info.Properties.Remove(property);
        });
        return new JsonSerializerOptions
        {
            TypeInfoResolver = resolver,
            PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
            UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
            AllowDuplicateProperties = false,
            RespectNullableAnnotations = true,
            RespectRequiredConstructorParameters = true,
            Converters = { new JsonStringEnumConverter(allowIntegerValues: false), new CacheExpectationConverter() },
        };
    }

    private sealed class CacheExpectationConverter : JsonConverter<CachePublicationExpectation>
    {
        public override CachePublicationExpectation Read(ref Utf8JsonReader reader, Type type, JsonSerializerOptions options)
        {
            var counts = JsonSerializer.Deserialize<Dictionary<string, int>>(ref reader, options)
                ?? throw new JsonException("Expected property names and publication counts.");
            return CachePublicationExpectation.Of(counts.Select(entry => (entry.Key, entry.Value)).ToArray());
        }

        public override void Write(Utf8JsonWriter writer, CachePublicationExpectation value, JsonSerializerOptions options)
            => throw new NotSupportedException("Conformance files are authored directly.");
    }
}
