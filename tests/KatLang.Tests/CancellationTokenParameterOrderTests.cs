using System.Reflection;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

/// <summary>
/// The repository convention: a <see cref="CancellationToken"/> is ALWAYS the last parameter of
/// a parameter list — in internal and private helpers as much as in public API — so a
/// parameter added to a signature that already ends with a token goes BEFORE the token. It
/// regressed twice by appending after an existing token (host operations, August 2026; the
/// random seed and the deferred-module-region flag, September 2026, fifteen internal
/// signatures), each time found only by review. The scan below reads every declared parameter
/// list of the KatLang assembly through reflection — methods, constructors (positional records
/// included), local functions, and delegate signatures — so a violation fails here instead.
/// Several tokens may end a list together; nothing may follow one.
/// </summary>
public class CancellationTokenParameterOrderTests
{
    private const BindingFlags DeclaredMembers =
        BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly;

    [Fact]
    public void EveryParameterListOfTheKatLangAssembly_EndsWithItsCancellationTokens()
    {
        var (violations, tokenLists) = Scan(typeof(KatLangEngine).Assembly.GetTypes());

        // The evaluator and loader entry points take tokens, so an empty scan is a broken scan.
        Assert.True(tokenLists > 0, "The scan found no parameter list with a CancellationToken.");
        Assert.Empty(violations);
    }

    [Fact]
    public void Scan_FlagsEveryParameterAfterAToken_AndSeesThroughLocalFunctionClosures()
    {
        var (violations, _) = Scan(
            [typeof(OrderFixture), typeof(OrderFixture.MisorderedHandler), typeof(OrderFixture.OrderedHandler)]);

        string[] expected =
        [
            "MisorderedHandler.Invoke(CancellationToken cancellationToken, String name)",
            "OrderFixture..ctor(CancellationToken cancellationToken, Int64? randomSeed)",
            "OrderFixture.Misordered(CancellationToken cancellationToken, Int32 value)",
            "OrderFixture.TokenFirst(CancellationToken cancellationToken, Boolean flag)",
        ];
        Assert.Equal(expected, violations.Order(StringComparer.Ordinal));
    }

    private static (List<string> Violations, int TokenLists) Scan(IEnumerable<Type> types)
    {
        var violations = new List<string>();
        var tokenLists = 0;
        foreach (var type in types)
        {
            foreach (var member in type.GetMethods(DeclaredMembers).Concat<MethodBase>(type.GetConstructors(DeclaredMembers)))
            {
                if (DeclaredParameters(member) is not { } parameters)
                    continue;

                var firstToken = Array.FindIndex(parameters, IsCancellationToken);
                if (firstToken < 0)
                    continue;

                tokenLists++;
                if (!parameters[firstToken..].All(IsCancellationToken))
                    violations.Add(Render(member, parameters));
            }
        }

        return (violations, tokenLists);
    }

    /// <summary>
    /// The parameter list the source declared, or <see langword="null"/> for a member whose
    /// list the source does not own: a delegate's <c>BeginInvoke</c> appends its callback and
    /// state after the signature and its constructor is the runtime's; a name containing
    /// <c>&lt;</c> is a compiler-generated method (a lambda takes the list of the delegate it
    /// converts to) or an explicit implementation of a generic interface (its contract's list).
    /// Among those only a local function declares its own list, compiled with its by-ref
    /// closure structs appended AFTER the declared parameters, so those are stripped.
    /// </summary>
    private static ParameterInfo[]? DeclaredParameters(MethodBase member)
    {
        if (member.DeclaringType!.IsSubclassOf(typeof(MulticastDelegate)))
            return member.Name == "Invoke" ? member.GetParameters() : null;

        if (!member.Name.Contains('<'))
            return member.GetParameters();

        if (!IsLocalFunction(member))
            return null;

        var parameters = member.GetParameters();
        var declaredCount = parameters.Length;
        while (declaredCount > 0
            && parameters[declaredCount - 1].ParameterType is { IsByRef: true } closure
            && closure.GetElementType()!.IsDefined(typeof(CompilerGeneratedAttribute), inherit: false))
        {
            declaredCount--;
        }

        return parameters[..declaredCount];
    }

    private static bool IsLocalFunction(MethodBase member) => member.Name.Contains(">g__");

    private static bool IsCancellationToken(ParameterInfo parameter)
    {
        var type = parameter.ParameterType.IsByRef ? parameter.ParameterType.GetElementType()! : parameter.ParameterType;
        return (Nullable.GetUnderlyingType(type) ?? type) == typeof(CancellationToken);
    }

    private static string Render(MethodBase member, IEnumerable<ParameterInfo> parameters)
    {
        // A local function's metadata name is <Container>g__Name|n_m; the numbering is the compiler's.
        var name = IsLocalFunction(member)
            ? member.Name[(member.Name.IndexOf(">g__", StringComparison.Ordinal) + 4)..member.Name.IndexOf('|')]
            : member.Name;
        return $"{member.DeclaringType!.Name}.{name}({string.Join(", ", parameters.Select(p => $"{TypeName(p.ParameterType)} {p.Name}"))})";
    }

    private static string TypeName(Type type)
        => type.IsByRef ? TypeName(type.GetElementType()!) + "&"
            : Nullable.GetUnderlyingType(type) is { } underlying ? TypeName(underlying) + "?"
            : type.Name;

    /// <summary>Violations and compliant shapes side by side; never executed, only scanned.</summary>
    private sealed class OrderFixture
    {
        internal OrderFixture(CancellationToken cancellationToken, long? randomSeed) { }

        internal OrderFixture(long? randomSeed, CancellationToken cancellationToken) { }

        internal delegate void MisorderedHandler(CancellationToken cancellationToken, string name);

        internal delegate void OrderedHandler(string name, CancellationToken cancellationToken);

        internal static void TokenFirst(CancellationToken cancellationToken, bool flag) { }

        internal static void TokenLast(bool flag, CancellationToken cancellationToken) { }

        internal static void TokensLast(bool flag, CancellationToken first, CancellationToken second) { }

        internal static int LocalFunctions(int seed)
        {
            // Both capture `seed` without becoming delegates, so each is compiled with a by-ref
            // closure parameter after its declared ones.
            return Ordered(1, CancellationToken.None) + Misordered(CancellationToken.None, 2);

            int Ordered(int value, CancellationToken cancellationToken) => seed + value;

            int Misordered(CancellationToken cancellationToken, int value) => seed + value;
        }
    }
}
