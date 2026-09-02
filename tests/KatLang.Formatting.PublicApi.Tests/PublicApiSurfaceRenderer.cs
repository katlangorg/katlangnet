using System.Globalization;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// Renders the public surface of an assembly as deterministic, human-reviewable
/// text — the format of <c>PublicApiBaseline.txt</c>. It reflects over the
/// COMPILED assembly, so the baseline pins what a NuGet consumer actually binds
/// against, not what the source appears to declare.
///
/// <para><b>Covered.</b> Every exported type plus protected and protected-
/// internal nested types reachable by an external subclass, with its kind —
/// class, record, struct, record struct, interface, enum, delegate — and its
/// static/abstract/sealed/readonly/ref modifiers; generic parameters with
/// variance and constraints (class, struct, unmanaged, new(), type constraints);
/// the base type when it is not object; the minimal set of implemented visible
/// interfaces (those not implied by the base type or by another listed
/// interface); and, DECLARED on the type only, every constructor, method,
/// operator (including conversions), property, indexer, event, field and
/// constant that is visible outside the assembly (public, protected, protected
/// internal). Members carry static/abstract/virtual/override/sealed,
/// required/init/readonly, parameter names and modifiers (this, params, ref,
/// out, in, ref readonly), optional-parameter defaults, constant values,
/// nullable reference annotations, tuple element names, and enum members with
/// their exact numeric values and underlying type. Compiler-generated public
/// members of records are real surface and are included. The API-significant
/// attributes Obsolete, Experimental, Flags, SetsRequiredMembers,
/// EditorBrowsable, and the compiler's nullable-flow contract attributes are
/// rendered.</para>
///
/// <para><b>Not covered.</b> Anything internal or private (a friend's view is
/// not the package contract); the assembly version and strong-name identity (a
/// release moves the version without changing the API); framework-inherited
/// members and interfaces implied by listed ones (so a runtime upgrade cannot
/// destabilize the baseline); the compiler-synthesized Obsolete marker on
/// constructors of types with required members (the <c>required</c> modifier
/// itself is rendered); attributes outside the compatibility allowlist; and
/// type forwarders. Compiler-synthesized record members are rendered as the
/// metadata declares them (a covariant
/// <c>&lt;Clone&gt;$</c> override appears as a new virtual slot).</para>
///
/// <para><b>Determinism.</b> Types are ordered by heading (ordinal), members by
/// kind, then name, then rendered signature (ordinal), enum members by numeric
/// value then name, and interfaces, constraints and attributes ordinally; all
/// formatting is culture-invariant; type names never carry assembly, version or
/// culture qualification; lines are joined with <c>\n</c>.</para>
/// </summary>
internal static class PublicApiSurfaceRenderer
{
    private const BindingFlags Declared =
        BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly;

    private static readonly Dictionary<Type, string> Keywords = new()
    {
        [typeof(void)] = "void",
        [typeof(object)] = "object",
        [typeof(string)] = "string",
        [typeof(bool)] = "bool",
        [typeof(char)] = "char",
        [typeof(byte)] = "byte",
        [typeof(sbyte)] = "sbyte",
        [typeof(short)] = "short",
        [typeof(ushort)] = "ushort",
        [typeof(int)] = "int",
        [typeof(uint)] = "uint",
        [typeof(long)] = "long",
        [typeof(ulong)] = "ulong",
        [typeof(float)] = "float",
        [typeof(double)] = "double",
        [typeof(decimal)] = "decimal",
        [typeof(nint)] = "nint",
        [typeof(nuint)] = "nuint",
    };

    private static readonly string[] KindLabels =
        ["const", "field", "ctor", "property", "indexer", "event", "method", "operator"];

    public static string Render(Assembly assembly)
        => Render(assembly.GetName().Name!, ConsumerVisibleTypes(assembly));

    /// <summary>
    /// <see cref="Assembly.GetExportedTypes"/> omits protected nested types,
    /// even though a consumer deriving from a public non-sealed declaring type
    /// can name and depend on them. Include that inheritance surface without
    /// admitting internal, private-protected, or protected members of a sealed
    /// declaring type that no external consumer can derive from.
    /// </summary>
    internal static IReadOnlyList<Type> ConsumerVisibleTypes(Assembly assembly)
        => assembly.GetExportedTypes()
            .Concat(assembly.GetTypes().Where(IsExternallyReachableProtectedNestedType))
            .Distinct()
            .ToList();

    public static string Render(string assemblyName, IEnumerable<Type> exportedTypes)
    {
        var nullability = new NullabilityInfoContext();
        var blocks = exportedTypes
            .Where(IsConsumerVisibleType)
            .Select(type => (Heading: TypeHeading(type), Text: RenderType(type, nullability)))
            .OrderBy(block => block.Heading, StringComparer.Ordinal)
            .ToList();

        var duplicates = blocks
            .GroupBy(block => block.Heading, StringComparer.Ordinal)
            .Where(group => group.Count() > 1)
            .Select(group => group.Key)
            .ToList();
        if (duplicates.Count > 0)
        {
            throw new InvalidOperationException(
                "Two exported types render under one heading (renderer canonicalization bug): " + string.Join(", ", duplicates));
        }

        var builder = new StringBuilder();
        builder.Append(Header(assemblyName));
        foreach (var block in blocks)
        {
            builder.Append('\n');
            builder.Append(block.Text);
        }

        return builder.ToString();
    }

    internal static string Header(string assemblyName)
        => $"# Public API surface of assembly {assemblyName}.\n" +
           "# GENERATED FILE - DO NOT EDIT BY HAND. Rendered from the compiled assembly by\n" +
           "# PublicApiSurfaceRenderer (tests/KatLang.Formatting.PublicApi.Tests). Regenerate with\n" +
           $"#   $env:{RegenerationFlags.PublicApi.Variable} = \"1\"; dotnet test .\\KatLang.slnx --filter PublicApiBaseline\n" +
           "# (that run rewrites this file and then fails by design: review the diff, clear the flag, rerun).\n" +
           "# One block per exported type in ordinal order of its heading; members sorted by kind, name,\n" +
           "# then signature; enum members by numeric value. See the renderer for the exact policy.\n";

    /// <summary>The heading (also the sort key) of a type block: its canonical name plus generic parameters.</summary>
    internal static string TypeHeading(Type type)
    {
        if (!type.IsGenericType)
            return BaseName(type);

        var parameters = type.GetGenericArguments()
            .Select(parameter => Variance(parameter) + parameter.Name)
            .ToArray();
        return NamedGenericType(type, parameters);
    }

    // ── Type blocks ─────────────────────────────────────────────────────────

    private static string RenderType(Type type, NullabilityInfoContext nullability)
    {
        var lines = new List<string> { TypeLine(type, nullability) };
        if (type.IsEnum)
        {
            lines.AddRange(EnumMembers(type));
        }
        else
        {
            lines.AddRange(ConstraintLines(type.IsGenericTypeDefinition ? type.GetGenericArguments() : []).Select(c => "  " + c));
            if (!IsDelegate(type))
                lines.AddRange(MemberLines(type, nullability));
        }

        return string.Join("\n", lines) + "\n";
    }

    private static string TypeLine(Type type, NullabilityInfoContext nullability)
    {
        var line = new StringBuilder();
        line.Append(AttributePrefix(type.GetCustomAttributesData()));
        line.Append(TypeAccess(type)).Append(' ');

        if (IsDelegate(type))
        {
            var invoke = type.GetMethod("Invoke")!;
            line.Append("delegate ")
                .Append(FormatReturn(invoke, nullability)).Append(' ')
                .Append(TypeHeading(type))
                .Append('(').Append(Parameters(invoke, nullability)).Append(')');
            return line.ToString();
        }

        line.Append(TypeKind(type)).Append(' ').Append(TypeHeading(type));
        var parents = Parents(type).ToList();
        if (parents.Count > 0)
            line.Append(" : ").Append(string.Join(", ", parents));
        return line.ToString();
    }

    private static string TypeKind(Type type)
    {
        if (type.IsEnum)
            return "enum";
        if (type.IsInterface)
            return "interface";

        var modifiers = new List<string>();
        if (type.IsValueType)
        {
            if (HasAttribute(type, "System.Runtime.CompilerServices.IsReadOnlyAttribute"))
                modifiers.Add("readonly");
            if (type.IsByRefLike)
                modifiers.Add("ref");
            modifiers.Add(IsRecordStruct(type) ? "record struct" : "struct");
            return string.Join(" ", modifiers);
        }

        if (type.IsAbstract && type.IsSealed)
        {
            modifiers.Add("static");
        }
        else
        {
            if (type.IsAbstract)
                modifiers.Add("abstract");
            if (type.IsSealed)
                modifiers.Add("sealed");
        }

        modifiers.Add(IsRecordClass(type) ? "record" : "class");
        return string.Join(" ", modifiers);
    }

    private static IEnumerable<string> Parents(Type type)
    {
        if (type.IsEnum)
        {
            yield return Format(Enum.GetUnderlyingType(type));
            yield break;
        }

        if (type.IsClass && type.BaseType is { } baseType && baseType != typeof(object))
            yield return Format(baseType);

        foreach (var name in MinimalInterfaces(type).Select(Format).OrderBy(name => name, StringComparer.Ordinal))
            yield return name;
    }

    /// <summary>
    /// The interfaces the type adds: all visible implemented interfaces minus
    /// those already implemented by the base type and those implied by another
    /// kept interface, so a framework interface hierarchy never fans out into
    /// the baseline.
    /// </summary>
    private static IEnumerable<Type> MinimalInterfaces(Type type)
    {
        var inherited = type.BaseType?.GetInterfaces().ToHashSet() ?? [];
        var own = type.GetInterfaces().Where(i => i.IsVisible && !inherited.Contains(i)).ToList();
        return own.Where(candidate => !own.Any(other => other != candidate && candidate.IsAssignableFrom(other)));
    }

    private static IEnumerable<string> EnumMembers(Type type)
        => type.GetFields(BindingFlags.Public | BindingFlags.Static)
            .Where(field => field.IsLiteral)
            .Select(field => (field.Name, Raw: field.GetRawConstantValue()!))
            .Select(member => (
                member.Name,
                Order: Convert.ToDecimal(member.Raw, CultureInfo.InvariantCulture),
                Text: Convert.ToString(member.Raw, CultureInfo.InvariantCulture)!))
            .OrderBy(member => member.Order)
            .ThenBy(member => member.Name, StringComparer.Ordinal)
            .Select(member => $"  {member.Name} = {member.Text}");

    // ── Members ─────────────────────────────────────────────────────────────

    private static IEnumerable<string> MemberLines(Type type, NullabilityInfoContext nullability)
    {
        var isInterface = type.IsInterface;
        var lines = new List<(int Rank, string Name, string Text)>();

        foreach (var field in type.GetFields(Declared))
        {
            if (field.IsSpecialName || !IsVisible(field))
                continue;
            lines.Add(IsConstant(field)
                ? (0, field.Name, ConstantLine(field))
                : (1, field.Name, FieldLine(field, nullability)));
        }

        foreach (var constructor in type.GetConstructors(Declared))
        {
            if (IsVisible(constructor))
                lines.Add((2, type.Name, ConstructorLine(type, constructor, nullability)));
        }

        foreach (var property in type.GetProperties(Declared))
        {
            var accessors = VisibleAccessors(property);
            if (accessors.Count == 0)
                continue;
            var isIndexer = property.GetIndexParameters().Length > 0;
            lines.Add((isIndexer ? 4 : 3, isIndexer ? "this" : property.Name,
                PropertyLine(property, accessors, isInterface, nullability)));
        }

        foreach (var evt in type.GetEvents(Declared))
        {
            var accessor = evt.AddMethod ?? evt.RemoveMethod;
            if (accessor is not null && IsVisible(accessor))
                lines.Add((5, evt.Name, EventLine(evt, accessor, isInterface, nullability)));
        }

        foreach (var method in type.GetMethods(Declared))
        {
            if (!IsVisible(method))
                continue;
            var isOperator = method.IsSpecialName && method.Name.StartsWith("op_", StringComparison.Ordinal);
            if (method.IsSpecialName && !isOperator)
                continue; // property and event accessors are rendered structurally on their owners
            lines.Add((isOperator ? 7 : 6, method.Name, MethodLine(method, isInterface, nullability)));
        }

        return lines
            .OrderBy(line => line.Rank)
            .ThenBy(line => line.Name, StringComparer.Ordinal)
            .ThenBy(line => line.Text, StringComparer.Ordinal)
            .Select(line => $"  {KindLabels[line.Rank],-8} {line.Text}");
    }

    private static string ConstantLine(FieldInfo field)
        => $"{AttributePrefix(field.GetCustomAttributesData())}{Access(field)} const {Format(field.FieldType)} {field.Name} = " +
           FormatConstant(ConstantValue(field), field.FieldType);

    private static string FieldLine(FieldInfo field, NullabilityInfoContext nullability)
    {
        var line = new StringBuilder();
        line.Append(AttributePrefix(field.GetCustomAttributesData()));
        line.Append(Access(field)).Append(' ');
        if (field.IsStatic)
            line.Append("static ");
        if (field.IsInitOnly)
            line.Append("readonly ");
        if (HasAttribute(field, "System.Runtime.CompilerServices.RequiredMemberAttribute"))
            line.Append("required ");
        line.Append(Format(field.FieldType, nullability.Create(field), useWriteState: false, TupleNames(field)));
        line.Append(' ').Append(field.Name);
        return line.ToString();
    }

    private static string ConstructorLine(Type type, ConstructorInfo constructor, NullabilityInfoContext nullability)
        => $"{AttributePrefix(constructor.GetCustomAttributesData())}{Access(constructor)} {StripArity(type.Name)}({Parameters(constructor, nullability)})";

    private static string PropertyLine(
        PropertyInfo property, List<(string Keyword, MethodInfo Accessor)> accessors, bool isInterface, NullabilityInfoContext nullability)
    {
        var propertyRank = accessors.Min(accessor => AccessRank(accessor.Accessor));
        var line = new StringBuilder();
        line.Append(AttributePrefix(PropertyContractAttributes(property)));
        line.Append(AccessName(propertyRank)).Append(' ');
        line.Append(MethodModifiers(accessors[0].Accessor, isInterface));
        if (HasAttribute(property, "System.Runtime.CompilerServices.RequiredMemberAttribute"))
            line.Append("required ");

        var info = nullability.Create(property);
        var propertyType = Format(property.PropertyType, info, useWriteState: property.GetMethod is null, TupleNames(property));
        if (property.PropertyType.IsByRef)
        {
            var getterReturn = property.GetMethod!.ReturnParameter;
            propertyType = (IsRefReadonly(getterReturn) ? "ref readonly " : "ref ") + propertyType;
        }
        line.Append(propertyType);
        line.Append(' ');

        var indexParameters = property.GetIndexParameters();
        if (indexParameters.Length > 0)
            line.Append("this[").Append(string.Join(", ", indexParameters.Select(p => Parameter(p, isThis: false, nullability)))).Append(']');
        else
            line.Append(property.Name);

        line.Append(" { ");
        foreach (var (keyword, accessor) in accessors)
        {
            var rank = AccessRank(accessor);
            if (rank != propertyRank)
                line.Append(AccessName(rank)).Append(' ');
            line.Append(keyword).Append("; ");
        }

        line.Append('}');
        return line.ToString();
    }

    private static string EventLine(EventInfo evt, MethodInfo accessor, bool isInterface, NullabilityInfoContext nullability)
        => $"{AttributePrefix(evt.GetCustomAttributesData())}{Access(accessor)} {MethodModifiers(accessor, isInterface)}" +
           $"{Format(evt.EventHandlerType!, nullability.Create(evt), useWriteState: false, null)} {evt.Name}";

    private static string MethodLine(MethodInfo method, bool isInterface, NullabilityInfoContext nullability)
    {
        var line = new StringBuilder();
        line.Append(AttributePrefix(method.GetCustomAttributesData()));
        line.Append(Access(method)).Append(' ');
        line.Append(MethodModifiers(method, isInterface));
        line.Append(FormatReturn(method, nullability)).Append(' ');
        line.Append(method.Name);
        if (method.IsGenericMethodDefinition)
            line.Append('<').Append(string.Join(", ", method.GetGenericArguments().Select(parameter => parameter.Name))).Append('>');
        line.Append('(').Append(Parameters(method, nullability)).Append(')');
        foreach (var constraint in ConstraintLines(method.IsGenericMethodDefinition ? method.GetGenericArguments() : []))
            line.Append(' ').Append(constraint);
        return line.ToString();
    }

    private static string MethodModifiers(MethodInfo method, bool isInterface)
    {
        var modifiers = new List<string>();
        if (method.IsStatic)
            modifiers.Add("static");

        if (isInterface)
        {
            if (!method.IsAbstract && !method.IsStatic)
                modifiers.Add("virtual"); // default interface implementation
        }
        else if (method.IsAbstract)
        {
            modifiers.Add("abstract");
        }
        else if (method.IsVirtual)
        {
            var isOverride = method.GetBaseDefinition() != method;
            if (isOverride)
            {
                if (method.IsFinal)
                    modifiers.Add("sealed");
                modifiers.Add("override");
            }
            else if (!method.IsFinal)
            {
                modifiers.Add("virtual");
            }
        }

        if (method.DeclaringType is { IsValueType: true } && HasAttribute(method, "System.Runtime.CompilerServices.IsReadOnlyAttribute"))
            modifiers.Add("readonly");

        return modifiers.Count == 0 ? "" : string.Join(" ", modifiers) + " ";
    }

    private static List<(string Keyword, MethodInfo Accessor)> VisibleAccessors(PropertyInfo property)
    {
        var accessors = new List<(string, MethodInfo)>();
        if (property.GetMethod is { } getter && IsVisible(getter))
            accessors.Add(("get", getter));
        if (property.SetMethod is { } setter && IsVisible(setter))
            accessors.Add((IsInit(setter) ? "init" : "set", setter));
        return accessors;
    }

    private static IEnumerable<CustomAttributeData> PropertyContractAttributes(PropertyInfo property)
    {
        foreach (var attribute in property.GetCustomAttributesData())
            yield return attribute;
        if (property.GetMethod is { } getter)
        {
            foreach (var attribute in getter.ReturnParameter.GetCustomAttributesData())
                yield return attribute;
        }
        if (property.SetMethod is { } setter)
        {
            foreach (var attribute in setter.GetParameters()[^1].GetCustomAttributesData())
                yield return attribute;
        }
    }

    private static bool IsInit(MethodInfo setter)
        => setter.ReturnParameter.GetRequiredCustomModifiers().Any(modifier => modifier == typeof(IsExternalInit));

    // ── Signatures ──────────────────────────────────────────────────────────

    private static string FormatReturn(MethodInfo method, NullabilityInfoContext nullability)
    {
        var prefix = AttributePrefix(method.ReturnParameter.GetCustomAttributesData());
        if (method.ReturnType.IsByRef)
        {
            prefix += IsRefReadonly(method.ReturnParameter) ? "ref readonly " : "ref ";
        }

        return prefix + Format(method.ReturnType, nullability.Create(method.ReturnParameter), useWriteState: false, TupleNames(method.ReturnParameter));
    }

    private static string Parameters(MethodBase method, NullabilityInfoContext nullability)
    {
        var parameters = method.GetParameters();
        var isExtension = HasAttribute(method, "System.Runtime.CompilerServices.ExtensionAttribute");
        return string.Join(", ", parameters.Select((parameter, index) => Parameter(parameter, isThis: index == 0 && isExtension, nullability)));
    }

    private static string Parameter(ParameterInfo parameter, bool isThis, NullabilityInfoContext nullability)
    {
        var text = new StringBuilder();
        text.Append(AttributePrefix(parameter.GetCustomAttributesData()));
        if (isThis)
            text.Append("this ");
        if (HasAttribute(parameter, "System.ParamArrayAttribute") || HasAttribute(parameter, "System.Runtime.CompilerServices.ParamCollectionAttribute"))
            text.Append("params ");

        if (parameter.ParameterType.IsByRef)
        {
            if (parameter.IsOut)
                text.Append("out ");
            else if (HasAttribute(parameter, "System.Runtime.CompilerServices.RequiresLocationAttribute"))
                text.Append("ref readonly ");
            else if (parameter.IsIn)
                text.Append("in ");
            else
                text.Append("ref ");
        }

        text.Append(Format(parameter.ParameterType, nullability.Create(parameter), useWriteState: !parameter.IsOut, TupleNames(parameter)));
        text.Append(' ').Append(parameter.Name ?? "arg");

        if (parameter.HasDefaultValue)
            text.Append(" = ").Append(FormatConstant(parameter.RawDefaultValue, parameter.ParameterType));
        else if (parameter.IsOptional)
            text.Append(" = default");

        return text.ToString();
    }

    private static IEnumerable<string> ConstraintLines(Type[] genericParameters)
    {
        foreach (var parameter in genericParameters)
        {
            var attributes = parameter.GenericParameterAttributes;
            var parts = new List<string>();
            if ((attributes & GenericParameterAttributes.ReferenceTypeConstraint) != 0)
                parts.Add(NullableMetadataFlag(parameter) == 2 ? "class?" : "class");

            var isValueType = (attributes & GenericParameterAttributes.NotNullableValueTypeConstraint) != 0;
            if (isValueType)
                parts.Add(HasAttribute(parameter, "System.Runtime.CompilerServices.IsUnmanagedAttribute") ? "unmanaged" : "struct");
            else if ((attributes & GenericParameterAttributes.ReferenceTypeConstraint) == 0
                     && NullableMetadataFlag(parameter) == 1)
                parts.Add("notnull");

            parts.AddRange(parameter.GetGenericParameterConstraints()
                .Where(constraint => constraint != typeof(ValueType))
                .Select(Format)
                .OrderBy(name => name, StringComparer.Ordinal));

            if (!isValueType && (attributes & GenericParameterAttributes.DefaultConstructorConstraint) != 0)
                parts.Add("new()");

            if (parts.Count > 0)
                yield return $"where {parameter.Name} : {string.Join(", ", parts)}";
        }
    }

    private static string Variance(Type parameter)
        => (parameter.GenericParameterAttributes & GenericParameterAttributes.Covariant) != 0 ? "out "
            : (parameter.GenericParameterAttributes & GenericParameterAttributes.Contravariant) != 0 ? "in "
            : "";

    // ── Type names ──────────────────────────────────────────────────────────

    internal static string Format(Type type)
        => Format(type, null, useWriteState: false, null);

    private static string Format(Type type, NullabilityInfo? info, bool useWriteState, Queue<string?>? tupleNames)
    {
        if (type.IsByRef)
            return Format(type.GetElementType()!, info, useWriteState, tupleNames);
        if (type.IsPointer)
            return Format(type.GetElementType()!, null, useWriteState, null) + "*";
        if (type.IsFunctionPointer)
        {
            var arguments = type.GetFunctionPointerParameterTypes()
                .Select(parameter => Format(parameter))
                .Append(Format(type.GetFunctionPointerReturnType()));
            var conventions = type.GetFunctionPointerCallingConventions()
                .Select(convention => convention.Name.Replace("CallConv", "", StringComparison.Ordinal))
                .OrderBy(name => name, StringComparer.Ordinal)
                .ToList();
            var callingConvention = conventions.Count == 0 ? "" : $" unmanaged[{string.Join(", ", conventions)}]";
            return $"delegate*{callingConvention}<{string.Join(", ", arguments)}>";
        }
        if (Nullable.GetUnderlyingType(type) is { } underlying)
            return Format(underlying, null, useWriteState, tupleNames) + "?";

        var annotated = info is not null && !type.IsValueType
            && (useWriteState ? info.WriteState : info.ReadState) == NullabilityState.Nullable;
        var suffix = annotated ? "?" : "";

        if (type.IsArray)
        {
            var element = Format(type.GetElementType()!, info?.ElementType, useWriteState, tupleNames);
            return $"{element}[{new string(',', type.GetArrayRank() - 1)}]{suffix}";
        }

        if (type.IsGenericParameter)
            return type.Name + suffix;

        if (type.IsGenericType)
        {
            var arguments = type.GetGenericArguments();
            var argumentInfos = info?.GenericTypeArguments;

            if (IsValueTuple(type) && arguments.Length >= 2)
            {
                var tupleElements = FlattenTupleElements(type, info).ToList();
                var elementNames = new string?[tupleElements.Count];
                if (tupleNames is not null)
                {
                    for (var i = 0; i < tupleElements.Count; i++)
                        elementNames[i] = tupleNames.Count > 0 ? tupleNames.Dequeue() : null;
                }

                var elements = tupleElements.Select((element, i) =>
                    Format(element.Type, element.Info, useWriteState, tupleNames)
                    + (elementNames[i] is { } name ? " " + name : ""));
                return $"({string.Join(", ", elements)}){suffix}";
            }

            var rendered = arguments.Select((argument, i) =>
                Format(argument, ArgumentInfo(argumentInfos, i), useWriteState, tupleNames)).ToArray();
            return NamedGenericType(type, rendered) + suffix;
        }

        return (Keywords.TryGetValue(type, out var keyword) ? keyword : BaseName(type)) + suffix;
    }

    private static NullabilityInfo? ArgumentInfo(NullabilityInfo[]? infos, int index)
        => infos is not null && index < infos.Length ? infos[index] : null;

    private static bool IsValueTuple(Type type)
        => type.IsGenericType && type.GetGenericTypeDefinition().FullName!.StartsWith("System.ValueTuple`", StringComparison.Ordinal);

    private static IEnumerable<(Type Type, NullabilityInfo? Info)> FlattenTupleElements(Type tuple, NullabilityInfo? info)
    {
        var arguments = tuple.GetGenericArguments();
        var infos = info?.GenericTypeArguments;
        var directCount = arguments.Length == 8 && IsValueTuple(arguments[7]) ? 7 : arguments.Length;
        for (var index = 0; index < directCount; index++)
            yield return (arguments[index], ArgumentInfo(infos, index));

        if (directCount == 7)
        {
            foreach (var rest in FlattenTupleElements(arguments[7], ArgumentInfo(infos, 7)))
                yield return rest;
        }
    }

    /// <summary>Namespace-qualified name with nested types joined by dots and no generic arity suffix.</summary>
    private static string BaseName(Type type)
    {
        var name = StripArity(type.Name);
        if (type.IsNested && type.DeclaringType is { } declaring)
            return BaseName(declaring) + "." + name;
        return string.IsNullOrEmpty(type.Namespace) ? name : type.Namespace + "." + name;
    }

    /// <summary>
    /// Reflection flattens the declaring type's generic arguments into every
    /// nested generic type. Put each argument back on the segment that declares
    /// it so Outer&lt;T&gt;.Inner&lt;U&gt; cannot collapse to Outer.Inner&lt;T, U&gt;.
    /// </summary>
    private static string NamedGenericType(Type type, IReadOnlyList<string> arguments)
    {
        var chain = new Stack<Type>();
        for (var current = type; current is not null; current = current.DeclaringType)
            chain.Push(current);

        var text = new StringBuilder();
        while (chain.Count > 0)
        {
            var segment = chain.Pop();
            if (text.Length == 0 && !string.IsNullOrEmpty(segment.Namespace))
                text.Append(segment.Namespace).Append('.');
            else if (text.Length > 0)
                text.Append('.');

            text.Append(StripArity(segment.Name));
            var inheritedCount = segment.DeclaringType?.GetGenericArguments().Length ?? 0;
            var totalCount = segment.IsGenericType ? segment.GetGenericArguments().Length : 0;
            var declaredCount = totalCount - inheritedCount;
            if (declaredCount > 0)
            {
                text.Append('<')
                    .Append(string.Join(", ", arguments.Skip(inheritedCount).Take(declaredCount)))
                    .Append('>');
            }
        }

        return text.ToString();
    }

    private static string StripArity(string name)
    {
        var tick = name.IndexOf('`');
        return tick < 0 ? name : name[..tick];
    }

    private static Queue<string?>? TupleNames(MemberInfo member)
        => TupleNames(member.GetCustomAttributesData());

    private static Queue<string?>? TupleNames(ParameterInfo parameter)
        => TupleNames(parameter.GetCustomAttributesData());

    private static Queue<string?>? TupleNames(IEnumerable<CustomAttributeData> attributes)
    {
        var attribute = attributes.FirstOrDefault(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.TupleElementNamesAttribute");
        if (attribute is null || attribute.ConstructorArguments.Count == 0)
            return null;

        var names = (IEnumerable<CustomAttributeTypedArgument>)attribute.ConstructorArguments[0].Value!;
        return new Queue<string?>(names.Select(argument => argument.Value as string));
    }

    // ── Constants and defaults ──────────────────────────────────────────────

    private static bool IsConstant(FieldInfo field)
        => field.IsLiteral || HasAttribute(field, "System.Runtime.CompilerServices.DecimalConstantAttribute");

    private static object? ConstantValue(FieldInfo field)
    {
        if (field.IsLiteral)
            return field.GetRawConstantValue();

        var attribute = field.GetCustomAttributesData().Single(item =>
            item.AttributeType.FullName == "System.Runtime.CompilerServices.DecimalConstantAttribute");
        var arguments = attribute.ConstructorArguments;
        var scale = Convert.ToByte(arguments[0].Value, CultureInfo.InvariantCulture);
        var negative = Convert.ToByte(arguments[1].Value, CultureInfo.InvariantCulture) != 0;
        var high = unchecked((int)Convert.ToUInt32(arguments[2].Value, CultureInfo.InvariantCulture));
        var middle = unchecked((int)Convert.ToUInt32(arguments[3].Value, CultureInfo.InvariantCulture));
        var low = unchecked((int)Convert.ToUInt32(arguments[4].Value, CultureInfo.InvariantCulture));
        return new decimal(low, middle, high, negative, scale);
    }

    internal static string FormatConstant(object? value, Type type)
    {
        if (type.IsByRef)
            type = type.GetElementType()!;

        if (value is null || value is DBNull || value is Missing)
            return type.IsValueType && Nullable.GetUnderlyingType(type) is null ? "default" : "null";

        var target = Nullable.GetUnderlyingType(type) ?? type;
        if (target.IsEnum)
        {
            var enumValue = Enum.ToObject(target, value);
            return Enum.IsDefined(target, enumValue)
                ? $"{BaseName(target)}.{enumValue}"
                : Convert.ToString(value, CultureInfo.InvariantCulture)!;
        }

        return value switch
        {
            string text => Quote(text),
            bool flag => flag ? "true" : "false",
            char character => "'" + Escape(character.ToString()) + "'",
            float single => single.ToString("R", CultureInfo.InvariantCulture),
            double number => number.ToString("R", CultureInfo.InvariantCulture),
            IFormattable formattable => formattable.ToString(null, CultureInfo.InvariantCulture),
            _ => Convert.ToString(value, CultureInfo.InvariantCulture) ?? "null",
        };
    }

    private static string Quote(string text) => "\"" + Escape(text) + "\"";

    private static string Escape(string text)
        => text.Replace("\\", "\\\\", StringComparison.Ordinal)
            .Replace("\"", "\\\"", StringComparison.Ordinal)
            .Replace("\r", "\\r", StringComparison.Ordinal)
            .Replace("\n", "\\n", StringComparison.Ordinal)
            .Replace("\t", "\\t", StringComparison.Ordinal);

    // ── Attributes and accessibility ────────────────────────────────────────

    /// <summary>
    /// The Obsolete marker the C# compiler synthesizes (paired with
    /// CompilerFeatureRequired) on every constructor of a type with required
    /// members so that older compilers refuse it. Modern consumers never see it
    /// as obsolescence, and the <c>required</c> modifier is rendered on the
    /// member itself, so it is not surface.
    /// </summary>
    private const string SynthesizedRequiredMembersObsoleteMessage =
        "Constructors of types with required members are not supported in this version of your compiler.";

    private static string AttributePrefix(IEnumerable<CustomAttributeData> attributes)
    {
        var rendered = new List<string>();
        foreach (var attribute in attributes)
        {
            var arguments = attribute.ConstructorArguments;
            switch (attribute.AttributeType.FullName)
            {
                case "System.ObsoleteAttribute":
                    var message = arguments.Count > 0 ? arguments[0].Value as string : null;
                    var isError = arguments.Count > 1 && arguments[1].Value is true;
                    if (isError && message == SynthesizedRequiredMembersObsoleteMessage)
                        break;
                    rendered.Add(message is null ? "[Obsolete]"
                        : isError ? $"[Obsolete({Quote(message)}, error: true)]"
                        : $"[Obsolete({Quote(message)})]");
                    break;
                case "System.Diagnostics.CodeAnalysis.ExperimentalAttribute":
                    rendered.Add($"[Experimental({Quote(arguments.Count > 0 ? arguments[0].Value as string ?? "" : "")})]");
                    break;
                case "System.FlagsAttribute":
                    rendered.Add("[Flags]");
                    break;
                case "System.Diagnostics.CodeAnalysis.SetsRequiredMembersAttribute":
                    rendered.Add("[SetsRequiredMembers]");
                    break;
                case "System.ComponentModel.EditorBrowsableAttribute":
                    var state = arguments.Count > 0 ? Convert.ToInt32(arguments[0].Value, CultureInfo.InvariantCulture) : 0;
                    rendered.Add($"[EditorBrowsable({(System.ComponentModel.EditorBrowsableState)state})]");
                    break;
                case "System.Diagnostics.CodeAnalysis.AllowNullAttribute":
                    rendered.Add("[AllowNull]");
                    break;
                case "System.Diagnostics.CodeAnalysis.DisallowNullAttribute":
                    rendered.Add("[DisallowNull]");
                    break;
                case "System.Diagnostics.CodeAnalysis.MaybeNullAttribute":
                    rendered.Add("[MaybeNull]");
                    break;
                case "System.Diagnostics.CodeAnalysis.NotNullAttribute":
                    rendered.Add("[NotNull]");
                    break;
                case "System.Diagnostics.CodeAnalysis.MaybeNullWhenAttribute":
                    rendered.Add($"[MaybeNullWhen({FormatBooleanArgument(arguments)})]");
                    break;
                case "System.Diagnostics.CodeAnalysis.NotNullWhenAttribute":
                    rendered.Add($"[NotNullWhen({FormatBooleanArgument(arguments)})]");
                    break;
                case "System.Diagnostics.CodeAnalysis.NotNullIfNotNullAttribute":
                    rendered.Add($"[NotNullIfNotNull({Quote(FormatStringArgument(arguments))})]");
                    break;
                case "System.Diagnostics.CodeAnalysis.DoesNotReturnAttribute":
                    rendered.Add("[DoesNotReturn]");
                    break;
                case "System.Diagnostics.CodeAnalysis.DoesNotReturnIfAttribute":
                    rendered.Add($"[DoesNotReturnIf({FormatBooleanArgument(arguments)})]");
                    break;
                case "System.Diagnostics.CodeAnalysis.MemberNotNullAttribute":
                    rendered.Add($"[MemberNotNull({string.Join(", ", FormatStringArguments(arguments).Select(Quote))})]");
                    break;
                case "System.Diagnostics.CodeAnalysis.MemberNotNullWhenAttribute":
                    rendered.Add($"[MemberNotNullWhen({FormatBooleanArgument(arguments)}, " +
                        $"{string.Join(", ", FormatStringArguments(arguments.Skip(1)).Select(Quote))})]");
                    break;
            }
        }

        rendered = rendered.Distinct(StringComparer.Ordinal).ToList();
        rendered.Sort(StringComparer.Ordinal);
        return rendered.Count == 0 ? "" : string.Join(" ", rendered) + " ";
    }

    private static string FormatBooleanArgument(IList<CustomAttributeTypedArgument> arguments)
        => arguments.Count > 0 && arguments[0].Value is true ? "true" : "false";

    private static string FormatStringArgument(IList<CustomAttributeTypedArgument> arguments)
        => arguments.Count > 0 ? arguments[0].Value as string ?? "" : "";

    private static IEnumerable<string> FormatStringArguments(IEnumerable<CustomAttributeTypedArgument> arguments)
    {
        foreach (var argument in arguments)
        {
            if (argument.Value is IEnumerable<CustomAttributeTypedArgument> items)
            {
                foreach (var item in items)
                    yield return item.Value as string ?? "";
            }
            else
            {
                yield return argument.Value as string ?? "";
            }
        }
    }

    private static byte? NullableMetadataFlag(Type genericParameter)
    {
        var attribute = genericParameter.GetCustomAttributesData().FirstOrDefault(item =>
            item.AttributeType.FullName == "System.Runtime.CompilerServices.NullableAttribute");
        if (attribute is null || attribute.ConstructorArguments.Count == 0)
            return null;

        var value = attribute.ConstructorArguments[0].Value;
        if (value is byte scalar)
            return scalar;
        if (value is IEnumerable<CustomAttributeTypedArgument> items)
            return items.Select(item => item.Value).OfType<byte>().FirstOrDefault();
        return null;
    }

    private static bool IsRefReadonly(ParameterInfo parameter)
        => HasAttribute(parameter, "System.Runtime.CompilerServices.IsReadOnlyAttribute")
           || parameter.GetRequiredCustomModifiers().Any(type =>
               type.FullName is "System.Runtime.CompilerServices.IsReadOnlyAttribute"
                   or "System.Runtime.CompilerServices.RequiresLocationAttribute")
           || parameter.GetOptionalCustomModifiers().Any(type =>
               type.FullName is "System.Runtime.CompilerServices.IsReadOnlyAttribute"
                   or "System.Runtime.CompilerServices.RequiresLocationAttribute");

    private static bool HasAttribute(MemberInfo member, string attributeFullName)
        => member.GetCustomAttributesData().Any(attribute => attribute.AttributeType.FullName == attributeFullName);

    private static bool HasAttribute(ParameterInfo parameter, string attributeFullName)
        => parameter.GetCustomAttributesData().Any(attribute => attribute.AttributeType.FullName == attributeFullName);

    private static bool IsVisible(MethodBase method) => method.IsPublic || method.IsFamily || method.IsFamilyOrAssembly;

    private static bool IsVisible(FieldInfo field) => field.IsPublic || field.IsFamily || field.IsFamilyOrAssembly;

    private static bool IsConsumerVisibleType(Type type)
        => type.IsVisible || IsExternallyReachableProtectedNestedType(type);

    private static bool IsExternallyReachableProtectedNestedType(Type type)
    {
        if (!type.IsNested || !(type.IsNestedFamily || type.IsNestedFamORAssem))
            return false;

        var declaring = type.DeclaringType!;
        return !declaring.IsSealed && IsConsumerVisibleType(declaring);
    }

    private static string Access(MethodBase method) => AccessName(AccessRank(method));

    private static string Access(FieldInfo field)
        => field.IsPublic ? "public" : field.IsFamilyOrAssembly ? "protected internal" : "protected";

    private static string TypeAccess(Type type)
        => !type.IsNested || type.IsNestedPublic ? "public"
            : type.IsNestedFamORAssem ? "protected internal"
            : "protected";

    private static int AccessRank(MethodBase method) => method.IsPublic ? 0 : method.IsFamilyOrAssembly ? 1 : 2;

    private static string AccessName(int rank) => rank switch { 0 => "public", 1 => "protected internal", _ => "protected" };

    private static bool IsDelegate(Type type)
        => typeof(Delegate).IsAssignableFrom(type) && type != typeof(Delegate) && type != typeof(MulticastDelegate);

    private static bool IsRecordClass(Type type)
        => type.GetMethod("<Clone>$", Declared) is not null;

    private static bool IsRecordStruct(Type type)
        => type.GetMethod("PrintMembers", Declared, null, [typeof(StringBuilder)], null) is not null;
}
