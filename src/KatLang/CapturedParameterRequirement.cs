namespace KatLang;

internal readonly record struct CapturedParameterRequirement(string Name, int OwnerDepth);
