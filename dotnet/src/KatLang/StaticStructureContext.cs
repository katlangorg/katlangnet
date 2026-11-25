namespace KatLang;

/// <summary>A pass's physical level carries this shared contextual identity; it owns no structural memo.</summary>
internal sealed class StaticStructureContext(StaticStructureOperation operation, StaticScopeKey key)
{
    internal StaticStructureOperation Operation { get; } = operation;
    internal StaticScopeKey Key { get; } = key;
    internal StaticStructureContext Inside(Algorithm sourceOrPublishedView, Pattern? branchPattern = null)
        => new(Operation, Operation.ContextOf(Key, sourceOrPublishedView, branchPattern));
}
