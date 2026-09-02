-- Root of the hand-written CoreTests regression suite. The guards live in the sibling domain modules
-- under CoreTests/ (each importing CoreTests.Common); this module only aggregates them so that
-- `lake build CoreTests` elaborates every domain.
import CoreTests.Common
import CoreTests.CallableSignatures
import CoreTests.OutputSemantics
import CoreTests.DotCallSemantics
import CoreTests.HigherOrderCalls
import CoreTests.Conditionals
import CoreTests.Strings
import CoreTests.SequenceCallbackBuiltins
import CoreTests.CollectionBuiltins
import CoreTests.SequenceBuiltinRegressions
import CoreTests.CollectingParameters
import CoreTests.Numerics
import CoreTests.DotReceiverSegments
import CoreTests.ParityGuards
import CoreTests.ValueBoundary
import CoreTests.ListValues
import CoreTests.CollectingBindings
import CoreTests.OutputBundle
