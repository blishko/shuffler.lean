module

public import Shuffler.Planner.Run.Defs

@[expose] public section

namespace Shuffler

-- Plans the shuffle under both wildcard policies when the choice matters: copies sitting in wildcard slots are
-- first left there and, if any demand was answered by such a copy, planned again taking them. The cheaper
-- successful plan (fewest spills, then fewest operations) is returned: its emitted stack, trace and plan, and the
-- spills it ends up with. A `result` of `none` is `StackTooDeep`, where the C++ leaves the source and the spills
-- untouched.
-- The reachable stack depth is fixed at MAX_SWAP_DEPTH, so the C++ assert on it always holds.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:1050-1064, 1078-1093.
def shuffle (source target : Stack) (spills : SpillSet) (spillingAllowed : Bool) :
    Except ShuffleErr (Planner.Result source target) := do
  _ ← requires (source.length ≤ 1024) "source stack exceeds 1024 slots"
  _ ← requires (target.length ≤ 1024) "target stack exceeds 1024 slots"
  _ ← requires (∀ slot ∈ target, slot.is_junk ∨ slot.can_be_freely_generated ∨ slot ∈ source ∨ spills.is_spilled slot)
    "target slot neither on the stack nor generatable"

  let leave ← Planner.run source target spills spillingAllowed .Leave
  if ¬ leave.sawWildcardCopy then
    return leave
  let take ← Planner.run source target spills spillingAllowed .Take
  let useTake := match leave.result, take.result with
    | some leaveResult, some takeResult =>
      decide (Prod.lexLt (take.state.spills.card, takeResult.trace.length)
        (leave.state.spills.card, leaveResult.trace.length))
    | leaveResult, _ => leaveResult.isNone
  return if useTake then take else leave

end Shuffler
