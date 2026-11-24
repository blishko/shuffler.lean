module

public import Shuffler.RemoveSurplus.Defs
public import Shuffler.PermuteAtLowestHeight.Defs
public import Shuffler.BuildBottomUp.Defs

@[expose] public section

namespace Shuffler.Emission

-- Each attempt starts from the source and its planned mapping.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:302-340, 638-646.
def run (source target : Stack) (mapping : Mapping source.length target.length)
    (spills : SpillSet) : Except ShuffleErr (Result source target spills) := do
  let mut state : State source target spills := {
    planned_mapping := mapping
    stack := source
    trace := .Lit source
    mapping
    pending_generations := mapping.unmapped_target_slots
  }

  -- removes all surplus (slots that have no destination in the target)
  let result ← removeSurplus state
  if result.blocked.isSome then return result
  state := result.state

  let result ← Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight state
  if result.blocked.isSome then return result
  state := result.state

  buildBottomUp state

end Shuffler.Emission
