module

public import Shuffler.Shuffle.Defs
import Shuffler.Planner.Run.Theorems
import all Batteries.Tactic.PrintOpaques
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.Range.Basic
import all Init.Data.List.Sort.Basic
import all Init.Prelude

@[expose] public section

namespace Shuffler

-- Within the stack limit and with every target slot available, every shuffle returns a result, including a
-- `StackTooDeep` one.
theorem shuffle_ok (source target : Stack) (spills : SpillSet) (spillingAllowed : Bool)
    (hsource : source.length ≤ 1024) (htarget : target.length ≤ 1024)
    (havailable : ∀ value ∈ target, value.is_junk ∨ value.can_be_freely_generated ∨
      value ∈ source ∨ spills.is_spilled value)
    (hlabels : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel) :
    ∃ result, shuffle source target spills spillingAllowed = .ok result := by
  obtain ⟨leave, hleave⟩ := Planner.run_ok source target spills spillingAllowed .Leave havailable hlabels
  obtain ⟨take, htake⟩ := Planner.run_ok source target spills spillingAllowed .Take havailable hlabels
  unfold shuffle
  rw [requires_of_true _ hsource, except_ok_bind, requires_of_true _ htarget, except_ok_bind,
    requires_of_true _ havailable, except_ok_bind, hleave, except_ok_bind]
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · rw [htake, except_ok_bind]
    exact ⟨_, rfl⟩

theorem shuffle_no_assertion (source target : Stack) (spills : SpillSet) (spillingAllowed : Bool)
    (hsource : source.length ≤ 1024) (htarget : target.length ≤ 1024)
    (havailable : ∀ value ∈ target, value.is_junk ∨ value.can_be_freely_generated ∨
      value ∈ source ∨ spills.is_spilled value)
    (hlabels : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel)
    (reason : String) :
    shuffle source target spills spillingAllowed ≠ .error (.assertion reason) := by
  obtain ⟨result, hr⟩ := shuffle_ok source target spills spillingAllowed hsource htarget havailable hlabels
  rw [hr]
  intro he
  cases he

/-- info: 'Shuffler.shuffle' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques shuffle

/-- info: 'Shuffler.shuffle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shuffle

/-- info: 'Shuffler.shuffle_ok' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques shuffle_ok

/-- info: 'Shuffler.shuffle_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shuffle_ok

/-- info: 'Shuffler.shuffle_no_assertion' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques shuffle_no_assertion

/-- info: 'Shuffler.shuffle_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shuffle_no_assertion

end Shuffler
