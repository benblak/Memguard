-- INSACERMO V0.11 — CAPABILITY-FORGETTING REVERSAL
-- Claim tested: the same coarse information state can be non-actionable under
-- one capability set and actionable under a strict capability expansion,
-- without acquiring any new observation.
namespace Insacermo

open TState EPlan

/-- Stage 1: current ambiguity {a,b} is actionable, but forgetting enough to
    enlarge it to {a,b,c} is unsafe under the current capabilities. -/
def capabilityForgetPreserveInput : ExecInput TState EPlan where
  sys := executableTernarySystem
  ambiguity := ternaryAB
  available := ternaryAvailable
  budget := 1
  probes := []
  repairs := []
  forgets := [ternaryWorlds]
  searchComplete := true

/-- Stage 2: after the distinction has been forgotten, the exact same coarse
    ambiguity {a,b,c} is not actionable under the original capabilities. -/
def capabilityForgetCoarseBefore : ExecInput TState EPlan where
  sys := executableTernarySystem
  ambiguity := ternaryWorlds
  available := ternaryAvailable
  budget := 1
  probes := []
  repairs := []
  forgets := []
  searchComplete := true

/-- Stage 3: no new information is acquired.  The ambiguity is still exactly
    {a,b,c}; only the capability list is enlarged by universalOne. -/
def capabilityForgetCoarseAfter : ExecInput TState EPlan where
  sys := executableTernarySystem
  ambiguity := ternaryWorlds
  available := ternaryAvailable ++ execTernaryRepair
  budget := 1
  probes := []
  repairs := []
  forgets := []
  searchComplete := true

local instance preserveGoodDecidable :
    DecidableRel capabilityForgetPreserveInput.sys.good := by
  simpa [capabilityForgetPreserveInput] using executableTernaryGoodDecidable

local instance coarseBeforeGoodDecidable :
    DecidableRel capabilityForgetCoarseBefore.sys.good := by
  simpa [capabilityForgetCoarseBefore] using executableTernaryGoodDecidable

local instance coarseAfterGoodDecidable :
    DecidableRel capabilityForgetCoarseAfter.sys.good := by
  simpa [capabilityForgetCoarseAfter] using executableTernaryGoodDecidable

#eval compile capabilityForgetPreserveInput
#eval compile capabilityForgetCoarseBefore
#eval compile capabilityForgetCoarseAfter

example : (compile capabilityForgetPreserveInput).label = ExecLabel.preserve := by
  native_decide

example : (compile capabilityForgetCoarseBefore).label = ExecLabel.refuse := by
  native_decide

example : (compile capabilityForgetCoarseAfter).label = ExecLabel.act := by
  native_decide

example : (compile capabilityForgetCoarseAfter).strategy = some EPlan.universalOne := by
  native_decide

/-- The information state is literally unchanged between the REFUSE and ACT
    cases.  Only capability changes. -/
example : capabilityForgetCoarseBefore.ambiguity = capabilityForgetCoarseAfter.ambiguity := by
  rfl

example : capabilityForgetCoarseBefore.probes = capabilityForgetCoarseAfter.probes := by
  rfl

example : OperationalSound capabilityForgetPreserveInput
    (compile capabilityForgetPreserveInput) :=
  compile_operational_sound capabilityForgetPreserveInput

example : OperationalSound capabilityForgetCoarseBefore
    (compile capabilityForgetCoarseBefore) :=
  compile_operational_sound capabilityForgetCoarseBefore

example : OperationalSound capabilityForgetCoarseAfter
    (compile capabilityForgetCoarseAfter) :=
  compile_operational_sound capabilityForgetCoarseAfter

end Insacermo
