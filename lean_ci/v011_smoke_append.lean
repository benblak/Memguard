
-- ===== V0.11 RUNTIME SMOKE TESTS =====
namespace Insacermo

open TState EPlan

/-- Pure ACT case: pair ambiguity is feasible and no unsafe forgetting candidate is declared. -/
def ternaryExecActInput : ExecInput TState EPlan where
  sys := executableTernarySystem
  ambiguity := ternaryAB
  available := ternaryAvailable
  budget := 1
  probes := []
  repairs := []
  forgets := []
  searchComplete := true

local instance ternaryExecActGoodDecidable :
    DecidableRel ternaryExecActInput.sys.good := by
  simpa [ternaryExecActInput] using executableTernaryGoodDecidable

local instance ternaryExecPreserveGoodDecidable :
    DecidableRel ternaryExecPreserveInput.sys.good := by
  simpa [ternaryExecPreserveInput] using executableTernaryGoodDecidable

local instance ternaryExecProbeGoodDecidable :
    DecidableRel ternaryExecProbeInput.sys.good := by
  simpa [ternaryExecProbeInput] using executableTernaryGoodDecidable

local instance ternaryExecRepairGoodDecidable :
    DecidableRel ternaryExecRepairInput.sys.good := by
  simpa [ternaryExecRepairInput] using executableTernaryGoodDecidable

local instance ternaryExecRefuseGoodDecidable :
    DecidableRel ternaryExecRefuseInput.sys.good := by
  simpa [ternaryExecRefuseInput] using executableTernaryGoodDecidable

local instance ternaryExecIncompleteGoodDecidable :
    DecidableRel ternaryExecIncompleteInput.sys.good := by
  simpa [ternaryExecIncompleteInput] using executableTernaryGoodDecidable

#eval compile ternaryExecActInput
#eval compile ternaryExecPreserveInput
#eval compile ternaryExecProbeInput
#eval compile ternaryExecRepairInput
#eval compile ternaryExecRefuseInput
#eval compile ternaryExecIncompleteInput

example : (compile ternaryExecActInput).label = ExecLabel.act := by native_decide
example : (compile ternaryExecActInput).strategy = some EPlan.ab := by native_decide

example : (compile ternaryExecPreserveInput).label = ExecLabel.preserve := by native_decide
example : (compile ternaryExecPreserveInput).candidateIndex = some 0 := by native_decide
example : (compile ternaryExecPreserveInput).strategy = some EPlan.ab := by native_decide

example : (compile ternaryExecProbeInput).label = ExecLabel.probe := by native_decide
example : (compile ternaryExecProbeInput).candidateIndex = some 0 := by native_decide
example : (compile ternaryExecProbeInput).strategy = none := by native_decide

example : (compile ternaryExecRepairInput).label = ExecLabel.repair := by native_decide
example : (compile ternaryExecRepairInput).candidateIndex = some 0 := by native_decide
example : (compile ternaryExecRepairInput).strategy = some EPlan.universalOne := by native_decide

example : (compile ternaryExecRefuseInput).label = ExecLabel.refuse := by native_decide
example : (compile ternaryExecRefuseInput).candidateIndex = none := by native_decide
example : (compile ternaryExecRefuseInput).strategy = none := by native_decide

example : (compile ternaryExecIncompleteInput).label = ExecLabel.incomplete := by native_decide
example : (compile ternaryExecIncompleteInput).candidateIndex = none := by native_decide
example : (compile ternaryExecIncompleteInput).strategy = none := by native_decide

/-- The generic soundness theorem applies to every concrete smoke-test input. -/
example : OperationalSound ternaryExecActInput (compile ternaryExecActInput) :=
  compile_operational_sound ternaryExecActInput
example : OperationalSound ternaryExecPreserveInput (compile ternaryExecPreserveInput) :=
  compile_operational_sound ternaryExecPreserveInput
example : OperationalSound ternaryExecProbeInput (compile ternaryExecProbeInput) :=
  compile_operational_sound ternaryExecProbeInput
example : OperationalSound ternaryExecRepairInput (compile ternaryExecRepairInput) :=
  compile_operational_sound ternaryExecRepairInput
example : OperationalSound ternaryExecRefuseInput (compile ternaryExecRefuseInput) :=
  compile_operational_sound ternaryExecRefuseInput
example : OperationalSound ternaryExecIncompleteInput (compile ternaryExecIncompleteInput) :=
  compile_operational_sound ternaryExecIncompleteInput

end Insacermo
