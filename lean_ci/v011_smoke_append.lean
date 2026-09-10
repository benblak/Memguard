
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

#eval compile ternaryExecActInput
#eval compile ternaryExecPreserveInput
#eval compile ternaryExecProbeInput
#eval compile ternaryExecRepairInput
#eval compile ternaryExecRefuseInput
#eval compile ternaryExecIncompleteInput

example : (compile ternaryExecActInput).label = .act := by native_decide
example : (compile ternaryExecActInput).strategy = some .ab := by native_decide

example : (compile ternaryExecPreserveInput).label = .preserve := by native_decide
example : (compile ternaryExecPreserveInput).candidateIndex = some 0 := by native_decide
example : (compile ternaryExecPreserveInput).strategy = some .ab := by native_decide

example : (compile ternaryExecProbeInput).label = .probe := by native_decide
example : (compile ternaryExecProbeInput).candidateIndex = some 0 := by native_decide
example : (compile ternaryExecProbeInput).strategy = none := by native_decide

example : (compile ternaryExecRepairInput).label = .repair := by native_decide
example : (compile ternaryExecRepairInput).candidateIndex = some 0 := by native_decide
example : (compile ternaryExecRepairInput).strategy = some .universalOne := by native_decide

example : (compile ternaryExecRefuseInput).label = .refuse := by native_decide
example : (compile ternaryExecRefuseInput).candidateIndex = none := by native_decide
example : (compile ternaryExecRefuseInput).strategy = none := by native_decide

example : (compile ternaryExecIncompleteInput).label = .incomplete := by native_decide
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
