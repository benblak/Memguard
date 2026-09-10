-- INSACERMO V0.11 — MINIMAL FOUR-WAY DEMO
-- Same engine, same ternary contract family, four operational outcomes.
namespace Insacermo

open TState EPlan

/-- ACT: the current ambiguity is already covered by an available plan. -/
def fourwayActInput : ExecInput TState EPlan where
  sys := executableTernarySystem
  ambiguity := ternaryAB
  available := ternaryAvailable
  budget := 1
  probes := []
  repairs := []
  forgets := []
  searchComplete := true

local instance fourwayActGoodDecidable : DecidableRel fourwayActInput.sys.good := by
  simpa [fourwayActInput] using executableTernaryGoodDecidable

local instance fourwayProbeGoodDecidable : DecidableRel ternaryExecProbeInput.sys.good := by
  simpa [ternaryExecProbeInput] using executableTernaryGoodDecidable

local instance fourwayRepairGoodDecidable : DecidableRel ternaryExecRepairInput.sys.good := by
  simpa [ternaryExecRepairInput] using executableTernaryGoodDecidable

local instance fourwayRefuseGoodDecidable : DecidableRel ternaryExecRefuseInput.sys.good := by
  simpa [ternaryExecRefuseInput] using executableTernaryGoodDecidable

#eval compile fourwayActInput
#eval compile ternaryExecProbeInput
#eval compile ternaryExecRepairInput
#eval compile ternaryExecRefuseInput

example : (compile fourwayActInput).label = ExecLabel.act := by native_decide
example : (compile ternaryExecProbeInput).label = ExecLabel.probe := by native_decide
example : (compile ternaryExecRepairInput).label = ExecLabel.repair := by native_decide
example : (compile ternaryExecRefuseInput).label = ExecLabel.refuse := by native_decide

example : OperationalSound fourwayActInput (compile fourwayActInput) :=
  compile_operational_sound fourwayActInput
example : OperationalSound ternaryExecProbeInput (compile ternaryExecProbeInput) :=
  compile_operational_sound ternaryExecProbeInput
example : OperationalSound ternaryExecRepairInput (compile ternaryExecRepairInput) :=
  compile_operational_sound ternaryExecRepairInput
example : OperationalSound ternaryExecRefuseInput (compile ternaryExecRefuseInput) :=
  compile_operational_sound ternaryExecRefuseInput

end Insacermo
