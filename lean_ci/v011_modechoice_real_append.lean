-- ===== V0.11 MODECHOICE REAL-DATA-DERIVED TEST =====
-- Source: MODECHOICE_PARETO_ACTIONABILITY.csv
-- CSV SHA256: 914efc0774d5803e8be3ee544ac618b2d516fc7a5810ba3b3b7e7ac505f1abe3
-- 14 rows x 4 observed modes; incidence relation generated mechanically from CSV.
namespace Insacermo

inductive MCWorld where
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7 | w8 | w9 | w10 | w11 | w12 | w13
  deriving DecidableEq, Repr

instance : Fintype MCWorld where
  elems := {.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7, .w8, .w9, .w10, .w11, .w12, .w13}
  complete := by intro x; cases x <;> simp

inductive MCPlan where
  | mode1 | mode2 | mode3 | mode4 | universalOne
  deriving DecidableEq, Repr

instance : Fintype MCPlan where
  elems := {.mode1, .mode2, .mode3, .mode4, .universalOne}
  complete := by intro x; cases x <;> simp

/-- Incidence copied mechanically from the CSV. `universalOne` is not in the
    CSV; it is a declared candidate repair and is excluded from current capability. -/
def mcGood : MCWorld → MCPlan → Prop
  | .w0, .mode1 => True
  | .w1, .mode1 => True
  | .w2, .mode1 => True
  | .w2, .mode2 => True
  | .w3, .mode1 => True
  | .w3, .mode2 => True
  | .w4, .mode1 => True
  | .w4, .mode2 => True
  | .w4, .mode4 => True
  | .w5, .mode1 => True
  | .w5, .mode2 => True
  | .w5, .mode4 => True
  | .w6, .mode1 => True
  | .w6, .mode3 => True
  | .w7, .mode1 => True
  | .w7, .mode3 => True
  | .w8, .mode1 => True
  | .w8, .mode3 => True
  | .w8, .mode4 => True
  | .w9, .mode1 => True
  | .w9, .mode3 => True
  | .w9, .mode4 => True
  | .w10, .mode1 => True
  | .w10, .mode4 => True
  | .w11, .mode1 => True
  | .w11, .mode4 => True
  | .w12, .mode4 => True
  | .w13, .mode4 => True
  | _, .universalOne => True
  | _, _ => False

def mcCost : MCPlan → Nat
  | _ => 1

def mcSystem : ContractSystem MCWorld MCPlan where
  good := mcGood
  cost := mcCost

instance mcGoodDecidable : DecidableRel mcSystem.good := by
  intro s π
  change Decidable (mcGood s π)
  cases s <;> cases π <;> simp only [mcGood] <;> infer_instance

def mcAllWorlds : List MCWorld := [.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7, .w8, .w9, .w10, .w11, .w12, .w13]
def mcAvailable : List MCPlan := [.mode1, .mode2, .mode3, .mode4]

def mcLocal : List MCWorld := [.w0, .w1]

def mcProbe : MCWorld → Nat
  | .w12 | .w13 => 1
  | _ => 0

def mcActInput : ExecInput MCWorld MCPlan where
  sys := mcSystem
  ambiguity := mcLocal
  available := mcAvailable
  budget := 1
  searchComplete := true

def mcPreserveInput : ExecInput MCWorld MCPlan where
  sys := mcSystem
  ambiguity := mcLocal
  available := mcAvailable
  budget := 1
  forgets := [mcAllWorlds]
  searchComplete := true

def mcProbeInput : ExecInput MCWorld MCPlan where
  sys := mcSystem
  ambiguity := mcAllWorlds
  available := mcAvailable
  budget := 1
  probes := [mcProbe]
  searchComplete := true

def mcRepairInput : ExecInput MCWorld MCPlan where
  sys := mcSystem
  ambiguity := mcAllWorlds
  available := mcAvailable
  budget := 1
  repairs := [[.universalOne]]
  searchComplete := true

def mcRefuseInput : ExecInput MCWorld MCPlan where
  sys := mcSystem
  ambiguity := mcAllWorlds
  available := mcAvailable
  budget := 1
  searchComplete := true

def mcIncompleteInput : ExecInput MCWorld MCPlan where
  sys := mcSystem
  ambiguity := mcAllWorlds
  available := mcAvailable
  budget := 1
  searchComplete := false

local instance mcActGoodDecidable : DecidableRel mcActInput.sys.good := by
  simpa [mcActInput] using mcGoodDecidable
local instance mcPreserveGoodDecidable : DecidableRel mcPreserveInput.sys.good := by
  simpa [mcPreserveInput] using mcGoodDecidable
local instance mcProbeGoodDecidable : DecidableRel mcProbeInput.sys.good := by
  simpa [mcProbeInput] using mcGoodDecidable
local instance mcRepairGoodDecidable : DecidableRel mcRepairInput.sys.good := by
  simpa [mcRepairInput] using mcGoodDecidable
local instance mcRefuseGoodDecidable : DecidableRel mcRefuseInput.sys.good := by
  simpa [mcRefuseInput] using mcGoodDecidable
local instance mcIncompleteGoodDecidable : DecidableRel mcIncompleteInput.sys.good := by
  simpa [mcIncompleteInput] using mcGoodDecidable

#eval compile mcActInput
#eval compile mcPreserveInput
#eval compile mcProbeInput
#eval compile mcRepairInput
#eval compile mcRefuseInput
#eval compile mcIncompleteInput

example : (compile mcActInput).label = ExecLabel.act := by native_decide
example : (compile mcActInput).strategy = some MCPlan.mode1 := by native_decide
example : (compile mcPreserveInput).label = ExecLabel.preserve := by native_decide
example : (compile mcPreserveInput).candidateIndex = some 0 := by native_decide
example : (compile mcPreserveInput).strategy = some MCPlan.mode1 := by native_decide
example : (compile mcProbeInput).label = ExecLabel.probe := by native_decide
example : (compile mcProbeInput).candidateIndex = some 0 := by native_decide
example : (compile mcRepairInput).label = ExecLabel.repair := by native_decide
example : (compile mcRepairInput).candidateIndex = some 0 := by native_decide
example : (compile mcRepairInput).strategy = some MCPlan.universalOne := by native_decide
example : (compile mcRefuseInput).label = ExecLabel.refuse := by native_decide
example : (compile mcIncompleteInput).label = ExecLabel.incomplete := by native_decide

def mcIsAdmissible (B : List MCWorld) : Bool :=
  (findAct? mcSystem mcAvailable 1 B).isSome

def mcAdmissibleCount : Nat :=
  (mcAllWorlds.powerset.filter mcIsAdmissible).length

def mcIsMinimalObstruction (B : List MCWorld) : Bool :=
  (! mcIsAdmissible B) && B.all (fun x => mcIsAdmissible (B.erase x))

def mcMinimalObstructions : List (List MCWorld) :=
  mcAllWorlds.powerset.filter mcIsMinimalObstruction

#eval mcAllWorlds.powerset.length
#eval mcAdmissibleCount
#eval mcMinimalObstructions.length
#eval mcMinimalObstructions

example : mcAllWorlds.powerset.length = 16384 := by native_decide
example : mcAdmissibleCount = 4288 := by native_decide
example : mcMinimalObstructions.length = 12 := by native_decide
example : mcMinimalObstructions.all (fun B => B.length == 2) = true := by native_decide

def mcExpectedBadPairs : List (List MCWorld) := [
  [.w0, .w12],
  [.w0, .w13],
  [.w1, .w12],
  [.w1, .w13],
  [.w2, .w12],
  [.w2, .w13],
  [.w3, .w12],
  [.w3, .w13],
  [.w6, .w12],
  [.w6, .w13],
  [.w7, .w12],
  [.w7, .w13]
]

example : mcExpectedBadPairs.length = 12 := by native_decide
example : mcExpectedBadPairs.all (fun B => ! mcIsAdmissible B) = true := by native_decide
example : mcExpectedBadPairs.all
    (fun B => B.all (fun x => mcIsAdmissible (B.erase x))) = true := by native_decide

example : OperationalSound mcActInput (compile mcActInput) :=
  compile_operational_sound mcActInput
example : OperationalSound mcPreserveInput (compile mcPreserveInput) :=
  compile_operational_sound mcPreserveInput
example : OperationalSound mcProbeInput (compile mcProbeInput) :=
  compile_operational_sound mcProbeInput
example : OperationalSound mcRepairInput (compile mcRepairInput) :=
  compile_operational_sound mcRepairInput
example : OperationalSound mcRefuseInput (compile mcRefuseInput) :=
  compile_operational_sound mcRefuseInput
example : OperationalSound mcIncompleteInput (compile mcIncompleteInput) :=
  compile_operational_sound mcIncompleteInput

end Insacermo
