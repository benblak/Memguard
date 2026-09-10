from pathlib import Path

RAW_SHA = "d2d72c1db440f8ffce01f58ed39fc1145569ec1703970dac1636c154fc01fd8e"
PROFILE_GROUPS = {1:[175,191],8:[5,15,22,26,27,28,51,56,58,59,60,61,63,65,67,68,69,70,75,76,77,79,80,85,95,99,100,102,104,105,108,110,123,124,126,127,128,132,133,135,138,139,140,141,142,143,144,148,149,150,152,154,158,164,166,167,170,174,179,186,201,206,210],9:[1,2,3,4,6,7,8,9,10,11,12,13,14,20,21,23,25,29,31,32,33,35,36,38,39,40,41,42,43,44,45,47,48,49,50,52,53,54,55,78,81,82,84,86,87,89,90,91,93,94,96,98,101,103,107,109,111,112,113,114,115,116,119,120,121,122,129,130,131,136,137,151,153,155,156,157,159,160,161,162,163,165,168,169,171,177,180,181,182,183,184,185,187,188,189,190,192,193,195,196,197,198,199,200,202,203,207,208,209],10:[66,106,117,125,134,173,176,178,205],11:[24,46,97,118,172,194,204],12:[19,57,62,64,71,72,73,74,83,145,146,147],13:[16,17,18,30,34,37,88,92]}

profile = {}
for code, ids in PROFILE_GROUPS.items():
    for i in ids:
        if i in profile:
            raise SystemExit(f"duplicate individual {i}")
        profile[i] = code
if set(profile) != set(range(1,211)):
    raise SystemExit("profile map does not cover exactly individuals 1..210")

profiles = ", ".join(str(profile[i]) for i in range(1,211))
worlds = ", ".join(str(i) for i in range(210))

src = f'''-- ===== INSACERMO V0.11 FULL-210 MODECHOICE BRIDGE V2 =====
-- Generated mechanically from statsmodels modechoice.csv
-- Raw source SHA256: {RAW_SHA}
-- World index 0 corresponds to ModeChoice individual 1; index 209 to individual 210.
-- Contract: Pareto-undominated in (gc, ttme+invt), both minimized.
-- Raw-data audit: 210 individuals, 840 rows; supports 208,20,16,126;
-- profile counts 1001:109,1000:63,1100:12,1010:9,1101:8,1011:7,0001:2;
-- pair conflicts 168.
-- Numeric universal frontier mechanically derived from raw values:
-- (30,180), (56,137), (58,90), (76,85), (92,80).
-- Lean verifies the exact induced 210-world incidence and V0.11 decisions.
-- Lean does not independently derive the numeric frontier from the 840 raw numbers.
namespace Insacermo

set_option maxRecDepth 10000

abbrev MC210World := Fin 210

inductive MC210Plan where
  | mode1 | mode2 | mode3 | mode4
  | r30_180 | r56_137 | r58_90 | r76_85 | r92_80
  deriving DecidableEq, Repr

instance : Fintype MC210Plan where
  elems := {{.mode1, .mode2, .mode3, .mode4, .r30_180, .r56_137, .r58_90, .r76_85, .r92_80}}
  complete := by intro x; cases x <;> simp

def mc210Profiles : List Nat := [{profiles}]

def mc210Profile (w : MC210World) : Nat :=
  mc210Profiles.get! w.val

def mc210Accepts : MC210World → MC210Plan → Bool
  | w, .mode1 => mc210Profile w / 8 % 2 == 1
  | w, .mode2 => mc210Profile w / 4 % 2 == 1
  | w, .mode3 => mc210Profile w / 2 % 2 == 1
  | w, .mode4 => mc210Profile w % 2 == 1
  | _, .r30_180 => true
  | _, .r56_137 => true
  | _, .r58_90 => true
  | _, .r76_85 => true
  | _, .r92_80 => true

def mc210Good (w : MC210World) (p : MC210Plan) : Prop :=
  mc210Accepts w p = true

def mc210System : ContractSystem MC210World MC210Plan where
  good := mc210Good
  cost := fun _ => 1

instance mc210GoodDecidable : DecidableRel mc210System.good := by
  intro s p
  change Decidable (mc210Accepts s p = true)
  infer_instance

def mc210AllWorlds : List MC210World := [{worlds}]
def mc210Available : List MC210Plan := [.mode1, .mode2, .mode3, .mode4]
def mc210Repairs : List (List MC210Plan) :=
  [[.r30_180], [.r56_137], [.r58_90], [.r76_85], [.r92_80]]

def mc210RefuseInput : ExecInput MC210World MC210Plan where
  sys := mc210System
  ambiguity := mc210AllWorlds
  available := mc210Available
  budget := 1
  searchComplete := true

def mc210RepairInput : ExecInput MC210World MC210Plan where
  sys := mc210System
  ambiguity := mc210AllWorlds
  available := mc210Available
  budget := 1
  repairs := mc210Repairs
  searchComplete := true

def mc210AfterRepairInput : ExecInput MC210World MC210Plan where
  sys := mc210System
  ambiguity := mc210AllWorlds
  available := .r30_180 :: mc210Available
  budget := 1
  searchComplete := true

local instance mc210RefuseGoodDecidable : DecidableRel mc210RefuseInput.sys.good := by
  simpa [mc210RefuseInput] using mc210GoodDecidable
local instance mc210RepairGoodDecidable : DecidableRel mc210RepairInput.sys.good := by
  simpa [mc210RepairInput] using mc210GoodDecidable
local instance mc210AfterRepairGoodDecidable : DecidableRel mc210AfterRepairInput.sys.good := by
  simpa [mc210AfterRepairInput] using mc210GoodDecidable

#eval mc210Profiles.length
#eval mc210AllWorlds.length
#eval compile mc210RefuseInput
#eval compile mc210RepairInput
#eval compile mc210AfterRepairInput

example : mc210Profiles.length = 210 := by native_decide
example : mc210AllWorlds.length = 210 := by native_decide
example : (compile mc210RefuseInput).label = ExecLabel.refuse := by native_decide
example : (compile mc210RepairInput).label = ExecLabel.repair := by native_decide
example : (compile mc210RepairInput).candidateIndex = some 0 := by native_decide
example : (compile mc210RepairInput).strategy = some MC210Plan.r30_180 := by native_decide
example : (compile mc210AfterRepairInput).label = ExecLabel.act := by native_decide
example : (compile mc210AfterRepairInput).strategy = some MC210Plan.r30_180 := by native_decide

def mc210SupportSize (p : MC210Plan) : Nat :=
  (mc210AllWorlds.filter (fun w => mc210Accepts w p)).length

#eval mc210SupportSize .mode1
#eval mc210SupportSize .mode2
#eval mc210SupportSize .mode3
#eval mc210SupportSize .mode4

example : mc210SupportSize .mode1 = 208 := by native_decide
example : mc210SupportSize .mode2 = 20 := by native_decide
example : mc210SupportSize .mode3 = 16 := by native_decide
example : mc210SupportSize .mode4 = 126 := by native_decide

def mc210ProfileCount (k : Nat) : Nat :=
  (mc210AllWorlds.filter (fun w => mc210Profile w == k)).length

example : mc210ProfileCount 9 = 109 := by native_decide
example : mc210ProfileCount 8 = 63 := by native_decide
example : mc210ProfileCount 12 = 12 := by native_decide
example : mc210ProfileCount 10 = 9 := by native_decide
example : mc210ProfileCount 13 = 8 := by native_decide
example : mc210ProfileCount 11 = 7 := by native_decide
example : mc210ProfileCount 1 = 2 := by native_decide

def mc210Pairs : List MC210World → List (MC210World × MC210World)
  | [] => []
  | x :: xs => xs.map (fun y => (x,y)) ++ mc210Pairs xs

def mc210PairActionable (xy : MC210World × MC210World) : Bool :=
  mc210Available.any (fun p => mc210Accepts xy.1 p && mc210Accepts xy.2 p)

def mc210MinimalPairConflicts : List (MC210World × MC210World) :=
  (mc210Pairs mc210AllWorlds).filter (fun xy => ! mc210PairActionable xy)

#eval (mc210Pairs mc210AllWorlds).length
#eval mc210MinimalPairConflicts.length
example : (mc210Pairs mc210AllWorlds).length = 21945 := by native_decide
example : mc210MinimalPairConflicts.length = 168 := by native_decide

example : mc210SupportSize .r30_180 = 210 := by native_decide
example : mc210SupportSize .r56_137 = 210 := by native_decide
example : mc210SupportSize .r58_90 = 210 := by native_decide
example : mc210SupportSize .r76_85 = 210 := by native_decide
example : mc210SupportSize .r92_80 = 210 := by native_decide

example : OperationalSound mc210RefuseInput (compile mc210RefuseInput) :=
  compile_operational_sound mc210RefuseInput
example : OperationalSound mc210RepairInput (compile mc210RepairInput) :=
  compile_operational_sound mc210RepairInput
example : OperationalSound mc210AfterRepairInput (compile mc210AfterRepairInput) :=
  compile_operational_sound mc210AfterRepairInput

end Insacermo
'''

Path('v011_modechoice_full210_bridge.lean').write_text(src)
print('WROTE full-210 V2', len(src), 'chars')
