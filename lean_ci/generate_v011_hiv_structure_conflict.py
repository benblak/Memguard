from pathlib import Path
from urllib.request import urlopen
import csv, io, hashlib

URL = 'https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/HIV.csv'
raw = urlopen(URL, timeout=120).read()
RAW_SHA = hashlib.sha256(raw).hexdigest()
rows = list(csv.DictReader(io.StringIO(raw.decode('utf-8-sig'))))
if len(rows) != 41913:
    raise SystemExit(f'expected 41913 rows, got {len(rows)}')

# Exact raw-SMILES conflicts: same observed molecular string, both binary labels.
groups = {}
for i,r in enumerate(rows):
    smi = str(r['smiles']).strip()
    y = int(float(r['HIV_active']))
    groups.setdefault(smi, []).append((i,y,r.get('activity','')))

conflicts = []
opposite_pairs = 0
conflicting_rows = 0
for smi, vals in groups.items():
    c0 = sum(y == 0 for _,y,_ in vals)
    c1 = sum(y == 1 for _,y,_ in vals)
    if c0 and c1:
        conflicts.append((smi, vals, c0, c1))
        opposite_pairs += c0*c1
        conflicting_rows += len(vals)

conflicts.sort(key=lambda x: x[0])
if (len(conflicts), conflicting_rows, opposite_pairs) != (28,76,54):
    raise SystemExit(f'unexpected conflict audit {(len(conflicts), conflicting_rows, opposite_pairs)}')

# Deterministic witness: lexicographically first conflicting exact SMILES.
smi, vals, c0, c1 = conflicts[0]
neg = next(v for v in vals if v[1] == 0)
pos = next(v for v in vals if v[1] == 1)
WITNESS_SHA = hashlib.sha256(smi.encode()).hexdigest()

receipt = f'''INSACERMO V0.11 — HIV STRUCTURE-CONFLICT WITNESS\nSOURCE={URL}\nRAW_SHA256={RAW_SHA}\nROWS=41913\nEXACT_SMILES_CONFLICT_GROUPS=28\nCONFLICTING_ROWS=76\nOPPOSITE_LABEL_PAIRS=54\nWITNESS_SMILES_SHA256={WITNESS_SHA}\nWITNESS_NEGATIVE_ROW={neg[0]}\nWITNESS_POSITIVE_ROW={pos[0]}\nWITNESS_NEGATIVE_ACTIVITY={neg[2]}\nWITNESS_POSITIVE_ACTIVITY={pos[2]}\nBOUNDARY=Dataset/contract observation conflict only; no biological impossibility claim.\n'''
Path('HIV_STRUCTURE_CONFLICT_RECEIPT.txt').write_text(receipt)

src = f'''-- ===== INSACERMO V0.11 HIV STRUCTURE-CONFLICT BRIDGE =====
-- Source downloaded mechanically from DeepChem MoleculeNet HIV.csv.
-- Raw SHA256: {RAW_SHA}
-- 41,913 rows; 28 exact-SMILES groups contain both binary labels;
-- 76 rows involved; 54 opposite-label row pairs.
-- Deterministic witness SMILES SHA256: {WITNESS_SHA}
-- Raw row indices: inactive={neg[0]}, active={pos[0]}.
-- IMPORTANT: this certifies an observation/label conflict in the dataset under
-- the declared structure-only contract. It is NOT a biological impossibility claim.
namespace Insacermo

inductive HIVWitnessWorld where
  | inactiveRow | activeRow
  deriving DecidableEq, Repr

instance : Fintype HIVWitnessWorld where
  elems := {{.inactiveRow, .activeRow}}
  complete := by intro x; cases x <;> simp

inductive HIVWitnessPlan where
  | inactive | active
  deriving DecidableEq, Repr

def hivWitnessGood : HIVWitnessWorld → HIVWitnessPlan → Prop
  | .inactiveRow, .inactive => True
  | .activeRow, .active => True
  | _, _ => False

def hivWitnessSystem : ContractSystem HIVWitnessWorld HIVWitnessPlan where
  good := hivWitnessGood
  cost := fun _ => 1

instance hivWitnessGoodDecidable : DecidableRel hivWitnessSystem.good := by
  intro s p
  change Decidable (hivWitnessGood s p)
  cases s <;> cases p <;> simp [hivWitnessGood]

-- Both rows have exactly the same observed molecular structure.
-- Any deterministic Nat-valued probe factored only through this structure code
-- therefore returns the same value on both witness worlds.
def hivStructureIdentity : HIVWitnessWorld → Nat
  | .inactiveRow => 0
  | .activeRow => 0

theorem any_structure_derived_probe_collides (g : Nat → Nat) :
    g (hivStructureIdentity .inactiveRow) = g (hivStructureIdentity .activeRow) := by
  rfl

def hivWitnessWorlds : List HIVWitnessWorld := [.inactiveRow, .activeRow]
def hivWitnessAvailable : List HIVWitnessPlan := [.inactive, .active]

def hivStructureProbe : HIVWitnessWorld → Nat := hivStructureIdentity

def hivWitnessInput : ExecInput HIVWitnessWorld HIVWitnessPlan where
  sys := hivWitnessSystem
  ambiguity := hivWitnessWorlds
  available := hivWitnessAvailable
  budget := 1
  probes := [hivStructureProbe]
  searchComplete := true

local instance hivWitnessInputGoodDecidable : DecidableRel hivWitnessInput.sys.good := by
  simpa [hivWitnessInput] using hivWitnessGoodDecidable

#eval compile hivWitnessInput

example : probeResolves hivWitnessSystem hivWitnessAvailable 1 hivWitnessWorlds hivStructureProbe = false := by
  native_decide

example : (compile hivWitnessInput).label = ExecLabel.refuse := by
  native_decide

example : (compile hivWitnessInput).candidateIndex = none := by
  native_decide

example : (compile hivWitnessInput).strategy = none := by
  native_decide

example : OperationalSound hivWitnessInput (compile hivWitnessInput) :=
  compile_operational_sound hivWitnessInput

end Insacermo
'''
Path('v011_hiv_structure_conflict_bridge.lean').write_text(src)
print('RAW_SHA256', RAW_SHA)
print('CONFLICT_GROUPS', len(conflicts))
print('CONFLICTING_ROWS', conflicting_rows)
print('OPPOSITE_LABEL_PAIRS', opposite_pairs)
print('WITNESS_SMILES_SHA256', WITNESS_SHA)
print('WITNESS_ROWS', neg[0], pos[0])
