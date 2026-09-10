from pathlib import Path
from urllib.request import urlopen
import csv, io, hashlib

URL = 'https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/HIV.csv'
raw = urlopen(URL, timeout=120).read()
RAW_SHA = hashlib.sha256(raw).hexdigest()
rows = list(csv.DictReader(io.StringIO(raw.decode('utf-8-sig'))))
if not rows:
    raise SystemExit('empty HIV dataset')
required = {'smiles','HIV_active'}
if not required.issubset(rows[0].keys()):
    raise SystemExit(f'missing required columns: {required-set(rows[0].keys())}')

# Exact raw-SMILES conflicts in the CURRENT public file downloaded during CI.
groups = {}
for i,r in enumerate(rows):
    smi = str(r['smiles']).strip()
    try:
        y = int(float(r['HIV_active']))
    except Exception:
        continue
    if y not in (0,1):
        continue
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
if not conflicts:
    raise SystemExit('no exact-SMILES opposite-label conflict found in current public HIV.csv')

# Deterministic witness: lexicographically first conflicting exact SMILES.
smi, vals, c0, c1 = conflicts[0]
neg = next(v for v in vals if v[1] == 0)
pos = next(v for v in vals if v[1] == 1)
WITNESS_SHA = hashlib.sha256(smi.encode()).hexdigest()

receipt = f'''INSACERMO V0.11 — HIV STRUCTURE-CONFLICT WITNESS\nSOURCE={URL}\nRAW_SHA256={RAW_SHA}\nROWS={len(rows)}\nEXACT_SMILES_CONFLICT_GROUPS={len(conflicts)}\nCONFLICTING_ROWS={conflicting_rows}\nOPPOSITE_LABEL_PAIRS={opposite_pairs}\nWITNESS_SMILES_SHA256={WITNESS_SHA}\nWITNESS_NEGATIVE_ROW={neg[0]}\nWITNESS_POSITIVE_ROW={pos[0]}\nWITNESS_NEGATIVE_ACTIVITY={neg[2]}\nWITNESS_POSITIVE_ACTIVITY={pos[2]}\nBOUNDARY=Dataset/contract observation conflict only; no biological impossibility claim.\n'''
Path('HIV_STRUCTURE_CONFLICT_RECEIPT.txt').write_text(receipt)

src = f'''-- ===== INSACERMO V0.11 HIV STRUCTURE-CONFLICT BRIDGE =====
-- Source downloaded mechanically from current public DeepChem HIV.csv.
-- Raw SHA256: {RAW_SHA}
-- Rows: {len(rows)}.
-- Exact-SMILES opposite-label groups: {len(conflicts)}.
-- Conflicting rows: {conflicting_rows}; opposite-label pairs: {opposite_pairs}.
-- Deterministic witness SMILES SHA256: {WITNESS_SHA}
-- Raw row indices: inactive={neg[0]}, active={pos[0]}.
-- IMPORTANT: this certifies an observation/label conflict in this downloaded
-- dataset under the declared structure-only contract. It is NOT a biological
-- impossibility claim and does not exhaust non-structural experimental probes.
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

-- Both witness rows have the same observed molecular structure. Any deterministic
-- Nat-valued probe that factors ONLY through that structure code must collide.
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
print('ROWS', len(rows))
print('CONFLICT_GROUPS', len(conflicts))
print('CONFLICTING_ROWS', conflicting_rows)
print('OPPOSITE_LABEL_PAIRS', opposite_pairs)
print('WITNESS_SMILES_SHA256', WITNESS_SHA)
print('WITNESS_ROWS', neg[0], pos[0])
