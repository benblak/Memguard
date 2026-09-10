from pathlib import Path
import hashlib

# This generator deliberately does NOT redownload the current DeepChem HIV.csv.
# The archived source was mechanically exhaustively audited outside Lean.
ARCHIVE_SHA='d0e985c9c1191c77958ac52a278338c241858394fd3b299f56113329e1fc935c'
ROWS=41913
CONFLICT_GROUPS=28
CONFLICTING_ROWS=76
OPPOSITE_PAIRS=54
NEG_ROW=14730
POS_ROW=19066
NEG_ACTIVITY='CI'
POS_ACTIVITY='CM'
SMILES='CC(=O)OC1CC2C(C)(C)C(=O)C=CC2(C)C2CCC3(C)C(c4ccoc4)C(=O)C4OC43C12C'
WITNESS_SHA=hashlib.sha256(SMILES.encode()).hexdigest()
assert WITNESS_SHA == 'b456806bb19d0d580776965e62d21b64f246b16eccce7075cdbd9498de54a3f1'

Path('HIV_STRUCTURE_CONFLICT_RECEIPT.txt').write_text(f'''INSACERMO V0.11 — HIV ARCHIVE STRUCTURE-CONFLICT WITNESS\nARCHIVED_RAW_SHA256={ARCHIVE_SHA}\nROWS={ROWS}\nEXACT_SMILES_CONFLICT_GROUPS={CONFLICT_GROUPS}\nCONFLICTING_ROWS={CONFLICTING_ROWS}\nOPPOSITE_LABEL_PAIRS={OPPOSITE_PAIRS}\nWITNESS_SMILES_SHA256={WITNESS_SHA}\nWITNESS_NEGATIVE_ROW={NEG_ROW}\nWITNESS_POSITIVE_ROW={POS_ROW}\nWITNESS_NEGATIVE_ACTIVITY={NEG_ACTIVITY}\nWITNESS_POSITIVE_ACTIVITY={POS_ACTIVITY}\nBOUNDARY=Archived-dataset observation conflict under structure-only contract; no biological impossibility claim.\n''')

src=f'''-- INSACERMO V0.11 — HIV ARCHIVE STRUCTURE-CONFLICT BRIDGE
-- Archived HIV.txt SHA256: {ARCHIVE_SHA}
-- Mechanical exhaustive source audit: {ROWS} rows; {CONFLICT_GROUPS} exact-SMILES
-- opposite-label groups; {CONFLICTING_ROWS} rows; {OPPOSITE_PAIRS} opposite-label pairs.
-- Deterministic witness rows: inactive={NEG_ROW}, active={POS_ROW}.
-- Witness SMILES SHA256: {WITNESS_SHA}
-- FORMAL BOUNDARY: Lean verifies only the induced two-world witness contract.
-- It does not independently parse the archived 41,913-row source.
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
  cases s <;> cases p
  · exact isTrue True.intro
  · exact isFalse (fun h => h)
  · exact isFalse (fun h => h)
  · exact isTrue True.intro

-- Both archived witness rows carry exactly the same observed SMILES string.
def hivObservedStructure : HIVWitnessWorld → Nat
  | .inactiveRow => 0
  | .activeRow => 0

theorem witness_observational_alias :
    hivObservedStructure .inactiveRow = hivObservedStructure .activeRow := by rfl

theorem every_structure_factored_probe_collides (g : Nat → Nat) :
    g (hivObservedStructure .inactiveRow) = g (hivObservedStructure .activeRow) := by rfl

def hivWitnessWorlds : List HIVWitnessWorld := [.inactiveRow, .activeRow]
def hivWitnessAvailable : List HIVWitnessPlan := [.inactive, .active]
def hivStructureProbe : HIVWitnessWorld → Nat := hivObservedStructure

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

example : probeResolves hivWitnessSystem hivWitnessAvailable 1 hivWitnessWorlds hivStructureProbe = false := by native_decide
example : (compile hivWitnessInput).label = ExecLabel.refuse := by native_decide
example : (compile hivWitnessInput).candidateIndex = none := by native_decide
example : (compile hivWitnessInput).strategy = none := by native_decide
example : OperationalSound hivWitnessInput (compile hivWitnessInput) :=
  compile_operational_sound hivWitnessInput

end Insacermo
'''
Path('v011_hiv_structure_conflict_bridge.lean').write_text(src)
print('ARCHIVED_RAW_SHA256', ARCHIVE_SHA)
print('ROWS', ROWS)
print('CONFLICT_GROUPS', CONFLICT_GROUPS)
print('CONFLICTING_ROWS', CONFLICTING_ROWS)
print('OPPOSITE_LABEL_PAIRS', OPPOSITE_PAIRS)
print('WITNESS_SMILES_SHA256', WITNESS_SHA)
print('WITNESS_ROWS', NEG_ROW, POS_ROW)
