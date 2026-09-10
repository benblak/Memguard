from pathlib import Path
from urllib.request import urlopen
import zipfile, io, csv, hashlib

URL = 'https://archive.ics.uci.edu/static/public/17/breast%2Bcancer%2Bwisconsin%2Bdiagnostic.zip'
ZIP = urlopen(URL, timeout=60).read()
ZIP_SHA = hashlib.sha256(ZIP).hexdigest()
with zipfile.ZipFile(io.BytesIO(ZIP)) as z:
    raw = z.read('wdbc.data')
RAW_SHA = hashlib.sha256(raw).hexdigest()
rows = list(csv.reader(io.StringIO(raw.decode())))
if len(rows) != 569:
    raise SystemExit(f'expected 569 rows, got {len(rows)}')

# wdbc.data columns: id, diagnosis, then 30 features in canonical WDBC order.
# Selected six features: mean texture, mean symmetry, radius error,
# smoothness error, worst area, worst compactness.
cols = [3, 10, 12, 15, 25, 27]
classes = [0 if r[1] == 'M' else 1 for r in rows]
if classes.count(0) != 212 or classes.count(1) != 357:
    raise SystemExit('unexpected class counts')

values = [[float(r[c]) for r in rows] for c in cols]
# n=569 => default linear quartiles fall exactly at sorted indices 142,284,426.
qs = []
for v in values:
    s = sorted(v)
    qs.append([s[142], s[284], s[426]])

bins = []
for i in range(569):
    bins.append([sum(values[f][i] >= q for q in qs[f]) for f in range(6)])

def encode(ds):
    return sum(int(d) * (4 ** i) for i, d in enumerate(ds))

full = [encode(r) for r in bins]
drops = []
for d in range(6):
    drops.append([encode([x for j,x in enumerate(r) if j != d]) for r in bins])

fibers = {}
for i,s in enumerate(full):
    fibers.setdefault(s,set()).add(classes[i])
if len(fibers) != 462 or any(len(v) != 1 for v in fibers.values()):
    raise SystemExit('full six-measure signature is not the expected pure 462-fiber partition')

mal = [i for i,c in enumerate(classes) if c == 0]
ben = [i for i,c in enumerate(classes) if c == 1]
unresolved = []
for d in range(6):
    unresolved.append(sum(drops[d][i] == drops[d][j] for i in mal for j in ben))
if unresolved != [15,16,9,6,8,16]:
    raise SystemExit(f'unexpected drop-one unresolved counts: {unresolved}')

# Canonical compact bridge fingerprint.
bridge_lines = ['id,class,signature,drop0,drop1,drop2,drop3,drop4,drop5']
for i in range(569):
    bridge_lines.append(','.join(map(str,[i,classes[i],full[i]]+[drops[d][i] for d in range(6)])))
bridge_txt = '\n'.join(bridge_lines) + '\n'
BRIDGE_SHA = hashlib.sha256(bridge_txt.encode()).hexdigest()
Path('WDBC_PROBE_569_BINNED.csv').write_text(bridge_txt)

constructors = ' | '.join(f'w{i}' for i in range(569))
elems = ', '.join(f'.w{i}' for i in range(569))
worlds = ', '.join(f'.w{i}' for i in range(569))
def arms(vals):
    return '\n'.join(f'  | .w{i} => {v}' for i,v in enumerate(vals))

src = f'''-- ===== INSACERMO V0.11 WDBC PROBE BRIDGE =====
-- Official UCI WDBC source downloaded by generator.
-- ZIP SHA256: {ZIP_SHA}
-- wdbc.data SHA256: {RAW_SHA}
-- binned bridge SHA256: {BRIDGE_SHA}
-- 569 worlds: 212 malignant, 357 benign.
-- Structural benchmark only; NOT a clinical diagnostic claim.
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace Insacermo

inductive WDBCWorld where
  | {constructors}
  deriving DecidableEq, Repr

instance : Fintype WDBCWorld where
  elems := {{{elems}}}
  complete := by intro x; cases x <;> native_decide

inductive WDBCPlan where
  | malignant | benign
  deriving DecidableEq, Repr

def wdbcClass : WDBCWorld → Bool
{arms(['false' if c == 0 else 'true' for c in classes])}

def wdbcSig : WDBCWorld → Nat
{arms(full)}

def wdbcDrop0 : WDBCWorld → Nat
{arms(drops[0])}
def wdbcDrop1 : WDBCWorld → Nat
{arms(drops[1])}
def wdbcDrop2 : WDBCWorld → Nat
{arms(drops[2])}
def wdbcDrop3 : WDBCWorld → Nat
{arms(drops[3])}
def wdbcDrop4 : WDBCWorld → Nat
{arms(drops[4])}
def wdbcDrop5 : WDBCWorld → Nat
{arms(drops[5])}

def wdbcGood : WDBCWorld → WDBCPlan → Prop
  | w, .malignant => wdbcClass w = false
  | w, .benign => wdbcClass w = true

def wdbcSystem : ContractSystem WDBCWorld WDBCPlan where
  good := wdbcGood
  cost := fun _ => 1

instance wdbcGoodDecidable : DecidableRel wdbcSystem.good := by
  intro s p
  change Decidable (wdbcGood s p)
  cases p <;> simp [wdbcGood] <;> infer_instance

def wdbcAllWorlds : List WDBCWorld := [{worlds}]
def wdbcAvailable : List WDBCPlan := [.malignant, .benign]

def wdbcRefuseInput : ExecInput WDBCWorld WDBCPlan where
  sys := wdbcSystem
  ambiguity := wdbcAllWorlds
  available := wdbcAvailable
  budget := 1
  searchComplete := true

def wdbcProbeInput : ExecInput WDBCWorld WDBCPlan where
  sys := wdbcSystem
  ambiguity := wdbcAllWorlds
  available := wdbcAvailable
  budget := 1
  probes := [wdbcDrop0, wdbcDrop1, wdbcDrop2, wdbcDrop3, wdbcDrop4, wdbcDrop5, wdbcSig]
  searchComplete := true

local instance wdbcRefuseGoodDecidable : DecidableRel wdbcRefuseInput.sys.good := by
  simpa [wdbcRefuseInput] using wdbcGoodDecidable
local instance wdbcProbeGoodDecidable : DecidableRel wdbcProbeInput.sys.good := by
  simpa [wdbcProbeInput] using wdbcGoodDecidable

#eval compile wdbcRefuseInput
#eval compile wdbcProbeInput

example : (compile wdbcRefuseInput).label = ExecLabel.refuse := by native_decide
example : (compile wdbcProbeInput).label = ExecLabel.probe := by native_decide
example : (compile wdbcProbeInput).candidateIndex = some 6 := by native_decide
example : (compile wdbcProbeInput).strategy = none := by native_decide

example : probeResolves wdbcSystem wdbcAvailable 1 wdbcAllWorlds wdbcDrop0 = false := by native_decide
example : probeResolves wdbcSystem wdbcAvailable 1 wdbcAllWorlds wdbcDrop1 = false := by native_decide
example : probeResolves wdbcSystem wdbcAvailable 1 wdbcAllWorlds wdbcDrop2 = false := by native_decide
example : probeResolves wdbcSystem wdbcAvailable 1 wdbcAllWorlds wdbcDrop3 = false := by native_decide
example : probeResolves wdbcSystem wdbcAvailable 1 wdbcAllWorlds wdbcDrop4 = false := by native_decide
example : probeResolves wdbcSystem wdbcAvailable 1 wdbcAllWorlds wdbcDrop5 = false := by native_decide
example : probeResolves wdbcSystem wdbcAvailable 1 wdbcAllWorlds wdbcSig = true := by native_decide

def wdbcMalignantCount : Nat := (wdbcAllWorlds.filter (fun w => wdbcClass w == false)).length
def wdbcBenignCount : Nat := (wdbcAllWorlds.filter (fun w => wdbcClass w == true)).length
#eval wdbcMalignantCount
#eval wdbcBenignCount
example : wdbcMalignantCount = 212 := by native_decide
example : wdbcBenignCount = 357 := by native_decide

example : OperationalSound wdbcRefuseInput (compile wdbcRefuseInput) :=
  compile_operational_sound wdbcRefuseInput
example : OperationalSound wdbcProbeInput (compile wdbcProbeInput) :=
  compile_operational_sound wdbcProbeInput

end Insacermo
'''
Path('v011_wdbc_probe_bridge.lean').write_text(src)
Path('WDBC_GENERATOR_RECEIPT.txt').write_text(
    f'ZIP_SHA256={ZIP_SHA}\nRAW_SHA256={RAW_SHA}\nBRIDGE_SHA256={BRIDGE_SHA}\n'
    f'ROWS=569\nMALIGNANT=212\nBENIGN=357\nFIBERS=462\nDROP_UNRESOLVED={unresolved}\n'
)
print('WROTE', len(src), 'Lean chars')
print('ZIP_SHA256', ZIP_SHA)
print('RAW_SHA256', RAW_SHA)
print('BRIDGE_SHA256', BRIDGE_SHA)
print('DROP_UNRESOLVED', unresolved)
