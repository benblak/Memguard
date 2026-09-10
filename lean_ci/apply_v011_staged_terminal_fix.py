from pathlib import Path
p = Path('InsacermoV011StageD.lean')
s = p.read_text()
old = '''              | false =>
                  simp [OperationalSound, hact, hprobe, hrepair, hcomplete]
                  exact ⟨hcurrent, hcomplete, hprobe, hrepair⟩
              | true =>
                  simp [OperationalSound, hact, hprobe, hrepair, hcomplete]
                  exact ⟨hcurrent, hcomplete, hprobe, hrepair⟩
'''
new = '''              | false =>
                  simp [OperationalSound, hact, hprobe, hrepair, hcomplete]
                  exact hcurrent
              | true =>
                  simp [OperationalSound, hact, hprobe, hrepair, hcomplete]
                  exact hcurrent
'''
if old not in s:
    raise SystemExit('terminal proof block not found')
p.write_text(s.replace(old, new))
print('PATCHED terminal branches')
