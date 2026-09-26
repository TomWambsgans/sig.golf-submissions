from pathlib import Path
import json
R=Path(__file__).resolve().parent
T=R/'output'
report=json.loads((R/'pc64-padding-report.json').read_text())
combined=[]
for name in ('keygen','sign','expand','verify'):
 words=[int(x,16) for x in (R/f'pc64-beta-{name}.hex').read_text().split()]
 sites=report[name]['sites']; count=(len(words)+95)//96
 ns='Pc64'+name.capitalize()+'Image'
 out=['import SigGolf.Riscv',f'namespace {ns}','open SigGolf.Riscv RiscvZkvm.Rv64','set_option maxRecDepth 16384','set_option maxHeartbeats 2000000']
 for k in range(count):
  chunk=words[96*k:96*(k+1)]
  out += [f'private def chunk{k} : List (BitVec 32) := [']
  for z in range(0,len(chunk),8):
   out += ['  '+', '.join(f'0x{w:08x}' for w in chunk[z:z+8])+(',' if z+8<len(chunk) else '')]
  out += [']',f'private theorem chunk{k}_len : chunk{k}.length = {len(chunk)} := by rfl']
 for k in range(count-1,-1,-1):
  out += [f'private def suffix{k} : List (BitVec 32) := '+(f'chunk{k} ++ suffix{k+1}' if k<count-1 else f'chunk{k}')]
  remaining=len(words)-96*k
  if k==count-1:
   out += [f'private theorem suffix{k}_len : suffix{k}.length = {remaining} := by',
           f'  simpa only [suffix{k}] using chunk{k}_len']
  else:
   out += [f'private theorem suffix{k}_len : suffix{k}.length = {remaining} := by',
           f'  simp only [suffix{k}, List.length_append, chunk{k}_len, suffix{k+1}_len]']
 out += ['def code : List (BitVec 32) := suffix0', 'def image : Image := ⟨code, []⟩',
         f'theorem code_length : code.length = {len(words)} := by simpa only [code] using suffix0_len',
         f'theorem image_byteSize : image.byteSize = {4*len(words)} := by simp [image, Image.byteSize, code_length]',
         'theorem image_data_empty : image.data = [] := rfl',
         '#print axioms code_length', '#print axioms image_byteSize', '#print axioms image_data_empty']
 for site in sites:
  for field,prefix in [('original_pc','original'),('stub_pc','stub')]:
   pc=int(site[field],16); ix=(pc-0x1000)//4; w=words[ix]; k=ix//96
   simp_args=['code']+[f'suffix{j}' for j in range(k+1)]+['List.getElem?_append']+[f'chunk{j}_len' for j in range(k)]+['Nat.reduceLT','Nat.reduceSub','if_true','if_false']
   out += [f'theorem {prefix}_{pc:04x}_word : code[{ix}]? = some 0x{w:08x} := by',
           '  simp only ['+', '.join(simp_args)+']',
           '  decide',f'#print axioms {prefix}_{pc:04x}_word']
  pc=int(site['stub_pc'],16); ix=(pc-0x1000)//4
  block=[int(w,16) for w in site['stub_words']]
  out += [f'theorem stub_{pc:04x}_block : (code.drop {ix}).take {len(block)} = [',
          '  '+', '.join(f'0x{w:08x}' for w in block),
          '] := by decide',f'#print axioms stub_{pc:04x}_block']
 out += [f'end {ns}']
 p=T/f'{ns}.lean';p.write_text('\n'.join(out)+'\n')
 combined += out[1:]
 print(p,len(words),len(sites))

combined_path=T/'SphincsBeta64Images.lean'
combined_path.write_text('import SigGolf.Statements\nimport RiscvZkvm.Rv64.Logic.MemRegion\nset_option linter.unusedSimpArgs false\n'+
                         '\n'.join(combined)+'\n')
print(combined_path)
