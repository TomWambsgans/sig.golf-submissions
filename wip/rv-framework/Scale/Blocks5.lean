import SigGolfCandidate.Rv.Scale.Code

namespace SigGolfCandidate.Rv.Scale
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

sym_block run250 := symRun { noAlias := true } seg250 (BitVec.ofNat 64 (0x1000 + 4 * 12500)) 50
theorem spec250 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12500))) (hobl : run250.res.obligs s) :
    Steps image s run250.res.steps run250.res.cycles (run250.res.toState s) :=
  symRun_sound run250 (codeAt_layout rfl layout_ok (i := 250) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run251 := symRun { noAlias := true } seg251 (BitVec.ofNat 64 (0x1000 + 4 * 12550)) 50
theorem spec251 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12550))) (hobl : run251.res.obligs s) :
    Steps image s run251.res.steps run251.res.cycles (run251.res.toState s) :=
  symRun_sound run251 (codeAt_layout rfl layout_ok (i := 251) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run252 := symRun { noAlias := true } seg252 (BitVec.ofNat 64 (0x1000 + 4 * 12600)) 50
theorem spec252 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12600))) (hobl : run252.res.obligs s) :
    Steps image s run252.res.steps run252.res.cycles (run252.res.toState s) :=
  symRun_sound run252 (codeAt_layout rfl layout_ok (i := 252) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run253 := symRun { noAlias := true } seg253 (BitVec.ofNat 64 (0x1000 + 4 * 12650)) 50
theorem spec253 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12650))) (hobl : run253.res.obligs s) :
    Steps image s run253.res.steps run253.res.cycles (run253.res.toState s) :=
  symRun_sound run253 (codeAt_layout rfl layout_ok (i := 253) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run254 := symRun { noAlias := true } seg254 (BitVec.ofNat 64 (0x1000 + 4 * 12700)) 50
theorem spec254 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12700))) (hobl : run254.res.obligs s) :
    Steps image s run254.res.steps run254.res.cycles (run254.res.toState s) :=
  symRun_sound run254 (codeAt_layout rfl layout_ok (i := 254) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run255 := symRun { noAlias := true } seg255 (BitVec.ofNat 64 (0x1000 + 4 * 12750)) 50
theorem spec255 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12750))) (hobl : run255.res.obligs s) :
    Steps image s run255.res.steps run255.res.cycles (run255.res.toState s) :=
  symRun_sound run255 (codeAt_layout rfl layout_ok (i := 255) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run256 := symRun { noAlias := true } seg256 (BitVec.ofNat 64 (0x1000 + 4 * 12800)) 50
theorem spec256 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12800))) (hobl : run256.res.obligs s) :
    Steps image s run256.res.steps run256.res.cycles (run256.res.toState s) :=
  symRun_sound run256 (codeAt_layout rfl layout_ok (i := 256) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run257 := symRun { noAlias := true } seg257 (BitVec.ofNat 64 (0x1000 + 4 * 12850)) 50
theorem spec257 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12850))) (hobl : run257.res.obligs s) :
    Steps image s run257.res.steps run257.res.cycles (run257.res.toState s) :=
  symRun_sound run257 (codeAt_layout rfl layout_ok (i := 257) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run258 := symRun { noAlias := true } seg258 (BitVec.ofNat 64 (0x1000 + 4 * 12900)) 50
theorem spec258 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12900))) (hobl : run258.res.obligs s) :
    Steps image s run258.res.steps run258.res.cycles (run258.res.toState s) :=
  symRun_sound run258 (codeAt_layout rfl layout_ok (i := 258) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run259 := symRun { noAlias := true } seg259 (BitVec.ofNat 64 (0x1000 + 4 * 12950)) 50
theorem spec259 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 12950))) (hobl : run259.res.obligs s) :
    Steps image s run259.res.steps run259.res.cycles (run259.res.toState s) :=
  symRun_sound run259 (codeAt_layout rfl layout_ok (i := 259) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run260 := symRun { noAlias := true } seg260 (BitVec.ofNat 64 (0x1000 + 4 * 13000)) 50
theorem spec260 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13000))) (hobl : run260.res.obligs s) :
    Steps image s run260.res.steps run260.res.cycles (run260.res.toState s) :=
  symRun_sound run260 (codeAt_layout rfl layout_ok (i := 260) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run261 := symRun { noAlias := true } seg261 (BitVec.ofNat 64 (0x1000 + 4 * 13050)) 50
theorem spec261 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13050))) (hobl : run261.res.obligs s) :
    Steps image s run261.res.steps run261.res.cycles (run261.res.toState s) :=
  symRun_sound run261 (codeAt_layout rfl layout_ok (i := 261) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run262 := symRun { noAlias := true } seg262 (BitVec.ofNat 64 (0x1000 + 4 * 13100)) 50
theorem spec262 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13100))) (hobl : run262.res.obligs s) :
    Steps image s run262.res.steps run262.res.cycles (run262.res.toState s) :=
  symRun_sound run262 (codeAt_layout rfl layout_ok (i := 262) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run263 := symRun { noAlias := true } seg263 (BitVec.ofNat 64 (0x1000 + 4 * 13150)) 50
theorem spec263 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13150))) (hobl : run263.res.obligs s) :
    Steps image s run263.res.steps run263.res.cycles (run263.res.toState s) :=
  symRun_sound run263 (codeAt_layout rfl layout_ok (i := 263) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run264 := symRun { noAlias := true } seg264 (BitVec.ofNat 64 (0x1000 + 4 * 13200)) 50
theorem spec264 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13200))) (hobl : run264.res.obligs s) :
    Steps image s run264.res.steps run264.res.cycles (run264.res.toState s) :=
  symRun_sound run264 (codeAt_layout rfl layout_ok (i := 264) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run265 := symRun { noAlias := true } seg265 (BitVec.ofNat 64 (0x1000 + 4 * 13250)) 50
theorem spec265 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13250))) (hobl : run265.res.obligs s) :
    Steps image s run265.res.steps run265.res.cycles (run265.res.toState s) :=
  symRun_sound run265 (codeAt_layout rfl layout_ok (i := 265) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run266 := symRun { noAlias := true } seg266 (BitVec.ofNat 64 (0x1000 + 4 * 13300)) 50
theorem spec266 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13300))) (hobl : run266.res.obligs s) :
    Steps image s run266.res.steps run266.res.cycles (run266.res.toState s) :=
  symRun_sound run266 (codeAt_layout rfl layout_ok (i := 266) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run267 := symRun { noAlias := true } seg267 (BitVec.ofNat 64 (0x1000 + 4 * 13350)) 50
theorem spec267 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13350))) (hobl : run267.res.obligs s) :
    Steps image s run267.res.steps run267.res.cycles (run267.res.toState s) :=
  symRun_sound run267 (codeAt_layout rfl layout_ok (i := 267) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run268 := symRun { noAlias := true } seg268 (BitVec.ofNat 64 (0x1000 + 4 * 13400)) 50
theorem spec268 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13400))) (hobl : run268.res.obligs s) :
    Steps image s run268.res.steps run268.res.cycles (run268.res.toState s) :=
  symRun_sound run268 (codeAt_layout rfl layout_ok (i := 268) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run269 := symRun { noAlias := true } seg269 (BitVec.ofNat 64 (0x1000 + 4 * 13450)) 50
theorem spec269 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13450))) (hobl : run269.res.obligs s) :
    Steps image s run269.res.steps run269.res.cycles (run269.res.toState s) :=
  symRun_sound run269 (codeAt_layout rfl layout_ok (i := 269) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run270 := symRun { noAlias := true } seg270 (BitVec.ofNat 64 (0x1000 + 4 * 13500)) 50
theorem spec270 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13500))) (hobl : run270.res.obligs s) :
    Steps image s run270.res.steps run270.res.cycles (run270.res.toState s) :=
  symRun_sound run270 (codeAt_layout rfl layout_ok (i := 270) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run271 := symRun { noAlias := true } seg271 (BitVec.ofNat 64 (0x1000 + 4 * 13550)) 50
theorem spec271 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13550))) (hobl : run271.res.obligs s) :
    Steps image s run271.res.steps run271.res.cycles (run271.res.toState s) :=
  symRun_sound run271 (codeAt_layout rfl layout_ok (i := 271) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run272 := symRun { noAlias := true } seg272 (BitVec.ofNat 64 (0x1000 + 4 * 13600)) 50
theorem spec272 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13600))) (hobl : run272.res.obligs s) :
    Steps image s run272.res.steps run272.res.cycles (run272.res.toState s) :=
  symRun_sound run272 (codeAt_layout rfl layout_ok (i := 272) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run273 := symRun { noAlias := true } seg273 (BitVec.ofNat 64 (0x1000 + 4 * 13650)) 50
theorem spec273 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13650))) (hobl : run273.res.obligs s) :
    Steps image s run273.res.steps run273.res.cycles (run273.res.toState s) :=
  symRun_sound run273 (codeAt_layout rfl layout_ok (i := 273) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run274 := symRun { noAlias := true } seg274 (BitVec.ofNat 64 (0x1000 + 4 * 13700)) 50
theorem spec274 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13700))) (hobl : run274.res.obligs s) :
    Steps image s run274.res.steps run274.res.cycles (run274.res.toState s) :=
  symRun_sound run274 (codeAt_layout rfl layout_ok (i := 274) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run275 := symRun { noAlias := true } seg275 (BitVec.ofNat 64 (0x1000 + 4 * 13750)) 50
theorem spec275 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13750))) (hobl : run275.res.obligs s) :
    Steps image s run275.res.steps run275.res.cycles (run275.res.toState s) :=
  symRun_sound run275 (codeAt_layout rfl layout_ok (i := 275) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run276 := symRun { noAlias := true } seg276 (BitVec.ofNat 64 (0x1000 + 4 * 13800)) 50
theorem spec276 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13800))) (hobl : run276.res.obligs s) :
    Steps image s run276.res.steps run276.res.cycles (run276.res.toState s) :=
  symRun_sound run276 (codeAt_layout rfl layout_ok (i := 276) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run277 := symRun { noAlias := true } seg277 (BitVec.ofNat 64 (0x1000 + 4 * 13850)) 50
theorem spec277 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13850))) (hobl : run277.res.obligs s) :
    Steps image s run277.res.steps run277.res.cycles (run277.res.toState s) :=
  symRun_sound run277 (codeAt_layout rfl layout_ok (i := 277) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run278 := symRun { noAlias := true } seg278 (BitVec.ofNat 64 (0x1000 + 4 * 13900)) 50
theorem spec278 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13900))) (hobl : run278.res.obligs s) :
    Steps image s run278.res.steps run278.res.cycles (run278.res.toState s) :=
  symRun_sound run278 (codeAt_layout rfl layout_ok (i := 278) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run279 := symRun { noAlias := true } seg279 (BitVec.ofNat 64 (0x1000 + 4 * 13950)) 50
theorem spec279 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 13950))) (hobl : run279.res.obligs s) :
    Steps image s run279.res.steps run279.res.cycles (run279.res.toState s) :=
  symRun_sound run279 (codeAt_layout rfl layout_ok (i := 279) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run280 := symRun { noAlias := true } seg280 (BitVec.ofNat 64 (0x1000 + 4 * 14000)) 50
theorem spec280 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14000))) (hobl : run280.res.obligs s) :
    Steps image s run280.res.steps run280.res.cycles (run280.res.toState s) :=
  symRun_sound run280 (codeAt_layout rfl layout_ok (i := 280) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run281 := symRun { noAlias := true } seg281 (BitVec.ofNat 64 (0x1000 + 4 * 14050)) 50
theorem spec281 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14050))) (hobl : run281.res.obligs s) :
    Steps image s run281.res.steps run281.res.cycles (run281.res.toState s) :=
  symRun_sound run281 (codeAt_layout rfl layout_ok (i := 281) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run282 := symRun { noAlias := true } seg282 (BitVec.ofNat 64 (0x1000 + 4 * 14100)) 50
theorem spec282 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14100))) (hobl : run282.res.obligs s) :
    Steps image s run282.res.steps run282.res.cycles (run282.res.toState s) :=
  symRun_sound run282 (codeAt_layout rfl layout_ok (i := 282) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run283 := symRun { noAlias := true } seg283 (BitVec.ofNat 64 (0x1000 + 4 * 14150)) 50
theorem spec283 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14150))) (hobl : run283.res.obligs s) :
    Steps image s run283.res.steps run283.res.cycles (run283.res.toState s) :=
  symRun_sound run283 (codeAt_layout rfl layout_ok (i := 283) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run284 := symRun { noAlias := true } seg284 (BitVec.ofNat 64 (0x1000 + 4 * 14200)) 50
theorem spec284 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14200))) (hobl : run284.res.obligs s) :
    Steps image s run284.res.steps run284.res.cycles (run284.res.toState s) :=
  symRun_sound run284 (codeAt_layout rfl layout_ok (i := 284) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run285 := symRun { noAlias := true } seg285 (BitVec.ofNat 64 (0x1000 + 4 * 14250)) 50
theorem spec285 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14250))) (hobl : run285.res.obligs s) :
    Steps image s run285.res.steps run285.res.cycles (run285.res.toState s) :=
  symRun_sound run285 (codeAt_layout rfl layout_ok (i := 285) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run286 := symRun { noAlias := true } seg286 (BitVec.ofNat 64 (0x1000 + 4 * 14300)) 50
theorem spec286 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14300))) (hobl : run286.res.obligs s) :
    Steps image s run286.res.steps run286.res.cycles (run286.res.toState s) :=
  symRun_sound run286 (codeAt_layout rfl layout_ok (i := 286) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run287 := symRun { noAlias := true } seg287 (BitVec.ofNat 64 (0x1000 + 4 * 14350)) 50
theorem spec287 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14350))) (hobl : run287.res.obligs s) :
    Steps image s run287.res.steps run287.res.cycles (run287.res.toState s) :=
  symRun_sound run287 (codeAt_layout rfl layout_ok (i := 287) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run288 := symRun { noAlias := true } seg288 (BitVec.ofNat 64 (0x1000 + 4 * 14400)) 50
theorem spec288 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14400))) (hobl : run288.res.obligs s) :
    Steps image s run288.res.steps run288.res.cycles (run288.res.toState s) :=
  symRun_sound run288 (codeAt_layout rfl layout_ok (i := 288) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run289 := symRun { noAlias := true } seg289 (BitVec.ofNat 64 (0x1000 + 4 * 14450)) 50
theorem spec289 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14450))) (hobl : run289.res.obligs s) :
    Steps image s run289.res.steps run289.res.cycles (run289.res.toState s) :=
  symRun_sound run289 (codeAt_layout rfl layout_ok (i := 289) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run290 := symRun { noAlias := true } seg290 (BitVec.ofNat 64 (0x1000 + 4 * 14500)) 50
theorem spec290 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14500))) (hobl : run290.res.obligs s) :
    Steps image s run290.res.steps run290.res.cycles (run290.res.toState s) :=
  symRun_sound run290 (codeAt_layout rfl layout_ok (i := 290) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run291 := symRun { noAlias := true } seg291 (BitVec.ofNat 64 (0x1000 + 4 * 14550)) 50
theorem spec291 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14550))) (hobl : run291.res.obligs s) :
    Steps image s run291.res.steps run291.res.cycles (run291.res.toState s) :=
  symRun_sound run291 (codeAt_layout rfl layout_ok (i := 291) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run292 := symRun { noAlias := true } seg292 (BitVec.ofNat 64 (0x1000 + 4 * 14600)) 50
theorem spec292 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14600))) (hobl : run292.res.obligs s) :
    Steps image s run292.res.steps run292.res.cycles (run292.res.toState s) :=
  symRun_sound run292 (codeAt_layout rfl layout_ok (i := 292) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run293 := symRun { noAlias := true } seg293 (BitVec.ofNat 64 (0x1000 + 4 * 14650)) 50
theorem spec293 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14650))) (hobl : run293.res.obligs s) :
    Steps image s run293.res.steps run293.res.cycles (run293.res.toState s) :=
  symRun_sound run293 (codeAt_layout rfl layout_ok (i := 293) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run294 := symRun { noAlias := true } seg294 (BitVec.ofNat 64 (0x1000 + 4 * 14700)) 50
theorem spec294 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14700))) (hobl : run294.res.obligs s) :
    Steps image s run294.res.steps run294.res.cycles (run294.res.toState s) :=
  symRun_sound run294 (codeAt_layout rfl layout_ok (i := 294) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run295 := symRun { noAlias := true } seg295 (BitVec.ofNat 64 (0x1000 + 4 * 14750)) 50
theorem spec295 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14750))) (hobl : run295.res.obligs s) :
    Steps image s run295.res.steps run295.res.cycles (run295.res.toState s) :=
  symRun_sound run295 (codeAt_layout rfl layout_ok (i := 295) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run296 := symRun { noAlias := true } seg296 (BitVec.ofNat 64 (0x1000 + 4 * 14800)) 50
theorem spec296 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14800))) (hobl : run296.res.obligs s) :
    Steps image s run296.res.steps run296.res.cycles (run296.res.toState s) :=
  symRun_sound run296 (codeAt_layout rfl layout_ok (i := 296) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run297 := symRun { noAlias := true } seg297 (BitVec.ofNat 64 (0x1000 + 4 * 14850)) 50
theorem spec297 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14850))) (hobl : run297.res.obligs s) :
    Steps image s run297.res.steps run297.res.cycles (run297.res.toState s) :=
  symRun_sound run297 (codeAt_layout rfl layout_ok (i := 297) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run298 := symRun { noAlias := true } seg298 (BitVec.ofNat 64 (0x1000 + 4 * 14900)) 50
theorem spec298 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14900))) (hobl : run298.res.obligs s) :
    Steps image s run298.res.steps run298.res.cycles (run298.res.toState s) :=
  symRun_sound run298 (codeAt_layout rfl layout_ok (i := 298) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run299 := symRun { noAlias := true } seg299 (BitVec.ofNat 64 (0x1000 + 4 * 14950)) 50
theorem spec299 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 14950))) (hobl : run299.res.obligs s) :
    Steps image s run299.res.steps run299.res.cycles (run299.res.toState s) :=
  symRun_sound run299 (codeAt_layout rfl layout_ok (i := 299) (by kernel_rfl) (by decide)) s hpc hobl

end SigGolfCandidate.Rv.Scale
