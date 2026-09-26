import SigGolfCandidate.Rv.Scale.Code

namespace SigGolfCandidate.Rv.Scale
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

sym_block run300 := symRun { noAlias := true } seg300 (BitVec.ofNat 64 (0x1000 + 4 * 15000)) 50
theorem spec300 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15000))) (hobl : run300.res.obligs s) :
    Steps image s run300.res.steps run300.res.cycles (run300.res.toState s) :=
  symRun_sound run300 (codeAt_layout rfl layout_ok (i := 300) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run301 := symRun { noAlias := true } seg301 (BitVec.ofNat 64 (0x1000 + 4 * 15050)) 50
theorem spec301 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15050))) (hobl : run301.res.obligs s) :
    Steps image s run301.res.steps run301.res.cycles (run301.res.toState s) :=
  symRun_sound run301 (codeAt_layout rfl layout_ok (i := 301) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run302 := symRun { noAlias := true } seg302 (BitVec.ofNat 64 (0x1000 + 4 * 15100)) 50
theorem spec302 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15100))) (hobl : run302.res.obligs s) :
    Steps image s run302.res.steps run302.res.cycles (run302.res.toState s) :=
  symRun_sound run302 (codeAt_layout rfl layout_ok (i := 302) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run303 := symRun { noAlias := true } seg303 (BitVec.ofNat 64 (0x1000 + 4 * 15150)) 50
theorem spec303 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15150))) (hobl : run303.res.obligs s) :
    Steps image s run303.res.steps run303.res.cycles (run303.res.toState s) :=
  symRun_sound run303 (codeAt_layout rfl layout_ok (i := 303) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run304 := symRun { noAlias := true } seg304 (BitVec.ofNat 64 (0x1000 + 4 * 15200)) 50
theorem spec304 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15200))) (hobl : run304.res.obligs s) :
    Steps image s run304.res.steps run304.res.cycles (run304.res.toState s) :=
  symRun_sound run304 (codeAt_layout rfl layout_ok (i := 304) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run305 := symRun { noAlias := true } seg305 (BitVec.ofNat 64 (0x1000 + 4 * 15250)) 50
theorem spec305 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15250))) (hobl : run305.res.obligs s) :
    Steps image s run305.res.steps run305.res.cycles (run305.res.toState s) :=
  symRun_sound run305 (codeAt_layout rfl layout_ok (i := 305) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run306 := symRun { noAlias := true } seg306 (BitVec.ofNat 64 (0x1000 + 4 * 15300)) 50
theorem spec306 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15300))) (hobl : run306.res.obligs s) :
    Steps image s run306.res.steps run306.res.cycles (run306.res.toState s) :=
  symRun_sound run306 (codeAt_layout rfl layout_ok (i := 306) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run307 := symRun { noAlias := true } seg307 (BitVec.ofNat 64 (0x1000 + 4 * 15350)) 50
theorem spec307 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15350))) (hobl : run307.res.obligs s) :
    Steps image s run307.res.steps run307.res.cycles (run307.res.toState s) :=
  symRun_sound run307 (codeAt_layout rfl layout_ok (i := 307) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run308 := symRun { noAlias := true } seg308 (BitVec.ofNat 64 (0x1000 + 4 * 15400)) 50
theorem spec308 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15400))) (hobl : run308.res.obligs s) :
    Steps image s run308.res.steps run308.res.cycles (run308.res.toState s) :=
  symRun_sound run308 (codeAt_layout rfl layout_ok (i := 308) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run309 := symRun { noAlias := true } seg309 (BitVec.ofNat 64 (0x1000 + 4 * 15450)) 50
theorem spec309 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15450))) (hobl : run309.res.obligs s) :
    Steps image s run309.res.steps run309.res.cycles (run309.res.toState s) :=
  symRun_sound run309 (codeAt_layout rfl layout_ok (i := 309) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run310 := symRun { noAlias := true } seg310 (BitVec.ofNat 64 (0x1000 + 4 * 15500)) 50
theorem spec310 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15500))) (hobl : run310.res.obligs s) :
    Steps image s run310.res.steps run310.res.cycles (run310.res.toState s) :=
  symRun_sound run310 (codeAt_layout rfl layout_ok (i := 310) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run311 := symRun { noAlias := true } seg311 (BitVec.ofNat 64 (0x1000 + 4 * 15550)) 50
theorem spec311 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15550))) (hobl : run311.res.obligs s) :
    Steps image s run311.res.steps run311.res.cycles (run311.res.toState s) :=
  symRun_sound run311 (codeAt_layout rfl layout_ok (i := 311) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run312 := symRun { noAlias := true } seg312 (BitVec.ofNat 64 (0x1000 + 4 * 15600)) 50
theorem spec312 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15600))) (hobl : run312.res.obligs s) :
    Steps image s run312.res.steps run312.res.cycles (run312.res.toState s) :=
  symRun_sound run312 (codeAt_layout rfl layout_ok (i := 312) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run313 := symRun { noAlias := true } seg313 (BitVec.ofNat 64 (0x1000 + 4 * 15650)) 50
theorem spec313 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15650))) (hobl : run313.res.obligs s) :
    Steps image s run313.res.steps run313.res.cycles (run313.res.toState s) :=
  symRun_sound run313 (codeAt_layout rfl layout_ok (i := 313) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run314 := symRun { noAlias := true } seg314 (BitVec.ofNat 64 (0x1000 + 4 * 15700)) 50
theorem spec314 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15700))) (hobl : run314.res.obligs s) :
    Steps image s run314.res.steps run314.res.cycles (run314.res.toState s) :=
  symRun_sound run314 (codeAt_layout rfl layout_ok (i := 314) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run315 := symRun { noAlias := true } seg315 (BitVec.ofNat 64 (0x1000 + 4 * 15750)) 50
theorem spec315 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15750))) (hobl : run315.res.obligs s) :
    Steps image s run315.res.steps run315.res.cycles (run315.res.toState s) :=
  symRun_sound run315 (codeAt_layout rfl layout_ok (i := 315) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run316 := symRun { noAlias := true } seg316 (BitVec.ofNat 64 (0x1000 + 4 * 15800)) 50
theorem spec316 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15800))) (hobl : run316.res.obligs s) :
    Steps image s run316.res.steps run316.res.cycles (run316.res.toState s) :=
  symRun_sound run316 (codeAt_layout rfl layout_ok (i := 316) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run317 := symRun { noAlias := true } seg317 (BitVec.ofNat 64 (0x1000 + 4 * 15850)) 50
theorem spec317 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15850))) (hobl : run317.res.obligs s) :
    Steps image s run317.res.steps run317.res.cycles (run317.res.toState s) :=
  symRun_sound run317 (codeAt_layout rfl layout_ok (i := 317) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run318 := symRun { noAlias := true } seg318 (BitVec.ofNat 64 (0x1000 + 4 * 15900)) 50
theorem spec318 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15900))) (hobl : run318.res.obligs s) :
    Steps image s run318.res.steps run318.res.cycles (run318.res.toState s) :=
  symRun_sound run318 (codeAt_layout rfl layout_ok (i := 318) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run319 := symRun { noAlias := true } seg319 (BitVec.ofNat 64 (0x1000 + 4 * 15950)) 50
theorem spec319 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 15950))) (hobl : run319.res.obligs s) :
    Steps image s run319.res.steps run319.res.cycles (run319.res.toState s) :=
  symRun_sound run319 (codeAt_layout rfl layout_ok (i := 319) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run320 := symRun { noAlias := true } seg320 (BitVec.ofNat 64 (0x1000 + 4 * 16000)) 50
theorem spec320 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16000))) (hobl : run320.res.obligs s) :
    Steps image s run320.res.steps run320.res.cycles (run320.res.toState s) :=
  symRun_sound run320 (codeAt_layout rfl layout_ok (i := 320) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run321 := symRun { noAlias := true } seg321 (BitVec.ofNat 64 (0x1000 + 4 * 16050)) 50
theorem spec321 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16050))) (hobl : run321.res.obligs s) :
    Steps image s run321.res.steps run321.res.cycles (run321.res.toState s) :=
  symRun_sound run321 (codeAt_layout rfl layout_ok (i := 321) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run322 := symRun { noAlias := true } seg322 (BitVec.ofNat 64 (0x1000 + 4 * 16100)) 50
theorem spec322 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16100))) (hobl : run322.res.obligs s) :
    Steps image s run322.res.steps run322.res.cycles (run322.res.toState s) :=
  symRun_sound run322 (codeAt_layout rfl layout_ok (i := 322) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run323 := symRun { noAlias := true } seg323 (BitVec.ofNat 64 (0x1000 + 4 * 16150)) 50
theorem spec323 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16150))) (hobl : run323.res.obligs s) :
    Steps image s run323.res.steps run323.res.cycles (run323.res.toState s) :=
  symRun_sound run323 (codeAt_layout rfl layout_ok (i := 323) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run324 := symRun { noAlias := true } seg324 (BitVec.ofNat 64 (0x1000 + 4 * 16200)) 50
theorem spec324 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16200))) (hobl : run324.res.obligs s) :
    Steps image s run324.res.steps run324.res.cycles (run324.res.toState s) :=
  symRun_sound run324 (codeAt_layout rfl layout_ok (i := 324) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run325 := symRun { noAlias := true } seg325 (BitVec.ofNat 64 (0x1000 + 4 * 16250)) 50
theorem spec325 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16250))) (hobl : run325.res.obligs s) :
    Steps image s run325.res.steps run325.res.cycles (run325.res.toState s) :=
  symRun_sound run325 (codeAt_layout rfl layout_ok (i := 325) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run326 := symRun { noAlias := true } seg326 (BitVec.ofNat 64 (0x1000 + 4 * 16300)) 50
theorem spec326 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16300))) (hobl : run326.res.obligs s) :
    Steps image s run326.res.steps run326.res.cycles (run326.res.toState s) :=
  symRun_sound run326 (codeAt_layout rfl layout_ok (i := 326) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run327 := symRun { noAlias := true } seg327 (BitVec.ofNat 64 (0x1000 + 4 * 16350)) 50
theorem spec327 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16350))) (hobl : run327.res.obligs s) :
    Steps image s run327.res.steps run327.res.cycles (run327.res.toState s) :=
  symRun_sound run327 (codeAt_layout rfl layout_ok (i := 327) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run328 := symRun { noAlias := true } seg328 (BitVec.ofNat 64 (0x1000 + 4 * 16400)) 50
theorem spec328 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16400))) (hobl : run328.res.obligs s) :
    Steps image s run328.res.steps run328.res.cycles (run328.res.toState s) :=
  symRun_sound run328 (codeAt_layout rfl layout_ok (i := 328) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run329 := symRun { noAlias := true } seg329 (BitVec.ofNat 64 (0x1000 + 4 * 16450)) 50
theorem spec329 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16450))) (hobl : run329.res.obligs s) :
    Steps image s run329.res.steps run329.res.cycles (run329.res.toState s) :=
  symRun_sound run329 (codeAt_layout rfl layout_ok (i := 329) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run330 := symRun { noAlias := true } seg330 (BitVec.ofNat 64 (0x1000 + 4 * 16500)) 50
theorem spec330 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16500))) (hobl : run330.res.obligs s) :
    Steps image s run330.res.steps run330.res.cycles (run330.res.toState s) :=
  symRun_sound run330 (codeAt_layout rfl layout_ok (i := 330) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run331 := symRun { noAlias := true } seg331 (BitVec.ofNat 64 (0x1000 + 4 * 16550)) 50
theorem spec331 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16550))) (hobl : run331.res.obligs s) :
    Steps image s run331.res.steps run331.res.cycles (run331.res.toState s) :=
  symRun_sound run331 (codeAt_layout rfl layout_ok (i := 331) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run332 := symRun { noAlias := true } seg332 (BitVec.ofNat 64 (0x1000 + 4 * 16600)) 50
theorem spec332 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16600))) (hobl : run332.res.obligs s) :
    Steps image s run332.res.steps run332.res.cycles (run332.res.toState s) :=
  symRun_sound run332 (codeAt_layout rfl layout_ok (i := 332) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run333 := symRun { noAlias := true } seg333 (BitVec.ofNat 64 (0x1000 + 4 * 16650)) 50
theorem spec333 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16650))) (hobl : run333.res.obligs s) :
    Steps image s run333.res.steps run333.res.cycles (run333.res.toState s) :=
  symRun_sound run333 (codeAt_layout rfl layout_ok (i := 333) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run334 := symRun { noAlias := true } seg334 (BitVec.ofNat 64 (0x1000 + 4 * 16700)) 50
theorem spec334 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16700))) (hobl : run334.res.obligs s) :
    Steps image s run334.res.steps run334.res.cycles (run334.res.toState s) :=
  symRun_sound run334 (codeAt_layout rfl layout_ok (i := 334) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run335 := symRun { noAlias := true } seg335 (BitVec.ofNat 64 (0x1000 + 4 * 16750)) 50
theorem spec335 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16750))) (hobl : run335.res.obligs s) :
    Steps image s run335.res.steps run335.res.cycles (run335.res.toState s) :=
  symRun_sound run335 (codeAt_layout rfl layout_ok (i := 335) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run336 := symRun { noAlias := true } seg336 (BitVec.ofNat 64 (0x1000 + 4 * 16800)) 50
theorem spec336 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16800))) (hobl : run336.res.obligs s) :
    Steps image s run336.res.steps run336.res.cycles (run336.res.toState s) :=
  symRun_sound run336 (codeAt_layout rfl layout_ok (i := 336) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run337 := symRun { noAlias := true } seg337 (BitVec.ofNat 64 (0x1000 + 4 * 16850)) 50
theorem spec337 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16850))) (hobl : run337.res.obligs s) :
    Steps image s run337.res.steps run337.res.cycles (run337.res.toState s) :=
  symRun_sound run337 (codeAt_layout rfl layout_ok (i := 337) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run338 := symRun { noAlias := true } seg338 (BitVec.ofNat 64 (0x1000 + 4 * 16900)) 50
theorem spec338 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16900))) (hobl : run338.res.obligs s) :
    Steps image s run338.res.steps run338.res.cycles (run338.res.toState s) :=
  symRun_sound run338 (codeAt_layout rfl layout_ok (i := 338) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run339 := symRun { noAlias := true } seg339 (BitVec.ofNat 64 (0x1000 + 4 * 16950)) 50
theorem spec339 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 16950))) (hobl : run339.res.obligs s) :
    Steps image s run339.res.steps run339.res.cycles (run339.res.toState s) :=
  symRun_sound run339 (codeAt_layout rfl layout_ok (i := 339) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run340 := symRun { noAlias := true } seg340 (BitVec.ofNat 64 (0x1000 + 4 * 17000)) 50
theorem spec340 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17000))) (hobl : run340.res.obligs s) :
    Steps image s run340.res.steps run340.res.cycles (run340.res.toState s) :=
  symRun_sound run340 (codeAt_layout rfl layout_ok (i := 340) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run341 := symRun { noAlias := true } seg341 (BitVec.ofNat 64 (0x1000 + 4 * 17050)) 50
theorem spec341 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17050))) (hobl : run341.res.obligs s) :
    Steps image s run341.res.steps run341.res.cycles (run341.res.toState s) :=
  symRun_sound run341 (codeAt_layout rfl layout_ok (i := 341) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run342 := symRun { noAlias := true } seg342 (BitVec.ofNat 64 (0x1000 + 4 * 17100)) 50
theorem spec342 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17100))) (hobl : run342.res.obligs s) :
    Steps image s run342.res.steps run342.res.cycles (run342.res.toState s) :=
  symRun_sound run342 (codeAt_layout rfl layout_ok (i := 342) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run343 := symRun { noAlias := true } seg343 (BitVec.ofNat 64 (0x1000 + 4 * 17150)) 50
theorem spec343 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17150))) (hobl : run343.res.obligs s) :
    Steps image s run343.res.steps run343.res.cycles (run343.res.toState s) :=
  symRun_sound run343 (codeAt_layout rfl layout_ok (i := 343) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run344 := symRun { noAlias := true } seg344 (BitVec.ofNat 64 (0x1000 + 4 * 17200)) 50
theorem spec344 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17200))) (hobl : run344.res.obligs s) :
    Steps image s run344.res.steps run344.res.cycles (run344.res.toState s) :=
  symRun_sound run344 (codeAt_layout rfl layout_ok (i := 344) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run345 := symRun { noAlias := true } seg345 (BitVec.ofNat 64 (0x1000 + 4 * 17250)) 50
theorem spec345 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17250))) (hobl : run345.res.obligs s) :
    Steps image s run345.res.steps run345.res.cycles (run345.res.toState s) :=
  symRun_sound run345 (codeAt_layout rfl layout_ok (i := 345) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run346 := symRun { noAlias := true } seg346 (BitVec.ofNat 64 (0x1000 + 4 * 17300)) 50
theorem spec346 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17300))) (hobl : run346.res.obligs s) :
    Steps image s run346.res.steps run346.res.cycles (run346.res.toState s) :=
  symRun_sound run346 (codeAt_layout rfl layout_ok (i := 346) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run347 := symRun { noAlias := true } seg347 (BitVec.ofNat 64 (0x1000 + 4 * 17350)) 50
theorem spec347 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17350))) (hobl : run347.res.obligs s) :
    Steps image s run347.res.steps run347.res.cycles (run347.res.toState s) :=
  symRun_sound run347 (codeAt_layout rfl layout_ok (i := 347) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run348 := symRun { noAlias := true } seg348 (BitVec.ofNat 64 (0x1000 + 4 * 17400)) 50
theorem spec348 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17400))) (hobl : run348.res.obligs s) :
    Steps image s run348.res.steps run348.res.cycles (run348.res.toState s) :=
  symRun_sound run348 (codeAt_layout rfl layout_ok (i := 348) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run349 := symRun { noAlias := true } seg349 (BitVec.ofNat 64 (0x1000 + 4 * 17450)) 50
theorem spec349 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 17450))) (hobl : run349.res.obligs s) :
    Steps image s run349.res.steps run349.res.cycles (run349.res.toState s) :=
  symRun_sound run349 (codeAt_layout rfl layout_ok (i := 349) (by kernel_rfl) (by decide)) s hpc hobl

end SigGolfCandidate.Rv.Scale
