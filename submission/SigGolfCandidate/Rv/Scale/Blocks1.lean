import SigGolfCandidate.Rv.Scale.Code

namespace SigGolfCandidate.Rv.Scale
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

sym_block run50 := symRun { noAlias := true } seg50 (BitVec.ofNat 64 (0x1000 + 4 * 2500)) 50
theorem spec50 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2500))) (hobl : run50.res.obligs s) :
    Steps image s run50.res.steps run50.res.cycles (run50.res.toState s) :=
  symRun_sound run50 (codeAt_layout rfl layout_ok (i := 50) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run51 := symRun { noAlias := true } seg51 (BitVec.ofNat 64 (0x1000 + 4 * 2550)) 50
theorem spec51 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2550))) (hobl : run51.res.obligs s) :
    Steps image s run51.res.steps run51.res.cycles (run51.res.toState s) :=
  symRun_sound run51 (codeAt_layout rfl layout_ok (i := 51) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run52 := symRun { noAlias := true } seg52 (BitVec.ofNat 64 (0x1000 + 4 * 2600)) 50
theorem spec52 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2600))) (hobl : run52.res.obligs s) :
    Steps image s run52.res.steps run52.res.cycles (run52.res.toState s) :=
  symRun_sound run52 (codeAt_layout rfl layout_ok (i := 52) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run53 := symRun { noAlias := true } seg53 (BitVec.ofNat 64 (0x1000 + 4 * 2650)) 50
theorem spec53 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2650))) (hobl : run53.res.obligs s) :
    Steps image s run53.res.steps run53.res.cycles (run53.res.toState s) :=
  symRun_sound run53 (codeAt_layout rfl layout_ok (i := 53) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run54 := symRun { noAlias := true } seg54 (BitVec.ofNat 64 (0x1000 + 4 * 2700)) 50
theorem spec54 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2700))) (hobl : run54.res.obligs s) :
    Steps image s run54.res.steps run54.res.cycles (run54.res.toState s) :=
  symRun_sound run54 (codeAt_layout rfl layout_ok (i := 54) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run55 := symRun { noAlias := true } seg55 (BitVec.ofNat 64 (0x1000 + 4 * 2750)) 50
theorem spec55 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2750))) (hobl : run55.res.obligs s) :
    Steps image s run55.res.steps run55.res.cycles (run55.res.toState s) :=
  symRun_sound run55 (codeAt_layout rfl layout_ok (i := 55) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run56 := symRun { noAlias := true } seg56 (BitVec.ofNat 64 (0x1000 + 4 * 2800)) 50
theorem spec56 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2800))) (hobl : run56.res.obligs s) :
    Steps image s run56.res.steps run56.res.cycles (run56.res.toState s) :=
  symRun_sound run56 (codeAt_layout rfl layout_ok (i := 56) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run57 := symRun { noAlias := true } seg57 (BitVec.ofNat 64 (0x1000 + 4 * 2850)) 50
theorem spec57 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2850))) (hobl : run57.res.obligs s) :
    Steps image s run57.res.steps run57.res.cycles (run57.res.toState s) :=
  symRun_sound run57 (codeAt_layout rfl layout_ok (i := 57) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run58 := symRun { noAlias := true } seg58 (BitVec.ofNat 64 (0x1000 + 4 * 2900)) 50
theorem spec58 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2900))) (hobl : run58.res.obligs s) :
    Steps image s run58.res.steps run58.res.cycles (run58.res.toState s) :=
  symRun_sound run58 (codeAt_layout rfl layout_ok (i := 58) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run59 := symRun { noAlias := true } seg59 (BitVec.ofNat 64 (0x1000 + 4 * 2950)) 50
theorem spec59 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2950))) (hobl : run59.res.obligs s) :
    Steps image s run59.res.steps run59.res.cycles (run59.res.toState s) :=
  symRun_sound run59 (codeAt_layout rfl layout_ok (i := 59) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run60 := symRun { noAlias := true } seg60 (BitVec.ofNat 64 (0x1000 + 4 * 3000)) 50
theorem spec60 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3000))) (hobl : run60.res.obligs s) :
    Steps image s run60.res.steps run60.res.cycles (run60.res.toState s) :=
  symRun_sound run60 (codeAt_layout rfl layout_ok (i := 60) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run61 := symRun { noAlias := true } seg61 (BitVec.ofNat 64 (0x1000 + 4 * 3050)) 50
theorem spec61 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3050))) (hobl : run61.res.obligs s) :
    Steps image s run61.res.steps run61.res.cycles (run61.res.toState s) :=
  symRun_sound run61 (codeAt_layout rfl layout_ok (i := 61) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run62 := symRun { noAlias := true } seg62 (BitVec.ofNat 64 (0x1000 + 4 * 3100)) 50
theorem spec62 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3100))) (hobl : run62.res.obligs s) :
    Steps image s run62.res.steps run62.res.cycles (run62.res.toState s) :=
  symRun_sound run62 (codeAt_layout rfl layout_ok (i := 62) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run63 := symRun { noAlias := true } seg63 (BitVec.ofNat 64 (0x1000 + 4 * 3150)) 50
theorem spec63 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3150))) (hobl : run63.res.obligs s) :
    Steps image s run63.res.steps run63.res.cycles (run63.res.toState s) :=
  symRun_sound run63 (codeAt_layout rfl layout_ok (i := 63) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run64 := symRun { noAlias := true } seg64 (BitVec.ofNat 64 (0x1000 + 4 * 3200)) 50
theorem spec64 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3200))) (hobl : run64.res.obligs s) :
    Steps image s run64.res.steps run64.res.cycles (run64.res.toState s) :=
  symRun_sound run64 (codeAt_layout rfl layout_ok (i := 64) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run65 := symRun { noAlias := true } seg65 (BitVec.ofNat 64 (0x1000 + 4 * 3250)) 50
theorem spec65 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3250))) (hobl : run65.res.obligs s) :
    Steps image s run65.res.steps run65.res.cycles (run65.res.toState s) :=
  symRun_sound run65 (codeAt_layout rfl layout_ok (i := 65) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run66 := symRun { noAlias := true } seg66 (BitVec.ofNat 64 (0x1000 + 4 * 3300)) 50
theorem spec66 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3300))) (hobl : run66.res.obligs s) :
    Steps image s run66.res.steps run66.res.cycles (run66.res.toState s) :=
  symRun_sound run66 (codeAt_layout rfl layout_ok (i := 66) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run67 := symRun { noAlias := true } seg67 (BitVec.ofNat 64 (0x1000 + 4 * 3350)) 50
theorem spec67 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3350))) (hobl : run67.res.obligs s) :
    Steps image s run67.res.steps run67.res.cycles (run67.res.toState s) :=
  symRun_sound run67 (codeAt_layout rfl layout_ok (i := 67) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run68 := symRun { noAlias := true } seg68 (BitVec.ofNat 64 (0x1000 + 4 * 3400)) 50
theorem spec68 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3400))) (hobl : run68.res.obligs s) :
    Steps image s run68.res.steps run68.res.cycles (run68.res.toState s) :=
  symRun_sound run68 (codeAt_layout rfl layout_ok (i := 68) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run69 := symRun { noAlias := true } seg69 (BitVec.ofNat 64 (0x1000 + 4 * 3450)) 50
theorem spec69 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3450))) (hobl : run69.res.obligs s) :
    Steps image s run69.res.steps run69.res.cycles (run69.res.toState s) :=
  symRun_sound run69 (codeAt_layout rfl layout_ok (i := 69) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run70 := symRun { noAlias := true } seg70 (BitVec.ofNat 64 (0x1000 + 4 * 3500)) 50
theorem spec70 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3500))) (hobl : run70.res.obligs s) :
    Steps image s run70.res.steps run70.res.cycles (run70.res.toState s) :=
  symRun_sound run70 (codeAt_layout rfl layout_ok (i := 70) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run71 := symRun { noAlias := true } seg71 (BitVec.ofNat 64 (0x1000 + 4 * 3550)) 50
theorem spec71 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3550))) (hobl : run71.res.obligs s) :
    Steps image s run71.res.steps run71.res.cycles (run71.res.toState s) :=
  symRun_sound run71 (codeAt_layout rfl layout_ok (i := 71) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run72 := symRun { noAlias := true } seg72 (BitVec.ofNat 64 (0x1000 + 4 * 3600)) 50
theorem spec72 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3600))) (hobl : run72.res.obligs s) :
    Steps image s run72.res.steps run72.res.cycles (run72.res.toState s) :=
  symRun_sound run72 (codeAt_layout rfl layout_ok (i := 72) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run73 := symRun { noAlias := true } seg73 (BitVec.ofNat 64 (0x1000 + 4 * 3650)) 50
theorem spec73 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3650))) (hobl : run73.res.obligs s) :
    Steps image s run73.res.steps run73.res.cycles (run73.res.toState s) :=
  symRun_sound run73 (codeAt_layout rfl layout_ok (i := 73) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run74 := symRun { noAlias := true } seg74 (BitVec.ofNat 64 (0x1000 + 4 * 3700)) 50
theorem spec74 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3700))) (hobl : run74.res.obligs s) :
    Steps image s run74.res.steps run74.res.cycles (run74.res.toState s) :=
  symRun_sound run74 (codeAt_layout rfl layout_ok (i := 74) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run75 := symRun { noAlias := true } seg75 (BitVec.ofNat 64 (0x1000 + 4 * 3750)) 50
theorem spec75 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3750))) (hobl : run75.res.obligs s) :
    Steps image s run75.res.steps run75.res.cycles (run75.res.toState s) :=
  symRun_sound run75 (codeAt_layout rfl layout_ok (i := 75) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run76 := symRun { noAlias := true } seg76 (BitVec.ofNat 64 (0x1000 + 4 * 3800)) 50
theorem spec76 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3800))) (hobl : run76.res.obligs s) :
    Steps image s run76.res.steps run76.res.cycles (run76.res.toState s) :=
  symRun_sound run76 (codeAt_layout rfl layout_ok (i := 76) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run77 := symRun { noAlias := true } seg77 (BitVec.ofNat 64 (0x1000 + 4 * 3850)) 50
theorem spec77 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3850))) (hobl : run77.res.obligs s) :
    Steps image s run77.res.steps run77.res.cycles (run77.res.toState s) :=
  symRun_sound run77 (codeAt_layout rfl layout_ok (i := 77) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run78 := symRun { noAlias := true } seg78 (BitVec.ofNat 64 (0x1000 + 4 * 3900)) 50
theorem spec78 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3900))) (hobl : run78.res.obligs s) :
    Steps image s run78.res.steps run78.res.cycles (run78.res.toState s) :=
  symRun_sound run78 (codeAt_layout rfl layout_ok (i := 78) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run79 := symRun { noAlias := true } seg79 (BitVec.ofNat 64 (0x1000 + 4 * 3950)) 50
theorem spec79 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 3950))) (hobl : run79.res.obligs s) :
    Steps image s run79.res.steps run79.res.cycles (run79.res.toState s) :=
  symRun_sound run79 (codeAt_layout rfl layout_ok (i := 79) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run80 := symRun { noAlias := true } seg80 (BitVec.ofNat 64 (0x1000 + 4 * 4000)) 50
theorem spec80 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4000))) (hobl : run80.res.obligs s) :
    Steps image s run80.res.steps run80.res.cycles (run80.res.toState s) :=
  symRun_sound run80 (codeAt_layout rfl layout_ok (i := 80) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run81 := symRun { noAlias := true } seg81 (BitVec.ofNat 64 (0x1000 + 4 * 4050)) 50
theorem spec81 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4050))) (hobl : run81.res.obligs s) :
    Steps image s run81.res.steps run81.res.cycles (run81.res.toState s) :=
  symRun_sound run81 (codeAt_layout rfl layout_ok (i := 81) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run82 := symRun { noAlias := true } seg82 (BitVec.ofNat 64 (0x1000 + 4 * 4100)) 50
theorem spec82 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4100))) (hobl : run82.res.obligs s) :
    Steps image s run82.res.steps run82.res.cycles (run82.res.toState s) :=
  symRun_sound run82 (codeAt_layout rfl layout_ok (i := 82) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run83 := symRun { noAlias := true } seg83 (BitVec.ofNat 64 (0x1000 + 4 * 4150)) 50
theorem spec83 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4150))) (hobl : run83.res.obligs s) :
    Steps image s run83.res.steps run83.res.cycles (run83.res.toState s) :=
  symRun_sound run83 (codeAt_layout rfl layout_ok (i := 83) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run84 := symRun { noAlias := true } seg84 (BitVec.ofNat 64 (0x1000 + 4 * 4200)) 50
theorem spec84 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4200))) (hobl : run84.res.obligs s) :
    Steps image s run84.res.steps run84.res.cycles (run84.res.toState s) :=
  symRun_sound run84 (codeAt_layout rfl layout_ok (i := 84) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run85 := symRun { noAlias := true } seg85 (BitVec.ofNat 64 (0x1000 + 4 * 4250)) 50
theorem spec85 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4250))) (hobl : run85.res.obligs s) :
    Steps image s run85.res.steps run85.res.cycles (run85.res.toState s) :=
  symRun_sound run85 (codeAt_layout rfl layout_ok (i := 85) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run86 := symRun { noAlias := true } seg86 (BitVec.ofNat 64 (0x1000 + 4 * 4300)) 50
theorem spec86 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4300))) (hobl : run86.res.obligs s) :
    Steps image s run86.res.steps run86.res.cycles (run86.res.toState s) :=
  symRun_sound run86 (codeAt_layout rfl layout_ok (i := 86) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run87 := symRun { noAlias := true } seg87 (BitVec.ofNat 64 (0x1000 + 4 * 4350)) 50
theorem spec87 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4350))) (hobl : run87.res.obligs s) :
    Steps image s run87.res.steps run87.res.cycles (run87.res.toState s) :=
  symRun_sound run87 (codeAt_layout rfl layout_ok (i := 87) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run88 := symRun { noAlias := true } seg88 (BitVec.ofNat 64 (0x1000 + 4 * 4400)) 50
theorem spec88 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4400))) (hobl : run88.res.obligs s) :
    Steps image s run88.res.steps run88.res.cycles (run88.res.toState s) :=
  symRun_sound run88 (codeAt_layout rfl layout_ok (i := 88) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run89 := symRun { noAlias := true } seg89 (BitVec.ofNat 64 (0x1000 + 4 * 4450)) 50
theorem spec89 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4450))) (hobl : run89.res.obligs s) :
    Steps image s run89.res.steps run89.res.cycles (run89.res.toState s) :=
  symRun_sound run89 (codeAt_layout rfl layout_ok (i := 89) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run90 := symRun { noAlias := true } seg90 (BitVec.ofNat 64 (0x1000 + 4 * 4500)) 50
theorem spec90 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4500))) (hobl : run90.res.obligs s) :
    Steps image s run90.res.steps run90.res.cycles (run90.res.toState s) :=
  symRun_sound run90 (codeAt_layout rfl layout_ok (i := 90) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run91 := symRun { noAlias := true } seg91 (BitVec.ofNat 64 (0x1000 + 4 * 4550)) 50
theorem spec91 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4550))) (hobl : run91.res.obligs s) :
    Steps image s run91.res.steps run91.res.cycles (run91.res.toState s) :=
  symRun_sound run91 (codeAt_layout rfl layout_ok (i := 91) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run92 := symRun { noAlias := true } seg92 (BitVec.ofNat 64 (0x1000 + 4 * 4600)) 50
theorem spec92 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4600))) (hobl : run92.res.obligs s) :
    Steps image s run92.res.steps run92.res.cycles (run92.res.toState s) :=
  symRun_sound run92 (codeAt_layout rfl layout_ok (i := 92) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run93 := symRun { noAlias := true } seg93 (BitVec.ofNat 64 (0x1000 + 4 * 4650)) 50
theorem spec93 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4650))) (hobl : run93.res.obligs s) :
    Steps image s run93.res.steps run93.res.cycles (run93.res.toState s) :=
  symRun_sound run93 (codeAt_layout rfl layout_ok (i := 93) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run94 := symRun { noAlias := true } seg94 (BitVec.ofNat 64 (0x1000 + 4 * 4700)) 50
theorem spec94 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4700))) (hobl : run94.res.obligs s) :
    Steps image s run94.res.steps run94.res.cycles (run94.res.toState s) :=
  symRun_sound run94 (codeAt_layout rfl layout_ok (i := 94) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run95 := symRun { noAlias := true } seg95 (BitVec.ofNat 64 (0x1000 + 4 * 4750)) 50
theorem spec95 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4750))) (hobl : run95.res.obligs s) :
    Steps image s run95.res.steps run95.res.cycles (run95.res.toState s) :=
  symRun_sound run95 (codeAt_layout rfl layout_ok (i := 95) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run96 := symRun { noAlias := true } seg96 (BitVec.ofNat 64 (0x1000 + 4 * 4800)) 50
theorem spec96 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4800))) (hobl : run96.res.obligs s) :
    Steps image s run96.res.steps run96.res.cycles (run96.res.toState s) :=
  symRun_sound run96 (codeAt_layout rfl layout_ok (i := 96) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run97 := symRun { noAlias := true } seg97 (BitVec.ofNat 64 (0x1000 + 4 * 4850)) 50
theorem spec97 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4850))) (hobl : run97.res.obligs s) :
    Steps image s run97.res.steps run97.res.cycles (run97.res.toState s) :=
  symRun_sound run97 (codeAt_layout rfl layout_ok (i := 97) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run98 := symRun { noAlias := true } seg98 (BitVec.ofNat 64 (0x1000 + 4 * 4900)) 50
theorem spec98 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4900))) (hobl : run98.res.obligs s) :
    Steps image s run98.res.steps run98.res.cycles (run98.res.toState s) :=
  symRun_sound run98 (codeAt_layout rfl layout_ok (i := 98) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run99 := symRun { noAlias := true } seg99 (BitVec.ofNat 64 (0x1000 + 4 * 4950)) 50
theorem spec99 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 4950))) (hobl : run99.res.obligs s) :
    Steps image s run99.res.steps run99.res.cycles (run99.res.toState s) :=
  symRun_sound run99 (codeAt_layout rfl layout_ok (i := 99) (by kernel_rfl) (by decide)) s hpc hobl

end SigGolfCandidate.Rv.Scale
