import SigGolfCandidate.Rv.Scale.Code

namespace SigGolfCandidate.Rv.Scale
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

sym_block run0 := symRun { noAlias := true } seg0 (BitVec.ofNat 64 (0x1000 + 4 * 0)) 50
theorem spec0 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 0))) (hobl : run0.res.obligs s) :
    Steps image s run0.res.steps run0.res.cycles (run0.res.toState s) :=
  symRun_sound run0 (codeAt_layout rfl layout_ok (i := 0) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run1 := symRun { noAlias := true } seg1 (BitVec.ofNat 64 (0x1000 + 4 * 50)) 50
theorem spec1 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 50))) (hobl : run1.res.obligs s) :
    Steps image s run1.res.steps run1.res.cycles (run1.res.toState s) :=
  symRun_sound run1 (codeAt_layout rfl layout_ok (i := 1) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run2 := symRun { noAlias := true } seg2 (BitVec.ofNat 64 (0x1000 + 4 * 100)) 50
theorem spec2 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 100))) (hobl : run2.res.obligs s) :
    Steps image s run2.res.steps run2.res.cycles (run2.res.toState s) :=
  symRun_sound run2 (codeAt_layout rfl layout_ok (i := 2) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run3 := symRun { noAlias := true } seg3 (BitVec.ofNat 64 (0x1000 + 4 * 150)) 50
theorem spec3 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 150))) (hobl : run3.res.obligs s) :
    Steps image s run3.res.steps run3.res.cycles (run3.res.toState s) :=
  symRun_sound run3 (codeAt_layout rfl layout_ok (i := 3) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run4 := symRun { noAlias := true } seg4 (BitVec.ofNat 64 (0x1000 + 4 * 200)) 50
theorem spec4 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 200))) (hobl : run4.res.obligs s) :
    Steps image s run4.res.steps run4.res.cycles (run4.res.toState s) :=
  symRun_sound run4 (codeAt_layout rfl layout_ok (i := 4) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run5 := symRun { noAlias := true } seg5 (BitVec.ofNat 64 (0x1000 + 4 * 250)) 50
theorem spec5 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 250))) (hobl : run5.res.obligs s) :
    Steps image s run5.res.steps run5.res.cycles (run5.res.toState s) :=
  symRun_sound run5 (codeAt_layout rfl layout_ok (i := 5) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run6 := symRun { noAlias := true } seg6 (BitVec.ofNat 64 (0x1000 + 4 * 300)) 50
theorem spec6 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 300))) (hobl : run6.res.obligs s) :
    Steps image s run6.res.steps run6.res.cycles (run6.res.toState s) :=
  symRun_sound run6 (codeAt_layout rfl layout_ok (i := 6) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run7 := symRun { noAlias := true } seg7 (BitVec.ofNat 64 (0x1000 + 4 * 350)) 50
theorem spec7 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 350))) (hobl : run7.res.obligs s) :
    Steps image s run7.res.steps run7.res.cycles (run7.res.toState s) :=
  symRun_sound run7 (codeAt_layout rfl layout_ok (i := 7) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run8 := symRun { noAlias := true } seg8 (BitVec.ofNat 64 (0x1000 + 4 * 400)) 50
theorem spec8 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 400))) (hobl : run8.res.obligs s) :
    Steps image s run8.res.steps run8.res.cycles (run8.res.toState s) :=
  symRun_sound run8 (codeAt_layout rfl layout_ok (i := 8) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run9 := symRun { noAlias := true } seg9 (BitVec.ofNat 64 (0x1000 + 4 * 450)) 50
theorem spec9 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 450))) (hobl : run9.res.obligs s) :
    Steps image s run9.res.steps run9.res.cycles (run9.res.toState s) :=
  symRun_sound run9 (codeAt_layout rfl layout_ok (i := 9) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run10 := symRun { noAlias := true } seg10 (BitVec.ofNat 64 (0x1000 + 4 * 500)) 50
theorem spec10 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 500))) (hobl : run10.res.obligs s) :
    Steps image s run10.res.steps run10.res.cycles (run10.res.toState s) :=
  symRun_sound run10 (codeAt_layout rfl layout_ok (i := 10) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run11 := symRun { noAlias := true } seg11 (BitVec.ofNat 64 (0x1000 + 4 * 550)) 50
theorem spec11 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 550))) (hobl : run11.res.obligs s) :
    Steps image s run11.res.steps run11.res.cycles (run11.res.toState s) :=
  symRun_sound run11 (codeAt_layout rfl layout_ok (i := 11) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run12 := symRun { noAlias := true } seg12 (BitVec.ofNat 64 (0x1000 + 4 * 600)) 50
theorem spec12 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 600))) (hobl : run12.res.obligs s) :
    Steps image s run12.res.steps run12.res.cycles (run12.res.toState s) :=
  symRun_sound run12 (codeAt_layout rfl layout_ok (i := 12) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run13 := symRun { noAlias := true } seg13 (BitVec.ofNat 64 (0x1000 + 4 * 650)) 50
theorem spec13 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 650))) (hobl : run13.res.obligs s) :
    Steps image s run13.res.steps run13.res.cycles (run13.res.toState s) :=
  symRun_sound run13 (codeAt_layout rfl layout_ok (i := 13) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run14 := symRun { noAlias := true } seg14 (BitVec.ofNat 64 (0x1000 + 4 * 700)) 50
theorem spec14 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 700))) (hobl : run14.res.obligs s) :
    Steps image s run14.res.steps run14.res.cycles (run14.res.toState s) :=
  symRun_sound run14 (codeAt_layout rfl layout_ok (i := 14) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run15 := symRun { noAlias := true } seg15 (BitVec.ofNat 64 (0x1000 + 4 * 750)) 50
theorem spec15 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 750))) (hobl : run15.res.obligs s) :
    Steps image s run15.res.steps run15.res.cycles (run15.res.toState s) :=
  symRun_sound run15 (codeAt_layout rfl layout_ok (i := 15) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run16 := symRun { noAlias := true } seg16 (BitVec.ofNat 64 (0x1000 + 4 * 800)) 50
theorem spec16 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 800))) (hobl : run16.res.obligs s) :
    Steps image s run16.res.steps run16.res.cycles (run16.res.toState s) :=
  symRun_sound run16 (codeAt_layout rfl layout_ok (i := 16) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run17 := symRun { noAlias := true } seg17 (BitVec.ofNat 64 (0x1000 + 4 * 850)) 50
theorem spec17 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 850))) (hobl : run17.res.obligs s) :
    Steps image s run17.res.steps run17.res.cycles (run17.res.toState s) :=
  symRun_sound run17 (codeAt_layout rfl layout_ok (i := 17) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run18 := symRun { noAlias := true } seg18 (BitVec.ofNat 64 (0x1000 + 4 * 900)) 50
theorem spec18 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 900))) (hobl : run18.res.obligs s) :
    Steps image s run18.res.steps run18.res.cycles (run18.res.toState s) :=
  symRun_sound run18 (codeAt_layout rfl layout_ok (i := 18) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run19 := symRun { noAlias := true } seg19 (BitVec.ofNat 64 (0x1000 + 4 * 950)) 50
theorem spec19 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 950))) (hobl : run19.res.obligs s) :
    Steps image s run19.res.steps run19.res.cycles (run19.res.toState s) :=
  symRun_sound run19 (codeAt_layout rfl layout_ok (i := 19) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run20 := symRun { noAlias := true } seg20 (BitVec.ofNat 64 (0x1000 + 4 * 1000)) 50
theorem spec20 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1000))) (hobl : run20.res.obligs s) :
    Steps image s run20.res.steps run20.res.cycles (run20.res.toState s) :=
  symRun_sound run20 (codeAt_layout rfl layout_ok (i := 20) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run21 := symRun { noAlias := true } seg21 (BitVec.ofNat 64 (0x1000 + 4 * 1050)) 50
theorem spec21 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1050))) (hobl : run21.res.obligs s) :
    Steps image s run21.res.steps run21.res.cycles (run21.res.toState s) :=
  symRun_sound run21 (codeAt_layout rfl layout_ok (i := 21) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run22 := symRun { noAlias := true } seg22 (BitVec.ofNat 64 (0x1000 + 4 * 1100)) 50
theorem spec22 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1100))) (hobl : run22.res.obligs s) :
    Steps image s run22.res.steps run22.res.cycles (run22.res.toState s) :=
  symRun_sound run22 (codeAt_layout rfl layout_ok (i := 22) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run23 := symRun { noAlias := true } seg23 (BitVec.ofNat 64 (0x1000 + 4 * 1150)) 50
theorem spec23 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1150))) (hobl : run23.res.obligs s) :
    Steps image s run23.res.steps run23.res.cycles (run23.res.toState s) :=
  symRun_sound run23 (codeAt_layout rfl layout_ok (i := 23) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run24 := symRun { noAlias := true } seg24 (BitVec.ofNat 64 (0x1000 + 4 * 1200)) 50
theorem spec24 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1200))) (hobl : run24.res.obligs s) :
    Steps image s run24.res.steps run24.res.cycles (run24.res.toState s) :=
  symRun_sound run24 (codeAt_layout rfl layout_ok (i := 24) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run25 := symRun { noAlias := true } seg25 (BitVec.ofNat 64 (0x1000 + 4 * 1250)) 50
theorem spec25 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1250))) (hobl : run25.res.obligs s) :
    Steps image s run25.res.steps run25.res.cycles (run25.res.toState s) :=
  symRun_sound run25 (codeAt_layout rfl layout_ok (i := 25) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run26 := symRun { noAlias := true } seg26 (BitVec.ofNat 64 (0x1000 + 4 * 1300)) 50
theorem spec26 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1300))) (hobl : run26.res.obligs s) :
    Steps image s run26.res.steps run26.res.cycles (run26.res.toState s) :=
  symRun_sound run26 (codeAt_layout rfl layout_ok (i := 26) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run27 := symRun { noAlias := true } seg27 (BitVec.ofNat 64 (0x1000 + 4 * 1350)) 50
theorem spec27 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1350))) (hobl : run27.res.obligs s) :
    Steps image s run27.res.steps run27.res.cycles (run27.res.toState s) :=
  symRun_sound run27 (codeAt_layout rfl layout_ok (i := 27) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run28 := symRun { noAlias := true } seg28 (BitVec.ofNat 64 (0x1000 + 4 * 1400)) 50
theorem spec28 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1400))) (hobl : run28.res.obligs s) :
    Steps image s run28.res.steps run28.res.cycles (run28.res.toState s) :=
  symRun_sound run28 (codeAt_layout rfl layout_ok (i := 28) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run29 := symRun { noAlias := true } seg29 (BitVec.ofNat 64 (0x1000 + 4 * 1450)) 50
theorem spec29 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1450))) (hobl : run29.res.obligs s) :
    Steps image s run29.res.steps run29.res.cycles (run29.res.toState s) :=
  symRun_sound run29 (codeAt_layout rfl layout_ok (i := 29) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run30 := symRun { noAlias := true } seg30 (BitVec.ofNat 64 (0x1000 + 4 * 1500)) 50
theorem spec30 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1500))) (hobl : run30.res.obligs s) :
    Steps image s run30.res.steps run30.res.cycles (run30.res.toState s) :=
  symRun_sound run30 (codeAt_layout rfl layout_ok (i := 30) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run31 := symRun { noAlias := true } seg31 (BitVec.ofNat 64 (0x1000 + 4 * 1550)) 50
theorem spec31 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1550))) (hobl : run31.res.obligs s) :
    Steps image s run31.res.steps run31.res.cycles (run31.res.toState s) :=
  symRun_sound run31 (codeAt_layout rfl layout_ok (i := 31) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run32 := symRun { noAlias := true } seg32 (BitVec.ofNat 64 (0x1000 + 4 * 1600)) 50
theorem spec32 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1600))) (hobl : run32.res.obligs s) :
    Steps image s run32.res.steps run32.res.cycles (run32.res.toState s) :=
  symRun_sound run32 (codeAt_layout rfl layout_ok (i := 32) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run33 := symRun { noAlias := true } seg33 (BitVec.ofNat 64 (0x1000 + 4 * 1650)) 50
theorem spec33 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1650))) (hobl : run33.res.obligs s) :
    Steps image s run33.res.steps run33.res.cycles (run33.res.toState s) :=
  symRun_sound run33 (codeAt_layout rfl layout_ok (i := 33) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run34 := symRun { noAlias := true } seg34 (BitVec.ofNat 64 (0x1000 + 4 * 1700)) 50
theorem spec34 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1700))) (hobl : run34.res.obligs s) :
    Steps image s run34.res.steps run34.res.cycles (run34.res.toState s) :=
  symRun_sound run34 (codeAt_layout rfl layout_ok (i := 34) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run35 := symRun { noAlias := true } seg35 (BitVec.ofNat 64 (0x1000 + 4 * 1750)) 50
theorem spec35 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1750))) (hobl : run35.res.obligs s) :
    Steps image s run35.res.steps run35.res.cycles (run35.res.toState s) :=
  symRun_sound run35 (codeAt_layout rfl layout_ok (i := 35) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run36 := symRun { noAlias := true } seg36 (BitVec.ofNat 64 (0x1000 + 4 * 1800)) 50
theorem spec36 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1800))) (hobl : run36.res.obligs s) :
    Steps image s run36.res.steps run36.res.cycles (run36.res.toState s) :=
  symRun_sound run36 (codeAt_layout rfl layout_ok (i := 36) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run37 := symRun { noAlias := true } seg37 (BitVec.ofNat 64 (0x1000 + 4 * 1850)) 50
theorem spec37 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1850))) (hobl : run37.res.obligs s) :
    Steps image s run37.res.steps run37.res.cycles (run37.res.toState s) :=
  symRun_sound run37 (codeAt_layout rfl layout_ok (i := 37) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run38 := symRun { noAlias := true } seg38 (BitVec.ofNat 64 (0x1000 + 4 * 1900)) 50
theorem spec38 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1900))) (hobl : run38.res.obligs s) :
    Steps image s run38.res.steps run38.res.cycles (run38.res.toState s) :=
  symRun_sound run38 (codeAt_layout rfl layout_ok (i := 38) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run39 := symRun { noAlias := true } seg39 (BitVec.ofNat 64 (0x1000 + 4 * 1950)) 50
theorem spec39 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 1950))) (hobl : run39.res.obligs s) :
    Steps image s run39.res.steps run39.res.cycles (run39.res.toState s) :=
  symRun_sound run39 (codeAt_layout rfl layout_ok (i := 39) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run40 := symRun { noAlias := true } seg40 (BitVec.ofNat 64 (0x1000 + 4 * 2000)) 50
theorem spec40 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2000))) (hobl : run40.res.obligs s) :
    Steps image s run40.res.steps run40.res.cycles (run40.res.toState s) :=
  symRun_sound run40 (codeAt_layout rfl layout_ok (i := 40) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run41 := symRun { noAlias := true } seg41 (BitVec.ofNat 64 (0x1000 + 4 * 2050)) 50
theorem spec41 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2050))) (hobl : run41.res.obligs s) :
    Steps image s run41.res.steps run41.res.cycles (run41.res.toState s) :=
  symRun_sound run41 (codeAt_layout rfl layout_ok (i := 41) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run42 := symRun { noAlias := true } seg42 (BitVec.ofNat 64 (0x1000 + 4 * 2100)) 50
theorem spec42 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2100))) (hobl : run42.res.obligs s) :
    Steps image s run42.res.steps run42.res.cycles (run42.res.toState s) :=
  symRun_sound run42 (codeAt_layout rfl layout_ok (i := 42) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run43 := symRun { noAlias := true } seg43 (BitVec.ofNat 64 (0x1000 + 4 * 2150)) 50
theorem spec43 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2150))) (hobl : run43.res.obligs s) :
    Steps image s run43.res.steps run43.res.cycles (run43.res.toState s) :=
  symRun_sound run43 (codeAt_layout rfl layout_ok (i := 43) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run44 := symRun { noAlias := true } seg44 (BitVec.ofNat 64 (0x1000 + 4 * 2200)) 50
theorem spec44 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2200))) (hobl : run44.res.obligs s) :
    Steps image s run44.res.steps run44.res.cycles (run44.res.toState s) :=
  symRun_sound run44 (codeAt_layout rfl layout_ok (i := 44) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run45 := symRun { noAlias := true } seg45 (BitVec.ofNat 64 (0x1000 + 4 * 2250)) 50
theorem spec45 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2250))) (hobl : run45.res.obligs s) :
    Steps image s run45.res.steps run45.res.cycles (run45.res.toState s) :=
  symRun_sound run45 (codeAt_layout rfl layout_ok (i := 45) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run46 := symRun { noAlias := true } seg46 (BitVec.ofNat 64 (0x1000 + 4 * 2300)) 50
theorem spec46 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2300))) (hobl : run46.res.obligs s) :
    Steps image s run46.res.steps run46.res.cycles (run46.res.toState s) :=
  symRun_sound run46 (codeAt_layout rfl layout_ok (i := 46) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run47 := symRun { noAlias := true } seg47 (BitVec.ofNat 64 (0x1000 + 4 * 2350)) 50
theorem spec47 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2350))) (hobl : run47.res.obligs s) :
    Steps image s run47.res.steps run47.res.cycles (run47.res.toState s) :=
  symRun_sound run47 (codeAt_layout rfl layout_ok (i := 47) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run48 := symRun { noAlias := true } seg48 (BitVec.ofNat 64 (0x1000 + 4 * 2400)) 50
theorem spec48 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2400))) (hobl : run48.res.obligs s) :
    Steps image s run48.res.steps run48.res.cycles (run48.res.toState s) :=
  symRun_sound run48 (codeAt_layout rfl layout_ok (i := 48) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run49 := symRun { noAlias := true } seg49 (BitVec.ofNat 64 (0x1000 + 4 * 2450)) 50
theorem spec49 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 2450))) (hobl : run49.res.obligs s) :
    Steps image s run49.res.steps run49.res.cycles (run49.res.toState s) :=
  symRun_sound run49 (codeAt_layout rfl layout_ok (i := 49) (by kernel_rfl) (by decide)) s hpc hobl

end SigGolfCandidate.Rv.Scale
