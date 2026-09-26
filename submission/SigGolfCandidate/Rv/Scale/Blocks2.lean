import SigGolfCandidate.Rv.Scale.Code

namespace SigGolfCandidate.Rv.Scale
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

sym_block run100 := symRun { noAlias := true } seg100 (BitVec.ofNat 64 (0x1000 + 4 * 5000)) 50
theorem spec100 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5000))) (hobl : run100.res.obligs s) :
    Steps image s run100.res.steps run100.res.cycles (run100.res.toState s) :=
  symRun_sound run100 (codeAt_layout rfl layout_ok (i := 100) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run101 := symRun { noAlias := true } seg101 (BitVec.ofNat 64 (0x1000 + 4 * 5050)) 50
theorem spec101 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5050))) (hobl : run101.res.obligs s) :
    Steps image s run101.res.steps run101.res.cycles (run101.res.toState s) :=
  symRun_sound run101 (codeAt_layout rfl layout_ok (i := 101) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run102 := symRun { noAlias := true } seg102 (BitVec.ofNat 64 (0x1000 + 4 * 5100)) 50
theorem spec102 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5100))) (hobl : run102.res.obligs s) :
    Steps image s run102.res.steps run102.res.cycles (run102.res.toState s) :=
  symRun_sound run102 (codeAt_layout rfl layout_ok (i := 102) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run103 := symRun { noAlias := true } seg103 (BitVec.ofNat 64 (0x1000 + 4 * 5150)) 50
theorem spec103 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5150))) (hobl : run103.res.obligs s) :
    Steps image s run103.res.steps run103.res.cycles (run103.res.toState s) :=
  symRun_sound run103 (codeAt_layout rfl layout_ok (i := 103) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run104 := symRun { noAlias := true } seg104 (BitVec.ofNat 64 (0x1000 + 4 * 5200)) 50
theorem spec104 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5200))) (hobl : run104.res.obligs s) :
    Steps image s run104.res.steps run104.res.cycles (run104.res.toState s) :=
  symRun_sound run104 (codeAt_layout rfl layout_ok (i := 104) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run105 := symRun { noAlias := true } seg105 (BitVec.ofNat 64 (0x1000 + 4 * 5250)) 50
theorem spec105 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5250))) (hobl : run105.res.obligs s) :
    Steps image s run105.res.steps run105.res.cycles (run105.res.toState s) :=
  symRun_sound run105 (codeAt_layout rfl layout_ok (i := 105) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run106 := symRun { noAlias := true } seg106 (BitVec.ofNat 64 (0x1000 + 4 * 5300)) 50
theorem spec106 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5300))) (hobl : run106.res.obligs s) :
    Steps image s run106.res.steps run106.res.cycles (run106.res.toState s) :=
  symRun_sound run106 (codeAt_layout rfl layout_ok (i := 106) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run107 := symRun { noAlias := true } seg107 (BitVec.ofNat 64 (0x1000 + 4 * 5350)) 50
theorem spec107 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5350))) (hobl : run107.res.obligs s) :
    Steps image s run107.res.steps run107.res.cycles (run107.res.toState s) :=
  symRun_sound run107 (codeAt_layout rfl layout_ok (i := 107) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run108 := symRun { noAlias := true } seg108 (BitVec.ofNat 64 (0x1000 + 4 * 5400)) 50
theorem spec108 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5400))) (hobl : run108.res.obligs s) :
    Steps image s run108.res.steps run108.res.cycles (run108.res.toState s) :=
  symRun_sound run108 (codeAt_layout rfl layout_ok (i := 108) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run109 := symRun { noAlias := true } seg109 (BitVec.ofNat 64 (0x1000 + 4 * 5450)) 50
theorem spec109 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5450))) (hobl : run109.res.obligs s) :
    Steps image s run109.res.steps run109.res.cycles (run109.res.toState s) :=
  symRun_sound run109 (codeAt_layout rfl layout_ok (i := 109) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run110 := symRun { noAlias := true } seg110 (BitVec.ofNat 64 (0x1000 + 4 * 5500)) 50
theorem spec110 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5500))) (hobl : run110.res.obligs s) :
    Steps image s run110.res.steps run110.res.cycles (run110.res.toState s) :=
  symRun_sound run110 (codeAt_layout rfl layout_ok (i := 110) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run111 := symRun { noAlias := true } seg111 (BitVec.ofNat 64 (0x1000 + 4 * 5550)) 50
theorem spec111 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5550))) (hobl : run111.res.obligs s) :
    Steps image s run111.res.steps run111.res.cycles (run111.res.toState s) :=
  symRun_sound run111 (codeAt_layout rfl layout_ok (i := 111) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run112 := symRun { noAlias := true } seg112 (BitVec.ofNat 64 (0x1000 + 4 * 5600)) 50
theorem spec112 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5600))) (hobl : run112.res.obligs s) :
    Steps image s run112.res.steps run112.res.cycles (run112.res.toState s) :=
  symRun_sound run112 (codeAt_layout rfl layout_ok (i := 112) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run113 := symRun { noAlias := true } seg113 (BitVec.ofNat 64 (0x1000 + 4 * 5650)) 50
theorem spec113 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5650))) (hobl : run113.res.obligs s) :
    Steps image s run113.res.steps run113.res.cycles (run113.res.toState s) :=
  symRun_sound run113 (codeAt_layout rfl layout_ok (i := 113) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run114 := symRun { noAlias := true } seg114 (BitVec.ofNat 64 (0x1000 + 4 * 5700)) 50
theorem spec114 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5700))) (hobl : run114.res.obligs s) :
    Steps image s run114.res.steps run114.res.cycles (run114.res.toState s) :=
  symRun_sound run114 (codeAt_layout rfl layout_ok (i := 114) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run115 := symRun { noAlias := true } seg115 (BitVec.ofNat 64 (0x1000 + 4 * 5750)) 50
theorem spec115 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5750))) (hobl : run115.res.obligs s) :
    Steps image s run115.res.steps run115.res.cycles (run115.res.toState s) :=
  symRun_sound run115 (codeAt_layout rfl layout_ok (i := 115) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run116 := symRun { noAlias := true } seg116 (BitVec.ofNat 64 (0x1000 + 4 * 5800)) 50
theorem spec116 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5800))) (hobl : run116.res.obligs s) :
    Steps image s run116.res.steps run116.res.cycles (run116.res.toState s) :=
  symRun_sound run116 (codeAt_layout rfl layout_ok (i := 116) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run117 := symRun { noAlias := true } seg117 (BitVec.ofNat 64 (0x1000 + 4 * 5850)) 50
theorem spec117 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5850))) (hobl : run117.res.obligs s) :
    Steps image s run117.res.steps run117.res.cycles (run117.res.toState s) :=
  symRun_sound run117 (codeAt_layout rfl layout_ok (i := 117) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run118 := symRun { noAlias := true } seg118 (BitVec.ofNat 64 (0x1000 + 4 * 5900)) 50
theorem spec118 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5900))) (hobl : run118.res.obligs s) :
    Steps image s run118.res.steps run118.res.cycles (run118.res.toState s) :=
  symRun_sound run118 (codeAt_layout rfl layout_ok (i := 118) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run119 := symRun { noAlias := true } seg119 (BitVec.ofNat 64 (0x1000 + 4 * 5950)) 50
theorem spec119 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 5950))) (hobl : run119.res.obligs s) :
    Steps image s run119.res.steps run119.res.cycles (run119.res.toState s) :=
  symRun_sound run119 (codeAt_layout rfl layout_ok (i := 119) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run120 := symRun { noAlias := true } seg120 (BitVec.ofNat 64 (0x1000 + 4 * 6000)) 50
theorem spec120 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6000))) (hobl : run120.res.obligs s) :
    Steps image s run120.res.steps run120.res.cycles (run120.res.toState s) :=
  symRun_sound run120 (codeAt_layout rfl layout_ok (i := 120) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run121 := symRun { noAlias := true } seg121 (BitVec.ofNat 64 (0x1000 + 4 * 6050)) 50
theorem spec121 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6050))) (hobl : run121.res.obligs s) :
    Steps image s run121.res.steps run121.res.cycles (run121.res.toState s) :=
  symRun_sound run121 (codeAt_layout rfl layout_ok (i := 121) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run122 := symRun { noAlias := true } seg122 (BitVec.ofNat 64 (0x1000 + 4 * 6100)) 50
theorem spec122 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6100))) (hobl : run122.res.obligs s) :
    Steps image s run122.res.steps run122.res.cycles (run122.res.toState s) :=
  symRun_sound run122 (codeAt_layout rfl layout_ok (i := 122) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run123 := symRun { noAlias := true } seg123 (BitVec.ofNat 64 (0x1000 + 4 * 6150)) 50
theorem spec123 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6150))) (hobl : run123.res.obligs s) :
    Steps image s run123.res.steps run123.res.cycles (run123.res.toState s) :=
  symRun_sound run123 (codeAt_layout rfl layout_ok (i := 123) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run124 := symRun { noAlias := true } seg124 (BitVec.ofNat 64 (0x1000 + 4 * 6200)) 50
theorem spec124 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6200))) (hobl : run124.res.obligs s) :
    Steps image s run124.res.steps run124.res.cycles (run124.res.toState s) :=
  symRun_sound run124 (codeAt_layout rfl layout_ok (i := 124) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run125 := symRun { noAlias := true } seg125 (BitVec.ofNat 64 (0x1000 + 4 * 6250)) 50
theorem spec125 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6250))) (hobl : run125.res.obligs s) :
    Steps image s run125.res.steps run125.res.cycles (run125.res.toState s) :=
  symRun_sound run125 (codeAt_layout rfl layout_ok (i := 125) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run126 := symRun { noAlias := true } seg126 (BitVec.ofNat 64 (0x1000 + 4 * 6300)) 50
theorem spec126 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6300))) (hobl : run126.res.obligs s) :
    Steps image s run126.res.steps run126.res.cycles (run126.res.toState s) :=
  symRun_sound run126 (codeAt_layout rfl layout_ok (i := 126) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run127 := symRun { noAlias := true } seg127 (BitVec.ofNat 64 (0x1000 + 4 * 6350)) 50
theorem spec127 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6350))) (hobl : run127.res.obligs s) :
    Steps image s run127.res.steps run127.res.cycles (run127.res.toState s) :=
  symRun_sound run127 (codeAt_layout rfl layout_ok (i := 127) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run128 := symRun { noAlias := true } seg128 (BitVec.ofNat 64 (0x1000 + 4 * 6400)) 50
theorem spec128 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6400))) (hobl : run128.res.obligs s) :
    Steps image s run128.res.steps run128.res.cycles (run128.res.toState s) :=
  symRun_sound run128 (codeAt_layout rfl layout_ok (i := 128) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run129 := symRun { noAlias := true } seg129 (BitVec.ofNat 64 (0x1000 + 4 * 6450)) 50
theorem spec129 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6450))) (hobl : run129.res.obligs s) :
    Steps image s run129.res.steps run129.res.cycles (run129.res.toState s) :=
  symRun_sound run129 (codeAt_layout rfl layout_ok (i := 129) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run130 := symRun { noAlias := true } seg130 (BitVec.ofNat 64 (0x1000 + 4 * 6500)) 50
theorem spec130 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6500))) (hobl : run130.res.obligs s) :
    Steps image s run130.res.steps run130.res.cycles (run130.res.toState s) :=
  symRun_sound run130 (codeAt_layout rfl layout_ok (i := 130) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run131 := symRun { noAlias := true } seg131 (BitVec.ofNat 64 (0x1000 + 4 * 6550)) 50
theorem spec131 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6550))) (hobl : run131.res.obligs s) :
    Steps image s run131.res.steps run131.res.cycles (run131.res.toState s) :=
  symRun_sound run131 (codeAt_layout rfl layout_ok (i := 131) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run132 := symRun { noAlias := true } seg132 (BitVec.ofNat 64 (0x1000 + 4 * 6600)) 50
theorem spec132 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6600))) (hobl : run132.res.obligs s) :
    Steps image s run132.res.steps run132.res.cycles (run132.res.toState s) :=
  symRun_sound run132 (codeAt_layout rfl layout_ok (i := 132) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run133 := symRun { noAlias := true } seg133 (BitVec.ofNat 64 (0x1000 + 4 * 6650)) 50
theorem spec133 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6650))) (hobl : run133.res.obligs s) :
    Steps image s run133.res.steps run133.res.cycles (run133.res.toState s) :=
  symRun_sound run133 (codeAt_layout rfl layout_ok (i := 133) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run134 := symRun { noAlias := true } seg134 (BitVec.ofNat 64 (0x1000 + 4 * 6700)) 50
theorem spec134 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6700))) (hobl : run134.res.obligs s) :
    Steps image s run134.res.steps run134.res.cycles (run134.res.toState s) :=
  symRun_sound run134 (codeAt_layout rfl layout_ok (i := 134) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run135 := symRun { noAlias := true } seg135 (BitVec.ofNat 64 (0x1000 + 4 * 6750)) 50
theorem spec135 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6750))) (hobl : run135.res.obligs s) :
    Steps image s run135.res.steps run135.res.cycles (run135.res.toState s) :=
  symRun_sound run135 (codeAt_layout rfl layout_ok (i := 135) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run136 := symRun { noAlias := true } seg136 (BitVec.ofNat 64 (0x1000 + 4 * 6800)) 50
theorem spec136 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6800))) (hobl : run136.res.obligs s) :
    Steps image s run136.res.steps run136.res.cycles (run136.res.toState s) :=
  symRun_sound run136 (codeAt_layout rfl layout_ok (i := 136) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run137 := symRun { noAlias := true } seg137 (BitVec.ofNat 64 (0x1000 + 4 * 6850)) 50
theorem spec137 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6850))) (hobl : run137.res.obligs s) :
    Steps image s run137.res.steps run137.res.cycles (run137.res.toState s) :=
  symRun_sound run137 (codeAt_layout rfl layout_ok (i := 137) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run138 := symRun { noAlias := true } seg138 (BitVec.ofNat 64 (0x1000 + 4 * 6900)) 50
theorem spec138 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6900))) (hobl : run138.res.obligs s) :
    Steps image s run138.res.steps run138.res.cycles (run138.res.toState s) :=
  symRun_sound run138 (codeAt_layout rfl layout_ok (i := 138) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run139 := symRun { noAlias := true } seg139 (BitVec.ofNat 64 (0x1000 + 4 * 6950)) 50
theorem spec139 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 6950))) (hobl : run139.res.obligs s) :
    Steps image s run139.res.steps run139.res.cycles (run139.res.toState s) :=
  symRun_sound run139 (codeAt_layout rfl layout_ok (i := 139) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run140 := symRun { noAlias := true } seg140 (BitVec.ofNat 64 (0x1000 + 4 * 7000)) 50
theorem spec140 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7000))) (hobl : run140.res.obligs s) :
    Steps image s run140.res.steps run140.res.cycles (run140.res.toState s) :=
  symRun_sound run140 (codeAt_layout rfl layout_ok (i := 140) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run141 := symRun { noAlias := true } seg141 (BitVec.ofNat 64 (0x1000 + 4 * 7050)) 50
theorem spec141 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7050))) (hobl : run141.res.obligs s) :
    Steps image s run141.res.steps run141.res.cycles (run141.res.toState s) :=
  symRun_sound run141 (codeAt_layout rfl layout_ok (i := 141) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run142 := symRun { noAlias := true } seg142 (BitVec.ofNat 64 (0x1000 + 4 * 7100)) 50
theorem spec142 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7100))) (hobl : run142.res.obligs s) :
    Steps image s run142.res.steps run142.res.cycles (run142.res.toState s) :=
  symRun_sound run142 (codeAt_layout rfl layout_ok (i := 142) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run143 := symRun { noAlias := true } seg143 (BitVec.ofNat 64 (0x1000 + 4 * 7150)) 50
theorem spec143 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7150))) (hobl : run143.res.obligs s) :
    Steps image s run143.res.steps run143.res.cycles (run143.res.toState s) :=
  symRun_sound run143 (codeAt_layout rfl layout_ok (i := 143) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run144 := symRun { noAlias := true } seg144 (BitVec.ofNat 64 (0x1000 + 4 * 7200)) 50
theorem spec144 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7200))) (hobl : run144.res.obligs s) :
    Steps image s run144.res.steps run144.res.cycles (run144.res.toState s) :=
  symRun_sound run144 (codeAt_layout rfl layout_ok (i := 144) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run145 := symRun { noAlias := true } seg145 (BitVec.ofNat 64 (0x1000 + 4 * 7250)) 50
theorem spec145 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7250))) (hobl : run145.res.obligs s) :
    Steps image s run145.res.steps run145.res.cycles (run145.res.toState s) :=
  symRun_sound run145 (codeAt_layout rfl layout_ok (i := 145) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run146 := symRun { noAlias := true } seg146 (BitVec.ofNat 64 (0x1000 + 4 * 7300)) 50
theorem spec146 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7300))) (hobl : run146.res.obligs s) :
    Steps image s run146.res.steps run146.res.cycles (run146.res.toState s) :=
  symRun_sound run146 (codeAt_layout rfl layout_ok (i := 146) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run147 := symRun { noAlias := true } seg147 (BitVec.ofNat 64 (0x1000 + 4 * 7350)) 50
theorem spec147 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7350))) (hobl : run147.res.obligs s) :
    Steps image s run147.res.steps run147.res.cycles (run147.res.toState s) :=
  symRun_sound run147 (codeAt_layout rfl layout_ok (i := 147) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run148 := symRun { noAlias := true } seg148 (BitVec.ofNat 64 (0x1000 + 4 * 7400)) 50
theorem spec148 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7400))) (hobl : run148.res.obligs s) :
    Steps image s run148.res.steps run148.res.cycles (run148.res.toState s) :=
  symRun_sound run148 (codeAt_layout rfl layout_ok (i := 148) (by kernel_rfl) (by decide)) s hpc hobl

sym_block run149 := symRun { noAlias := true } seg149 (BitVec.ofNat 64 (0x1000 + 4 * 7450)) 50
theorem spec149 (s : MachineState) (hpc : s.pc = (BitVec.ofNat 64 (0x1000 + 4 * 7450))) (hobl : run149.res.obligs s) :
    Steps image s run149.res.steps run149.res.cycles (run149.res.toState s) :=
  symRun_sound run149 (codeAt_layout rfl layout_ok (i := 149) (by kernel_rfl) (by decide)) s hpc hobl

end SigGolfCandidate.Rv.Scale
