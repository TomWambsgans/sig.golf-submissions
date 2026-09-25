import SigGolfCandidate.SphincsVerifierFtsForestHashTrace

namespace SigGolfCandidate.SphincsVerifierFtsLayer5Prefix
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def layer5PrefixState (state : MachineState) : MachineState :=
  let s1 := execInstrBr state (.ADDI .x6 .x0 5)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 120)
  let s7 := execInstrBr s6 (.LD .x6 .x28 0)
  let s8 := execInstrBr s7 (.SRLI .x6 .x6 4)
  let s9 := execInstrBr s8 (.LUI .x28 0x43)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 8)
  let s11 := execInstrBr s10 (.SD .x28 .x6 0)
  let s12 := execInstrBr s11 (.LUI .x28 0x43)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 120)
  let s14 := execInstrBr s13 (.LD .x6 .x28 0)
  let s15 := execInstrBr s14 (.SRLI .x6 .x6 0)
  let s16 := execInstrBr s15 (.ANDI .x6 .x6 15)
  let s17 := execInstrBr s16 (.LUI .x28 0x43)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 32)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.ADDI .x6 .x0 0)
  let s21 := execInstrBr s20 (.LUI .x28 0x43)
  let s22 := execInstrBr s21 (.ADDI .x28 .x28 16)
  let s23 := execInstrBr s22 (.SD .x28 .x6 0)
  let s24 := execInstrBr s23 (.LUI .x28 0x43)
  let s25 := execInstrBr s24 (.ADDI .x28 .x28 32)
  let s26 := execInstrBr s25 (.LD .x6 .x28 0)
  let s27 := execInstrBr s26 (.LUI .x28 0x43)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 24)
  let s29 := execInstrBr s28 (.SD .x28 .x6 0)
  s29

theorem layer5Prefix_block (state : MachineState) (pc : state.pc = 0x1d74) :
    OrdinarySteps SphincsImages.verify state 29 (layer5PrefixState state) ∧
    (layer5PrefixState state).pc = 0x1de8 := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 5)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 120)
  let s7 := execInstrBr s6 (.LD .x6 .x28 0)
  let s8 := execInstrBr s7 (.SRLI .x6 .x6 4)
  let s9 := execInstrBr s8 (.LUI .x28 0x43)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 8)
  let s11 := execInstrBr s10 (.SD .x28 .x6 0)
  let s12 := execInstrBr s11 (.LUI .x28 0x43)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 120)
  let s14 := execInstrBr s13 (.LD .x6 .x28 0)
  let s15 := execInstrBr s14 (.SRLI .x6 .x6 0)
  let s16 := execInstrBr s15 (.ANDI .x6 .x6 15)
  let s17 := execInstrBr s16 (.LUI .x28 0x43)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 32)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.ADDI .x6 .x0 0)
  let s21 := execInstrBr s20 (.LUI .x28 0x43)
  let s22 := execInstrBr s21 (.ADDI .x28 .x28 16)
  let s23 := execInstrBr s22 (.SD .x28 .x6 0)
  let s24 := execInstrBr s23 (.LUI .x28 0x43)
  let s25 := execInstrBr s24 (.ADDI .x28 .x28 32)
  let s26 := execInstrBr s25 (.LD .x6 .x28 0)
  let s27 := execInstrBr s26 (.LUI .x28 0x43)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 24)
  let s29 := execInstrBr s28 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x1d78 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1d7c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1d80 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1d84 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1d88 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1d8c := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1d90 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1d94 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1d98 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x1d9c := by simp [s10, execInstrBr, p9]
  have p11 : s11.pc = 0x1da0 := by simp [s11, execInstrBr, p10]
  have p12 : s12.pc = 0x1da4 := by simp [s12, execInstrBr, p11]
  have p13 : s13.pc = 0x1da8 := by simp [s13, execInstrBr, p12]
  have p14 : s14.pc = 0x1dac := by simp [s14, execInstrBr, p13]
  have p15 : s15.pc = 0x1db0 := by simp [s15, execInstrBr, p14]
  have p16 : s16.pc = 0x1db4 := by simp [s16, execInstrBr, p15]
  have p17 : s17.pc = 0x1db8 := by simp [s17, execInstrBr, p16]
  have p18 : s18.pc = 0x1dbc := by simp [s18, execInstrBr, p17]
  have p19 : s19.pc = 0x1dc0 := by simp [s19, execInstrBr, p18]
  have p20 : s20.pc = 0x1dc4 := by simp [s20, execInstrBr, p19]
  have p21 : s21.pc = 0x1dc8 := by simp [s21, execInstrBr, p20]
  have p22 : s22.pc = 0x1dcc := by simp [s22, execInstrBr, p21]
  have p23 : s23.pc = 0x1dd0 := by simp [s23, execInstrBr, p22]
  have p24 : s24.pc = 0x1dd4 := by simp [s24, execInstrBr, p23]
  have p25 : s25.pc = 0x1dd8 := by simp [s25, execInstrBr, p24]
  have p26 : s26.pc = 0x1ddc := by simp [s26, execInstrBr, p25]
  have p27 : s27.pc = 0x1de0 := by simp [s27, execInstrBr, p26]
  have p28 : s28.pc = 0x1de4 := by simp [s28, execInstrBr, p27]
  have p29 : s29.pc = 0x1de8 := by simp [s29, execInstrBr, p28]
  have trace : OrdinarySteps SphincsImages.verify state 29 s29 := by
    apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 5)) 28
    · rw [fetch_index SphincsImages.verify state 861 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 27
    · rw [fetch_index SphincsImages.verify s1 862 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 26
    · rw [fetch_index SphincsImages.verify s2 863 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 25
    · rw [fetch_index SphincsImages.verify s3 864 (by decide)
        (by simpa using p3)]
      decide
    · have pointer : s3.getReg .x28 = 0x43000 := by
        simp [s3, s2, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 24
    · rw [fetch_index SphincsImages.verify s4 865 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 120)) 23
    · rw [fetch_index SphincsImages.verify s5 866 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.LD .x6 .x28 0)) 22
    · rw [fetch_index SphincsImages.verify s6 867 (by decide)
        (by simpa using p6)]
      decide
    · have pointer : s6.getReg .x28 = 0x43078 := by
        simp [s6, s5, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s7, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s7 s8 _ (.base (.SRLI .x6 .x6 4)) 21
    · rw [fetch_index SphincsImages.verify s7 868 (by decide)
        (by simpa using p7)]
      decide
    · rfl
    apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x43)) 20
    · rw [fetch_index SphincsImages.verify s8 869 (by decide)
        (by simpa using p8)]
      decide
    · rfl
    apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 8)) 19
    · rw [fetch_index SphincsImages.verify s9 870 (by decide)
        (by simpa using p9)]
      decide
    · rfl
    apply OrdinarySteps.step s10 s11 _ (.base (.SD .x28 .x6 0)) 18
    · rw [fetch_index SphincsImages.verify s10 871 (by decide)
        (by simpa using p10)]
      decide
    · have pointer : s10.getReg .x28 = 0x43008 := by
        simp [s10, s9, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s11, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x43)) 17
    · rw [fetch_index SphincsImages.verify s11 872 (by decide)
        (by simpa using p11)]
      decide
    · rfl
    apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 120)) 16
    · rw [fetch_index SphincsImages.verify s12 873 (by decide)
        (by simpa using p12)]
      decide
    · rfl
    apply OrdinarySteps.step s13 s14 _ (.base (.LD .x6 .x28 0)) 15
    · rw [fetch_index SphincsImages.verify s13 874 (by decide)
        (by simpa using p13)]
      decide
    · have pointer : s13.getReg .x28 = 0x43078 := by
        simp [s13, s12, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s14, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s14 s15 _ (.base (.SRLI .x6 .x6 0)) 14
    · rw [fetch_index SphincsImages.verify s14 875 (by decide)
        (by simpa using p14)]
      decide
    · rfl
    apply OrdinarySteps.step s15 s16 _ (.base (.ANDI .x6 .x6 15)) 13
    · rw [fetch_index SphincsImages.verify s15 876 (by decide)
        (by simpa using p15)]
      decide
    · rfl
    apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 0x43)) 12
    · rw [fetch_index SphincsImages.verify s16 877 (by decide)
        (by simpa using p16)]
      decide
    · rfl
    apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 32)) 11
    · rw [fetch_index SphincsImages.verify s17 878 (by decide)
        (by simpa using p17)]
      decide
    · rfl
    apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x6 0)) 10
    · rw [fetch_index SphincsImages.verify s18 879 (by decide)
        (by simpa using p18)]
      decide
    · have pointer : s18.getReg .x28 = 0x43020 := by
        simp [s18, s17, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s19, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x6 .x0 0)) 9
    · rw [fetch_index SphincsImages.verify s19 880 (by decide)
        (by simpa using p19)]
      decide
    · rfl
    apply OrdinarySteps.step s20 s21 _ (.base (.LUI .x28 0x43)) 8
    · rw [fetch_index SphincsImages.verify s20 881 (by decide)
        (by simpa using p20)]
      decide
    · rfl
    apply OrdinarySteps.step s21 s22 _ (.base (.ADDI .x28 .x28 16)) 7
    · rw [fetch_index SphincsImages.verify s21 882 (by decide)
        (by simpa using p21)]
      decide
    · rfl
    apply OrdinarySteps.step s22 s23 _ (.base (.SD .x28 .x6 0)) 6
    · rw [fetch_index SphincsImages.verify s22 883 (by decide)
        (by simpa using p22)]
      decide
    · have pointer : s22.getReg .x28 = 0x43010 := by
        simp [s22, s21, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s23, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s23 s24 _ (.base (.LUI .x28 0x43)) 5
    · rw [fetch_index SphincsImages.verify s23 884 (by decide)
        (by simpa using p23)]
      decide
    · rfl
    apply OrdinarySteps.step s24 s25 _ (.base (.ADDI .x28 .x28 32)) 4
    · rw [fetch_index SphincsImages.verify s24 885 (by decide)
        (by simpa using p24)]
      decide
    · rfl
    apply OrdinarySteps.step s25 s26 _ (.base (.LD .x6 .x28 0)) 3
    · rw [fetch_index SphincsImages.verify s25 886 (by decide)
        (by simpa using p25)]
      decide
    · have pointer : s25.getReg .x28 = 0x43020 := by
        simp [s25, s24, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s26, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s26 s27 _ (.base (.LUI .x28 0x43)) 2
    · rw [fetch_index SphincsImages.verify s26 887 (by decide)
        (by simpa using p26)]
      decide
    · rfl
    apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x28 .x28 24)) 1
    · rw [fetch_index SphincsImages.verify s27 888 (by decide)
        (by simpa using p27)]
      decide
    · rfl
    apply OrdinarySteps.step s28 s29 _ (.base (.SD .x28 .x6 0)) 0
    · rw [fetch_index SphincsImages.verify s28 889 (by decide)
        (by simpa using p28)]
      decide
    · have pointer : s28.getReg .x28 = 0x43018 := by
        simp [s28, s27, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      simp [s29, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, pointer, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  constructor
  · simpa only [layer5PrefixState] using trace
  · simpa only [layer5PrefixState] using p29

theorem layer5Prefix_cells (state : MachineState) :
    (layer5PrefixState state).getMem 0x43000 = 5 ∧
    (layer5PrefixState state).getMem 0x43008 =
      state.getMem 0x43078 >>> 4 ∧
    (layer5PrefixState state).getMem 0x43020 =
      state.getMem 0x43078 &&& 15 ∧
    (layer5PrefixState state).getMem 0x43010 = 0 ∧
    (layer5PrefixState state).getMem 0x43018 =
      state.getMem 0x43078 &&& 15 := by
  simp [layer5PrefixState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLayer5Prefix.layer5Prefix_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms layer5Prefix_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLayer5Prefix.layer5Prefix_cells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms layer5Prefix_cells

end SigGolfCandidate.SphincsVerifierFtsLayer5Prefix
