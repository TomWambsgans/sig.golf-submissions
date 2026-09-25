import SigGolfCandidate.SphincsMaskedMaskXor

namespace SigGolfCandidate.SphincsMaskedMaskLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedMaskCode SphincsMaskedMaskNode SphincsMaskedMaskXor
open SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsMaskedLeafRefinement
open SphincsVerifierFtsRootCopy SphincsSecurity
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def next (hash : Hash) (s : MachineState) := finish (applyXor (xorSetup (answer hash s)))

theorem finish_counter (s : MachineState) :
    (finish s).getMem 0x430d0 = s.getMem 0x430d0 + 1 ∧
      (finish s).getMem 0x430d8 = s.getMem 0x430d8 + 20 := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem finish_frame (s : MachineState) (a : Word) (h0 : a ≠ 0x430d0#64) (h1 : a ≠ 0x430d8#64) :
    (finish s).getMem a = s.getMem a := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1]

theorem finish_pc (s : MachineState) (pc : s.pc = 0x1bc4) :
    (finish s).pc = if s.getMem 0x430d0 + 1 = 4095 then 0x1c14 else 0x1a78 := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

structure Controls (s : MachineState) (node : Nat) : Prop where
  counter : s.getMem 0x430d0 = BitVec.ofNat 64 node
  pointer : s.getMem 0x430d8 = BitVec.ofNat 64 (0x88+20*node)

theorem node_contract (hash : Hash) (s : MachineState) (node : Nat) (pc : s.pc = 0x1a78)
    (ctl : Controls s node) (bound : node < 4095) :
    Trace hash SphincsMaskedImages.keygen s 121 136 1 2 (next hash s) ∧
      Controls (next hash s) (node+1) ∧
      (next hash s).pc = if node+1=4095 then 0x1c14 else 0x1a78 := by
  have anode := (answer_frame hash s 0x430d0 (by decide)).trans ctl.counter
  have aptr := (answer_frame hash s 0x430d8 (by decide)).trans ctl.pointer
  have regs := xorSetup_registers (answer hash s)
  have src : (xorSetup (answer hash s)).getReg .x6 = BitVec.ofNat 64 (0x88+20*node) := regs.1.trans aptr
  have apc := answer_pc hash s pc
  have xpc := xorSetup_pc _ apc
  have endpc := xor_pc _ xpc
  have xnode : (applyXor (xorSetup (answer hash s))).getMem 0x430d0 = BitVec.ofNat 64 node := by
    rw [applyXor_high_frame _ _ src (by omega) _ (by decide),xorSetup_frame]
    exact anode
  have xptr : (applyXor (xorSetup (answer hash s))).getMem 0x430d8 = BitVec.ofNat 64 (0x88+20*node) := by
    rw [applyXor_high_frame _ _ src (by omega) _ (by decide),xorSetup_frame]
    exact aptr
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · exact (answer_trace hash s pc).trans ((xorSetup_block _ apc).trace.trans
      ((xor_block _ _ xpc src regs.2 (by omega) (by dsimp [MEMORY_BYTES];omega)).trace.trans (finish_block _ endpc).trace))
  · rw [next,(finish_counter _).1,xnode]
    exact (BitVec.ofNat_add _ _).symm
  · rw [next,(finish_counter _).2,xptr]
    change BitVec.ofNat 64 (0x88+20*node) + BitVec.ofNat 64 20 = _
    rw [← BitVec.ofNat_add]
    congr 1
  · rw [next,finish_pc _ endpc,xnode]
    rw [show BitVec.ofNat 64 node + 1 = BitVec.ofNat 64 (node+1) from (BitVec.ofNat_add _ _).symm]
    have eq : (BitVec.ofNat 64 (node+1) : Word) = 4095 ↔ node+1=4095 := by
      constructor
      · intro h
        have h := congrArg BitVec.toNat h
        change (BitVec.ofNat 64 (node+1)).toNat = 4095 at h
        simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show node+1 < 2^64 by omega)] using h
      · intro h;rw [h];rfl
    simp only [eq]

def nodes (hash : Hash) : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => nodes hash n (next hash s)

theorem nodes_contract (hash : Hash) (s : MachineState) (node count : Nat)
    (pc : s.pc = if node=4095 then 0x1c14 else 0x1a78)
    (ctl : Controls s node) (bound : node+count ≤ 4095) :
    Trace hash SphincsMaskedImages.keygen s (121*count) (136*count) count (2*count) (nodes hash count s) ∧
      Controls (nodes hash count s) (node+count) ∧
      (nodes hash count s).pc = if node+count=4095 then 0x1c14 else 0x1a78 := by
  induction count generalizing s node with
  | zero => simpa [nodes] using And.intro (Trace.refl s) (And.intro ctl pc)
  | succ count ih =>
    have nodeBound : node<4095 := by omega
    have entry : s.pc = 0x1a78 := by simpa [show node≠4095 by omega] using pc
    obtain ⟨run,control,loc⟩ := node_contract hash s node entry ctl nodeBound
    obtain ⟨tail,controls,location⟩ := ih (next hash s) (node+1) loc control (by omega)
    refine ⟨?_,?_,?_⟩
    · simpa [nodes,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run.trans tail
    · simpa [nodes,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using controls
    · simpa [nodes,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using location

theorem init_controls (s : MachineState) : Controls (init s) 0 := by
  constructor <;> simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def masked (hash : Hash) (s : MachineState) := rootCopy (nodes hash 4095 (init s))

/-- Every tree node is masked and the masked root is copied into the cache header. -/
theorem masked_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1a18) :
    Trace hash SphincsMaskedImages.keygen s 495532 556957 4095 8190 (masked hash s) ∧
      (masked hash s).pc = 0x1c48 := by
  obtain ⟨run,control,loc⟩ := nodes_contract hash (init s) 0 4095
    (by simpa using init_pc s pc) (init_controls s) (by decide)
  have endpc : (nodes hash 4095 (init s)).pc = 0x1c14 := by simpa using loc
  exact ⟨(init_block s pc).trace.trans (run.trans (rootCopy_block _ endpc).trace),rootCopy_pc _ endpc⟩

/-- info: 'SigGolfCandidate.SphincsMaskedMaskLoop.nodes_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodes_contract

/-- info: 'SigGolfCandidate.SphincsMaskedMaskLoop.masked_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms masked_trace

end SigGolfCandidate.SphincsMaskedMaskLoop
