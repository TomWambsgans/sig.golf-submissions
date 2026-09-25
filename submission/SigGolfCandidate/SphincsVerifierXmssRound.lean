import SigGolfCandidate.SphincsVerifierXmssNext
import SigGolfCandidate.SphincsVerifierXmssAnswer

namespace SigGolfCandidate.SphincsVerifierXmssRound
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssPairSemantic
open SigGolfCandidate.SphincsVerifierXmssPrefix
open SigGolfCandidate.SphincsVerifierXmssNodeReady
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsVerifierXmssAnswer
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierWotsLeafResult
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def pairInstructions (s : MachineState) : Nat :=
  if s.getMem 0x43070 &&& 1 = 0 then 34 else 35

def pairState (s : MachineState) : MachineState :=
  if s.getMem 0x43070 &&& 1 = 0 then leftPairState' s else rightPairState s

def readyState (s : MachineState) : MachineState :=
  nodeReadyState (nodePrefixState (pairState s))

theorem ready_trace (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay)
    (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0) :
    OrdinarySteps SphincsImages.verify s (pairInstructions s + 64)
      (readyState s) ∧
    (readyState s).pc = nodeHashPc lay ∧
    (readyState s).getReg .x10 = 0x40000 ∧
    (readyState s).getReg .x11 = 640 ∧
    (readyState s).getReg .x12 = 0x42000 ∧
    (readyState s).getReg .x5 = 1 := by
  by_cases even : s.getMem 0x43070 &&& 1 = 0
  · have pair := leftPair_trace lay s pc even pointer pointerValue small aligned
    have pref :=  prefix_block lay (leftPairState' s) (by
      simpa [pairPc, nodePc] using pair.2)
    have hpc : (nodePrefixState (leftPairState' s)).pc = tagPc lay := by
      rw [pref.2]
      fin_cases lay <;> decide
    have ready := ready_block lay (nodePrefixState (leftPairState' s)) hpc
    have trace : OrdinarySteps SphincsImages.verify s 98
        (nodeReadyState (nodePrefixState (leftPairState' s))) := by
      simpa using (pair.1.append pref.1).append ready.1
    simp only [pairInstructions, pairState, even, if_true, readyState]
    exact ⟨trace, ready.2.1, ready.2.2.1, ready.2.2.2.1,
      ready.2.2.2.2.1, ready.2.2.2.2.2⟩

  · have pair := rightPair_trace lay s pc even pointer pointerValue small aligned
    have pref :=  prefix_block lay (rightPairState s) (by
      simpa [pairPc, nodePc] using pair.2)
    have hpc : (nodePrefixState (rightPairState s)).pc = tagPc lay := by
      rw [pref.2]
      fin_cases lay <;> decide
    have ready := ready_block lay (nodePrefixState (rightPairState s)) hpc
    have trace : OrdinarySteps SphincsImages.verify s 99
        (nodeReadyState (nodePrefixState (rightPairState s))) := by
      simpa using (pair.1.append pref.1).append ready.1
    simp only [pairInstructions, pairState, even, if_false, readyState]
    exact ⟨trace, ready.2.1, ready.2.2.1, ready.2.2.2.1,
      ready.2.2.2.2.1, ready.2.2.2.2.2⟩


def roundState (hash : Hash) (lay : Layer) (s : MachineState) : MachineState :=
  nextState lay (nodeHashNext hash (readyState s))

theorem round_executes (hash : Hash) (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay)
    (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify (roundState hash lay s)
      steps result) :
    Executes hash SphincsImages.verify s
      (steps + pairInstructions s + 91)
      (result.charge (pairInstructions s + 106) 1 2) := by
  let r := readyState s
  let answer := hash (hashInput r)
  let hashed := writeHash r answer
  let copied := leafAnswerCopyState hashed
  have pre := ready_trace lay s pc pointer pointerValue small aligned
  have hpc : hashed.pc = nodeHashPc lay + 4 := by
    have rpc : r.pc = nodeHashPc lay := pre.2.1
    simp [hashed, writeHash, rpc]
  have copy := nodeAnswerCopy_block lay hashed hpc
  have cpc : copied.pc = advancePc lay := by
    simpa [copied, advancePc] using nodeAnswerCopy_pc lay hashed hpc
  have next := next_block lay copied cpc
  have post : OrdinarySteps SphincsImages.verify hashed 26
      (roundState hash lay s) := by
    simpa [roundState, nodeHashNext, r, answer, hashed, copied] using
      copy.append next
  have postExec := post.then_executes tail
  have hashExec := nodeHash_step hash lay r pre.2.1 pre.2.2.1
    pre.2.2.2.1 pre.2.2.2.2.1 pre.2.2.2.2.2
    (steps + 26) (result.charge 26 0 0) postExec
  have total := pre.1.then_executes hashExec
  convert total using 1
  · omega
  · cases result
    simp [Execution.charge]
    omega

#print axioms ready_trace
#print axioms round_executes

end SigGolfCandidate.SphincsVerifierXmssRound
