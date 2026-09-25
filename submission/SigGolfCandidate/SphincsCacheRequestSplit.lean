import SigGolfCandidate.SphincsMaskedSignReject
import SigGolfCandidate.SphincsMaskedSignHonestAuthentication

/-! Public three-way split of one supplied cache. -/

namespace SigGolfCandidate.SphincsCacheRequestSplit
open SigGolf SigGolf.Riscv OracleComp
open SphincsSecurity SphincsBridge SphincsMaskedChainDomain
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

def authenticatedBytes : Nat := 2 ^ 17 - 20

def authPrefix (cache : Cache) : BitVec (8 * authenticatedBytes) :=
  cache.extractLsb' 0 _

def macTag (cache : Cache) : BitVec 160 :=
  cache.extractLsb' (8 * authenticatedBytes) 160

def ciphertext (cache : Cache) : Fin authenticatedBytes → UInt8 :=
  fun i => UInt8.ofBitVec (cache.extractLsb' (8 * i.val) 8)

theorem auth_prefix_eq_of_ciphertext_eq (cache canonical : Cache)
    (hcipher : ciphertext cache = ciphertext canonical) :
    authPrefix cache = authPrefix canonical := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let i : Fin authenticatedBytes := ⟨bit / 8, by omega⟩
  let j := bit % 8
  have hj : j < 8 := Nat.mod_lt _ (by decide)
  have hindex : 8 * i.val + j = bit := by
    dsimp [i, j]
    omega
  have hbyte := congrArg (fun b : UInt8 => b.toBitVec.getLsbD j)
    (congrFun hcipher i)
  simp only [ciphertext, UInt8.toBitVec_ofBitVec,
    BitVec.getLsbD_extractLsb', decide_eq_true hj,
    Bool.true_and] at hbyte
  simp only [authPrefix, BitVec.getLsbD_extractLsb',
    decide_eq_true hbit, Bool.true_and, Nat.zero_add]
  simpa only [hindex] using hbyte

theorem ciphertext_ne_of_auth_prefix_ne (cache canonical : Cache)
    (hprefix : authPrefix cache ≠ authPrefix canonical) :
    ciphertext cache ≠ ciphertext canonical := by
  intro hcipher
  exact hprefix (auth_prefix_eq_of_ciphertext_eq cache canonical hcipher)

theorem cacheCiphertext_eq_ofFn (cache : Cache) :
    SphincsMaskedKeygenRefinement.cacheCiphertext cache =
      List.ofFn (ciphertext cache) := rfl

theorem cache_eq_of_prefix_tag (a b : Cache)
    (hprefix : authPrefix a = authPrefix b)
    (htag : macTag a = macTag b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hleft : i < 8 * authenticatedBytes
  · have hbit := congrArg
      (fun v : BitVec (8 * authenticatedBytes) =>
        v.getLsbD i) hprefix
    simp only [authPrefix, BitVec.getLsbD_extractLsb',
      decide_eq_true hleft, Bool.true_and, Nat.zero_add] at hbit
    exact hbit
  · let j := i - 8 * authenticatedBytes
    have hj : j < 160 := by
      dsimp [j, authenticatedBytes, CACHE_BYTES] at *
      omega
    have hbit := congrArg (fun v : BitVec 160 => v.getLsbD j) htag
    simp only [macTag, BitVec.getLsbD_extractLsb',
      decide_eq_true hj, Bool.true_and] at hbit
    have hindex : 8 * authenticatedBytes + j = i := by
      dsimp [j]
      omega
    simpa only [hindex] using hbit

theorem cache_three_way (cache canonical : Cache) :
    cache = canonical ∨
      (authPrefix cache = authPrefix canonical ∧ macTag cache ≠ macTag canonical) ∨
      authPrefix cache ≠ authPrefix canonical := by
  by_cases hp : authPrefix cache = authPrefix canonical
  · by_cases ht : macTag cache = macTag canonical
    · exact Or.inl (cache_eq_of_prefix_tag cache canonical hp ht)
    · exact Or.inr (Or.inl ⟨hp, ht⟩)
  · exact Or.inr (Or.inr hp)

theorem slice_eq_of_prefix_eq (cache canonical : Cache)
    (hprefix : authPrefix cache = authPrefix canonical)
    (start len : Nat) (hbound : start + len ≤ 8 * authenticatedBytes) :
    cache.extractLsb' start len = canonical.extractLsb' start len := by
  have h := congrArg (fun v : BitVec (8 * authenticatedBytes) =>
    v.extractLsb' start len) hprefix
  simpa only [authPrefix,
    BitVec.extractLsb'_extractLsb'_of_le hbound] using h

theorem cache_ciphertext_eq_of_prefix_eq (cache canonical : Cache)
    (hprefix : authPrefix cache = authPrefix canonical) :
    SphincsMaskedKeygenRefinement.cacheCiphertext cache =
      SphincsMaskedKeygenRefinement.cacheCiphertext canonical := by
  apply congrArg List.ofFn
  funext i
  apply congrArg UInt8.ofBitVec
  exact slice_eq_of_prefix_eq cache canonical hprefix (8 * i.val) 8 (by
    have := i.isLt
    dsimp [authenticatedBytes]
    omega)

theorem first_mismatch {α : Type} (left right : Fin 5 → α)
    (h : ¬∀ i, left i = right i) :
    ∃ i : Fin 5, (∀ j : Fin 5, j.val < i.val → left j = right j) ∧
      left i ≠ right i := by
  classical
  letI : DecidableEq α := Classical.decEq α
  by_cases h0 : left 0 = right 0
  · by_cases h1 : left 1 = right 1
    · by_cases h2 : left 2 = right 2
      · by_cases h3 : left 3 = right 3
        · have h4 : left 4 ≠ right 4 := by
            intro h4
            apply h
            intro i
            fin_cases i <;> assumption
          exact ⟨4, by intro j hj; fin_cases j <;> simp_all, h4⟩
        · exact ⟨3, by intro j hj; fin_cases j <;> simp_all, h3⟩
      · exact ⟨2, by intro j hj; fin_cases j <;> simp_all, h2⟩
    · exact ⟨1, by intro j hj; fin_cases j <;> simp_all, h1⟩
  · exact ⟨0, by intro j hj; omega, h0⟩

theorem bitvec160_eq_of_lanes (a b : BitVec 160)
    (h : ∀ i : Fin 5, a.extractLsb' (32 * i.val) 32 =
      b.extractLsb' (32 * i.val) 32) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let i : Fin 5 := ⟨bit / 32, by omega⟩
  let j := bit % 32
  have hj : j < 32 := Nat.mod_lt _ (by decide)
  have hindex : 32 * i.val + j = bit := by
    dsimp [i, j]
    omega
  have hpart := congrArg (fun w : BitVec 32 => w.getLsbD j) (h i)
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hj,
    Bool.true_and] at hpart
  simpa only [hindex] using hpart

theorem wrong_tag_detected (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message)
    (hparameter : cache.extractLsb' (8 * 20) 160 =
      SphincsMaskedKeygenRefinement.parameter hash secretKey)
    (parameterEqual : ∀ j : Fin 5,
      (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (hwrong : macTag cache ≠
      truncateHash (hash (toQuery (SphincsCacheSecretDomains.macInput
        (SphincsMaskedKeygenRefinement.parameter hash secretKey)
        secretKey (SphincsMaskedKeygenRefinement.cacheCiphertext cache))))) :
    ¬∀ i : Fin 5,
      (SphincsMaskedSignHonestAuthentication.macState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      (SphincsMaskedSignHonestAuthentication.macState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x2004c + 4 * i.val)) := by
  let parameter := SphincsMaskedKeygenRefinement.parameter hash secretKey
  let entry := SphincsMaskedSignPrefix.entryState secretKey cache message
  let checked := SphincsMaskedSignHonestAuthentication.checkedState hash secretKey cache message
  let authenticated := SphincsMaskedSignHonestAuthentication.macState hash secretKey cache message
  have hentryPar := SphincsMaskedSignRootValue.entry_cache_words20
    secretKey cache message 20 (by decide) (by decide)
  rw [hparameter] at hentryPar
  have hpar : Words20 checked 0x74 parameter :=
    SphincsMaskedSignHonestAuthentication.frame_words20 entry checked
      (SphincsMaskedSignHonestAuthentication.checked_frame hash secretKey cache message)
      0x74 (by decide) parameter hentryPar
  have hkey : SphincsMaskedSecretDomain.Words32 checked secretKey :=
    SphincsMaskedSignHonestAuthentication.frame_words32 entry checked
      (SphincsMaskedSignHonestAuthentication.checked_frame hash secretKey cache message)
      secretKey (SphincsMaskedSignRootValue.entry_key_words32 secretKey cache message)
  have hpc : checked.pc = 0x1144 := by
    have ppc : (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).pc =
        0x10e8 := by
      simp [SphincsMaskedSignHonestAuthentication.parameterState,
        SphincsMaskedSignPrefix.afterHashState, writeHash,
        SphincsMaskedSignPrefix.firstHash_pc,
        SphincsMaskedSignPrefix.afterJump_pc]
    exact SphincsMaskedSignParameterCheck.comparison_pc _ ppc parameterEqual
  have hcontract := SphincsMaskedMacRestoration.contract hash SphincsMaskedImages.sign
    0x1144 SphincsMaskedMacTrace.sign_code checked hpc parameter secretKey hpar hkey
  have hcomputed := hcontract.2.2.2
  rw [SphincsMaskedSignHonestAuthentication.checked_ciphertext] at hcomputed
  have hentryTag := SphincsMaskedSignRootValue.entry_cache_words20
    secretKey cache message 131052 (by decide) (by decide)
  change Words20 entry 0x2004c (macTag cache) at hentryTag
  have hcheckedTag : Words20 checked 0x2004c (macTag cache) :=
    SphincsMaskedSignHonestAuthentication.frame_words20 entry checked
      (SphincsMaskedSignHonestAuthentication.checked_frame hash secretKey cache message)
      0x2004c (by decide) (macTag cache) hentryTag
  have hstored : Words20 authenticated 0x2004c (macTag cache) :=
    SphincsMaskedSignHonestAuthentication.frame_words20 checked authenticated
      hcontract.2.2.1 0x2004c (by decide) (macTag cache) hcheckedTag
  intro hall
  have hlanes : ∀ i : Fin 5,
      (truncateHash (hash (toQuery (SphincsCacheSecretDomains.macInput parameter secretKey
        (SphincsMaskedKeygenRefinement.cacheCiphertext cache))))).extractLsb' (32 * i.val) 32 =
        (macTag cache).extractLsb' (32 * i.val) 32 := by
    intro i
    exact (hcomputed i).symm.trans ((hall i).trans (hstored i))
  exact hwrong (bitvec160_eq_of_lanes _ _ hlanes).symm

theorem parameter_equal_implies_cache_field (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message)
    (parameterEqual : ∀ j : Fin 5,
      (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x74 + 4 * j.val))) :
    cache.extractLsb' (8 * 20) 160 =
      SphincsMaskedKeygenRefinement.parameter hash secretKey := by
  let entry := SphincsMaskedSignPrefix.entryState secretKey cache message
  let ps := SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message
  have hentry := SphincsMaskedSignRootValue.entry_cache_words20
    secretKey cache message 20 (by decide) (by decide)
  have hpar : Words20 ps 0x74 (cache.extractLsb' (8 * 20) 160) :=
    SphincsMaskedSignHonestAuthentication.frame_words20 entry ps
      (SphincsMaskedSignHonestAuthentication.parameter_frame hash secretKey cache message)
      0x74 (by decide) _ hentry
  apply bitvec160_eq_of_lanes
  intro i
  have hpi := parameterEqual i
  rw [SphincsMaskedSignParameterCheck.afterHash_words32, hpar i] at hpi
  change (cache.extractLsb' (8 * 20) 160).extractLsb' (32 * i.val) 32 =
    ((hash (toQuery (keygenHashInput 0 .parameter secretKey))).extractLsb'
      0 digestBits).extractLsb' (32 * i.val) 32
  rw [BitVec.extractLsb'_extractLsb'_of_le (by
    have := i.isLt
    dsimp [digestBits]
    omega)]
  exact hpi.symm

theorem sign_runWith_failure_of_execution (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message)
    (steps cycles calls compressions : Nat)
    (finalState : RiscvZkvm.Rv64.MachineState)
    (execution : Executes hash (SphincsSubmission.submission.image .sign)
      (SphincsMaskedSignPrefix.entryState secretKey cache message)
      steps ⟨.failure, finalState, cycles, calls, compressions⟩)
    (hsteps : steps ≤ CYCLE_LIMIT) :
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).value = none ∧
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).hashCalls = calls := by
  have hrun := runWith_of_executes SphincsSubmission.submission hash .sign
    (secretKey, cache, message)
    (SphincsMaskedSignPrefix.entryState secretKey cache message)
    steps _
    (SphincsMaskedSignPrefix.entry_loaded secretKey cache message)
    execution hsteps
  simp [hrun]

theorem tag_comparison_mismatch_rejects (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message)
    (parameterEqual : ∀ j : Fin 5,
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (tagMismatch : ¬∀ i : Fin 5,
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).value = none ∧
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).hashCalls = 2 := by
  let s := SphincsMaskedMacTrace.result hash 0x1144
    (SphincsMaskedSignParameterCheck.afterComparison
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey))
  obtain ⟨i, prior, different⟩ := first_mismatch
    (fun i : Fin 5 => s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)))
    (fun i : Fin 5 => s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val)))
    (by simpa only [s] using tagMismatch)
  have execution := SphincsMaskedSignReject.loaded_tag_mismatch_rejects
    hash secretKey cache message i parameterEqual prior different
  have himage : SphincsSubmission.submission.image .sign =
      SphincsMaskedImages.sign := rfl
  rw [← himage] at execution
  have hsteps : 338 + 3 * i.val ≤ CYCLE_LIMIT := by
    have := i.isLt
    norm_num [CYCLE_LIMIT] at *
    omega
  have hrun := runWith_of_executes SphincsSubmission.submission hash .sign
    (secretKey, cache, message)
    (SphincsMaskedSignPrefix.entryState secretKey cache message)
    (338 + 3 * i.val) _
    (SphincsMaskedSignPrefix.entry_loaded secretKey cache message)
    execution hsteps
  simp [hrun]

theorem wrong_tag_rejects (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message)
    (parameterEqual : ∀ j : Fin 5,
      (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
        (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (hwrong : macTag cache ≠
      truncateHash (hash (toQuery (SphincsCacheSecretDomains.macInput
        (SphincsMaskedKeygenRefinement.parameter hash secretKey)
        secretKey (SphincsMaskedKeygenRefinement.cacheCiphertext cache))))) :
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).value = none ∧
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).hashCalls = 2 := by
  have hpar := parameter_equal_implies_cache_field hash secretKey cache message parameterEqual
  exact tag_comparison_mismatch_rejects hash secretKey cache message parameterEqual
    (wrong_tag_detected hash secretKey cache message hpar parameterEqual hwrong)

theorem parameter_comparison_mismatch_rejects (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message)
    (parameterMismatch : ¬∀ i : Fin 5,
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).value = none ∧
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).hashCalls = 1 := by
  let s := SphincsMaskedSignPrefix.afterHashState hash
    (SphincsMaskedSignPrefix.afterJumpState secretKey cache message) secretKey
  obtain ⟨i, prior, different⟩ := first_mismatch
    (fun i : Fin 5 => s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)))
    (fun i : Fin 5 => s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)))
    (by simpa only [s] using parameterMismatch)
  have execution := SphincsMaskedSignReject.loaded_parameter_mismatch_rejects
    hash secretKey cache message i prior different
  have himage : SphincsSubmission.submission.image .sign =
      SphincsMaskedImages.sign := rfl
  rw [← himage] at execution
  have hsteps : 83 + 3 * i.val ≤ CYCLE_LIMIT := by
    have := i.isLt
    norm_num [CYCLE_LIMIT] at *
    omega
  exact sign_runWith_failure_of_execution hash secretKey cache message
    (83 + 3 * i.val) (98 + 3 * i.val) 1 2 _ execution hsteps

def ParameterPass (hash : Hash) (secretKey : SigGolf.SecretKey)
    (cache : Cache) (message : SigGolf.Message) : Prop :=
  ∀ i : Fin 5,
    (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
      (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
    (SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message).getWord32
      (BitVec.ofNat 64 (0x74 + 4 * i.val))

def TagPass (hash : Hash) (secretKey : SigGolf.SecretKey) (cache : Cache) : Prop :=
  macTag cache = truncateHash (hash (toQuery (SphincsCacheSecretDomains.macInput
    (SphincsMaskedKeygenRefinement.parameter hash secretKey)
    secretKey (SphincsMaskedKeygenRefinement.cacheCiphertext cache))))

theorem parameter_pass_of_field (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message)
    (hfield : cache.extractLsb' (8 * 20) 160 =
      SphincsMaskedKeygenRefinement.parameter hash secretKey) :
    ParameterPass hash secretKey cache message := by
  let entry := SphincsMaskedSignPrefix.entryState secretKey cache message
  let ps := SphincsMaskedSignHonestAuthentication.parameterState hash secretKey cache message
  have hentry := SphincsMaskedSignRootValue.entry_cache_words20
    secretKey cache message 20 (by decide) (by decide)
  rw [hfield] at hentry
  have hpar : Words20 ps 0x74 (SphincsMaskedKeygenRefinement.parameter hash secretKey) :=
    SphincsMaskedSignHonestAuthentication.frame_words20 entry ps
      (SphincsMaskedSignHonestAuthentication.parameter_frame hash secretKey cache message)
      0x74 (by decide) _ hentry
  intro i
  rw [SphincsMaskedSignParameterCheck.afterHash_words32, hpar i]
  unfold SphincsMaskedKeygenRefinement.parameter truncateHash
  exact (BitVec.extractLsb'_extractLsb'_of_le (by
    have := i.isLt
    omega)).symm

theorem same_prefix_wrong_tag_rejects (hash : Hash)
    (secretKey : SigGolf.SecretKey) (canonical cache : Cache)
    (message : SigGolf.Message)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics hash secretKey canonical)
    (hprefix : authPrefix cache = authPrefix canonical)
    (htag : macTag cache ≠ macTag canonical) :
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).value = none ∧
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).hashCalls = 2 := by
  have hfield := slice_eq_of_prefix_eq cache canonical hprefix (8 * 20) 160
    (by decide)
  rw [sem.parameterWords] at hfield
  have hpass := parameter_pass_of_field hash secretKey cache message hfield
  have hciph := cache_ciphertext_eq_of_prefix_eq cache canonical hprefix
  have hcanonical : macTag canonical =
      truncateHash (hash (toQuery (SphincsCacheSecretDomains.macInput
        (SphincsMaskedKeygenRefinement.parameter hash secretKey)
        secretKey (SphincsMaskedKeygenRefinement.cacheCiphertext canonical)))) := by
    exact sem.tag
  have hwrong : ¬TagPass hash secretKey cache := by
    intro hgood
    apply htag
    unfold TagPass at hgood
    rw [hciph] at hgood
    exact hgood.trans hcanonical.symm
  exact wrong_tag_rejects hash secretKey cache message hpass hwrong

theorem one_request_authentication_split (hash : Hash)
    (secretKey : SigGolf.SecretKey) (cache : Cache) (message : SigGolf.Message) :
    (¬ParameterPass hash secretKey cache message ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).value = none ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).hashCalls = 1) ∨
    (ParameterPass hash secretKey cache message ∧
      ¬TagPass hash secretKey cache ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).value = none ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).hashCalls = 2) ∨
    (ParameterPass hash secretKey cache message ∧ TagPass hash secretKey cache) := by
  classical
  by_cases hp : ParameterPass hash secretKey cache message
  · by_cases ht : TagPass hash secretKey cache
    · exact Or.inr (Or.inr ⟨hp, ht⟩)
    · have failed := wrong_tag_rejects hash secretKey cache message hp ht
      exact Or.inr (Or.inl ⟨hp, ht, failed.1, failed.2⟩)
  · have failed := parameter_comparison_mismatch_rejects hash secretKey cache message hp
    exact Or.inl ⟨hp, failed.1, failed.2⟩

theorem canonical_cache_passes (hash : Hash)
    (secretKey : SigGolf.SecretKey) (canonical : Cache) (message : SigGolf.Message)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics hash secretKey canonical) :
    ParameterPass hash secretKey canonical message ∧
      TagPass hash secretKey canonical := by
  constructor
  · exact (SphincsMaskedSignHonestAuthentication.honest_checks
      hash secretKey canonical message sem).1
  · exact sem.tag

theorem altered_prefix_request (hash : Hash)
    (secretKey : SigGolf.SecretKey) (canonical cache : Cache)
    (message : SigGolf.Message)
    (hprefix : authPrefix cache ≠ authPrefix canonical) :
    (¬ParameterPass hash secretKey cache message ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).value = none ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).hashCalls = 1) ∨
    (ParameterPass hash secretKey cache message ∧
      ¬TagPass hash secretKey cache ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).value = none ∧
      (SphincsSubmission.submission.runWith hash .sign
        (secretKey, cache, message)).hashCalls = 2) ∨
    (ciphertext cache ≠ ciphertext canonical ∧ TagPass hash secretKey cache) := by
  rcases one_request_authentication_split hash secretKey cache message with
    failedParameter | failedTag | passed
  · exact Or.inl failedParameter
  · exact Or.inr (Or.inl failedTag)
  · exact Or.inr (Or.inr
      ⟨ciphertext_ne_of_auth_prefix_ne cache canonical hprefix, passed.2⟩)

theorem altered_prefix_no_mac_hit_rejects (hash : Hash)
    (secretKey : SigGolf.SecretKey) (canonical cache : Cache)
    (message : SigGolf.Message)
    (hprefix : authPrefix cache ≠ authPrefix canonical)
    (hmiss : ¬TagPass hash secretKey cache) :
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).value = none ∧
    (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).hashCalls ≤ 2 := by
  rcases altered_prefix_request hash secretKey canonical cache message hprefix with
    hparameter | htag | hhit
  · exact ⟨hparameter.2.1, by rw [hparameter.2.2]; omega⟩
  · exact ⟨htag.2.2.1, by rw [htag.2.2.2]⟩
  · exact False.elim (hmiss hhit.2)

end SigGolfCandidate.SphincsCacheRequestSplit

/-- info: 'SigGolfCandidate.SphincsCacheRequestSplit.cache_three_way' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheRequestSplit.cache_three_way

/-- info: 'SigGolfCandidate.SphincsCacheRequestSplit.tag_comparison_mismatch_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheRequestSplit.tag_comparison_mismatch_rejects

/-- info: 'SigGolfCandidate.SphincsCacheRequestSplit.parameter_comparison_mismatch_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheRequestSplit.parameter_comparison_mismatch_rejects

/-- info: 'SigGolfCandidate.SphincsCacheRequestSplit.one_request_authentication_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheRequestSplit.one_request_authentication_split

/-- info: 'SigGolfCandidate.SphincsCacheRequestSplit.same_prefix_wrong_tag_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheRequestSplit.same_prefix_wrong_tag_rejects

/-- info: 'SigGolfCandidate.SphincsCacheRequestSplit.altered_prefix_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheRequestSplit.altered_prefix_request

/-- info: 'SigGolfCandidate.SphincsCacheRequestSplit.altered_prefix_no_mac_hit_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheRequestSplit.altered_prefix_no_mac_hit_rejects
