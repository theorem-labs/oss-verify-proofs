From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Reusable Require Import YK11 YK0i YK15 YM06 YM06_cf YM05 YM02 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO0p YO0d_cf.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Contract SlotAgree Uniform.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require RoomShapesDraft.
Import ListNotations.
Local Open Scope Z_scope.

(* The allocator side of crealizes' uniformity: a cut-free allocator walk reaches placement nodes only at its
   own mmap / brk nodes, and there every successor realizes the same trace set and is cut-free, so all
   successors have the same observable traces (YK15.realizes_obs_iff); the step emits no event. *)

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Let segs := ms_segs B.

Lemma svc_place_uniform : forall c, ms_svc_pending (cfg_ms c) = None -> place_uniform segs c.
Proof using.
  intros [ms md] H. apply place_uniform_nonplacement. intros x8 len. exact (instr_not_placement segs ms md x8 len H).
Qed.

Lemma obs_same : forall c1 c2 T, realizes segs c1 T -> cut_free segs c1 -> realizes segs c2 T -> cut_free segs c2 ->
  forall tr, obs_trace_cfg segs ACFG c1 tr <-> obs_trace_cfg segs ACFG c2 tr.
Proof using.
  intros c1 c2 T R1 C1 R2 C2 tr. split; intros Ht.
  - apply (proj2 (realizes_obs_iff segs c2 T R2 C2 tr)). apply (proj1 (realizes_obs_iff segs c1 T R1 C1 tr)). exact Ht.
  - apply (proj2 (realizes_obs_iff segs c1 T R1 C1 tr)). apply (proj1 (realizes_obs_iff segs c2 T R2 C2 tr)). exact Ht.
Qed.

Theorem SR_cfv_SRcf : forall c Q, SR_cfv segs c Q -> SRcf B c Q.
Proof using.
  intros c Q H T HK. apply crealizes_intro.
  - apply (SR_cfv_SR segs c Q H). intros c' HQ. exact (crealizes_realizes B c' T (HK c' HQ)).
  - apply (avoid_cut_free segs c Q (avoidv_avoid segs c Q (SR_cfv_avoidv segs c Q H))).
    intros c' HQ. exact (crealizes_cut_free B c' T (HK c' HQ)).
  - intros tr c'' Hst. destruct (star_first segs Q c tr c'' Hst) as [Hr | (c1 & tr2 & HQ & _ & Hst2)].
    + exact (svc_place_uniform c'' (SR_cfv_avoidi segs c Q H c'' Hr)).
    + exact (crealizes_uniform B c1 T (HK c1 HQ) tr2 c'' Hst2).
Qed.

Lemma mreal_cf_rc {R} : forall (t : itree astate R) c Q T,
  mreal_cf segs c t Q -> safe t -> ok04 mgrant t -> roomcf (vml c) t ->
  (forall c', (exists r tr, cpath04 t tr r /\ Q r c') -> crealizes B c' T) ->
  realizes segs c T /\ cut_free segs c.
Proof using.
  intros t c Q T H Hs Hok Hrm HK.
  apply (SR_cf_crealizes segs c _ T (mreal_cf_SR_cf segs t c Q H Hs Hok Hrm)).
  intros c' Hc'. split; [exact (crealizes_realizes B c' T (HK c' Hc')) | exact (crealizes_cut_free B c' T (HK c' Hc'))].
Qed.

(* The cut-free allocator walk as a crealizes CPS: what the contracts are proved from. *)
Theorem mreal_cf_SRcf {R} : forall (t : itree astate R) c (Q : R -> config -> Prop),
  mreal_cf segs c t Q -> safe t -> ok04 mgrant t -> roomcf (vml c) t ->
  SRcf B c (fun c' => exists r tr, cpath04 t tr r /\ Q r c').
Proof using.
  intros t c Q H Hs Hok Hrm T HK.
  destruct (mreal_cf_rc t c Q T H Hs Hok Hrm HK) as [Hr Hc].
  apply crealizes_intro; [exact Hr | exact Hc |].
  intros tr c'' Hst.
  destruct (mreal_cf_reach segs t c Q (vml c) tr c'' eq_refl H Hs Hok Hrm Hst)
    as [Ha | [(pre & q & s & k & Hsub & HJ & HV & Hkn) | (r & trl & c' & tr2 & Hp & HQ & Hst2)]].
  - exact (svc_place_uniform c'' Ha).
  - assert (Su : safe (IAsk q s k)) by exact (subt_inherit safe safe_sub pre t _ Hsub Hs).
    assert (Ok : ok04 mgrant (IAsk q s k)) by exact (subt_inherit (ok04 mgrant) (ok04_sub mgrant) pre t _ Hsub Hok).
    assert (Rm : roomcf (vml c) (IAsk q s k)) by exact (subt_inherit (roomcf (vml c)) (roomcf_sub (vml c)) pre t _ Hsub Hrm).
    assert (SUB : forall z c3, canswer04 q z -> mreal_cf segs c3 (k z) Q -> vml c3 = vml c ->
      realizes segs c3 T /\ cut_free segs c3).
    { intros z c3 Hz Hm HV3. apply (mreal_cf_rc (k z) c3 Q T Hm (safe_sub q s k z Su Hz) (ok04_sub mgrant q s k z Ok Hz)).
      - rewrite HV3. exact (roomcf_sub (vml c) q s k z Rm Hz).
      - intros c4 (r & trl & Hp & HQ). apply HK. exists r, (pre ++ (q, z) :: trl). split; [|exact HQ].
        apply (subt_cpath04 pre t (IAsk q s k) ((q, z) :: trl) r Hsub). cbn. auto. }
    intros x8 len Hpl e1 c1 e2 c2 Hs1 Hs2.
    destruct (knode_cf_succ segs c'' q s k Q (vml c) HJ HV Hkn Ok Rm e1 c1 Hs1) as (He1 & z1 & Hz1 & Hm1 & HV1).
    destruct (knode_cf_succ segs c'' q s k Q (vml c) HJ HV Hkn Ok Rm e2 c2 Hs2) as (He2 & z2 & Hz2 & Hm2 & HV2).
    split; [congruence|].
    destruct (SUB z1 c1 Hz1 Hm1 HV1) as [R1 C1]. destruct (SUB z2 c2 Hz2 Hm2 HV2) as [R2 C2].
    exact (obs_same c1 c2 T R1 C1 R2 C2).
  - exact (crealizes_uniform B c' T (HK c' (ex_intro _ r (ex_intro _ trl (conj Hp HQ)))) tr2 c'' Hst2).
Qed.

(* The tset form, for the driver walk's allocation sites: each answer of the tree leads to its own leaf trace set. *)
Theorem mreal_tset_cfu {R} : forall (t : itree astate R) c (Q : R -> config -> Prop) (K : R -> TSet),
  mreal_cf segs c t Q -> safe t -> jinv K t -> gtree mgrant t -> roomcf (vml c) t ->
  (forall r c' tr, cpath t tr r -> Q r c' -> crealizes B c' (K r)) ->
  crealizes B c (tset t K).
Proof using.
  intros t c Q K H Hs Hj Hg Hrm HK.
  assert (CORE : forall u c0, (exists pre, subt t pre u) -> mreal_cf segs c0 u Q -> vml c0 = vml c ->
    realizes segs c0 (tset u K) /\ cut_free segs c0).
  { intros u c0 (pre & Hsub) Hm HV0.
    assert (Su : safe u) by exact (subt_inherit safe safe_sub pre t u Hsub Hs).
    assert (Ju : jinv K u) by exact (subt_inherit (jinv K) (jinv_sub K) pre t u Hsub Hj).
    assert (Gu : gtree mgrant u) by exact (subt_inherit (gtree mgrant) (gtree_sub mgrant) pre t u Hsub Hg).
    assert (Ru : roomcf (vml c) u) by exact (subt_inherit (roomcf (vml c)) (roomcf_sub (vml c)) pre t u Hsub Hrm).
    split.
    - apply (mreal_tset segs u c0 Q K (mreal_cf_mreal segs u c0 Q Hm) Su Ju Gu).
      intros r c' tr Hp HQ.
      exact (crealizes_realizes B c' (K r) (HK r c' (pre ++ tr) (subt_cpath pre t u tr r Hsub Hp) HQ)).
    - apply (avoid_cut_free segs c0 (fun c' => exists r tr, cpath04 u tr r /\ Q r c')).
      + apply avoidv_avoid. rewrite <- HV0 in Ru.
        exact (mreal_cf_avoid segs u c0 Q (vml c0) eq_refl Hm Su (gtree_ok04 mgrant u Gu) Ru).
      + intros c' (r & tr & Hp & HQ).
        exact (crealizes_cut_free B c' (K r)
          (HK r c' (pre ++ tr) (subt_cpath pre t u tr r Hsub (cpath04_cpath u tr r Hp)) HQ)). }
  destruct (CORE t c (ex_intro _ [] eq_refl) H eq_refl) as [Hr Hc].
  apply crealizes_intro; [exact Hr | exact Hc |].
  intros tr c'' Hst.
  destruct (mreal_cf_reach segs t c Q (vml c) tr c'' eq_refl H Hs (gtree_ok04 mgrant t Hg) Hrm Hst)
    as [Ha | [(pre & q & s & k & Hsub & HJ & HV & Hkn) | (r & trl & c' & tr2 & Hp & HQ & Hst2)]].
  - exact (svc_place_uniform c'' Ha).
  - assert (Gq : gtree mgrant (IAsk q s k)) by exact (subt_inherit (gtree mgrant) (gtree_sub mgrant) pre t _ Hsub Hg).
    assert (Rq : roomcf (vml c) (IAsk q s k)) by exact (subt_inherit (roomcf (vml c)) (roomcf_sub (vml c)) pre t _ Hsub Hrm).
    assert (S1 : exists pre', subt t pre' (k 1)) by (exists (pre ++ [(q, 1)]); exact (subt_app pre t q s k 1 Hsub (canswer04_1 q))).
    intros x8 len Hpl e1 c1 e2 c2 Hs1 Hs2.
    destruct (knode_cf_succ_g segs c'' q s k Q (vml c) HJ HV Hkn Gq Rq e1 c1 Hs1) as (He1 & Hm1 & HV1).
    destruct (knode_cf_succ_g segs c'' q s k Q (vml c) HJ HV Hkn Gq Rq e2 c2 Hs2) as (He2 & Hm2 & HV2).
    split; [congruence|].
    destruct (CORE (k 1) c1 S1 Hm1 HV1) as [R1 C1]. destruct (CORE (k 1) c2 S1 Hm2 HV2) as [R2 C2].
    exact (obs_same c1 c2 _ R1 C1 R2 C2).
  - exact (crealizes_uniform B c' (K r) (HK r c' trl (cpath04_cpath t trl r Hp) HQ) tr2 c'' Hst2).
Qed.

Section u.
Variable MR : MR_t.

Theorem malloc_tset_cfu :
  malloc_realizes_cf B MR ->
  forall L A regs mem md n (K : option sptr * astate -> TSet),
  call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
  jinv K (malloc n A) -> gtree mgrant (malloc n A) ->
  roomcf (vm_limit (m_vmmaps md)) (malloc n A) ->
  (forall r c' tr, cpath (malloc n A) tr r -> malloc_leaf B MR L A regs mem md n r c' -> crealizes B c' (K r)) ->
  crealizes B (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md) (tset (malloc n A) K).
Proof using.
  intros HM L A regs mem md n K Hpre Hn Hrange Hj Hg Hrm HK.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  apply (mreal_tset_cfu _ _ _ K (HM L A regs mem md n Hpre Hn Hrange));
    [apply malloc_safe; [exact HW | lia] | exact Hj | exact Hg | exact Hrm | exact HK].
Qed.

Theorem free_tset_cfu :
  free_realizes_cf B MR ->
  forall L A regs mem md p n (K : unit * astate -> TSet),
  call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  jinv K (free (Some p) A) -> gtree mgrant (free (Some p) A) ->
  roomcf (vm_limit (m_vmmaps md)) (free (Some p) A) ->
  (forall r c' tr, cpath (free (Some p) A) tr r -> free_leaf B MR L A regs mem md p n r c' -> crealizes B c' (K r)) ->
  crealizes B (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md) (tset (free (Some p) A) K).
Proof using.
  intros HF L A regs mem md p n K Hpre Hin Hp Hj Hg Hrm HK.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  apply (mreal_tset_cfu _ _ _ K (HF L A regs mem md p n Hpre Hin Hp));
    [eapply free_safe; [exact HW | exact Hin] | exact Hj | exact Hg | exact Hrm | exact HK].
Qed.
End u.

End A.
