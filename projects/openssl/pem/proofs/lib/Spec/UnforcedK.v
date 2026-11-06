(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Decode NodesCfg DecodeCfg DecodeCfg2.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog KInv KStep Relim.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Export Unforced.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation nstep := NodesCfg.nstep_c (only parsing).
Import ListNotations.
Open Scope Z_scope.

Definition KLIM : Z := 2 ^ 30.
Definition SMALLREQ : Z := 2 ^ 24.

(* [comment removed for export] *)
Definition GK (h : VmMaps) : Prop :=
  (forall e, In e (vm_maps h) -> PGSZ <= bv_unsigned (snd e))
  /\ KLIM + SMALLREQ <= vm_limit h
  /\ bv_unsigned (vm_start_brk h) <= 2 ^ 33.

Lemma GK_ext : forall h h',
  GK h -> incl (vm_maps h') (vm_maps h) -> vm_limit h' = vm_limit h -> vm_start_brk h' = vm_start_brk h -> GK h'.
Proof.
  intros h h' (G1 & G2 & G3) Hi E1 E2. split; [|split; [rewrite E1; exact G2| rewrite E2; exact G3]].
  intros e He. apply G1. apply Hi. exact He.
Qed.

Lemma GK_cons : forall h h' e,
  GK h -> vm_maps h' = e :: vm_maps h -> PGSZ <= bv_unsigned (snd e) ->
  vm_limit h' = vm_limit h -> vm_start_brk h' = vm_start_brk h -> GK h'.
Proof.
  intros h h' e (G1 & G2 & G3) Em He E1 E2. split; [|split; [rewrite E1; exact G2| rewrite E2; exact G3]].
  intros x Hx. rewrite Em in Hx. destruct Hx as [<-|Hx]; [exact He| exact (G1 x Hx)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma count_le_live : forall l, (forall e, In e l -> PGSZ <= bv_unsigned (snd e)) ->
  PGSZ * Z.of_nat (length l) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros H; cbn -[Z.of_nat Z.mul]; [lia|].
  rewrite Nat2Z.inj_succ. pose proof (H (b, s) (or_introl eq_refl)) as Hs. cbn in Hs.
  specialize (IH ltac:(intros e He; apply H; right; exact He)). unfold PGSZ in *. lia.
Qed.

Lemma four_xy_le_sq : forall x y, 0 <= x -> 0 <= y -> 4 * (x * y) <= (x + y) * (x + y).
Proof. intros x y Hx Hy. pose proof (Z.square_nonneg (x - y)). nia. Qed.

Lemma region_free_app_iff : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[a s] l1 IH]; intros l2 lo n; cbn; [reflexivity|].
  rewrite IH. destruct (negb (iv_overlap lo n a s)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gk_gap : forall {CE : Ceiling} L pbrk mo nZ,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < nZ -> nZ mod page_size = 0 ->
  (nZ <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + nZ <= KLIM) ->
  vm_gap_available (m_vmmaps mo) nZ = true.
Proof.
  intros CE L pbrk mo nZ HK (G1 & G2 & G3) Hlive HnZ HnAl Hreq.
  set (h := m_vmmaps mo) in *.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). fold h in S1, S2, S3, S4.
  pose proof (kl_top _ _ _ HK) as Htop. fold h in Htop.
  set (F := bv_unsigned (vm_start_brk h)) in *.
  pose proof (count_le_live (vm_maps h) G1) as Hcnt.
  unfold vm_live_bytes in Hlive, Hreq.
  set (N := Z.of_nat (length (vm_maps h))) in *.
  set (LV := live_bytes (vm_maps h)) in *.
  pose proof (live_bytes_nonneg (vm_maps h)) as HLV. fold LV in HLV.
  ceil_bounds.
  (* [comment removed for export] *)
  assert (HW : F + nZ + gap_weight nZ (vm_maps h) <= alloc_top h).
  { rewrite gap_weight_sizes. fold N LV. rewrite Htop.
    assert (HNn : 0 <= N) by (unfold N; lia).
    unfold PGSZ, KLIM, SMALLREQ in *.
    rewrite Z.mul_add_distr_l.
    assert (HN4 : N * 4095 <= LV) by lia.
    destruct Hreq as [Hs|Hb].
    - (* [comment removed for export] *)
      assert (HN : N <= 2^18) by lia.
      assert (HP : N * nZ <= 2^18 * 2^24) by (apply Z.mul_le_mono_nonneg; lia).
      lia.
    - (* [comment removed for export] *)
      assert (E1 : (4096 * N) * nZ <= LV * nZ) by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite <- Z.mul_assoc in E1.
      pose proof (four_xy_le_sq LV nZ HLV ltac:(lia)) as E2.
      assert (E3 : (LV + nZ) * (LV + nZ) <= 2^30 * 2^30) by (apply Z.mul_le_mono_nonneg; lia).
      set (P := N * nZ) in *. set (Q := LV * nZ) in *. set (SQ := (LV + nZ) * (LV + nZ)) in *.
      lia. }
  destruct (gap_exists (vm_maps h) nZ F (alloc_top h) ltac:(lia) ltac:(unfold PGSZ in *; lia)
              ltac:(rewrite Htop; lia) ltac:(rewrite page_size_eq; exact S2) HW)
    as (g & Hgal & HgF & Hgtop & Hgfree).
  (* [comment removed for export] *)
  apply (proj2 (vm_gap_available_iff h nZ)). exists (Z_to_bv 64 g).
  split; [|split; [|split]].
  - rewrite u64_lit' by lia. exact Hgal.
  - rewrite u64_lit' by lia. lia.
  - rewrite u64_lit' by lia. exact Hgtop.
  - rewrite region_free_app_iff, Hgfree, Bool.andb_true_r.
    apply region_free_intro. intros a sz Hin.
    pose proof (kl_resv_top _ _ _ HK (a, sz) Hin) as Hr. fold h F in Hr. unfold ehi in Hr. cbn [fst snd] in Hr.
    unfold iv_overlap. rewrite u64_lit' by lia.
    apply andb_false_iff. left. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma gk_budget : forall mo nZ,
  vm_clean mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  (nZ <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + nZ <= KLIM) ->
  vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros mo nZ Hc (_ & G2 & _) Hl Hreq. pose proof (vm_backing_used_le_live mo Hc).
  unfold KLIM, SMALLREQ in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_mmap_anon_noerr : forall {CE : Ceiling} len prot mo rsp mo' evs,
  0 < len -> mmap_len len < 2^64 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (if prot =? PROT_NONE then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 MAPF) mo (mmap_len len)) = false ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE len prot mo rsp mo' evs Hlen Hlen2 Hprot Hnr H.
  exact (nstep_c_mmap_anon_noerr len prot mo rsp mo' evs Hlen Hlen2 Hprot Hnr H).
Qed.

(* [comment removed for export] *)
Lemma gk_refusable_false : forall {CE : Ceiling} L pbrk mo len prot,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < len -> prot = PROT_NONE \/ prot = PROT_RW ->
  (mmap_len len <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + mmap_len len <= KLIM) ->
  (if prot =? PROT_NONE then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 MAPF) mo (mmap_len len)) = false.
Proof.
  intros CE L pbrk mo len prot HK HG Hl Hlen Hprot Hreq.
  pose proof (mmap_len_ge len Hlen) as Hb. pose proof (mmap_len_aligned len) as Hal.
  assert (Hgap : vm_gap_available (m_vmmaps mo) (mmap_len len) = true).
  { exact (gk_gap L pbrk mo (mmap_len len) HK HG Hl ltac:(lia) ltac:(rewrite page_size_eq; exact Hal) Hreq). }
  destruct Hprot as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
  - unfold mmap_reserve_refusable. rewrite Hgap. reflexivity.
  - unfold mmap_grant_refusable. rewrite Hgap, Bool.orb_false_r.
    unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbn iota.
    rewrite (proj2 (Z.leb_le _ _)); [reflexivity|].
    apply gk_budget; [exact (minv_clean _ (kl_minv _ _ _ HK))| exact HG| exact Hl| exact Hreq].
Qed.

Lemma gk_mmap_noerr : forall {CE : Ceiling} L pbrk mo len prot rsp mo' evs,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < len < 2^63 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (mmap_len len <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + mmap_len len <= KLIM) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE L pbrk mo len prot rsp mo' evs HK HG Hl Hlen Hprot Hreq Hst.
  pose proof (mmap_len_ge len ltac:(lia)) as Hb.
  apply (nstep_mmap_anon_noerr len prot mo rsp mo' evs ltac:(lia) ltac:(lia) Hprot); [|exact Hst].
  exact (gk_refusable_false L pbrk mo len prot HK HG Hl ltac:(lia) Hprot Hreq).
Qed.

(* [comment removed for export] *)
Lemma nstep_mprotect_noerr : forall {CE : Ceiling} addr mo rsp mo' evs,
  0 <= addr -> addr + PGSZ < 2^64 -> addr mod PGSZ = 0 ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) = true ->
  nstep (NMprotect addr PGSZ PROT_RW) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE addr mo rsp mo' evs Ha0 Ha1 Hal Hbud H.
  exact (nstep_c_mprotect_noerr' addr mo rsp mo' evs Ha0 Ha1 Hal Hbud H).
Qed.


(* [comment removed for export] *)
Lemma gk_mprotect_budget : forall mo a n,
  vm_clean mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  mprotect_budget_ok mo a n = true.
Proof.
  intros mo a n Hc (_ & G2 & _) Hl. unfold mprotect_budget_ok, vm_backing_within_limit.
  apply Z.leb_le.
  pose proof (vm_backing_used_le_live (mprotect_model_next mo a n) (vm_clean_mprotect_model_next mo a n Hc)) as H.
  assert (E : vm_live_bytes (m_vmmaps (mprotect_model_next mo a n)) = vm_live_bytes (m_vmmaps mo)) by reflexivity.
  assert (E2 : vm_limit (m_vmmaps (mprotect_model_next mo a n)) = vm_limit (m_vmmaps mo)) by reflexivity.
  rewrite E2. unfold KLIM, SMALLREQ in *. lia.
Qed.
