(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger VmGap.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require BackingAlgebra.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocInv_defs MallocInv_word MallocInv_vm MallocInv_budget MallocInv_vmfree MallocInv_ametax_iface MallocSureVm.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Abbreviation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma maps_pw_pw' : forall l, maps_pw l -> maps_pw' l.
Proof. induction l as [|[a n] r IH]; cbn; [auto | intros [H1 H2]; split; [exact H1 | exact (IH H2)]]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem areas_le_backed : forall A h, WF A -> VMok A h ->
  4096 * Z.of_nat (length (a_areas A)) <= vm_backed_bytes h.
Proof.
  intros A h HW HV.
  pose proof (ivs_wf_of_nw _ (vm_maps_nw A h HV)) as Wm.
  rewrite (backed_sem h Wm).
  apply pages_le_count.
  - apply (proj1 (NoDup_ListNoDup _)). exact (wf_areas_nodup A HW).
  - intros pg Hpg. exact (proj1 (wf_areas_al A HW pg Hpg)).
  - intros pg Hpg. destruct (wf_areas_al A HW pg Hpg) as (_ & Hr). unfold heap_range in Hr.
    destruct (vm_areas_cov A h HV pg Hpg) as ((b & s & Hin & Hlo & Hhi) & Hfree).
    exists b, s. split; [exact Hin|]. split; [exact Hlo|]. split; [exact Hhi|].
    intros x Hx. apply negb_true_iff.
    pose proof alloc_ceiling_range as CR.
    apply (region_free_not_covered (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) x Hfree).
    rewrite !uZ by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lsum_app : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1 as [|[c n] r IH]; intros l2; cbn [lsum app]; [lia | rewrite IH; lia]. Qed.

Lemma lsum_nonneg : forall l, 0 <= lsum l.
Proof. induction l as [|[c n] r IH]; cbn [lsum]; lia. Qed.

Lemma lsum_le_each : forall l M, 0 <= M -> (forall c n, In (c, n) l -> n <= M) -> lsum l <= Z.of_nat (length l) * M.
Proof.
  induction l as [|[c n] r IH]; intros M HM H; cbn [lsum length]; [lia|].
  rewrite Nat2Z.inj_succ. pose proof (H c n (or_introl eq_refl)).
  pose proof (IH M HM (fun c' n' Hin => H c' n' (or_intror Hin))). lia.
Qed.

Lemma pow2_shift_le : forall A, WF A ->
  0 <= a_ctx A KShift < 48 /\ 2 ^ (a_ctx A KShift) <= Z.of_nat (length (a_areas A)) + 50.
Proof.
  intros A HW. pose proof (wf_shift A HW) as H48. pose proof (wf_ctx_nonneg A HW KShift) as H0.
  destruct (wf_shift_acct A HW) as (_ & Q2 & _). split; lia.
Qed.

(* [comment removed for export] *)
Theorem next_block_le : forall A, WF A -> a_ctx A KAac = 0 ->
  2 ^ (a_ctx A KShift + 13) <= 4096 * (Z.of_nat (length (a_areas A)) + 50).
Proof.
  intros A HW Haac. pose proof (wf_shift A HW) as H48. pose proof (wf_ctx_nonneg A HW KShift) as H0.
  destruct (wf_shift_acct A HW) as (Q1 & _ & _). rewrite Haac in Q1.
  replace (a_ctx A KShift + 13) with (12 + (a_ctx A KShift + 1)) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. lia.
Qed.

Theorem mblocks_sum_le : forall A, WF A ->
  lsum (a_mblocks A) <= 48 * (4096 * (Z.of_nat (length (a_areas A)) + 50)).
Proof.
  intros A HW. destruct (pow2_shift_le A HW) as [[H0 H48] Hp].
  destruct (wf_shift_acct A HW) as (_ & _ & Q3).
  set (M := 4096 * (Z.of_nat (length (a_areas A)) + 50)).
  assert (HM : 0 <= M) by (unfold M; lia).
  eapply Z.le_trans; [apply (lsum_le_each (a_mblocks A) M HM)|].
  - intros c n Hin. destruct (wf_mblocks_sz A HW c n Hin) as (_ & [_ Hn] & _).
    eapply Z.le_trans; [exact Hn|]. unfold M.
    apply Z.le_trans with (2 ^ (12 + a_ctx A KShift)); [apply Z.pow_le_mono_r; lia|].
    rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. lia.
  - nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cont_of (cl : Z * Z) : Z * Z := (fst cl, fst cl + Z.max 0 (snd cl)).

Lemma csum_conts : forall l, csum (map cont_of l) = lsum l.
Proof. induction l as [|[c n] r IH]; cbn [map csum lsum fold_right cont_of fst snd]; [reflexivity|]. fold (csum (map cont_of r)). rewrite IH. lia. Qed.

Theorem live_le : forall A h, WF A -> VMok A h ->
  vm_live_bytes h <= vm_backed_bytes h + (u (vm_brk h) - u (vm_start_brk h)) + lsum (a_mblocks A ++ a_xmaps A).
Proof.
  intros A h HW HV.
  pose proof (ivs_wf_of_nw _ (vm_maps_nw A h HV)) as Wm.
  rewrite (live_backed_cov h Wm).
  destruct (vm_brk_valid A h HV) as (_ & Hsb & _).
  set (conts := (u (vm_start_brk h), u (vm_brk h)) :: map cont_of (a_mblocks A ++ a_xmaps A)).
  assert (Hc : BackingAlgebra.sum_count (BackingAlgebra.covered (vm_noaccess h)) (vm_maps h) <= csum conts).
  { apply cov_le_containers.
    - apply maps_pw_pw'. exact (vm_pw A h HV).
    - intros c [<- | Hin]; [cbn [fst snd]; lia|].
      apply in_map_iff in Hin as ([c0 n0] & <- & _). cbn [cont_of fst snd]. lia.
    - intros [b sz] Hin. destruct (vm_all A h HV b sz Hin) as [(ma & mt & aib & sl & Hma & Hr & Hml & Eb & Es) | [[Hb1 Hb2] | (c & l & Hcl & Hc1 & Hc2)]].
      + (* [comment removed for export] *) left.
        destruct (vm_grp A h HV ma mt aib sl Hma Hr Hml) as [_ Hfree].
        assert (Ebw : Z_to_bv 64 (mt_mem mt) = b) by (rewrite <- Eb; apply Z_to_bv_bv_unsigned).
        assert (Esw : Z_to_bv 64 (grp_map_len mt) = sz) by (rewrite <- Es; apply Z_to_bv_bv_unsigned).
        rewrite Ebw, Esw in Hfree.
        unfold BackingAlgebra.iv_count. apply BackingAlgebra.zcount_false. intros x Hx.
        unfold BackingAlgebra.B, BackingAlgebra.S in Hx. cbn [fst snd] in Hx. pose proof (u64_range sz).
        rewrite Z2Nat.id in Hx by lia.
        exact (region_free_not_covered (vm_noaccess h) b sz x Hfree Hx).
      + (* [comment removed for export] *) right. exists (u (vm_start_brk h), u (vm_brk h)). split; [left; reflexivity|].
        unfold inside. cbn [fst snd]. apply andb_true_iff. split; apply Z.leb_le; lia.
      + (* [comment removed for export] *) right. exists (cont_of (c, l)). split; [right; apply in_map; exact Hcl|].
        unfold inside, cont_of. cbn [fst snd]. apply andb_true_iff. split; apply Z.leb_le; lia. }
  unfold conts in Hc. cbn [csum fold_right fst snd] in Hc. fold (csum (map cont_of (a_mblocks A ++ a_xmaps A))) in Hc.
  rewrite csum_conts in Hc. lia.
Qed.

(* [comment removed for export] *)
Corollary live_le_areas : forall A h, WF A -> VMok A h ->
  vm_live_bytes h <= vm_backed_bytes h + 4096 * (Z.of_nat (length (a_areas A)) + 1)
                     + 48 * (4096 * (Z.of_nat (length (a_areas A)) + 50)) + lsum (a_xmaps A).
Proof.
  intros A h HW HV. pose proof (live_le A h HW HV) as H. rewrite lsum_app in H.
  pose proof (mblocks_sum_le A HW). pose proof (proj2 (vm_brk_span A h HV)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reserved_below : forall A h, VMok A h ->
  forall b s, In (b, s) (vm_reserved h) -> u b + u s <= 2^32.
Proof.
  intros A h HV b s Hin. rewrite (vm_res A h HV) in Hin.
  destruct (mlo_reserved_in b s Hin) as (_ & H2 & _). pose proof (mlo_hull (ML:=ML)). lia.
Qed.

Theorem node_gap_na : forall A h n, WF A -> VMok A h ->
  0 < n -> n mod 4096 = 0 ->
  2^32 + (vm_backed_bytes h + 4096 * (Z.of_nat (length (a_areas A)) + 1)
          + 48 * (4096 * (Z.of_nat (length (a_areas A)) + 50)) + lsum (a_xmaps A))
       + Z.of_nat (length (vm_maps h)) * (n + 4095) + n <= alloc_ceiling ->
  exists a, grant_ok_na_vm h a n = true.
Proof.
  intros A h n HW HV Hn Hal Hroom.
  apply (gap_exists_na h n (2^32) Hn Hal); [lia | reflexivity | exact (reserved_below A h HV) |].
  rewrite (vm_top A h HV). pose proof (live_le_areas A h HW HV).
  pose proof (Zle_0_nat (length (vm_maps h))). nia.
Qed.

Theorem node_gap : forall A h n, WF A -> VMok A h ->
  0 < n -> n mod 4096 = 0 ->
  2^32 + (vm_backed_bytes h + 4096 * (Z.of_nat (length (a_areas A)) + 1)
          + 48 * (4096 * (Z.of_nat (length (a_areas A)) + 50)) + lsum (a_xmaps A))
       + Z.of_nat (length (vm_maps h)) * (n + 4095) + n <= alloc_ceiling ->
  vm_backed_bytes h + n <= vm_limit h ->
  exists a, grant_ok_vm h a n = true.
Proof.
  intros A h n HW HV Hn Hal Hroom Hbud.
  destruct (node_gap_na A h n HW HV Hn Hal Hroom) as [a Ha].
  exists a. unfold grant_ok_vm. unfold grant_ok_na_vm in Ha. rewrite Ha.
  rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity.
Qed.

End WithLayout.
