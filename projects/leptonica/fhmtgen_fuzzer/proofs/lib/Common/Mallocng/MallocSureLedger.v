(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec AgentLib VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require BackingAlgebra.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import MallocInv_budget MallocSureVm.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Abbreviation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
Theorem backed_cons_le : forall h h' (a n : word),
  vm_maps h' = (a, n) :: vm_maps h -> vm_noaccess h' = vm_noaccess h ->
  maps_nw' (vm_maps h) -> u a + u n <= 2^64 ->
  vm_backed_bytes h' <= vm_backed_bytes h + u n.
Proof.
  intros h h' a n Em En Hnw Han.
  pose proof (ivs_wf_of_nw _ Hnw) as Wm.
  assert (Wm' : BA.ivs_wf (vm_maps h')) by (rewrite Em; apply BA.ivs_wf_cons; [exact Han | exact Wm]).
  rewrite (backed_sem h Wm), (backed_sem h' Wm'). rewrite Em, En. cbn [BA.sum_count].
  pose proof (iv_count_le_size (fun x => negb (BA.covered (vm_noaccess h) x)) (a, n)) as Hc. cbn [snd] in Hc. lia.
Qed.

Corollary backed_mmap_le : forall h (a n : word),
  maps_nw' (vm_maps h) -> u a + u n <= 2^64 ->
  vm_backed_bytes (vm_mmap a n h) <= vm_backed_bytes h + u n.
Proof. intros h a n Hnw Han. apply (backed_cons_le h (vm_mmap a n h) a n); [reflexivity | reflexivity | exact Hnw | exact Han]. Qed.

Corollary backed_brk_grow_le : forall h (req : word),
  maps_nw' (vm_maps h) -> u (vm_brk h) + u (req - vm_brk h)%bv <= 2^64 ->
  vm_backed_bytes (vm_brk_grow req h) <= vm_backed_bytes h + u (req - vm_brk h)%bv.
Proof.
  intros h req Hnw Han.
  apply (backed_cons_le h (vm_brk_grow req h) (vm_brk h) (req - vm_brk h)%bv); [reflexivity | reflexivity | exact Hnw | exact Han].
Qed.

(* [comment removed for export] *)
Theorem backed_fixed_ok_le : forall h (a n : word),
  maps_nw' (vm_maps h) -> maps_nw' (vm_noaccess h) ->
  vm_backed_bytes (vm_fixed_ok a n h) <= vm_backed_bytes h.
Proof.
  intros h a n Hnw Hnwn.
  pose proof (ivs_wf_of_nw _ Hnw) as Wm. pose proof (ivs_wf_of_nw _ Hnwn) as Wn.
  pose proof (u64_range n) as Rn.
  rewrite (backed_sem h Wm). rewrite (backed_sem (vm_fixed_ok a n h)) by exact Wm.
  cbn [vm_maps vm_noaccess vm_fixed_ok].
  destruct (BA.maps_subtract_sem (vm_noaccess h) (u a) (u a + u n) Wn ltac:(lia)) as (_ & _ & Cv).
  apply BA.sum_count_mono. intros x Hx.
  unfold BA.covered in Hx. cbn [existsb] in Hx. fold (BA.covered (maps_subtract (vm_noaccess h) (u a) (u a + u n)) x) in Hx.
  rewrite Cv in Hx. unfold BA.in_iv, BA.B, BA.S in Hx. cbn [fst snd] in Hx.
  destruct (BA.covered (vm_noaccess h) x); [| reflexivity].
  destruct (BA.in_rng (u a) (u a + u n) x); cbn in Hx; discriminate Hx.
Qed.

(* [comment removed for export] *)
Lemma pw_diff_base_disjoint : forall l (b1 s1 b2 s2 : word),
  maps_pw' l -> In (b1, s1) l -> In (b2, s2) l -> b1 <> b2 ->
  u b1 + u s1 <= u b2 \/ u b2 + u s2 <= u b1.
Proof.
  induction l as [|[b s] r IH]; intros b1 s1 b2 s2 Hpw H1 H2 Hne; [contradiction|].
  destruct Hpw as [Hf Hpw].
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as <- <-. injection E2 as <- <-. exfalso. exact (Hne eq_refl).
  - injection E1 as <- <-. pose proof (region_free_In r b s b2 s2 Hf H2) as Ho. unfold iv_overlap in Ho.
    apply andb_false_iff in Ho as [Ho | Ho]; apply Z.ltb_ge in Ho; lia.
  - injection E2 as <- <-. pose proof (region_free_In r b s b1 s1 Hf H1) as Ho. unfold iv_overlap in Ho.
    apply andb_false_iff in Ho as [Ho | Ho]; apply Z.ltb_ge in Ho; lia.
  - exact (IH b1 s1 b2 s2 Hpw H1 H2 Hne).
Qed.

Lemma sum_count_filter_le : forall P (f : word * word -> bool) l,
  BA.sum_count P (List.filter f l) <= BA.sum_count P l.
Proof.
  intros P f l. induction l as [|q r IH]; cbn [List.filter BA.sum_count]; [lia|].
  pose proof (BA.zcount_nonneg P (BA.B q) (Z.to_nat (BA.S q))) as H0. unfold BA.iv_count in *.
  destruct (f q); cbn [BA.sum_count]; unfold BA.iv_count; lia.
Qed.

Lemma sum_count_ext_in : forall P Q l,
  (forall e, In e l -> BA.iv_count P e = BA.iv_count Q e) -> BA.sum_count P l = BA.sum_count Q l.
Proof.
  intros P Q l. induction l as [|q r IH]; intros H; cbn [BA.sum_count]; [reflexivity|].
  rewrite (H q (or_introl eq_refl)), (IH (fun e He => H e (or_intror He))). reflexivity.
Qed.

Theorem backed_munmap_le : forall h (a n : word),
  maps_nw' (vm_maps h) -> maps_nw' (vm_noaccess h) -> maps_pw' (vm_maps h) ->
  In (a, n) (vm_maps h) ->
  vm_backed_bytes (vm_munmap a n h) <= vm_backed_bytes h.
Proof.
  intros h a n Hnw Hnwn Hpw Hin.
  pose proof (ivs_wf_of_nw _ Hnw) as Wm. pose proof (ivs_wf_of_nw _ Hnwn) as Wn.
  pose proof (u64_range n) as Rn.
  assert (Wm' : BA.ivs_wf (map_remove (vm_maps h) a)) by (unfold map_remove; apply BA.ivs_wf_filter; exact Wm).
  rewrite (backed_sem h Wm). rewrite (backed_sem (vm_munmap a n h)) by exact Wm'.
  cbn [vm_maps vm_noaccess vm_munmap].
  destruct (BA.maps_subtract_sem (vm_noaccess h) (u a) (u a + u n) Wn ltac:(lia)) as (_ & _ & Cv).
  eapply Z.le_trans; [| apply (sum_count_filter_le _ (fun p => negb (bv_eqb (fst p) a)) (vm_maps h))].
  unfold map_remove. apply Z.eq_le_incl. apply sum_count_ext_in.
  intros [b s] He. apply filter_In in He as [He Hb]. cbn [fst] in Hb. apply negb_true_iff in Hb.
  assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in Hb; discriminate).
  pose proof (pw_diff_base_disjoint (vm_maps h) b s a n Hpw He Hin Hne) as D.
  unfold BA.iv_count. apply BA.zcount_ext. intros x Hx. unfold BA.B, BA.S in Hx. cbn [fst snd] in Hx.
  pose proof (u64_range s). rewrite Z2Nat.id in Hx by lia. rewrite Cv.
  replace (BA.in_rng (u a) (u a + u n) x) with false
    by (symmetry; unfold BA.in_rng; apply andb_false_iff; destruct D; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
  cbn [negb]. rewrite andb_true_r. reflexivity.
Qed.
