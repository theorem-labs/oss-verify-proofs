(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec AgentLib VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require BackingAlgebra.
Import ListNotations.
Local Open Scope Z_scope.

Module BA := BackingAlgebra.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
Fixpoint maps_pw' (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | (a, n) :: r => region_free r a n = true /\ maps_pw' r
  end.

(* [comment removed for export] *)
Definition maps_nw' (l : list (word * word)) : Prop :=
  forall b sz, In (b, sz) l -> u b + u sz <= 2^64.

Lemma ivs_wf_of_nw : forall l, maps_nw' l -> BA.ivs_wf l.
Proof. intros l H [b sz] Hin. unfold BA.iv_wf, BA.B, BA.S. cbn [fst snd]. exact (H b sz Hin). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma overlap_sum_free_sub : forall r (a n : word) lo hi,
  region_free r a n = true -> u a <= lo -> hi <= u a + u n -> lo <= hi ->
  BA.overlap_sum r lo hi = 0.
Proof.
  induction r as [|[b s] r IH]; intros a n lo hi Hf H1 H2 H3; [reflexivity|].
  cbn [region_free] in Hf. apply andb_true_iff in Hf as [Hf1 Hf2].
  rewrite BA.overlap_sum_cons, (IH a n lo hi Hf2 H1 H2 H3).
  destruct (Z.eq_dec lo hi) as [-> | Hne].
  - unfold BA.iv_count. rewrite BA.zcount_false; [lia|]. intros x _. unfold BA.in_rng.
    apply andb_false_iff. destruct (Z.le_gt_cases hi x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
  - rewrite BA.iv_count_in_rng_disjoint; [lia|].
    apply negb_true_iff in Hf1. unfold iv_overlap in Hf1. unfold BA.B, BA.S. cbn [fst snd].
    apply andb_false_iff in Hf1 as [Hf1|Hf1]; apply Z.ltb_ge in Hf1; lia.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_inside_pw : forall l (b sz : word) lo hi,
  maps_pw' l -> In (b, sz) l -> u b <= lo -> hi <= u b + u sz -> lo <= hi ->
  BA.overlap_sum l lo hi <= hi - lo.
Proof.
  induction l as [|[a n] r IH]; intros b sz lo hi Hpw Hin H1 H2 H3; [destruct Hin|].
  destruct Hpw as [Hf Hpw]. rewrite BA.overlap_sum_cons.
  destruct Hin as [E | Hin].
  - injection E as -> ->. rewrite (overlap_sum_free_sub r b sz lo hi Hf H1 H2 H3).
    pose proof (BA.iv_count_in_rng_le (b, sz) lo hi H3). lia.
  - pose proof (IH b sz lo hi Hpw Hin H1 H2 H3) as IH'.
    destruct (Z.eq_dec lo hi) as [-> | Hne].
    + unfold BA.iv_count. rewrite BA.zcount_false; [lia|]. intros x _. unfold BA.in_rng.
      apply andb_false_iff. destruct (Z.le_gt_cases hi x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
    + rewrite BA.iv_count_in_rng_disjoint; [lia|].
      pose proof (region_free_In r a n b sz Hf Hin) as Ho. unfold iv_overlap in Ho. unfold BA.B, BA.S. cbn [fst snd].
      apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma backed_sem : forall h, BA.ivs_wf (vm_maps h) ->
  vm_backed_bytes h = BA.sum_count (fun x => negb (BA.covered (vm_noaccess h) x)) (vm_maps h).
Proof. intros h Hwf. unfold vm_backed_bytes, vm_backed_maps. apply (proj1 (BA.live_msa _ _ Hwf)). Qed.

(* [comment removed for export] *)
Theorem backed_unprotect_le : forall h (p n b sz : word),
  maps_nw' (vm_maps h) -> maps_nw' (vm_noaccess h) -> maps_pw' (vm_maps h) ->
  In (b, sz) (vm_maps h) -> u b <= u p -> u p + u n <= u b + u sz ->
  vm_backed_bytes (vm_unprotect p n h) <= vm_backed_bytes h + u n.
Proof.
  intros h p n b sz Hnw Hnwn Hpw Hin H1 H2.
  pose proof (ivs_wf_of_nw _ Hnw) as Wm. pose proof (ivs_wf_of_nw _ Hnwn) as Wn.
  pose proof (u64_range n) as Rn.
  rewrite (backed_sem h Wm). rewrite (backed_sem (vm_unprotect p n h)) by exact Wm.
  cbn [vm_maps vm_noaccess vm_unprotect].
  destruct (BA.maps_subtract_sem (vm_noaccess h) (u p) (u p + u n) Wn ltac:(lia)) as (_ & _ & Cv).
  eapply Z.le_trans.
  { apply (BA.sum_count_mono _ (fun x => negb (BA.covered (vm_noaccess h) x) || BA.in_rng (u p) (u p + u n) x)).
    intros x. rewrite Cv. destruct (BA.covered (vm_noaccess h) x), (BA.in_rng (u p) (u p + u n) x); cbn; congruence. }
  pose proof (BA.sum_count_or_le (fun x => negb (BA.covered (vm_noaccess h) x)) (BA.in_rng (u p) (u p + u n)) (vm_maps h)).
  pose proof (overlap_sum_inside_pw (vm_maps h) b sz (u p) (u p + u n) Hpw Hin H1 H2 ltac:(lia)) as Ho.
  unfold BA.overlap_sum in Ho. cbv beta in *. lia.
Qed.

(* [comment removed for export] *)
Theorem backed_noacc_le : forall h (a n : word),
  maps_nw' (vm_maps h) -> u a + u n <= 2^64 ->
  vm_backed_bytes (vm_noacc a n h) <= vm_backed_bytes h.
Proof.
  intros h a n Hnw Han.
  pose proof (ivs_wf_of_nw _ Hnw) as Wm.
  assert (Wm' : BA.ivs_wf (vm_maps (vm_noacc a n h))).
  { cbn [vm_maps vm_noacc]. apply BA.ivs_wf_cons; [exact Han | exact Wm]. }
  rewrite (backed_sem h Wm), (backed_sem _ Wm'). cbn [vm_maps vm_noaccess vm_noacc BA.sum_count].
  pose proof (u64_range n) as Rn. pose proof (u64_range a) as Ra.
  assert (Z0 : BA.iv_count (fun x => negb (BA.covered ((a, n) :: vm_noaccess h) x)) (a, n) = 0).
  { unfold BA.iv_count. apply BA.zcount_false. intros x Hx. unfold BA.B, BA.S in Hx. cbn [fst snd] in Hx.
    rewrite Z2Nat.id in Hx by lia.
    unfold BA.covered. cbn [existsb]. unfold BA.in_iv, BA.in_rng, BA.B, BA.S. cbn [fst snd].
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Z0.
  pose proof (BA.sum_count_mono (fun x => negb (BA.covered ((a, n) :: vm_noaccess h) x))
                (fun x => negb (BA.covered (vm_noaccess h) x)) (vm_maps h)) as M.
  assert (HM : forall x, negb (BA.covered ((a, n) :: vm_noaccess h) x) = true -> negb (BA.covered (vm_noaccess h) x) = true).
  { intros x. unfold BA.covered. cbn [existsb]. destruct (BA.in_iv (a, n) x); cbn; [discriminate | exact (fun H => H)]. }
  specialize (M HM). lia.
Qed.

(* [comment removed for export] *)
Corollary mprot_ok_vm_intro : forall h (p n b sz : word),
  maps_nw' (vm_maps h) -> maps_nw' (vm_noaccess h) -> maps_pw' (vm_maps h) ->
  In (b, sz) (vm_maps h) -> u b <= u p -> u p + u n <= u b + u sz ->
  vm_backed_bytes h + u n <= vm_limit h ->
  mprot_ok_vm h p n = true.
Proof.
  intros h p n b sz Hnw Hnwn Hpw Hin H1 H2 Hb. unfold mprot_ok_vm. apply Z.leb_le.
  pose proof (backed_unprotect_le h p n b sz Hnw Hnwn Hpw Hin H1 H2).
  replace (vm_limit h) with (vm_limit (vm_unprotect p n h)) in Hb by reflexivity. cbn [vm_limit vm_unprotect] in *. lia.
Qed.
