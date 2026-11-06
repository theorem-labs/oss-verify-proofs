(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngExc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition gpart (s : astate) : list mcell := flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s).

Definition EXC_ok (s : astate) (EXC : list loc) : Prop :=
  forall l, In l EXC -> exists c, In c (gpart s) /\ mc_loc c = l /\ mc_w c = 8%nat.

Lemma image_parts : forall s, image s = ctx_cells s ++ areas_cells s (st_areas s) ++ gpart s.
Proof. reflexivity. Qed.

Lemma pw_cross : forall L (A B : list mcell) x y, pairwise ranges_disjoint (map (cell_range L) (A ++ B)) ->
  In x A -> In y B -> ranges_disjoint (cell_range L x) (cell_range L y).
Proof.
  intros L A B x y H Hx Hy. rewrite map_app in H.
  apply (pairwise_In_app ranges_disjoint (map (cell_range L) A) (map (cell_range L) B) H); apply in_map; assumption.
Qed.

Lemma loc_neq_of_disj : forall L c1 c2, ranges_disjoint (cell_range L c1) (cell_range L c2) -> (1 <= mc_w c1)%nat -> (1 <= mc_w c2)%nat ->
  mc_loc c1 <> mc_loc c2.
Proof. intros L c1 c2 D W1 W2 E. unfold ranges_disjoint, cell_range in D. cbn [fst snd] in D. rewrite E in D. lia. Qed.

(* [comment removed for export] *)
Lemma not_exc_front : forall L s EXC c, PW L s -> EXC_ok s EXC -> In c (ctx_cells s ++ areas_cells s (st_areas s)) ->
  ~ In (mc_loc c) EXC.
Proof.
  intros L s EXC c HPW HEX Hc Hin. destruct (HEX _ Hin) as (h & Hh & Eh & Wh).
  unfold PW in HPW. rewrite image_parts, app_assoc in HPW.
  pose proof (pw_cross L _ _ c h HPW Hc Hh) as D.
  assert (Wc : (1 <= mc_w c)%nat) by (apply (image_cell_width s c); rewrite image_parts, app_assoc; apply in_app_iff; left; exact Hc).
  apply (loc_neq_of_disj L c h D Wc ltac:(rewrite Wh; lia)). symmetry. exact Eh.
Qed.

(* [comment removed for export] *)
Lemma not_exc_group : forall L s EXC c, PW L s -> EXC_ok s EXC -> In c (gpart s) -> mc_w c <> 8%nat -> ~ In (mc_loc c) EXC.
Proof.
  intros L s EXC c HPW HEX Hc Hw Hin. destruct (HEX _ Hin) as (h & Hh & Eh & Wh).
  assert (Hne : c <> h) by (intros ->; exact (Hw Wh)).
  assert (Hc' : In c (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact Hc).
  assert (Hh' : In h (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact Hh).
  pose proof (pairwise_map_In _ (cell_range L) _ _ _ HPW Hc' Hh' Hne) as [D|D].
  - apply (loc_neq_of_disj L c h D (image_cell_width s c Hc') (image_cell_width s h Hh')). symmetry. exact Eh.
  - apply (loc_neq_of_disj L h c D (image_cell_width s h Hh') (image_cell_width s c Hc')). exact Eh.
Qed.

(* [comment removed for export] *)
Section RB.
Variable segs : list Segment.

#[using="Type"] Lemma repr_x_holds : forall L s bv EXC c, repr_x L s bv EXC -> In c (image s) -> ~ In (mc_loc c) EXC -> cell_holds L bv c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s bv EXC c (_ & _ & HC & _) Hc Hn. destruct (proj1 (Forall_forall _ _) HC c Hc) as [He|H]; [contradiction | exact H].
Qed.

#[using="Type"] Lemma repr_x_rdn : forall L s m EXC c, repr_x L s (bview segs m) EXC -> In c (image s) -> ~ In (mc_loc c) EXC ->
  (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  rdn segs m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof. LiaFast.lf_pins LiaFast.u0. intros L s m EXC c HR Hc Hn Hv Hw. apply holds_rdn; [exact (repr_x_holds L s _ EXC c HR Hc Hn) | exact Hv | exact Hw]. Qed.
End RB.

(* [comment removed for export] *)
Lemma ctx_in_front : forall s c, In c (ctx_cells s) -> In c (ctx_cells s ++ areas_cells s (st_areas s)).
Proof. intros s c H. apply in_app_iff. left. exact H. Qed.

Lemma act_in_ctx : forall s k, (k < 48)%nat -> In (act_cell k (nth k (st_active s) None)) (ctx_cells s).
Proof.
  intros s k Hk. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. unfold act_cell.
  apply (in_map (fun k0 => MCell (LCtx (CTX_active + 8 * Z.of_nat k0)) 8 (optr (nth k0 (st_active s) None)))). apply in_seq. lia.
Qed.

Lemma usage_in_ctx : forall s k, (k < 48)%nat -> In (MCell (LCtx (CTX_usage + 8 * Z.of_nat k)) 8 (VZ (nth k (st_usage s) 0))) (ctx_cells s).
Proof.
  intros s k Hk. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply (in_map (fun k0 => MCell (LCtx (CTX_usage + 8 * Z.of_nat k0)) 8 (VZ (nth k0 (st_usage s) 0)))). apply in_seq. lia.
Qed.

Lemma unmap_in_ctx : forall s k, (k < 32)%nat -> In (MCell (LCtx (CTX_unmap_seq + Z.of_nat k)) 1 (VZ (nth k (st_unmap_seq s) 0))) (ctx_cells s).
Proof.
  intros s k Hk. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply (in_map (fun k0 => MCell (LCtx (CTX_unmap_seq + Z.of_nat k0)) 1 (VZ (nth k0 (st_unmap_seq s) 0)))). apply in_seq. lia.
Qed.

Lemma bounce_in_ctx : forall s k, (k < 32)%nat -> In (MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ (nth k (st_bounces s) 0))) (ctx_cells s).
Proof.
  intros s k Hk. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
  apply (in_map (fun k0 => MCell (LCtx (CTX_bounces + Z.of_nat k0)) 1 (VZ (nth k0 (st_bounces s) 0)))). apply in_seq. lia.
Qed.

Lemma seq_in_ctx : forall s, In (MCell (LCtx CTX_seq) 1 (VZ (st_seq s))) (ctx_cells s).
Proof. intros s. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.

Lemma fmh_in_ctx : forall s, In (MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s))) (ctx_cells s).
Proof. intros s. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.

(* [comment removed for export] *)
Lemma msc_in_front : forall s g x c, KS s -> MT s g = Some x -> In c (meta_slot_cells g (Some x)) ->
  In c (ctx_cells s ++ areas_cells s (st_areas s)).
Proof.
  intros s g x c [ND KO] Hg Hc. apply in_app_iff. right.
  apply (Permutation_in c (Permutation_sym (areas_cells_perm s (st_areas s)))). apply in_app_iff. right.
  assert (Hk : In g (keys s)) by (eapply MT_keys; exact Hg).
  pose proof (KO g Hk) as F. assert (Hs : In g (all_slots (st_areas s))).
  { assert (In g (List.filter (fun q => sptr_eqb q g) (all_slots (st_areas s)))) by (rewrite F; left; reflexivity).
    apply List.filter_In in H. exact (proj1 H). }
  apply in_flat_map. exists g. split; [exact Hs|]. unfold mcells. change (mlookup (st_metas s) g) with (MT s g). rewrite Hg. exact Hc.
Qed.

Lemma group_in_gpart : forall s g am c, MT s g = Some (MUsed am) -> List.NoDup (keys s) -> In c (group_cells g am) -> In c (gpart s).
Proof.
  intros s g am c Hg ND Hc. unfold gpart. apply in_flat_map. exists (g, am). split; [|exact Hc].
  apply (used_metas_iff s g am ND). exact Hg.
Qed.

Lemma act_in_ctx_img : forall s k, (k < 48)%nat -> In (act_cell k (nth k (st_active s) None)) (image s).
Proof. intros s k Hk. rewrite image_parts, app_assoc. apply in_app_iff. left. apply ctx_in_front. exact (act_in_ctx s k Hk). Qed.
