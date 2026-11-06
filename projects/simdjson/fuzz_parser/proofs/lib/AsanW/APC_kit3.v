(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma lb_remove_ne : forall p b LB A n, In b (lb_remove p LB) -> b <> HB p A n.
Proof.
  intros p b LB A n H E. subst b. unfold lb_remove in H. apply list_elem_of_In in H. apply list_elem_of_filter in H as [H _].
  cbn [ab_kind abkind_eqb] in H. rewrite N.eqb_refl in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma uchain_pres_above : forall m m' top pc sp fp k tr,
  uchain m top pc sp fp k tr -> sp + 16 <= fp ->
  (forall a, sp <= a < top -> m' (wa a) = m (wa a)) -> uchain m' top pc sp fp k tr.
Proof.
  intros m m' top pc sp fp k tr H HF HM. eapply uchain_frame; [exact H|]. intros a Ha. apply HM. lia.
Qed.
(* [comment removed for export] *)
Lemma uchain_of_pres : forall CI LB m m' top pc sp fp k tr,
  aheap_pres CI LB sp m m' -> top <= 2^47 -> 0 <= sp ->
  uchain m top pc sp fp k tr -> sp + 16 <= fp -> uchain m' top pc sp fp k tr.
Proof.
  intros CI LB m m' top pc sp fp k tr HP HT A0 H HF. eapply uchain_pres_above; [exact H| exact HF|].
  intros a Ha.
  destruct (HP a ltac:(lia) ltac:(left; lia)) as [E _]. exact E.
Qed.

Lemma uchain_of_pres_x : forall CI LB X n m m' top pc sp fp k tr,
  aheap_pres_x CI LB sp X n m m' -> X + n <= sp -> top <= 2^47 -> 0 <= sp ->
  uchain m top pc sp fp k tr -> sp + 16 <= fp -> uchain m' top pc sp fp k tr.
Proof.
  intros CI LB X n m m' top pc sp fp k tr HP HX HT A0 H HF. eapply uchain_pres_above; [exact H| exact HF|].
  intros a Ha. destruct (HP a ltac:(lia) ltac:(left; lia) ltac:(lia)) as [E _]. exact E.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_cons_ne : forall p b L, ab_kind b <> ABHeap p -> lb_remove p (b :: L) = b :: lb_remove p L.
Proof.
  intros p b L H. unfold lb_remove. rewrite filter_cons_True; [reflexivity|].
  destruct b as [k A n]; cbn [ab_kind] in *. destruct k as [q|c]; cbn [abkind_eqb]; [|exact I].
  destruct (N.eqb_spec q p); [subst; contradiction| exact I].
Qed.
Lemma lb_remove_cons_hd : forall p A n L, lb_remove p (HB p A n :: L) = lb_remove p L.
Proof.
  intros p A n L. unfold lb_remove. rewrite filter_cons_False; [reflexivity|]. cbn [ab_kind abkind_eqb]. rewrite N.eqb_refl. cbn. tauto.
Qed.
Lemma lb_remove_notin : forall p L, ~ In p (hb_ids L) -> lb_remove p L = L.
Proof.
  intros p L. induction L as [|b L IH]; intros H; [reflexivity|].
  rewrite lb_remove_cons_ne.
  - f_equal. apply IH. intros Hi. apply H. cbn [hb_ids flat_map]. apply in_or_app. right. exact Hi.
  - intros E. apply H. cbn [hb_ids flat_map]. rewrite E. apply in_or_app. left. left. reflexivity.
Qed.
Lemma lb_remove_app : forall p L1 L2, lb_remove p (L1 ++ L2) = lb_remove p L1 ++ lb_remove p L2.
Proof. intros p L1 L2. unfold lb_remove. apply stdpp.list_basics.list.filter_app. Qed.
Lemma hb_ids_app : forall L1 L2, hb_ids (L1 ++ L2) = hb_ids L1 ++ hb_ids L2.
Proof. intros L1 L2. unfold hb_ids. apply flat_map_app. Qed.

Section Blk.
  Variable AI : AMallocIface.
  (* [comment removed for export] *)
  Lemma removed_not_client : forall L RNG st LB m p A n LB' SP a, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    (forall b, In b LB' -> In b LB /\ b <> HB p A n) -> ATOP <= SP ->
    aclient_addr (aci AI) LB' SP a -> ~ (A <= a < A + n).
  Proof.
    intros L RNG st LB m p A n LB' SP a AH HIN HL HS Hc Ha.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & (B1 & B2 & B3 & B4) & _).
    pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). atop_facts.
    destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    - destruct (HL b Hb) as [Hb' Hne].
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HIN Hb' (not_eq_sym Hne)) as D. cbn [ab_addr ab_size] in D. lia.
    - assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]];
          [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        destruct (HL _ Hb') as [Hb'' _]. pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb'') as BB. cbn [ab_addr ab_size] in BB.
        unfold AIMG_HI in BB. lia. }
      pose proof (shad_band1 a' ltac:(lia) ltac:(unfold KEND; lia)) as SB.
      exact (ablk_clear_band _ _ _ B1 SB Ha).
  Qed.
End Blk.

(* [comment removed for export] *)
Lemma shadow_cell_of_run : forall m X k j, X mod 8 = 0 -> 0 <= X -> 0 <= j < k ->
  rw_cells asegs m (Z.shiftr X 3 + 2147450880) [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))] ->
  rw_cells asegs m (Z.shiftr (X + 8 * j) 3 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros m X k j HX H0 Hj H.
  replace (Z.shiftr (X + 8 * j) 3) with (Z.shiftr X 3 + j)
    by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  replace (Z.to_nat k) with (Z.to_nat j + (1 + Z.to_nat (k - j - 1)))%nat in H by lia.
  apply rw_cells_run_split in H as [_ H]. apply rw_cells_run_split in H as [H _].
  rewrite Z2Nat.id in H by lia.
  eapply InitMem.rw_cells_recast; [replace (Z.shiftr X 3 + j + 2147450880) with (Z.shiftr X 3 + 2147450880 + j) by lia; exact H
                                 | cbn; repeat split| vm_compute; reflexivity| reflexivity].
Qed.

End CANSEC1.

(* [comment removed for export] *)
Definition parkedA (P : Prop) : Prop := P.
Ltac park_memA m := repeat match goal with
  | H : rw_cells asegs m _ _ |- _ => lazymatch type of H with ?T => change (parkedA T) in H end
  | H : bytes_at asegs m _ _ |- _ => lazymatch type of H with ?T => change (parkedA T) in H end end.
Ltac parkA H := lazymatch type of H with ?T => change (parkedA T) in H end.
Ltac unparkA := repeat match goal with H : parkedA _ |- _ => unfold parkedA in H end.
(* [comment removed for export] *)
Definition skippedB (P : Prop) : Prop := P.
Ltac trmB MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells asegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells asegs mn A cs)
                by (eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  | H : bytes_at asegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at asegs mn A bs) by (eapply bytes_at_transport; [exact H| exact MU| cbn [disjoint_from]; lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  | H : stk asegs mo ?lo ?hi |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : stk asegs mn lo hi) by (eapply stk_transport_disjoint; [exact H| exact MU| exact WM| cbn [disjoint_from]; lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  | H : wr_at asegs mo ?A ?n |- _ =>
      let H' := fresh "T" in assert (H' : wr_at asegs mn A n) by (eapply wr_at_transport; [exact H| exact WM]); clear H; rename H' into H
  end end;
  repeat match goal with H : skippedB _ |- _ => unfold skippedB in H end.
