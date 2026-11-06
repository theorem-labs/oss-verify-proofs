(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Exec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Malloc RawAlloc Prelim YajlBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : PState -> list block -> mem -> Model -> Prop.

(* [comment removed for export] *)
Lemma ystatics_range : forall LB SP A n,
  (A = RY_CALLBACKS /\ n = 88) \/ (A = RY_BUF_ALLOC_ERROR /\ n = 32) \/ (A = RY_NOOP_ALLOCS /\ n = 32) ->
  rclient_range LB SP A n.
Proof.
  intros LB SP A n H. right. left.
  unfold RY_CALLBACKS, RY_BUF_ALLOC_ERROR, RY_NOOP_ALLOCS, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.

Lemma RYST_after_call : forall s LB m mo LBx SPx m' s' LB' mo',
  RYST HK s LB m mo -> rheap_pres LBx SPx m m' -> HK s' LB' m' mo' -> RYST HK s' LB' m' mo'.
Proof.
  intros s LB m mo LBx SPx m' s' LB' mo' (H0 & C1 & C2 & C3) HP HK'. split; [exact HK'|].
  split; [| split]; (eapply rheap_pres_rw_cells; [exact HP| eassumption| apply ystatics_range]).
  - left. split; [reflexivity|]. reflexivity.
  - right; left. split; [reflexivity|]. reflexivity.
  - right; right. split; [reflexivity|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ystatics (m : mem) : Prop :=
  rw_cells usegs m RY_CALLBACKS (callbacks_cells ryc)
  /\ rw_cells usegs m RY_BUF_ALLOC_ERROR (buf_alloc_error_cells ryc)
  /\ rw_cells usegs m RY_NOOP_ALLOCS noop_allocs_cells.
Lemma RYST_split : forall s LB m mo, RYST HK s LB m mo <-> HK s LB m mo /\ ystatics m.
Proof. intros. unfold RYST, ystatics. tauto. Qed.
Lemma ystatics_pres : forall LBx SPx m m', ystatics m -> rheap_pres LBx SPx m m' -> ystatics m'.
Proof.
  intros LBx SPx m m' (C1 & C2 & C3) HP.
  split; [| split]; (eapply rheap_pres_rw_cells; [exact HP| eassumption| apply ystatics_range]).
  - left. auto.
  - right; left. auto.
  - right; right. auto.
Qed.

Lemma Forall_disjoint_from : forall W lo0 hi0 A n,
  Forall (fun iv : Z * Z => snd iv <= lo0 \/ hi0 <= fst iv) W -> lo0 <= A -> A + n <= hi0 -> disjoint_from W A n.
Proof.
  intros W lo0 hi0 A n FW H1 H2. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion FW as [|x l F1 F2]; subst. cbn in F1. split; [lia| apply IH; exact F2].
Qed.

(* [comment removed for export] *)
Lemma ystatics_munch : forall W m m',
  ystatics m -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv : Z * Z => snd iv <= RY_CALLBACKS \/ RY_CALLBACKS + 152 <= fst iv) W -> ystatics m'.
Proof.
  intros W m m' (C1 & C2 & C3) MU WM FW.
  pose proof (fun A n => Forall_disjoint_from W _ _ A n FW) as D.
  unfold RY_CALLBACKS, RY_BUF_ALLOC_ERROR, RY_NOOP_ALLOCS in *.
  split; [| split].
  - eapply rw_cells_transport; [exact C1| exact MU| exact WM| apply D; cbn; unfold RY_CALLBACKS, RY_BUF_ALLOC_ERROR, RY_NOOP_ALLOCS; lia].
  - eapply rw_cells_transport; [exact C2| exact MU| exact WM| apply D; cbn; unfold RY_CALLBACKS, RY_BUF_ALLOC_ERROR, RY_NOOP_ALLOCS; lia].
  - eapply rw_cells_transport; [exact C3| exact MU| exact WM| apply D; cbn; unfold RY_CALLBACKS, RY_BUF_ALLOC_ERROR, RY_NOOP_ALLOCS; lia].
Qed.

(* [comment removed for export] *)
Lemma yown_writes : HK_frame_stmt HK -> forall s LB m m' mo W B,
  HK s LB m mo -> rauxv_ok m B -> munch W m m' -> wmono usegs m m' ->
  Forall (rclient_write_ok LB) W ->
  Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) W ->
  HK s LB m' mo /\ rauxv_ok m' B.
Proof.
  intros HKF s LB m m' mo W B H AX MU WM F1 F2. split.
  - eapply HKF; eauto.
  - eapply rauxv_ok_frame; eauto.
Qed.

(* [comment removed for export] *)
Lemma ypres_frame : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells usegs m A cs -> SP <= A -> rw_cells usegs m' A cs.
Proof. intros. eapply rheap_pres_rw_cells; eauto. left. assumption. Qed.

Lemma ypres_block : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells usegs m A cs ->
  (exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b) ->
  rw_cells usegs m' A cs.
Proof. intros. eapply rheap_pres_rw_cells; eauto. right; right. assumption. Qed.

Lemma ypres_block_bytes : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at usegs m A bs ->
  (exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (length bs) <= blk_addr b + blk_size b) ->
  bytes_at usegs m' A bs.
Proof. intros. eapply rheap_pres_bytes_at; eauto. right; right. assumption. Qed.

Lemma ypres_text : forall LB SP m m' T txt,
  rheap_pres LB SP m m' -> text_at usegs m T txt ->
  ((exists b, In b LB /\ blk_addr b <= T /\ T + zlength txt <= blk_addr b + blk_size b) \/ zlength txt = 0) ->
  text_at usegs m' T txt.
Proof.
  intros LB SP m m' T txt HP (TB & TF & T0 & TL) HR. split; [| auto].
  destruct HR as [HR| Z0].
  - eapply rheap_pres_bytes_at; eauto. right; right. rewrite zbytes_length. unfold zlength in HR. exact HR.
  - destruct txt; [| unfold zlength in Z0; cbn in Z0; lia]. destruct TB as (B0 & B1 & _).
    split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma rsegs_ro_addr : forall a, 0x10000 <= a -> a + 1 <= 0x24000 -> ro_addr usegs (wa a) = true.
Proof.
  intros a H1 H2. unfold ro_addr. rewrite wa_unsigned by lia.
  unfold usegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments.
  cbn [find_segment Ubsan.Ubsan_segment_000 Ubsan.Ubsan_segment_001 seg_base seg_size].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 12288%N) with 12288.
  change (Z.of_N 77824%N) with 77824. change (Z.of_N 69632%N) with 69632.
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + 1) (65536 + 12288)); cbn [andb]; try reflexivity; try lia.
  all: destruct (Z.leb_spec 77824 a); destruct (Z.leb_spec (a + 1) (77824 + 69632)); cbn [andb]; try reflexivity; try lia.
Qed.

Lemma rodata_bytes_persist : forall m m' A bs,
  bytes_at usegs m A bs -> mem_inv usegs m -> mem_inv usegs m' ->
  0x10000 <= A -> A + Z.of_nat (length bs) <= 0x24000 ->
  bytes_at usegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & HB) MI MI' HA HL. split; [exact H0|]. split; [exact H1|].
  intros i Hi. specialize (HB i Hi).
  pose proof (rsegs_ro_addr (A + Z.of_nat i) ltac:(lia) ltac:(lia)) as RO.
  unfold mrd in *.
  destruct (m (wa (A + Z.of_nat i))) eqn:E. { exfalso. pose proof (MI _ _ E). congruence. }
  destruct (m' (wa (A + Z.of_nat i))) eqn:E'. { exfalso. pose proof (MI' _ _ E'). congruence. }
  exact HB.
Qed.

(* [comment removed for export] *)
Lemma bptr_eqb_refl : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
  rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
  - rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
  - exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + apply H. left. apply bptr_eqb_eq in E. exact E.
    + apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
  intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.

Lemma lb_remove_hd : forall p b LB, blk_id b = p -> List.NoDup (map blk_id (b :: LB)) -> lb_remove p (b :: LB) = LB.
Proof. intros p b LB <- ND. apply lb_remove_head. exact ND. Qed.

Lemma lb_remove_second : forall p b0 b LB,
  blk_id b = p -> List.NoDup (map blk_id (b0 :: b :: LB)) -> lb_remove p (b0 :: b :: LB) = b0 :: LB.
Proof.
  intros p b0 b LB <- ND. unfold lb_remove. rewrite filter_cons.
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct (decide _) as [Y|N].
  - f_equal. apply (lb_remove_head b LB). exact ND.
  - exfalso. apply N. destruct (bptr_eqb (blk_id b0) (blk_id b)) eqn:E; [| exact I].
    apply bptr_eqb_eq in E. apply NI. left. symmetry. exact E.
Qed.

(* [comment removed for export] *)
Lemma HK_nodup : HK_blocks_stmt HK -> forall s LB m mo, HK s LB m mo -> List.NoDup (map blk_id LB).
Proof. intros HB s LB m mo H. exact (proj2 (proj2 (HB _ _ _ _ H))). Qed.

End S.

(* [comment removed for export] *)
End RC__1.
Ltac rz_seg HKS HKx :=
  let Hh := fresh "Hh" in let Hl := fresh "Hl" in
  destruct (HKS _ _ _ _ HKx) as [Hh Hl];
  lazymatch goal with
  | |- realizes_cfg ?cf ?segs (mkCfg _ ?mo) ?K =>
      eapply (rz_evt (fun ms' => realizes_cfg cf segs (mkCfg ms' mo) K));
      [ | exact Hh | exact Hl | clear Hh Hl; let X := fresh in intros ? X; exact X ]
  end.
