(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState Mem Cells Frame Arr Step Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.MState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Mem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Cells OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Step OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut BzWalkArith3 GlueCarve DecTac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLia.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac is_pos_lit p := lazymatch p with xH => idtac | xO ?q => is_pos_lit q | xI ?q => is_pos_lit q end.
Ltac is_z_lit c := lazymatch c with Z0 => idtac | Zpos ?p => is_pos_lit p | Zneg ?p => is_pos_lit p end.
Ltac zlit_in H :=
  repeat match type of H with context [Z.of_nat ?n] =>
    let c := eval vm_compute in (Z.of_nat n) in is_z_lit c; progress (change (Z.of_nat n) with c in H) end;
  repeat match type of H with context [Z.add (Zpos ?a) (Zpos ?b)] =>
    is_pos_lit a; is_pos_lit b; let c := eval vm_compute in (Z.add (Zpos a) (Zpos b)) in change (Z.add (Zpos a) (Zpos b)) with c in H end.
Ltac zlit :=
  repeat match goal with |- context [Z.of_nat ?n] =>
    let c := eval vm_compute in (Z.of_nat n) in is_z_lit c; progress (change (Z.of_nat n) with c) end;
  repeat match goal with |- context [Z.add (Zpos ?a) (Zpos ?b)] =>
    is_pos_lit a; is_pos_lit b; let c := eval vm_compute in (Z.add (Zpos a) (Zpos b)) in change (Z.add (Zpos a) (Zpos b)) with c end.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition jw8 (J : list byte) (off : Z) : word := le_bytes_to_word (jseg J off 8).
Definition jb1 (J : list byte) (off : Z) : byte := nth (Z.to_nat off) J (Z_to_bv 8 0).
End ACeilS1.

#[local] Transparent jw4.
Section ACeilS2. Context {ACEIL__ : ACeil}.


Definition jcell (J : list byte) (off : Z) (s : nat) : cell :=
  if Nat.eqb s 1 then C1 (jb1 J off) else if Nat.eqb s 4 then C4 (jw4 J off) else if Nat.eqb s 8 then C8 (jw8 J off)
  else CB s (jseg J off (Z.of_nat s)).
Fixpoint jcells (J : list byte) (off : Z) (shape : list nat) : list cell :=
  match shape with
  | [] => []
  | s :: sh => jcell J off s :: jcells J (off + Z.of_nat s) sh
  end.

Lemma jseg_app : forall J off a b, 0 <= off -> 0 <= a -> 0 <= b -> jseg J off (a + b) = jseg J off a ++ jseg J (off + a) b.
Proof.
  intros J off a b Ho Ha Hb. rewrite !jseg_eq. rewrite Z2Nat.inj_add by lia. rewrite <- take_take_drop. f_equal.
  rewrite drop_drop. f_equal. f_equal. lia.
Qed.
Lemma jseg_all : forall J n, Z.of_nat (length J) = n -> jseg J 0 n = J.
Proof. intros J n H. rewrite jseg_eq. cbn [Z.to_nat drop]. apply take_ge. lia. Qed.
Lemma jseg_cat : forall J off a off2 b c, 0 <= off -> 0 <= a -> 0 <= b -> off2 = off + a -> c = a + b ->
  jseg J off a ++ jseg J off2 b = jseg J off c.
Proof. intros J off a off2 b c Ho Ha Hb -> ->. symmetry. apply jseg_app; lia. Qed.
Lemma take1_drop : forall (l : list byte) k d, (k < length l)%nat -> take 1 (drop k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d H; [cbn in H; lia|].
  destruct k as [|k]; [reflexivity|]. cbn. apply IH. cbn in H. lia.
Qed.
Lemma jseg_1 : forall J off, 0 <= off -> off + 1 <= Z.of_nat (length J) -> jseg J off 1 = [jb1 J off].
Proof.
  intros J off Ho H. rewrite jseg_eq. unfold jb1. change (Z.to_nat 1) with 1%nat. apply take1_drop. lia.
Qed.

Lemma jcell_size : forall J off s, csize (jcell J off s) = s.
Proof.
  intros J off s. unfold jcell.
  destruct (Nat.eqb_spec s 1) as [->|N1]; [reflexivity|]. destruct (Nat.eqb_spec s 4) as [->|N4]; [reflexivity|].
  destruct (Nat.eqb_spec s 8) as [->|N8]; reflexivity.
Qed.
Lemma jcell_wf : forall J off s, 0 <= off -> off + Z.of_nat s <= Z.of_nat (length J) -> cell_wf (jcell J off s).
Proof.
  intros J off s Ho H. unfold jcell.
  destruct (Nat.eqb_spec s 1) as [->|N1]; [exact I|]. destruct (Nat.eqb_spec s 4) as [->|N4]; [exact I|].
  destruct (Nat.eqb_spec s 8) as [->|N8]; [exact I|]. cbn. rewrite jseg_length_nat by lia. lia.
Qed.
Lemma jcell_bytes : forall J off s, 0 <= off -> off + Z.of_nat s <= Z.of_nat (length J) -> cbytes (jcell J off s) = jseg J off (Z.of_nat s).
Proof.
  intros J off s Ho H. unfold jcell.
  destruct (Nat.eqb_spec s 1) as [->|N1].
  { cbn [cbytes]. symmetry. apply jseg_1; lia. }
  destruct (Nat.eqb_spec s 4) as [->|N4].
  { cbn [cbytes]. unfold jw4. apply le4_of_bytes. rewrite jseg_length_nat by lia. reflexivity. }
  destruct (Nat.eqb_spec s 8) as [->|N8].
  { cbn [cbytes]. unfold jw8. apply le8_of_bytes. rewrite jseg_length_nat by lia. reflexivity. }
  reflexivity.
Qed.

Lemma jcells_size : forall J shape off, cells_size (jcells J off shape) = sum_nat shape.
Proof. induction shape as [|s sh IH]; intros off; cbn [jcells cells_size sum_nat]; [reflexivity|]. rewrite jcell_size, IH. reflexivity. Qed.
Lemma jcells_wf : forall J shape off, 0 <= off -> off + Z.of_nat (sum_nat shape) <= Z.of_nat (length J) -> cells_wf (jcells J off shape).
Proof.
  induction shape as [|s sh IH]; intros off Ho H; cbn [jcells cells_wf sum_nat] in *; [exact I|].
  split; [apply jcell_wf; lia| apply IH; lia].
Qed.
Lemma jcells_bytes : forall J shape off, 0 <= off -> off + Z.of_nat (sum_nat shape) <= Z.of_nat (length J) ->
  cells_bytes (jcells J off shape) = jseg J off (Z.of_nat (sum_nat shape)).
Proof.
  induction shape as [|s sh IH]; intros off Ho H; cbn [jcells cells_bytes sum_nat] in *.
  - rewrite jseg_eq. reflexivity.
  - rewrite jcell_bytes by lia. rewrite IH by lia. rewrite Nat2Z.inj_add. rewrite jseg_app by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ESHAPE1 : list nat := [8; 8; 4; 4; 8; 8; 8; 4; 4; 8; 8; 8; 8; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4]%nat.
Definition ESHAPE2 : list nat := [4; 4; 8; 4; 4; 4; 4]%nat.
Definition EJ1 (J : list byte) : list cell := jcells J 0 ESHAPE1.
Definition EJ2 (J : list byte) : list cell := jcells J 640 ESHAPE2.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SSHAPE : list nat := [8; 4; 4; 4; 4; 8; 4; 4; 4; 4; 8; 8; 8; 8]%nat.
(* [comment removed for export] *)

Section WithSegs.
  Variable segs : list Segment.

  Lemma carve_cb : forall m A n bs cs,
    rw_cells segs m A [CB n bs] -> cells_wf cs -> cells_bytes cs = bs -> cells_size cs = n -> rw_cells segs m A cs.
  Proof.
    intros m A n bs cs H W B S. eapply (rw_cells_recell segs); [exact H | exact W | |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact S.
  Qed.

  Lemma rw_cells_cons_iff : forall m A c cs,
    rw_cells segs m A (c :: cs) <-> rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
  Proof.
    intros m A c cs. change (c :: cs) with ([c] ++ cs). rewrite (DecTac2.rw_cells_app_iff segs m A [c] cs).
    cbn [cells_size]. rewrite Nat.add_0_r. reflexivity.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EL3 (J : list byte) : list cell :=
    EJ1 J ++ [CB 256 (jseg J 128 256); CB 256 (jseg J 384 256)] ++ EJ2 J ++ [CB (Z.to_nat 55096) (jseg J 672 55096)].
  Lemma estate_carve3 : forall m E J,
    rw_cells segs m E [CB (Z.to_nat ESTATE_SIZE) J] -> Z.of_nat (length J) = ESTATE_SIZE ->
    rw_cells segs m E (EJ1 J) /\
    rw_cells segs m (E + 128) [CB 256 (jseg J 128 256)] /\
    rw_cells segs m (E + 384) [CB 256 (jseg J 384 256)] /\
    rw_cells segs m (E + 640) (EJ2 J) /\
    rw_cells segs m (E + 672) [CB (Z.to_nat 55096) (jseg J 672 55096)].
  Proof.
    intros m E J H LJ. unfold ESTATE_SIZE in *.
    assert (X : rw_cells segs m E (EL3 J)).
    { eapply carve_cb; [exact H | | |].
      - unfold EL3, EJ1, EJ2. rewrite !cells_wf_app.
        repeat match goal with |- _ /\ _ => split end;
        first [ apply jcells_wf; cbn [sum_nat ESHAPE1 ESHAPE2 SSHAPE Nat.add]; zlit; lia
              | cbn [cells_wf cell_wf]; rewrite ?jseg_length_nat by lia; repeat split; reflexivity ].
      - unfold EL3, EJ1, EJ2. rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
        rewrite !jcells_bytes by (cbn [sum_nat ESHAPE1 ESHAPE2 Nat.add length]; zlit; lia). cbn [sum_nat ESHAPE1 ESHAPE2 Nat.add]. zlit.
        rewrite <- ?app_assoc. etransitivity; [| exact (jseg_all J 55768 LJ)].
        rewrite (jseg_cat J 640 32 672 55096 55128) by lia. rewrite (jseg_cat J 384 256 640 55128 55384) by lia.
        rewrite (jseg_cat J 128 256 384 55384 55640) by lia. rewrite (jseg_cat J 0 128 128 55640 55768) by lia. reflexivity.
      - unfold EL3, EJ1, EJ2. rewrite !cells_size_app, !jcells_size. reflexivity. }
    unfold EL3 in X.
    apply (proj1 (DecTac2.rw_cells_app_iff segs m E _ _)) in X. destruct X as [X1 X]. unfold EJ1 in X. rewrite jcells_size in X. cbn [sum_nat Nat.add ESHAPE1] in X. zlit_in X. fold ESHAPE1 in X1 |- *.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X2 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X3 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
    apply (proj1 (DecTac2.rw_cells_app_iff segs m _ _ _)) in X. destruct X as [X4 X5]. unfold EJ2 in X5. rewrite jcells_size in X5. cbn [sum_nat Nat.add ESHAPE2] in X5. zlit_in X5.
    rewrite <- ?Z.add_assoc in X5. zlit_in X5.
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact X5].
  Qed.

  Definition ERL (J : list byte) : list cell :=
    [CB 1032 (jseg J 672 1032); CB 18002 (jseg J 1704 18002); CB 18002 (jseg J 19706 18002); CB 1548 (jseg J 37708 1548);
     CB 6192 (jseg J 39256 6192); CB 6192 (jseg J 45448 6192); CB 4128 (jseg J 51640 4128)].
  Lemma erest_carve : forall m E J,
    rw_cells segs m (E + 672) [CB (Z.to_nat 55096) (jseg J 672 55096)] -> Z.of_nat (length J) = ESTATE_SIZE ->
    u32arr segs m (E + 672) (ovw znew (jseg J 672 1032) 258) /\
    u8arr segs m (E + 1704) (ovb znew (jseg J 1704 18002) 18002) /\
    u8arr segs m (E + 19706) (ovb znew (jseg J 19706 18002) 18002) /\
    u8arr segs m (E + 37708) (ovb znew (jseg J 37708 1548) 1548) /\
    u32arr segs m (E + 39256) (ovw znew (jseg J 39256 6192) 1548) /\
    u32arr segs m (E + 45448) (ovw znew (jseg J 45448 6192) 1548) /\
    u32arr segs m (E + 51640) (ovw znew (jseg J 51640 4128) 1032).
  Proof.
    intros m E J H LJ. unfold ESTATE_SIZE in *.
    assert (X : rw_cells segs m (E + 672) (ERL J)).
    { eapply carve_cb; [exact H | | |].
      - unfold ERL. cbn [cells_wf cell_wf]. rewrite ?jseg_length_nat by lia. repeat split; reflexivity.
      - unfold ERL. cbn [cells_bytes cbytes]. rewrite !app_nil_r. rewrite <- ?app_assoc.
        rewrite (jseg_cat J 45448 6192 51640 4128 10320) by lia. rewrite (jseg_cat J 39256 6192 45448 10320 16512) by lia.
        rewrite (jseg_cat J 37708 1548 39256 16512 18060) by lia. rewrite (jseg_cat J 19706 18002 37708 18060 36062) by lia.
        rewrite (jseg_cat J 1704 18002 19706 36062 54064) by lia. rewrite (jseg_cat J 672 1032 1704 54064 55096) by lia. reflexivity.
      - unfold ERL. reflexivity. }
    unfold ERL in X.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X5 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X6 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X7 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X8 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X9 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
    apply (proj1 (rw_cells_cons_iff _ _ _ _)) in X. destruct X as [X10 X11]. cbn [csize] in X11. rewrite <- ?Z.add_assoc in X11. zlit_in X11.
    split; [apply (ovw_init segs m _ 258); [exact X5| lia]|].
    split; [apply (ovb_init segs m _ 18002); [exact X6| lia]|].
    split; [apply (ovb_init segs m _ 18002); [exact X7| lia]|].
    split; [apply (ovb_init segs m _ 1548); [exact X8| lia]|].
    split; [apply (ovw_init segs m _ 1548); [exact X9| lia]|].
    split; [apply (ovw_init segs m _ 1548); [exact X10| lia]|].
    apply (ovw_init segs m _ 1032); [exact X11| lia].
  Qed.
End WithSegs.
End ACeilS2.


#[global] Opaque jw4 jw8 jb1.
