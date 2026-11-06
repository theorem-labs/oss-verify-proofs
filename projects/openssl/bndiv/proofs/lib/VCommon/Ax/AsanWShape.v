(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec ShapeAlg ShapeAlgCfg NodesCfg ExitSim.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliVerdict CliSpecG.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KD (msg : list byte) (fs : Fs.Fs) (o : list byte) : TSet :=
  t_emit (W 2 (skipn (length o) msg)) (t_exit (Z_to_bv 64 2) fs).

Lemma KD_nil : forall msg fs, KD msg fs [] = t_die msg fs.
Proof. reflexivity. Qed.

Lemma is_prefix_app_same {A} : forall (l a b : list A), is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof. induction l as [|x l IH]; intros a b H; [exact H|]. cbn. split; [reflexivity | apply IH; exact H]. Qed.

Lemma t_emit_app : forall e1 e2 T, t_eq (t_emit (e1 ++ e2) T) (t_emit e1 (t_emit e2 T)).
Proof.
  intros e1 e2 T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + destruct (is_prefix_app_split e1 e2 tr Hp) as [H1 | (tr2 & -> & H2)].
      * left. exact H1.
      * right. exists tr2. split; [reflexivity|]. left. exact H2.
    + right. exists (e2 ++ tr'). split; [rewrite app_assoc; reflexivity|]. right. exists tr'. split; [reflexivity | exact HT].
  - intros [Hp | (tr' & -> & [Hp2 | (tr2 & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_same. exact Hp2.
    + right. exists tr2. split; [rewrite app_assoc; reflexivity | exact HT].
Qed.

Lemma W_app : forall ch a b, W ch (a ++ b) = W ch a ++ W ch b.
Proof. intros. unfold W. apply map_app. Qed.

Lemma skipn_prefix : forall (msg o bs : list byte), firstn (length (o ++ bs)) msg = o ++ bs ->
  skipn (length o) msg = bs ++ skipn (length (o ++ bs)) msg.
Proof.
  intros msg o bs H. rewrite <- (firstn_skipn (length (o ++ bs)) msg) at 1. rewrite H.
  rewrite <- app_assoc. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma KD_emit : forall msg fs o bs, firstn (length (o ++ bs)) msg = o ++ bs ->
  t_eq (KD msg fs o) (t_emit (W 2 bs) (KD msg fs (o ++ bs))).
Proof.
  intros msg fs o bs H. unfold KD. rewrite (skipn_prefix msg o bs H), W_app. apply t_emit_app.
Qed.

Lemma KD_end : forall msg fs, t_eq (KD msg fs msg) (t_exit (Z_to_bv 64 2) fs).
Proof.
  intros msg fs. unfold KD. rewrite skipn_all. apply t_emit_nil_eq. apply t_emit_has_nil.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma path_eqb_false : forall p q, p <> q -> path_eqb p q = false.
Proof. intros p q H. destruct (path_eqb p q) eqn:E; [|reflexivity]. apply path_eqb_eq in E. contradiction. Qed.

Lemma specG_usage : forall argv fs, length argv <> 2%nat ->
  specG argv fs = t_die (msg_usage (hd [] argv)) fs.
Proof. intros argv fs H. destruct argv as [|a [|p [|x r]]]; try reflexivity. cbn in H. lia. Qed.

Lemma specG_toolong : forall a p fs, (4096 <= length p)%nat ->
  specG [a; p] fs = t_die (msg_cannot_open p) fs.
Proof. intros a p fs H. cbn [specG]. rewrite (proj2 (Nat.leb_le _ _) H). reflexivity. Qed.

Lemma specG_empty : forall a fs, specG [a; []] fs = t_die (msg_cannot_open []) fs.
Proof. reflexivity. Qed.

Lemma specG_dot : forall a fs,
  specG [a; dot_path] fs = t_alt2 (t_die (msg_cannot_open dot_path) fs) (t_die (msg_read_error dot_path) fs).
Proof. reflexivity. Qed.

Lemma specG_absent : forall a p fs, (length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup fs p = None ->
  specG [a; p] fs = t_die (msg_cannot_open p) fs.
Proof.
  intros a p fs H1 H2 H3 H4. cbn [specG]. rewrite (proj2 (Nat.leb_gt _ _) H1).
  rewrite (path_eqb_false p [] H2), (path_eqb_false p dot_path H3), H4. reflexivity.
Qed.

Lemma specG_file : forall a p fs data, (length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup fs p = Some data ->
  specG [a; p] fs = t_alt2 (t_die (msg_cannot_open p) fs) (t_bodyG data fs).
Proof.
  intros a p fs data H1 H2 H3 H4. cbn [specG]. rewrite (proj2 (Nat.leb_gt _ _) H1).
  rewrite (path_eqb_false p [] H2), (path_eqb_false p dot_path H3), H4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_alt_two : forall (I : Type) (T : I -> TSet) (T1 T2 : TSet) (i1 i2 : I),
  (forall i, t_eq (T i) T1 \/ t_eq (T i) T2) -> t_eq (T i1) T1 -> t_eq (T i2) T2 ->
  T1 [] -> T2 [] ->
  t_eq (t_alt (fun i => t_emit [] (T i))) (t_alt2 T1 T2).
Proof.
  intros I T T1 T2 i1 i2 Hall H1 H2 N1 N2 tr. unfold t_alt, t_alt2. split.
  - intros [i Hi]. destruct (Hall i) as [E|E].
    + left. apply E. apply (t_emit_nil_eq (T i)); [apply E; exact N1 | exact Hi].
    + right. apply E. apply (t_emit_nil_eq (T i)); [apply E; exact N2 | exact Hi].
  - intros [HT|HT].
    + exists i1. apply (t_emit_nil_eq (T i1)); [apply H1; exact N1 | apply H1; exact HT].
    + exists i2. apply (t_emit_nil_eq (T i2)); [apply H2; exact N2 | apply H2; exact HT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_and_255_z : forall c : Z, (0 <= c < 256)%Z -> bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = Z_to_bv 64 c.
Proof.
  intros c Hc. apply bv_eq. rewrite bv_and_unsigned, !bvu_z by lia.
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section Exit.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Theorem rzc_exit_raw : forall ms model w (code : word),
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (rg ms 17 = Z_to_bv 64 94 \/ rg ms 17 = Z_to_bv 64 93) ->
  rg ms 10 = code ->
  realizes_cfg segs cfg (mkCfg ms model) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model w code Hsvc HF HE Hh H17 H10.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Ecall; [exact HF | exact HE] | apply acc_ok_nil |].
  assert (G0 : ms_gpr (latch ms) 0 = code) by (rewrite <- H10; reflexivity).
  rewrite <- G0. apply (rzc_exit segs cfg (latch ms) model (rg ms 17)); [exact Hh | reflexivity |].
  unfold is_exit_no. destruct H17 as [->| ->]; [right | left]; reflexivity.
Qed.

Corollary rzc_exit_raw_lit : forall ms model w (c : Z),
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (rg ms 17 = Z_to_bv 64 94 \/ rg ms 17 = Z_to_bv 64 93) ->
  rg ms 10 = Z_to_bv 64 c -> (0 <= c < 256)%Z ->
  realizes_cfg segs cfg (mkCfg ms model) (t_exit (Z_to_bv 64 c) (m_fs model)).
Proof.
  intros ms model w c Hsvc HF HE Hh H17 H10 Hc.
  rewrite <- (bv_and_255_z c Hc). eapply rzc_exit_raw; eassumption.
Qed.

End Exit.
