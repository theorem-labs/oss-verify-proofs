(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec StepTac StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition diag_cells : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (0x27efc8, 8%nat, 0xdd824);   (* [comment removed for export] *)
    (0x2dab08, 8%nat, 0x2dc5c0);   (* [comment removed for export] *)
    (0x2dab50, 8%nat, 0x26ef68);   (* [comment removed for export] *)
    (0x2dab58, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dab60, 8%nat, 0x2dab08);   (* [comment removed for export] *)
    (0x2db120, 8%nat, 0x30f4b8);   (* [comment removed for export] *)
    (0x2db150, 8%nat, 0x27efd8);   (* [comment removed for export] *)
    (0x2db158, 8%nat, 0x27efc8);   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0x2dc160, 8%nat, 0x2dc160);   (* [comment removed for export] *)
    (0x2dc5c0, 4%nat, 5);         (* [comment removed for export] *)
    (0x2dc5c8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc5d0, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc5e0, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc5e8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc5f8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc608, 8%nat, 0x272e44);   (* [comment removed for export] *)
    (0x2dc618, 8%nat, 0x30fb50);   (* [comment removed for export] *)
    (0x2dc620, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc638, 4%nat, 2);         (* [comment removed for export] *)
    (0x2dc648, 4%nat, 0);         (* [comment removed for export] *)
    (0x2dc64c, 4%nat, 0xffffffff);(* [comment removed for export] *)
    (0x2dc650, 4%nat, 0xffffffff);(* [comment removed for export] *)
    (0x2dc6a8, 8%nat, 0x2dc5c0);   (* [comment removed for export] *)
    (0x2dc7a8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc7b0, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc7c8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc7d8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc82c, 4%nat, 0xffffffff);(* [comment removed for export] *)
    (0x2dc888, 8%nat, 0x2dc7a0);   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0x2dc8f8, 1%nat, 0);         (* [comment removed for export] *)
    (0x30f4cc, 4%nat, 0);         (* [comment removed for export] *)
    (0x30f4d8, 8%nat, 0);         (* [comment removed for export] *)
    (0x30f6e8, 4%nat, 0);         (* [comment removed for export] *)
    (0x30f70b, 1%nat, 0);         (* [comment removed for export] *)
    (0x2dc798, 8%nat, 0x2dc6b0);  (* [comment removed for export] *)
    (0x30fb40, 8%nat, 0);         (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0x2dc73c, 4%nat, 0xffffffff);(* [comment removed for export] *)
    (0x2dc6d8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc6e8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc6b8, 8%nat, 0);         (* [comment removed for export] *)
    (0x2dc6c0, 8%nat, 0);         (* [comment removed for export] *)
    (0x27efd0, 8%nat, 0xea710);   (* [comment removed for export] *)
    (0x2ecb38, 1%nat, 0);         (* [comment removed for export] *)
    (0x2ecb3c, 1%nat, 0);         (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0x30f4c8, 1%nat, 0);         (* [comment removed for export] *)
    (0x30f4d0, 4%nat, 0);         (* [comment removed for export] *)
    (0x30f4e0, 8%nat, 0);         (* [comment removed for export] *)
    (0x2ec900, 1%nat, 0);         (* [comment removed for export] *)
    (0x2ec904, 1%nat, 0)          (* [comment removed for export] *)
  ]%Z.

(* [comment removed for export] *)
Definition pf1_cells : list (Z * nat * Z) :=
  [(0x2db120, 8%nat, 0x30f4b8);  (* [comment removed for export] *)
   (0x2dc7a0, 4%nat, 5);        (* [comment removed for export] *)
   (0x2dc7c0, 8%nat, 0);        (* [comment removed for export] *)
   (0x2dc7c8, 8%nat, 0);        (* [comment removed for export] *)
   (0x2dc7d8, 8%nat, 0);        (* [comment removed for export] *)
   (0x2dc7e8, 8%nat, 0x2738f4);  (* [comment removed for export] *)
   (0x2dc7f8, 8%nat, 0x30ff60);  (* [comment removed for export] *)
   (0x2dc800, 8%nat, 1024);     (* [comment removed for export] *)
   (0x2dc818, 4%nat, 1);        (* [comment removed for export] *)
   (0x2dc828, 4%nat, 0);        (* [comment removed for export] *)
   (0x2dc82c, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0x2dc830, 4%nat, 10)        (* [comment removed for export] *)]%Z.

Definition cell_kn (c : Z * nat * Z) : kentry :=
  match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end.
Definition kn_cells (cs : list (Z * nat * Z)) : list kentry := map cell_kn cs.

Definition cell_ok (mem : word -> option byte) (c : Z * nat * Z) : Prop :=
  match c with (a, w, v) =>
    rdn RSEGS mem (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end.
Definition cells_ok (mem : word -> option byte) (cs : list (Z * nat * Z)) : Prop :=
  Forall (cell_ok mem) cs.

Definition cell_wf_b (c : Z * nat * Z) : bool :=
  match c with (a, w, v) =>
    ((1 <=? Z.of_nat w) && (Z.of_nat w <=? 8) && (0 <=? a) && (a + Z.of_nat w <=? 2 ^ 64))%Z end.

Lemma cell_know : forall E mem c, cell_wf_b c = true -> cell_ok mem c -> kentry_ok RSEGS E mem (cell_kn c).
Proof.
  intros E mem [[a w] v] Hwf Hc. unfold cell_wf_b in Hwf.
  repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  apply Z.leb_le in Hwf. repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_kn. eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) a w (ELit v) (Z_to_bv 64 v));
    [reflexivity | reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia |].
  rewrite u_small by lia. rewrite Z.add_0_l. exact Hc.
Qed.

Lemma cells_know : forall E mem cs,
  forallb cell_wf_b cs = true -> cells_ok mem cs -> know_ok RSEGS E mem (kn_cells cs).
Proof.
  intros E mem cs. induction cs as [|c cs IH]; intros Hwf Hok.
  - constructor.
  - cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 H2].
    inversion Hok; subst. constructor; [apply cell_know; assumption | apply IH; assumption].
Qed.

Lemma diag_cells_wf : forallb cell_wf_b diag_cells = true.
Proof. vm_compute. reflexivity. Qed.

Corollary diag_cells_know : forall E mem, cells_ok mem diag_cells -> know_ok RSEGS E mem (kn_cells diag_cells).
Proof. intros E mem H. apply cells_know; [apply diag_cells_wf | exact H]. Qed.

(* [comment removed for export] *)
Lemma know_ok_app : forall E mem k1 k2,
  know_ok RSEGS E mem k1 -> know_ok RSEGS E mem k2 -> know_ok RSEGS E mem (k1 ++ k2).
Proof. intros E mem k1 k2 H1 H2. unfold know_ok. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Definition cells_agree (mem mem' : word -> option byte) (cs : list (Z * nat * Z)) : Prop :=
  Forall (fun c => match c with (a, w, _) =>
    forall i, (a <= i < a + Z.of_nat w)%Z -> mem' (Z_to_bv 64 i) = mem (Z_to_bv 64 i) end) cs.

Lemma cell_ok_agree : forall mem mem' a w v,
  cell_wf_b (a, w, v) = true ->
  (forall i, (a <= i < a + Z.of_nat w)%Z -> mem' (Z_to_bv 64 i) = mem (Z_to_bv 64 i)) ->
  cell_ok mem (a, w, v) -> cell_ok mem' (a, w, v).
Proof.
  intros mem mem' a w v Hwf Hag Hc. unfold cell_ok in *. unfold cell_wf_b in Hwf.
  repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  rewrite (rdn_ext RSEGS w mem' mem (Z_to_bv 64 a)); [exact Hc | rewrite u_small by lia; lia |].
  intros x Hx. rewrite u_small in Hx by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hag. lia.
Qed.

Lemma cells_ok_agree : forall mem mem' cs,
  forallb cell_wf_b cs = true -> cells_agree mem mem' cs -> cells_ok mem cs -> cells_ok mem' cs.
Proof.
  intros mem mem' cs. induction cs as [|[[a w] v] cs IH]; intros Hwf Hag Hok; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 H2].
  inversion Hag; subst. inversion Hok; subst.
  constructor; [eapply cell_ok_agree; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CANARY : Z := 0x30f4b8.
Definition canary_ok (mem : word -> option byte) (can : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)) /\ (0 <= can < 2 ^ 64)%Z.

Lemma canary_know : forall E mem k can,
  ev E k = Z_to_bv 64 can -> canary_ok mem can ->
  kentry_ok RSEGS E mem (KWord (SA (ELit 0) CANARY) 8%nat (EVar k)).
Proof.
  intros E mem k can Hk [Hc Hr]. unfold CANARY in *.
  eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) 0x30f4b8 8%nat (EVar k) (Z_to_bv 64 can));
    [reflexivity | cbn [edenot]; exact Hk | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia |].
  rewrite u_small by lia. rewrite Z.add_0_l. exact Hc.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
