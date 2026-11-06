(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sop := OP_AUIPC | OP_IMM | OP_LOAD | OP_STORE | OP_FLOAD | OP_JAL.

(* [comment removed for export] *)
Definition app7 (o : sop) (u : positive) : positive :=
  match o with
  | OP_AUIPC => (u~0~0~1~0~1~1~1)%positive   (* [comment removed for export] *)
  | OP_IMM   => (u~0~0~1~0~0~1~1)%positive   (* [comment removed for export] *)
  | OP_LOAD  => (u~0~0~0~0~0~1~1)%positive   (* [comment removed for export] *)
  | OP_STORE => (u~0~1~0~0~0~1~1)%positive   (* [comment removed for export] *)
  | OP_FLOAD => (u~0~0~0~0~1~1~1)%positive   (* [comment removed for export] *)
  | OP_JAL   => (u~1~1~0~1~1~1~1)%positive   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition up25 (z : Z) : positive := Z.to_pos ((z / 128) mod 33554432).

Lemma up25_lt : forall z, Zpos (up25 z) < 33554432.
Proof.
  intros z. unfold up25. pose proof (Z.mod_pos_bound (z / 128) 33554432 ltac:(lia)) as H.
  destruct ((z / 128) mod 33554432) eqn:E; cbn [Z.to_pos]; lia.
Qed.

Lemma app7_wf : forall o z, BvWf 32 (Zpos (app7 o (up25 z))).
Proof.
  intros o z. apply bv_wf_in_range. change (bv_modulus 32) with 4294967296.
  pose proof (up25_lt z) as H. destruct o; cbn [app7]; lia.
Qed.

Section Defs.
Context {RL : Reloc}.

(* [comment removed for export] *)
Definition rl_raw (c : Z) : bv 32 := Z_to_bv 32 (slookup rl_stab c).
Definition rl_w (o : sop) (c : Z) : bv 32 := @BV 32 (Zpos (app7 o (up25 (slookup rl_stab c)))) (app7_wf o _).

(* [comment removed for export] *)
Definition rl_ins (c : Z) : instr :=
  match decode_any (rl_raw c) with Some (i, _) => i | None => Ebreak end.
Definition rl_imm20 (c : Z) : bv 20 :=
  match rl_ins c with Auipc _ imm | Lui _ imm => imm | _ => Z_to_bv 20 0 end.
Definition rl_imm12 (c : Z) : bv 12 :=
  match rl_ins c with
  | OpImm _ _ _ imm | Load _ _ _ _ imm | Store _ _ _ imm | FLoad _ _ _ imm | FStore _ _ _ imm
  | Jalr _ _ imm | OpImm32 _ _ imm => imm
  | _ => Z_to_bv 12 0
  end.
Definition rl_imm21 (c : Z) : bv 21 :=
  match rl_ins c with Jal _ imm => imm | _ => Z_to_bv 21 0 end.

(* [comment removed for export] *)
Definition rl_hi (b : positive) (c : Z) : word :=
  v_auipc (rl (rl_delta b) c) (Z.shiftl (bv_signed (rl_imm20 c)) 12).

End Defs.
Arguments rl_raw : simpl never.
Arguments rl_w : simpl never.
Arguments rl_ins : simpl never.
Arguments rl_imm20 : simpl never.
Arguments rl_imm12 : simpl never.
Arguments rl_imm21 : simpl never.
Arguments rl_hi : simpl never.

(* [comment removed for export] *)
Lemma rl_w_not_ecall : forall {RL : Reloc} o c, is_ecall (rl_w o c) = false.
Proof. intros RL o c. destruct o; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sshape :=
| SH20 (f : bv 20 -> instr)        (* [comment removed for export] *)
| SH12 (f : bv 12 -> instr)        (* [comment removed for export] *)
| SH21 (f : bv 21 -> instr).       (* [comment removed for export] *)

Inductive skind :=
| SK_auipc
| SK_lo12 (ca : Z) (X : positive) (t : Z)   (* [comment removed for export] *)
| SK_jal (X : positive) (t : Z).            (* [comment removed for export] *)

Record csite := mkSite { cs_addr : Z; cs_blk : positive; cs_op : sop; cs_shape : sshape; cs_kind : skind }.

Section Check.
Context {RL : Reloc}.

Definition shape_ins (c : Z) (sh : sshape) : instr :=
  match sh with
  | SH20 f => f (rl_imm20 c)
  | SH12 f => f (rl_imm12 c)
  | SH21 f => f (rl_imm21 c)
  end.

Definition kind_ok (b : positive) (c : Z) (k : skind) : bool :=
  match k with
  | SK_auipc => true
  | SK_lo12 ca X t => bv_eqb (v_addi (rl_hi b ca) (bv_signed (rl_imm12 c))) (rl (rl_delta X) t)
  | SK_jal X t => bv_eqb (btgt (rl (rl_delta b) c) (bv_signed (rl_imm21 c))) (rl (rl_delta X) t)
  end.

Definition site_ok (s : csite) : bool :=
  fetch_is rl_segs (cs_addr s + rl_delta (cs_blk s)) (bv_unsigned (rl_w (cs_op s) (cs_addr s)))
  && bv_eqb (rl_w (cs_op s) (cs_addr s)) (rl_raw (cs_addr s))
  && bool_decide (decode_any (rl_w (cs_op s) (cs_addr s)) = Some (shape_ins (cs_addr s) (cs_shape s), 4%Z))
  && kind_ok (cs_blk s) (cs_addr s) (cs_kind s).

Definition sites_check (tbl : list csite) : bool := forallb site_ok tbl.

Section Sound.
Variable tbl : list csite.
Hypothesis Hok : sites_check tbl = true.

Lemma site_nth_ok : forall i s, nth_error tbl i = Some s -> site_ok s = true.
Proof.
  intros i s Hi. unfold sites_check in Hok. rewrite forallb_forall in Hok.
  exact (Hok s (nth_error_In _ _ Hi)).
Qed.

Theorem site_F : forall i s, nth_error tbl i = Some s ->
  fetch_word rl_segs (rl (rl_delta (cs_blk s)) (cs_addr s)) = Some (rl_w (cs_op s) (cs_addr s)).
Proof.
  intros i s Hi. pose proof (site_nth_ok i s Hi) as H. unfold site_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  unfold rl. exact (fetch_is_sound _ _ _ _ H eq_refl).
Qed.

Theorem site_D : forall i s, nth_error tbl i = Some s ->
  decode_any (rl_w (cs_op s) (cs_addr s)) = Some (shape_ins (cs_addr s) (cs_shape s), 4%Z).
Proof.
  intros i s Hi. pose proof (site_nth_ok i s Hi) as H. unfold site_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  exact (bool_decide_eq_true_1 _ H).
Qed.

Lemma bv_eqb_true : forall (n : N) (x y : bv n), bv_eqb x y = true -> x = y.
Proof. intros n x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Theorem site_V : forall i s ca X t, nth_error tbl i = Some s -> cs_kind s = SK_lo12 ca X t ->
  v_addi (rl_hi (cs_blk s) ca) (bv_signed (rl_imm12 (cs_addr s))) = rl (rl_delta X) t.
Proof.
  intros i s ca X t Hi Hk. pose proof (site_nth_ok i s Hi) as H. unfold site_ok in H.
  apply andb_prop in H as [_ H]. rewrite Hk in H. cbn [kind_ok] in H. exact (bv_eqb_true _ _ _ H).
Qed.

Theorem site_J : forall i s X t, nth_error tbl i = Some s -> cs_kind s = SK_jal X t ->
  btgt (rl (rl_delta (cs_blk s)) (cs_addr s)) (bv_signed (rl_imm21 (cs_addr s))) = rl (rl_delta X) t.
Proof.
  intros i s X t Hi Hk. pose proof (site_nth_ok i s Hi) as H. unfold site_ok in H.
  apply andb_prop in H as [_ H]. rewrite Hk in H. cbn [kind_ok] in H. exact (bv_eqb_true _ _ _ H).
Qed.
End Sound.
End Check.

(* [comment removed for export] *)
Fixpoint site_find (tbl : list csite) (i0 : nat) (c : Z) : option (nat * positive * skind) :=
  match tbl with
  | [] => None
  | s :: tbl' => if Z.eqb c (cs_addr s) then Some (i0, cs_blk s, cs_kind s) else site_find tbl' (S i0) c
  end.
