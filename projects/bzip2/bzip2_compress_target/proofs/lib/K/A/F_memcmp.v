(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow IcptSpec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small I_qck.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow IcptSpec2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac br_dec := unfold bv_eqb; try unfold z64; rewrite ?unsigned_lit by (cbn [length] in *; lia);
  first [ apply (proj2 (Bool.negb_true_iff _)); apply Z.eqb_neq; cbn [length] in *; lia | apply (proj2 (Bool.negb_false_iff _)); apply Z.eqb_eq; cbn [length] in *; lia
        | apply Z.eqb_eq; cbn [length] in *; lia | apply Z.eqb_neq; cbn [length] in *; lia ].
Local Ltac brT := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; br_dec] end.
Local Ltac brF := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; br_dec] end.

Definition memcmp_entry : Z := 0xc6134.

Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom bsegs).

Lemma bytes_at_cons_inv : forall (m : mem) p (x : byte) r, bytes_at bsegs m p (x :: r) -> bytes_at bsegs m p [x] /\ bytes_at bsegs m (p + 1) r.
Proof. intros m p x r H. change (x :: r) with ([x] ++ r) in H. apply bytes_at_app in H. exact H. Qed.

(* [comment removed for export] *)
Lemma memcmp_loop : forall (b1 b2 : list byte) (p1 p2 : Z) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  b1 <> [] -> length b2 = length b1 -> Z.of_nat (length b1) < 2^62 ->
  0 <= p1 -> p1 + Z.of_nat (length b1) <= 2^63 -> 0 <= p2 -> p2 + Z.of_nat (length b1) <= 2^63 ->
  bytes_at bsegs m p1 b1 -> bytes_at bsegs m p2 b2 -> mem_inv bsegs m ->
  evt bsegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc6138) fc None m (seg_rom bsegs)).
Proof.
  induction b1 as [|x r1 IH]; intros [|y r2] p1 p2 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    NE HL HN P1 P1h P2 P2h B1 B2 MI; try congruence; cbn [length] in HL; try discriminate.
  destruct (bytes_at_cons_inv m p1 x r1 B1) as (X1 & B1'). destruct (bytes_at_cons_inv m p2 y r2 B2) as (Y1 & B2').
  pose proof (ro_C1_of_bytes m p1 x X1) as CX. pose proof (ro_C1_of_bytes m p2 y Y1) as CY.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 x) as RX. pose proof (bv_unsigned_in_range 8 y) as RY. unfold bv_modulus in RX, RY. cbn in RX, RY.
  cbn [length] in *. rewrite Nat2Z.inj_succ in *.
  lstep. lstep. cbv beta.
  assert (EUx : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia).
  assert (EUy : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia).
  cbn [memcmp_res].
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|NEQ].
  - lstep. brF.
    do 3 lstep.
    replace (Z.succ (Z.of_nat (length r1)) + -1) with (Z.of_nat (length r1)) by lia.
    destruct r1 as [|x' r1'].
    + destruct r2 as [|y' r2']; [|cbn [length] in HL; lia]. cbn [length Z.of_nat memcmp_res].
      lstep. brF. do 2 lstep.
      apply evt_done. unfold memcmp_post. do 14 eexists. reflexivity.
    + lstep. brT.
      apply (IH r2 (p1 + 1) (p2 + 1)); try assumption; try congruence; cbn [length] in *; try lia.
  - lstep. brT. do 2 lstep.
    apply evt_done. unfold memcmp_post. do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma memcmp_spec : forall (b1 b2 : list byte) (p1 p2 : Z) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  length b2 = length b1 -> Z.of_nat (length b1) < 2^62 ->
  0 <= p1 -> p1 + Z.of_nat (length b1) <= 2^63 -> 0 <= p2 -> p2 + Z.of_nat (length b1) <= 2^63 ->
  bytes_at bsegs m p1 b1 -> bytes_at bsegs m p2 b2 -> mem_inv bsegs m ->
  evt bsegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memcmp_entry) fc None m (seg_rom bsegs)).
Proof.
  intros b1 b2 p1 p2 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HL HN P1 P1h P2 P2h B1 B2 MI.
  unfold memcmp_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct b1 as [|x r1].
  - destruct b2 as [|y r2]; [|cbn [length] in HL; lia]. cbn [length Z.of_nat memcmp_res].
    lstep. brT. do 2 lstep.
    apply evt_done. unfold memcmp_post. do 14 eexists. reflexivity.
  - assert (EUn : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (x :: r1)))) = Z.of_nat (length (x :: r1))) by (apply unsigned_lit; lia).
    lstep. brF.
    apply memcmp_loop; try assumption; congruence.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small I_qck IcptSpec2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac br_dec := unfold bv_eqb; try unfold z64; rewrite ?unsigned_lit by (cbn [length] in *; lia);
  first [ apply (proj2 (Bool.negb_true_iff _)); apply Z.eqb_neq; cbn [length] in *; lia | apply (proj2 (Bool.negb_false_iff _)); apply Z.eqb_eq; cbn [length] in *; lia
        | apply Z.eqb_eq; cbn [length] in *; lia | apply Z.eqb_neq; cbn [length] in *; lia ].
Local Ltac brT := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; br_dec] end.
Local Ltac brF := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; br_dec] end.

Definition memcmp_entry : Z := 0xb8d54.

Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom asegs).

Lemma bytes_at_cons_inv : forall (m : mem) p (x : byte) r, bytes_at asegs m p (x :: r) -> bytes_at asegs m p [x] /\ bytes_at asegs m (p + 1) r.
Proof. intros m p x r H. change (x :: r) with ([x] ++ r) in H. apply bytes_at_app in H. exact H. Qed.

(* [comment removed for export] *)
Lemma memcmp_loop : forall (b1 b2 : list byte) (p1 p2 : Z) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  b1 <> [] -> length b2 = length b1 -> Z.of_nat (length b1) < 2^62 ->
  0 <= p1 -> p1 + Z.of_nat (length b1) <= 2^63 -> 0 <= p2 -> p2 + Z.of_nat (length b1) <= 2^63 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> mem_inv asegs m ->
  evt asegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb8d58) fc None m (seg_rom asegs)).
Proof.
  induction b1 as [|x r1 IH]; intros [|y r2] p1 p2 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    NE HL HN P1 P1h P2 P2h B1 B2 MI; try congruence; cbn [length] in HL; try discriminate.
  destruct (bytes_at_cons_inv m p1 x r1 B1) as (X1 & B1'). destruct (bytes_at_cons_inv m p2 y r2 B2) as (Y1 & B2').
  pose proof (ro_C1_of_bytes m p1 x X1) as CX. pose proof (ro_C1_of_bytes m p2 y Y1) as CY.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 8 x) as RX. pose proof (bv_unsigned_in_range 8 y) as RY. unfold bv_modulus in RX, RY. cbn in RX, RY.
  cbn [length] in *. rewrite Nat2Z.inj_succ in *.
  lstep. lstep. cbv beta.
  assert (EUx : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia).
  assert (EUy : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia).
  cbn [memcmp_res].
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|NEQ].
  - lstep. brF.
    do 3 lstep.
    replace (Z.succ (Z.of_nat (length r1)) + -1) with (Z.of_nat (length r1)) by lia.
    destruct r1 as [|x' r1'].
    + destruct r2 as [|y' r2']; [|cbn [length] in HL; lia]. cbn [length Z.of_nat memcmp_res].
      lstep. brF. do 2 lstep.
      apply evt_done. unfold memcmp_post. do 14 eexists. reflexivity.
    + lstep. brT.
      apply (IH r2 (p1 + 1) (p2 + 1)); try assumption; try congruence; cbn [length] in *; try lia.
  - lstep. brT. do 2 lstep.
    apply evt_done. unfold memcmp_post. do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma memcmp_spec : forall (b1 b2 : list byte) (p1 p2 : Z) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  length b2 = length b1 -> Z.of_nat (length b1) < 2^62 ->
  0 <= p1 -> p1 + Z.of_nat (length b1) <= 2^63 -> 0 <= p2 -> p2 + Z.of_nat (length b1) <= 2^63 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> mem_inv asegs m ->
  evt asegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memcmp_entry) fc None m (seg_rom asegs)).
Proof.
  intros b1 b2 p1 p2 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HL HN P1 P1h P2 P2h B1 B2 MI.
  unfold memcmp_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct b1 as [|x r1].
  - destruct b2 as [|y r2]; [|cbn [length] in HL; lia]. cbn [length Z.of_nat memcmp_res].
    lstep. brT. do 2 lstep.
    apply evt_done. unfold memcmp_post. do 14 eexists. reflexivity.
  - assert (EUn : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (x :: r1)))) = Z.of_nat (length (x :: r1))) by (apply unsigned_lit; lia).
    lstep. brF.
    apply memcmp_loop; try assumption; congruence.
Qed.
