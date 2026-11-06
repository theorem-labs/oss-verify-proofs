(* The short instruction segments of check_round_trip in fuzz_frame.plain, stated in
   crt_defs.v: the prologue up to the first malloc (crt_seg1), the second malloc (crt_seg2), the
   two frees (crt_segf1, crt_segf2) and the epilogue (crt_segx).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_fields_c crt_defs.
Import ListNotations.
Open Scope Z_scope.

Ltac crt_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Ltac crt_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.

Ltac crt_w := crt_usub; rewrite ?Z.shiftl_mul_pow2 by lia;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

Ltac crt_fin := apply evt_done; f_equal; crt_regs; crt_w.

(* Decide a branch whose condition the context fixes. *)
Ltac crt_take b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold_cond; crt_usub; fold_lit_ux; solve_cond_rec]
  end.

(* The end of crt_seg1: the registers, the footprint and the 144-byte frame. *)
Ltac crt_s1_done :=
  apply evt_done; unfold crt_s1_post;
  do 16 eexists; split;
  [ | split; [eassumption|]; split; [eassumption|]; unfold crt_saved;
      match goal with |- rw_cells _ _ (bv_unsigned ?sp - 144) _ =>
        replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia end;
      eassumption ];
  f_equal; crt_regs; crt_w.

(** * 0x13058 .. jal malloc (0x130ac) *)

Lemma crt_seg1_ok : crt_seg1_stmt.
Proof.
  unfold crt_seg1_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m w buf lo b
    ST LO HC HL HW RO.
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLe).
  assert (NB : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite (length_fr_body b HC); lia).
  pose proof (ro_cells_bound _ _ _ _ RO) as RB.
  change (Z.of_nat (cells_size (spec_cells buf b))) with 80 in RB.
  unfold spec_cells in RO.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 144%nat ST.
  do 18 step.
  (* bltu a0, s3: 60 < 30 + body_len skips the clamp to 60. *)
  step.
  if_cases C; zify_cond C; rewrite ?unsigned_lit in C by lia.
  - assert (FN : frame_len (length (fr_body b)) = fr_body_len b + 30) by (unfold frame_len; lia).
    rewrite FN.
    do 2 step.
    crt_s1_done.
  - assert (FN : frame_len (length (fr_body b)) = 60) by (unfold frame_len; lia).
    rewrite FN.
    do 3 step.
    crt_s1_done.
Qed.

(** * 0x130b0 .. jal malloc (0x130bc) *)

Lemma crt_seg2_ok : crt_seg2_stmt.
Proof.
  unfold crt_seg2_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m out HO.
  step. crt_take false.
  do 3 step.
  crt_fin.
Qed.

(** * 0x134c8 .. jal free (0x134cc) *)

Lemma crt_segf1_ok : crt_segf1_stmt.
Proof.
  unfold crt_segf1_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  crt_fin.
Qed.

(** * 0x134d0 .. jal free (0x134d4) *)

Lemma crt_segf2_ok : crt_segf2_stmt.
Proof.
  unfold crt_segf2_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  crt_fin.
Qed.

(** * 0x134d8 .. ret *)

Lemma crt_segx_ok : crt_segx_stmt.
Proof.
  unfold crt_segx_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j h
    vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 FR.
  unfold crt_saved in FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 15 step.
  crt_fin.
Qed.
