From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcRecLib RcLeafLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import joined_byte_c.
Import ListNotations.
Open Scope Z_scope.

(* T2: `not a1,a0` then `bltu a1,a2`: ~(p + 5) < i is false when p + 5 + i < 2^64. *)
Lemma jb_not : forall x y, 0 <= x -> 0 <= y -> x + y < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. rewrite (unsigned_lit x) by lia. rewrite lnot_mod64 by lia.
  assert (E : Z.lnot x mod 2^64 = 2^64 - 1 - x)
    by (rewrite Z.lnot_eq_pred_opp; symmetry; apply Z.mod_unique_pos with (q := -1); lia).
  rewrite E. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

(* subw, addiw: a 32-bit result in [0, 2^31) sign-extends to itself. *)
Lemma jb_swrap : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma jb_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. pose proof (byte_range b). unfold zxb. apply unsigned_lit. lia. Qed.

Lemma jb_rd : forall segs m A (b : byte) A', bytes_at segs m A [b] -> A' = A ->
  ov_read_bytes segs m (wa A') 1 = Some [b].
Proof.
  intros segs m A b A' H ->. rewrite <- (Z.add_0_r A). exact (rcl_rd segs m A [b] 0 b H eq_refl).
Qed.

Ltac jb_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu, zxb; cbn [negb]; fold_lit_ux;
  repeat (rewrite unsigned_lit by lia); solve_cond_rec.

Ltac jb_if v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; jb_cond]
  end.

Theorem joined_byte_holds : joined_byte_contract.
Proof.
  unfold joined_byte_contract, JOINED_BYTE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m i nb b
    Hi Ha2 Hal HN Hq HB.
  subst a2.
  assert (Ri : 9 <= i <= 10) by lia.
  pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. unfold inr64 in R0, R1.
  pose proof (byte_range nb) as Bn.
  pose proof (jb_rd rsegs m (bv_unsigned a0 + 4) nb (bv_unsigned a0 + 4) HN eq_refl) as RDn.
  (* +0x00 andi, +0x04 bnez: T1 (p mod 4 = 0) *)
  step. rewrite rcl_land3, Hal.
  step. jb_if false.
  (* +0x08 lbu a3 = nb; +0x0c bgeu a2,a3 *)
  step. clear RDn.
  step.
  destruct (Z.ltb_spec i (bv_unsigned nb)) as [E | E].
  - (* body path: i < nb *)
    replace (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) with (bv_unsigned a0 + 5 + i) in HB
      by (unfold jb_addr; rewrite (proj2 (Z.ltb_lt _ _) E); reflexivity).
    pose proof HB as (HB0 & HB1 & _). change (Z.of_nat (length [b])) with 1 in HB1.
    jb_if false.
    step. step.
    (* +0x18 bltu: T2 *)
    step. rewrite (jb_not (bv_unsigned a0 + 5) i) by lia. cbv iota.
    step. step.
    pose proof (jb_rd rsegs m (bv_unsigned a0 + 5 + i) b (bv_unsigned a0 + 5 + i) HB eq_refl) as RDb.
    step. step.
    apply evt_done. do 3 eexists. reflexivity.
  - (* last path: nb <= i *)
    pose proof (Hq E) as Hq0.
    replace (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i)
      with (bv_unsigned a1 + (9 + i - bv_unsigned nb)) in HB
      by (unfold jb_addr; rewrite (proj2 (Z.ltb_ge _ _) E); reflexivity).
    pose proof HB as (HB0 & HB1 & _). change (Z.of_nat (length [b])) with 1 in HB1.
    jb_if true.
    (* +0x24 subw: i - nb; +0x28 addiw: 9 + i - nb *)
    step. rewrite (unsigned_lit i) by lia. rewrite jb_zxb. rewrite (jb_swrap (i - bv_unsigned nb)) by lia.
    step. rewrite (unsigned_lit (i - bv_unsigned nb)) by lia. rewrite (jb_swrap (i - bv_unsigned nb + 9)) by lia.
    (* +0x2c add: t = q + (9 + i - nb); +0x30 bltu: T3 *)
    step.
    step. jb_if false.
    (* +0x34 .. +0x40: T4 *)
    step. step. step.
    step. rewrite rc_ubchk by (try rewrite unsigned_lit by lia; lia). cbv iota.
    (* +0x44 beqz a1: T5 *)
    step. rewrite (rc_neq0w a1) by lia. cbv iota.
    pose proof (jb_rd rsegs m (bv_unsigned a1 + (9 + i - bv_unsigned nb)) b
                  (i - bv_unsigned nb + 9 + bv_unsigned a1) HB ltac:(lia)) as RDb.
    step. step.
    apply evt_done. do 3 eexists. reflexivity.
Qed.
