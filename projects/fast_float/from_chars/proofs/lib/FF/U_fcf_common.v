(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export U_from_chars_float_stmt Spf_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation USEGS := Ubsan.M.loaded_segments.

Section CTX.
  Variable c : spf_ctx.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
  #[local] Notation NEED := from_chars_float_need.
  #[local] Notation POST := (from_chars_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  Definition fmt : Z := bv_unsigned a3.

  (* [comment removed for export] *)
  Record ufcf_pre : Prop := UFCF_PRE {
    pre_FMT  : (fmt = 1 \/ fmt = 4 \/ fmt = 5)%Z;
    pre_A4   : a4 = Z_to_bv 64 FCF_OPT2;
    pre_TXT  : bytes_at USEGS m0 P bs;
    pre_LEN  : Z.of_nat (length bs) = L;
    pre_RANGE : (0 <= L < 2^40)%Z;
    pre_ENW  : (E < 2^64 - 8)%Z;
    pre_VAL  : rw_cells USEGS m0 V [C4 v];
    pre_VAL4 : (V mod 4 = 0)%Z;
    pre_ST   : stk USEGS m0 (bv_unsigned sp - NEED) (bv_unsigned sp);
    pre_AL   : (bv_unsigned sp mod 16 = 0)%Z;
    pre_LO   : (0x99000 <= bv_unsigned sp - NEED)%Z;
    pre_P0   : (0 < P)%Z;
    pre_V0   : (0 < V)%Z;
    pre_VLO  : (0x99000 <= V)%Z;
    pre_PR1  : pristine m0 0x10000 0x22000;
    pre_PR2  : pristine m0 U_FMIN (U_FMIN + 4);
    pre_FRM  : frm0 fc;
    pre_SEP1 : (bv_unsigned sp <= P \/ 16 <= P /\ E <= bv_unsigned sp - NEED)%Z;
    pre_SEP2 : (V + 4 <= bv_unsigned sp - NEED \/ bv_unsigned sp <= V)%Z;
    pre_SEP3 : (E <= V \/ V + 4 <= P)%Z }.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fmt_tests : ufcf_pre ->
    Z.land fmt 256 = 0%Z /\ Z.land fmt 32 = 0%Z /\ Z.land fmt 128 = 0%Z /\ Z.land fmt 16 = 0%Z /\ Z.land fmt 64 = 0%Z.
  Proof. LiaFast.lf_pins LiaFast.u0. intros PRE. destruct (pre_FMT PRE) as [E1|[E1|E1]]; rewrite E1; repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition savesU : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition pinv (lo : list cell) (m : word -> option byte) : Prop :=
    bytes_at USEGS m P bs
    /\ rw_cells USEGS m SP lo
    /\ Z.of_nat (cells_size lo) = 24%Z
    /\ rw_cells USEGS m (bv_unsigned (r_sp c) + -104)%Z savesU
    /\ stk USEGS m (bv_unsigned sp - NEED) SP
    /\ rw_cells USEGS m V [C4 v]
    /\ pristine m 0x10000 0x22000
    /\ pristine m U_FMIN (U_FMIN + 4)
    /\ munch W m0 m
    /\ wmono USEGS m0 m.

  (* [comment removed for export] *)
  Definition K_26058 : Prop :=
    forall junk m (x1 x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x29 x30 x31 : word) (k1 : Z),
      pinv [CB 24 junk] m -> (0 <= k1 <= 1)%Z -> (k1 < L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) x6 (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 x12 a3 a4
                 (txb bs k1) x16 x17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) x29 x30 x31)
            F (Z_to_bv 64 0x2800c) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_262f4 : Prop :=
    forall junk m (x1 x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x29 x30 x31 : word) (k1 kI : Z),
      pinv [CB 24 junk] m -> (1 <= L)%Z -> (0 <= k1 <= 1)%Z -> (k1 <= kI <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) x6 (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 x12 a3 a4
                 (Z_to_bv 64 (P + kI)) x16 x17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) x29 x30 x31)
            F (Z_to_bv 64 0x282a8) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_2654c : Prop :=
    forall lo m (x1 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x30 x31 : word) (k1 kp ex dc : Z),
      pinv lo m -> (1 <= L)%Z -> (0 <= k1 <= kp)%Z -> (kp <= L)%Z -> (- 2^41 <= ex <= 0)%Z -> (- 2^41 <= dc <= 2^41)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 ex) (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 x12 a3 a4
                 (Z_to_bv 64 (P + kp)) x16 x17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 dc) x30 x31)
            F (Z_to_bv 64 0x28500) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_268b4 : Prop :=
    forall lo m (x1 x6 x8 x9 x12 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x30 x31 : word) (k1 dc : Z),
      pinv lo m -> (1 <= L)%Z -> (0 <= k1 <= L)%Z -> (- 2^41 <= dc <= 2^41)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) x6 (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 x12 a3 a4
                 x15 x16 x17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 dc) x30 x31)
            F (Z_to_bv 64 0x28868) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_26a48 : Prop :=
    forall lo m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      pinv lo m ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x289fc) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_26988 : Prop :=
    forall lo m (x1 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      pinv lo m -> (1 <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 a0 a1 x12 a3 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2893c) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_26df4 : Prop :=
    forall lo m (x1 x6 x7 x8 x9 x12 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      pinv lo m -> (1 <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) x6 x7 x8 x9 a0 a1 x12 a3 a4 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28da8) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_26cfc : Prop :=
    forall lo m (F' : bvmap 5 word) (fc' : bv 32) (v' : word)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      frm0 fc' ->
      rw_cells USEGS m SP lo -> Z.of_nat (cells_size lo) = 24%Z ->
      rw_cells USEGS m (bv_unsigned (r_sp c) + -104)%Z savesU ->
      stk USEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m V [C4 v'] ->
      munch W m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F' (Z_to_bv 64 0x28cb0) fc' None m (seg_rom USEGS)).
End CTX.
