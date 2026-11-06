(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export P_slow_path_float_stmt Spf_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation PSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTX.
  Variable c : spf_ctx.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  Record spf_pre : Prop := SPF_PRE {
    pre_TXT  : bytes_at PSEGS m0 P bs;
    pre_LEN  : Z.of_nat (length bs) = L;
    pre_RANGE : (1 <= L < 2^40)%Z;
    pre_ENW  : (E < 2^64 - 8)%Z;
    pre_A5   : a5 = Z_to_bv 64 0;
    pre_VAL  : rw_cells PSEGS m0 V [C4 v];
    pre_VAL4 : (V mod 4 = 0)%Z;
    pre_ST   : stk PSEGS m0 (bv_unsigned sp - NEED) (bv_unsigned sp);
    pre_AL   : (bv_unsigned sp mod 16 = 0)%Z;
    pre_LO   : (0x97000 <= bv_unsigned sp - NEED)%Z;
    pre_P0   : (0 < P)%Z;
    pre_V0   : (0 < V)%Z;
    pre_VLO  : (0x97000 <= V)%Z;
    pre_PR1  : pristine m0 0x10000 0x22000;
    pre_PR2  : pristine m0 P_FMIN (P_FMIN + 4);
    pre_FRM  : frm0 fc;
    pre_SEP1 : (bv_unsigned sp <= P \/ 16 <= P /\ E <= bv_unsigned sp - NEED)%Z;   (* [comment removed for export] *)
    pre_SEP2 : (V + 4 <= bv_unsigned sp - NEED \/ bv_unsigned sp <= V)%Z;
    pre_SEP3 : (E <= V \/ V + 4 <= P)%Z }.

  (* [comment removed for export] *)
  Definition frameA (junk : list byte) : list cell :=
    [CB 584 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition pinv (junk : list byte) (m : word -> option byte) : Prop :=
    bytes_at PSEGS m P bs
    /\ rw_cells PSEGS m SP (frameA junk)
    /\ stk PSEGS m (bv_unsigned sp - NEED) SP
    /\ rw_cells PSEGS m V [C4 v]
    /\ pristine m 0x10000 0x22000
    /\ pristine m P_FMIN (P_FMIN + 4)
    /\ munch W m0 m
    /\ wmono PSEGS m0 m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition K_264b4 : Prop :=
    forall junk m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                    x26 x27 x28 x29 x30 x31 : word),
      pinv junk m ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x283a4) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_25c00 : Prop :=
    forall junk m (x1 x5 x6 x7 x9 x12 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (ng k2 k3 : Z),
      pinv junk m -> (0 <= ng <= 1)%Z -> (0 <= k2 <= k3)%Z -> (k3 <= L)%Z -> (k3 <= 1)%Z ->
      (k3 < L -> x16 = txb bs k3)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) a1 x12 a3 a4 x15 x16 x17
                 (Z_to_bv 64 (P + k2)) (Z_to_bv 64 (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27af0) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_25e78 : Prop :=
    forall junk m (x1 x5 x6 x7 x9 x12 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (ng k3 kI : Z),
      pinv junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (kI <= L)%Z -> (k3 <= 1)%Z ->
      digs bs k3 kI ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) a1 x12 a3 a4 (Z_to_bv 64 (P + kI)) x16 x17
                 x18 (Z_to_bv 64 (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27d68) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition spans (k3 kI fp fL kp : Z) : Prop :=
    ((fp = 0 /\ fL = 0 /\ kp = kI)
     \/ (fp = P + kI + 1 /\ kI < L /\ tx bs kI = bv_unsigned a4 mod 256 /\ kp = kI + 1 + fL
         /\ digs bs (kI + 1) (kI + 1 + fL)))%Z.

  Definition K_25fb0 : Prop :=
    forall junk m (x1 x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (ng k3 kI fp fL kp : Z),
      pinv junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (0 <= fL)%Z ->
      (kI <= kp <= L)%Z -> digs bs k3 kI -> spans k3 kI fp fL kp -> (0 < (kI - k3) + fL)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 fL) (Z_to_bv 64 ((kI - k3) + fL)) x7 a2 x9
                 (Z_to_bv 64 ng) a1 x12 a3 a4 (Z_to_bv 64 (P + kI)) (Z_to_bv 64 (kI - k3)) (Z_to_bv 64 fp)
                 (Z_to_bv 64 (P + kp)) (Z_to_bv 64 (P + k3)) (Z_to_bv 64 (- fL))
                 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27ea0) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_261dc : Prop :=
    forall junk m (x1 x7 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (ng k3 kI fp fL kp kq xn : Z),
      pinv junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (0 <= fL)%Z ->
      (kI <= kp <= kq)%Z -> (kq <= L)%Z -> digs bs k3 kI -> spans k3 kI fp fL kp ->
      (0 < (kI - k3) + fL)%Z -> (- 2^32 < xn < 2^32)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 fL) (Z_to_bv 64 ((kI - k3) + fL)) x7 a2
                 (Z_to_bv 64 (P + kq)) (Z_to_bv 64 ng) a1 x12 (Z_to_bv 64 xn) a4
                 (Z_to_bv 64 (P + kI)) (Z_to_bv 64 (kI - k3)) (Z_to_bv 64 fp)
                 (Z_to_bv 64 (P + kp)) (Z_to_bv 64 (P + k3)) (Z_to_bv 64 (- fL + xn))
                 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x280cc) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_266d0 : Prop :=
    forall junk m (x1 x6 x7 x11 x14 x15 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q : word) (ng k3 kI fp fL kq tm : Z),
      pinv junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (0 <= fL)%Z ->
      (kI <= kq <= L)%Z ->
      ((fp = 0 /\ fL = 0) \/ (fp = P + kI + 1 /\ kI + 1 + fL <= L))%Z ->
      (0 <= tm <= 1)%Z -> (tm = 1 -> 0 < bv_unsigned w < 2^64 - 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 fL) x6 x7 a2
                 (Z_to_bv 64 (P + kq)) (Z_to_bv 64 ng) x11 w (Z_to_bv 64 tm) x14 x15
                 (Z_to_bv 64 (kI - k3)) (Z_to_bv 64 fp) x18 (Z_to_bv 64 (P + k3)) q
                 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x285c0) fc None m (seg_rom PSEGS)).

End CTX.
