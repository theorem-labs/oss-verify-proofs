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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export U_slow_path_double_stmt Spf_text.
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
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  Record uspd_pre : Prop := USPF_PRE {
    pre_TXT  : bytes_at USEGS m0 P bs;
    pre_LEN  : Z.of_nat (length bs) = L;
    pre_RANGE : (1 <= L < 2^40)%Z;
    pre_ENW  : (E < 2^64 - 8)%Z;
    pre_A5   : a5 = Z_to_bv 64 0;
    pre_VAL  : rw_cells USEGS m0 V [C8 v];
    pre_VAL8 : (V mod 8 = 0)%Z;
    pre_ST   : stk USEGS m0 (bv_unsigned sp - NEED) (bv_unsigned sp);
    pre_AL   : (bv_unsigned sp mod 16 = 0)%Z;
    pre_LO   : (0x99000 <= bv_unsigned sp - NEED)%Z;
    pre_P0   : (0 < P)%Z;
    pre_V0   : (0 < V)%Z;
    pre_VLO  : (0x99000 <= V)%Z;
    pre_PR1  : pristine m0 0x10000 0x22000;
    pre_PR2  : pristine m0 U_FMIN_D (U_FMIN_D + 4);
    pre_FRM  : frm0 fc;
    pre_SEP1 : (bv_unsigned sp <= P \/ 16 <= P /\ E <= bv_unsigned sp - NEED)%Z;   (* [comment removed for export] *)
    pre_SEP2 : (V + 8 <= bv_unsigned sp - NEED \/ bv_unsigned sp <= V)%Z;
    pre_SEP3 : (E <= V \/ V + 8 <= P)%Z }.

  Definition usaves : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition uframeA (junk : list byte) : list cell := CB 600 junk :: usaves.
  Definition uframeB (j0 j1 : list byte) : list cell := CB 8 j0 :: C8 a2 :: CB 584 j1 :: usaves.

  Definition upinv_with (fr : list cell) (m : word -> option byte) : Prop :=
    bytes_at USEGS m P bs
    /\ rw_cells USEGS m SP fr
    /\ stk USEGS m (bv_unsigned sp - NEED) SP
    /\ rw_cells USEGS m V [C8 v]
    /\ pristine m 0x10000 0x22000
    /\ pristine m U_FMIN_D (U_FMIN_D + 4)
    /\ munch W m0 m
    /\ wmono USEGS m0 m.
  Definition upinv (junk : list byte) (m : word -> option byte) : Prop := upinv_with (uframeA junk) m.
  Definition upinvB (j0 j1 : list byte) (m : word -> option byte) : Prop := upinv_with (uframeB j0 j1) m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition K_228a0 : Prop :=
    forall junk m (x1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 : Z),
      upinv junk m -> (0 <= k3 <= L)%Z -> (k3 <= 1)%Z -> (k3 < L -> x14 = Zw (tx bs k3))%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 (Zw DP) (Zw (tx bs 0)) a3 x14 x15 x16 x17
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24854) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_22c1c : Prop :=
    forall junk m (x1 x5 x6 x7 x8 x9 x10 x14 x15 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI : Z),
      upinv junk m -> (0 <= k3 <= kI)%Z -> (kI <= L)%Z -> (k3 <= 1)%Z -> digs bs k3 kI ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 (Zw DP) (Zw (tx bs 0)) a3 x14 x15 (Zw (P + kI)) x17
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24bd0) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition uspans (k3 kI fp fL kp : Z) : Prop :=
    ((fp = 0 /\ fL = 0 /\ kp = kI)
     \/ (fp = P + kI + 1 /\ kI < L /\ tx bs kI = DP /\ kp = kI + 1 + fL
         /\ digs bs (kI + 1) (kI + 1 + fL)))%Z.

  (* [comment removed for export] *)
  Definition K_22d70 : Prop :=
    forall junk m (x1 x6 x7 x8 x10 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (k3 kI fp fL kp : Z),
      upinv junk m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (0 <= fL)%Z ->
      (kI <= kp <= L)%Z -> digs bs k3 kI -> uspans k3 kI fp fL kp -> (0 < (kI - k3) + fL)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw ((kI - k3) + fL)) x6 x7 x8 (Zw (P + kp)) x10 (Zw DP) (Zw (tx bs 0)) a3
                 (Zw (kI - k3)) (Zw fp) (Zw (P + kI)) (Zw fL)
                 (Zw (P + k3)) a1 (Zw (- fL)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24d24) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_232bc : Prop :=
    forall junk m (x1 x6 x7 x8 x10 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (k3 kI fp fL kp kq xn : Z),
      upinv junk m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (0 <= fL)%Z ->
      (kI <= kp <= kq)%Z -> (kq <= L)%Z -> digs bs k3 kI -> uspans k3 kI fp fL kp ->
      (0 < (kI - k3) + fL)%Z -> (- 2^32 < xn < 2^32)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw ((kI - k3) + fL)) x6 x7 x8 (Zw (P + kq)) x10 (Zw DP) (Zw (tx bs 0)) (Zw xn)
                 (Zw (kI - k3)) (Zw fp) (Zw (P + kI)) (Zw fL)
                 (Zw (P + k3)) a1 (Zw (- fL + xn)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25270) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_23648 : Prop :=
    forall junk m (x1 x5 x6 x7 x8 x13 x16 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (w q : word)
           (k3 kI fp fL kq tm : Z),
      upinv junk m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (0 <= fL)%Z ->
      (kI <= kq <= L)%Z ->
      ((fp = 0 /\ fL = 0) \/ (fp = P + kI + 1 /\ kI + 1 + fL <= L))%Z ->
      (0 <= tm <= 1)%Z -> (tm = 1 -> 0 < bv_unsigned w < 2^64 - 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kq)) w (Zw tm) (Zw (tx bs 0)) x13
                 (Zw (kI - k3)) (Zw fp) x16 (Zw fL)
                 (Zw (P + k3)) a1 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x255fc) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_236d8e : Prop :=
    forall junk m (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      upinv junk m ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 (Zw 0) (Zw 0) (Zw 0) x13 x14 x15 x16 x17
                 x18 a1 (Zw 0) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2568c) fc None m (seg_rom USEGS)).

End CTX.
