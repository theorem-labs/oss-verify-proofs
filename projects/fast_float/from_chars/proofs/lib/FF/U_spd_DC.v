(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.

Module U_spd_commonT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export U_spd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
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
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
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
  Definition frameT (j16 : list byte) (q w lm : word) (ng tm : Z) (j5 : list byte) (k3 kI fp fL : Z)
                    (rest : list cell) : list cell :=
    [CB 16 j16; C8 q; C8 w; C8 lm; C1 (Z_to_bv 8 ng); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 tm); CB 5 j5;
     C8 (Zw (P + k3)); C8 (Zw (kI - k3)); C8 (Zw fp); C8 (Zw fL)]
    ++ rest ++ usaves c.

  (* [comment removed for export] *)
  Definition tinv (cells : list cell) (m : word -> option byte) : Prop :=
    bytes_at USEGS m P bs
    /\ rw_cells USEGS m SP cells
    /\ stk USEGS m (bv_unsigned sp - NEED) SP
    /\ rw_cells USEGS m V [C8 v]
    /\ pristine m 0x10000 0x22000
    /\ pristine m U_FMIN_D (U_FMIN_D + 4)
    /\ munch W mI m
    /\ wmono USEGS mI m.

  #[using="Type"] Lemma tinv_upinv : forall junk m, upinv c junk m <-> tinv (uframeA c junk) m.
  Proof. LiaFast.lf_pins LiaFast.u0. intros; unfold upinv, upinv_with, tinv; tauto. Qed.

  (* [comment removed for export] *)
  Definition pnsok (ng k3 kI fp fL tm : Z) (w : word) : Prop :=
    (0 <= ng <= 1)%Z /\ (0 <= k3 <= kI)%Z /\ (kI <= L)%Z /\ (0 <= fL)%Z
    /\ ((fp = 0 /\ fL = 0) \/ (fp = P + kI + 1 /\ kI + 1 + fL <= L))%Z
    /\ (0 <= tm <= 1)%Z /\ (tm = 1 -> 0 < bv_unsigned w < 2^64 - 1)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition K_236d0 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm : Z),
      tinv (frameT j16 q w lm ng tm j5 k3 kI fp fL [CB 520 r]) m -> pnsok ng k3 kI fp fL tm w ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w (Zw tm) (Zw ng) (Zw 1) x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25684) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_236f0 : Prop :=
    forall m (cells : list cell)
           (x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q : word) (ng : Z),
      bytes_at USEGS m P bs ->
      rw_cells USEGS m SP cells -> Z.of_nat (cells_size cells) = 600%Z ->
      rw_cells USEGS m (SP + 600)%Z (usaves c) ->
      stk USEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m V [C8 v] ->
      pristine m 0x10000 0x22000 -> pristine m U_FMIN_D (U_FMIN_D + 4) ->
      munch W mI m -> wmono USEGS mI m ->
      (0 <= ng <= 1)%Z -> (-22 <= bv_signed q <= 22)%Z -> (bv_unsigned w <= 2^53)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w x11 (Zw ng) x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x256a4) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_23764 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm tf : Z),
      tinv (frameT j16 q w lm ng tm j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL tm w ->
      (tf = 0 \/ (tf = 1 /\ tm = 1))%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w (Zw tf) (Zw ng) x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25718) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_23964 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am ap : word) (ng k3 kI fp fL : Z),
      tinv (frameT j16 q w lm ng 1 j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (bv_signed q < -342 -> am = Zw 0 /\ ap = Zw 0)%Z ->
      (308 < bv_signed q -> am = Zw 0 /\ ap = Zw 2047)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w x11 (Zw ng) x13 x14 x15 x16 x17
                 am ap q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25918) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_23bb0 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL : Z),
      tinv (frameT j16 q w lm ng 1 j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (-342 <= bv_signed q <= 308)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w x11 (Zw ng) x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25b64) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_23cf4 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am : word) (ng k3 kI fp fL X : Z),
      tinv (frameT j16 q w lm ng 1 j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (-342 <= bv_signed q <= 308)%Z -> (-33100 <= X <= -30600)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w x11 (Zw ng) x13 x14 x15 x16 x17
                 am (Zw X) q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25ca8) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_23e64 : Prop :=
    forall m (cells : list cell) (j16 : list byte)
           (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q : word) (ng : Z),
      bytes_at USEGS m P bs ->
      rw_cells USEGS m SP ([CB 16 j16; C8 q; C8 w] ++ cells) -> Z.of_nat (cells_size cells) = 568%Z ->
      rw_cells USEGS m (SP + 600)%Z (usaves c) ->
      stk USEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m V [C8 v] ->
      pristine m 0x10000 0x22000 -> pristine m U_FMIN_D (U_FMIN_D + 4) ->
      munch W mI m -> wmono USEGS mI m ->
      (0 <= ng <= 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 x11 (Zw ng) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25e18) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_23ea0 : Prop :=
    forall m (cells : list cell) (F' : bvmap 5 word) (fc' : bv 32) (v' : word)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      frm0 fc' ->
      rw_cells USEGS m SP cells -> Z.of_nat (cells_size cells) = 600%Z ->
      rw_cells USEGS m (SP + 600)%Z (usaves c) ->
      stk USEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m V [C8 v'] ->
      munch W mI m -> wmono USEGS mI m ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F' (Zw 0x25e54) fc' None m (seg_rom USEGS)).

End CTX.
End U_spd_commonT.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_tbl U_memset.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_parse_mantissa.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_small_add U_parse_mantissa U_positive_digit_comp_d_stmt U_negative_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_small_mul OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_small_add OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_negative_digit_comp_d_stmt.
Import ListNotations.

Module U_spd_A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memset.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[local] Ltac open_upinv H :=
    unfold upinv, upinvB, upinv_with in H;
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold uframeA, uframeB, usaves in FR;
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[using="Type"] #[local] Lemma rw_CB_len : forall segs m A n junk rest, rw_cells segs m A (CB n junk :: rest) -> length junk = n.
  Proof. LiaFast.lf_pins LiaFast.u0. intros segs m A n junk rest [[Hwf _] _]. cbn in Hwf. tauto. Qed.

  (* [comment removed for export] *)
  #[local] Ltac to_frameA FR :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A ?cs =>
        let n := eval compute in (Nat.sub (List.length cs) 13) in
        let mid := take_cells n cs in
        let post := drop_cells n cs in
        apply (rw_cells_merge segs m A [] mid post) in FR;
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ _ (CB 600 ?j :: _) => set (junk_m := j) in FR; clearbody junk_m
        end
    end.

  (* [comment removed for export] *)
  #[local] Ltac call_memset27 FR :=
    let LJA := fresh "LJA" in let LJJ := fresh "LJJ" in let OLD := fresh "OLD" in let OBJn := fresh "OBJn" in
    let Ua0 := fresh "Ua0" in let Ua2 := fresh "Ua2" in
    let FRlo := fresh "FRlo" in let FR2 := fresh "FR2" in let OBJ := fresh "OBJ" in let FRhi := fresh "FRhi" in
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (CB 48 ?ja :: ?rest) =>
        pose proof (rw_CB_len segs m A 48 ja rest FR) as LJA;
        apply (rw_cells_split_CB segs m A [] 48 ja rest [16; 27; 5]%nat) in FR; [ | reflexivity ];
        cbn [app mk_CB_cells] in FR
    end;
    chunk_split FR 1%nat FRlo FR2; chunk_split FR2 1%nat OBJ FRhi;
    lazymatch type of OBJ with
    | rw_cells ?segs ?m ?B [CB 27 ?jj] =>
        pose proof (rw_CB_len segs m B 27 jj [] OBJ) as LJJ;
        pose proof (u8arr_of_rw_cells segs m B 27 jj OBJ) as OLD; clear OBJ;
        pose proof (unsigned_lit B ltac:(lia)) as Ua0;
        pose proof (unsigned_lit 27 ltac:(lia)) as Ua2
    end;
    step; (* [comment removed for export] *)
    call memset_spec;
    [ reflexivity
    | rewrite unsigned_lit by lia; exact OLD
    | rewrite unsigned_lit by lia; rewrite LJJ; reflexivity
    | rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
    | ];
    lazymatch goal with
    | HB : bytes_at ?segs ?m' _ (repeat _ _), HW : wr_at _ _ _ _ |- _ =>
        rewrite ?unsigned_lit in HB, HW by lia;
        pose proof (rw_cells_of_u8arr segs m' _ _ (conj HB HW)) as OBJn;
        rewrite repeat_length in OBJn; change (Z.to_nat 27) with 27%nat in OBJn;
        clear HB HW; try clear OLD; try clear Ua0; try clear Ua2;
        chunk_join FRlo OBJn FR2; chunk_join FR2 FRhi FR
    end.

  Hypothesis C_236d8e : K_236d8e c.
  Hypothesis C_228a0 : K_228a0 c.

  #[local] Ltac mk_upinv TXT FR ST VAL PR1 PR2 MU WM :=
    split; [exact TXT|]; split; [exact FR|]; split; [unfold slow_path_double_need; exact ST|]; split; [exact VAL|];
    split; [exact PR1|]; split; [unfold U_FMIN_D; exact PR2|]; split; [exact MU | exact WM].

  (* [comment removed for export] *)
  #[using="PRE C_236d8e C_228a0"] Lemma uspd_A :
    evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Zw 0x245ac) fc None mI (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_236d8e C_228a0 : LiaFast.U) => LiaFast.u0).
    unfold K_236d8e in C_236d8e. unfold K_228a0 in C_228a0.
    pre_facts.
    pose proof (pre_ST c PRE) as ST. unfold slow_path_double_need in ST.
    pose proof (pre_TXT c PRE) as TXT. pose proof (pre_VAL c PRE) as VAL.
    pose proof (pre_PR1 c PRE) as PR1. pose proof (pre_PR2 c PRE) as PR2. unfold U_FMIN_D in PR2.
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    pose proof (munch_refl W mI) as MU. cbv beta delta [slow_path_double_W slow_path_double_need] in MU.
    pose proof (wmono_refl USEGS mI) as WM.
    carve_frame 704%nat ST.
    do 14 step.   (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 600 ?j :: _) => set (junk0 := j) in FR; clearbody junk0 end.
    step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z.land (bv_unsigned a4) 255) with DP
      by (change 255%Z with (2^8 - 1)%Z; rewrite zb_land_mask by lia; reflexivity).
    rewrite (pre_A5 c PRE).
    step. (* [comment removed for export] *)
    if_true.
    step. (* [comment removed for export] *)
    if_cases Hnull; [| cond_cleanup Hnull; exfalso; lia]. clear Hnull.
    txt_rd TXT 0%Z RD. rewrite wa_P0 in RD.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) 0%Z. pose proof (tx_range bs 0) as R0.
    assert (UPINV : upinv c junk0 m) by (mk_upinv TXT FR ST VAL PR1 PR2 MU WM).
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (SIGN : forall x10,
      evt USEGS POST
        (MS (mkR ra (Zw SP) gp tp t0 t1 t2 s0 s1 x10 (Zw DP) (Zw (tx bs 0)) a3 a4 (Zw 0) a6 a7
                 a0 a1 s4 s5 s6 a2 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Zw 0x2465c) fc None m (seg_rom USEGS))).
    { intros x10.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
      step. (* [comment removed for export] *)
      if_cases Hend.
      - cond_cleanup Hend.
        (* [comment removed for export] *)
        step. step. step. step. (* [comment removed for export] *)
        step. step. step. (* [comment removed for export] *)
        call_memset27 FR.
        do 5 step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_true.
        to_frameA FR.
        goto (eapply C_236d8e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
      - cond_cleanup Hend.
        txt_rd TXT 1%Z RD.
        step. (* [comment removed for export] *)
        clear RD. fold_tx (r_bs c) 1%Z. pose proof (tx_range bs 1) as R1.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hdig.
        + clear Hdig.
          step. (* [comment removed for export] *)
          goto (eapply C_228a0 with (k3 := 1%Z)); [exact UPINV | lia | lia | intros; reflexivity].
        + clear Hdig.
          step. (* [comment removed for export] *)
          if_cases Hdp.
          * clear Hdp.
            step. (* [comment removed for export] *)
            goto (eapply C_228a0 with (k3 := 1%Z)); [exact UPINV | lia | lia | intros; reflexivity].
          * clear Hdp.
            (* [comment removed for export] *)
            step. step. step. step. (* [comment removed for export] *)
            step. step. step. (* [comment removed for export] *)
            call_memset27 FR.
            do 5 step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_true.
            to_frameA FR.
            goto (eapply C_236d8e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM. }
    step. (* [comment removed for export] *)
    if_cases Hminus; [apply SIGN|].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hplus.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_228a0 with (k3 := 0%Z)); [exact UPINV | lia | lia | intros; reflexivity].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H43.
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (eapply C_228a0 with (k3 := 0%Z)); [exact UPINV | lia | lia | intros; reflexivity].
      + apply SIGN.
  Qed.
End BLK.
End U_spd_A.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* [comment removed for export] *)
Lemma magic_div10000 : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 3777893186295716171) 64))) 11 = (x / 10000)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite unsigned_lit by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.
Lemma magic_div100 : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr x 2)) * 2951479051793528259) 64))) 2 = (x / 100)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (unsigned_lit (x / 2^2)) by (Z.div_mod_to_equations; nia).
  rewrite unsigned_lit by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.
Lemma magic_div10 : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 14757395258967641293) 64))) 3 = (x / 10)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite unsigned_lit by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.
Lemma sci_T_bound : forall mv T uw, (1 <= mv)%Z -> (0 <= T)%Z -> (mv * 10^T <= uw)%Z -> (uw < 2^64)%Z -> (T <= 19)%Z.
Proof.
  intros mv T uw H1 H2 H3 H4.
  destruct (Z.le_gt_cases T 19) as [|HT]; [assumption|]. exfalso.
  assert (10 ^ 20 <= 10 ^ T)%Z by (apply Z.pow_le_mono_r; lia).
  assert (0 < 10 ^ T)%Z by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.
Lemma pow10_step : forall mv d k uw, (0 <= d)%Z -> (0 < k)%Z -> (0 <= mv)%Z -> (mv * 10^d <= uw)%Z ->
  ((mv / 10^k) * 10^(d + k) <= uw)%Z.
Proof.
  intros mv d k uw Hd Hk Hmv H. rewrite Z.pow_add_r by lia.
  assert (0 < 10 ^ k)%Z by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 10 ^ d)%Z by (apply Z.pow_pos_nonneg; lia).
  assert ((mv / 10 ^ k) * 10 ^ k <= mv)%Z by (Z.div_mod_to_equations; nia).
  nia.
Qed.
Lemma bytes_at_slice : forall m A bs i n, bytes_at USEGS m A bs -> (i + n <= length bs)%nat ->
  bytes_at USEGS m (A + Z.of_nat i) (firstn n (skipn i bs)).
Proof.
  intros m A bs i n H Hle.
  rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn i bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.
Lemma cb2_c2_zero : forall m A,
  rw_cells USEGS m A [CB 2 (repeat (Z_to_bv 8 0) 2)] -> rw_cells USEGS m A [C2 (Z_to_bv 64 0)].
Proof.
  intros m A [[Hwf Hb] Hw]. split; [split|]; [cbn; tauto | exact Hb | exact Hw].
Qed.
Lemma shiftr_small_0 : forall dg n, (0 <= dg < 2^32)%Z -> (32 <= n)%Z -> Z.shiftr dg n = 0%Z.
Proof.
  intros dg n H Hn. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|].
  eapply Z.lt_le_trans; [apply (proj2 H)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma c8_as_c4s : forall m A dg, (0 <= dg < 2^32)%Z ->
  rw_cells USEGS m A [C8 (Z_to_bv 64 dg)] -> rw_cells USEGS m A [C4 (Z_to_bv 64 dg); C4 (Z_to_bv 64 0)].
Proof.
  intros m A dg Hdg [[Hwf Hb] Hw]. split; [split|]; [cbn; tauto | | exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. unfold le8, le4, word_to_le_bytes.
  rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_shiftr by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8)) by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8+8+8)) by lia.
  rewrite !Z.shiftr_0_l. exact (fun H => H).
Qed.
Lemma c4s_as_c8 : forall m A dg, (0 <= dg < 2^32)%Z ->
  rw_cells USEGS m A [C4 (Z_to_bv 64 dg); C4 (Z_to_bv 64 0)] -> rw_cells USEGS m A [C8 (Z_to_bv 64 dg)].
Proof.
  intros m A dg Hdg [[Hwf Hb] Hw]. split; [split|]; [cbn; tauto | | exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. unfold le8, le4, word_to_le_bytes.
  rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_shiftr by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8)) by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8+8+8)) by lia.
  rewrite !Z.shiftr_0_l. exact (fun H => H).
Qed.
(* [comment removed for export] *)
Lemma swrap32_wordz : forall x, (- 2^31 <= x < 2^31)%Z -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.
Lemma swrap32_wordz_add : forall x k, (- 2^31 <= x < 2^31)%Z -> (- 2^31 <= x + k < 2^31)%Z ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + k) = (x + k)%Z.
Proof.
  intros x k Hx Hk. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma usx32_small : forall dg, (0 <= dg < 2^31)%Z -> bv_unsigned (sx32 (Z_to_bv 64 dg)) = dg.
Proof.
  intros dg H. unfold sx32. rewrite (swrap32_wordz dg) by lia. apply unsigned_lit. lia.
Qed.

Section ZLEMMAS.
Open Scope Z_scope.
(* [comment removed for export] *)
#[using="Type"] Lemma cap_pos : forall b dg e, 0 <= dg -> 0 <= e -> e + dg <= 329 -> 0 <= b ->
  b < 2 ^ (64 * (dg / 19 + 3)) -> b * 10 ^ e < BIG_CAP.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b dg e Hdg He Hs Hb Hlt. unfold BIG_CAP.
  assert (H10 : 10 ^ e <= 2 ^ (4 * e)).
  { rewrite Z.pow_mul_r by lia. change (2 ^ 4) with 16. apply Z.pow_le_mono_l. lia. }
  assert (H2 : 2 ^ (64 * (dg / 19 + 3)) * 2 ^ (4 * e) <= 2 ^ 3968).
  { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; [lia|]. Z.div_mod_to_equations. lia. }
  assert (0 < 10 ^ e) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= 2 ^ (4 * e)) by (apply Z.pow_nonneg; lia).
  nia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma zx32_shifts : forall X : Z,
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 X)) 32))) 32)) = (X mod 2^32)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite !unsigned_lit_wrap.
  Z.div_mod_to_equations. lia.
Qed.
End ZLEMMAS.

Lemma zxb_lit8 : forall t, (0 <= t < 256)%Z -> zxb (Z_to_bv 8 t) = Z_to_bv 64 t.
Proof.
  intros t Ht. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256%Z. apply Z.mod_small. lia.
Qed.

Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[local] Ltac open_upinv H :=
    unfold upinv, upinvB, upinv_with in H;
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold uframeA, uframeB, usaves in FR;
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[using="Type"] #[local] Lemma rw_CB_len : forall segs m A n junk rest, rw_cells segs m A (CB n junk :: rest) -> length junk = n.
  Proof. LiaFast.lf_pins LiaFast.u0. intros segs m A n junk rest [[Hwf _] _]. cbn in Hwf. tauto. Qed.

  (* [comment removed for export] *)
  #[local] Ltac to_frameA FR :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A ?cs =>
        let n := eval compute in (Nat.sub (List.length cs) 13) in
        let mid := take_cells n cs in
        let post := drop_cells n cs in
        apply (rw_cells_merge segs m A [] mid post) in FR;
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ _ (CB 600 ?j :: _) => set (junk_m := j) in FR; clearbody junk_m
        end
    end.

  (* [comment removed for export] *)
  #[local] Ltac call_memset27 FR :=
    let LJA := fresh "LJA" in let LJJ := fresh "LJJ" in let OLD := fresh "OLD" in let OBJn := fresh "OBJn" in
    let Ua0 := fresh "Ua0" in let Ua2 := fresh "Ua2" in
    let FRlo := fresh "FRlo" in let FR2 := fresh "FR2" in let OBJ := fresh "OBJ" in let FRhi := fresh "FRhi" in
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (CB 48 ?ja :: ?rest) =>
        pose proof (rw_CB_len segs m A 48 ja rest FR) as LJA;
        apply (rw_cells_split_CB segs m A [] 48 ja rest [16; 27; 5]%nat) in FR; [ | reflexivity ];
        cbn [app mk_CB_cells] in FR
    end;
    chunk_split FR 1%nat FRlo FR2; chunk_split FR2 1%nat OBJ FRhi;
    lazymatch type of OBJ with
    | rw_cells ?segs ?m ?B [CB 27 ?jj] =>
        pose proof (rw_CB_len segs m B 27 jj [] OBJ) as LJJ;
        pose proof (u8arr_of_rw_cells segs m B 27 jj OBJ) as OLD; clear OBJ;
        pose proof (unsigned_lit B ltac:(lia)) as Ua0;
        pose proof (unsigned_lit 27 ltac:(lia)) as Ua2
    end;
    step; (* [comment removed for export] *)
    call memset_spec;
    [ reflexivity
    | rewrite unsigned_lit by lia; exact OLD
    | rewrite unsigned_lit by lia; rewrite LJJ; reflexivity
    | rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
    | ];
    lazymatch goal with
    | HB : bytes_at ?segs ?m' _ (repeat _ _), HW : wr_at _ _ _ _ |- _ =>
        rewrite ?unsigned_lit in HB, HW by lia;
        pose proof (rw_cells_of_u8arr segs m' _ _ (conj HB HW)) as OBJn;
        rewrite repeat_length in OBJn; change (Z.to_nat 27) with 27%nat in OBJn;
        clear HB HW; try clear OLD; try clear Ua0; try clear Ua2;
        chunk_join FRlo OBJn FR2; chunk_join FR2 FRhi FR
    end.

  (* [comment removed for export] *)
  #[local] Ltac ms_leaf_eq ::=
    first [ reflexivity
          | apply (f_equal (Z_to_bv 64)); lia
          | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
          | lazymatch goal with
            | |- ?a = Z_to_bv 64 ?e =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned
                  | first [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ] ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ first [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ]
                  | apply Z_to_bv_bv_unsigned ]
            end ].

  (* [comment removed for export] *)
  #[local] Ltac ms_eq_tac ::=
    cbv beta delta [mkR];
    repeat first [ reflexivity
                 | ms_leaf_eq
                 | lazymatch goal with
                   | |- ?a = _ => lazymatch type of a with
                                  | bv _ => fail
                                  | _ => progress f_equal
                                  end
                   end ].

  (* [comment removed for export] *)
  #[local] Tactic Notation "goto" tactic3(tac) := (eapply evt_eq; [ | tac ]; [ ms_eq_tac; try first [ ms_leaf_eq | lia ] | .. ]).

  (* [comment removed for export] *)
  #[local] Ltac kill_chk H :=
    exfalso; cond_cleanup H; unsign_chk H; rewrite ?signed_lit in H by lia;
    repeat match type of H with context [if (?a <? ?b)%Z then _ else _] => destruct (Z.ltb_spec0 a b) end;
    Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis positive_digit_comp_d_spec : positive_digit_comp_d_stmt.
  Hypothesis negative_digit_comp_d_spec : negative_digit_comp_d_stmt.
  Hypothesis C_23e64 : K_23e64 c.

  (* [comment removed for export] *)
  #[local] Ltac exact_at H :=
    first [ exact H
          | lazymatch goal with
            | |- rw_cells _ _ ?a _ => lazymatch type of H with rw_cells _ _ ?b _ => replace a with b by lia; exact H end
            | |- u64arr _ _ ?a _ => lazymatch type of H with u64arr _ _ ?b _ => replace a with b by lia; exact H end
            | |- bytes_at _ _ ?a _ => lazymatch type of H with bytes_at _ _ ?b _ => replace a with b by lia; exact H end
            | |- stk _ _ ?a ?b => lazymatch type of H with stk _ _ ?a' ?b' => replace a with a' by lia; replace b with b' by lia; exact H end
            end ].

  #[local] Ltac pose_sp_lits :=
    repeat match goal with |- context [Some (Z_to_bv 64 (bv_unsigned (r_sp c) + ?k)%Z)] =>
      lazymatch goal with
      | _ : bv_unsigned (Z_to_bv 64 (bv_unsigned (r_sp c) + k)%Z) = _ |- _ => fail
      | _ => pose proof (unsigned_lit (bv_unsigned (r_sp c) + k)%Z ltac:(lia))
      end end.
  #[local] Ltac rewrite_sp_lits :=
    repeat match goal with U : bv_unsigned (Z_to_bv 64 (bv_unsigned (r_sp c) + ?k)%Z) = _ |- _ => rewrite !U end.
  #[local] Ltac rewrite_sp_lits_all :=
    repeat match goal with U : bv_unsigned (Z_to_bv 64 (bv_unsigned (r_sp c) + ?k)%Z) = _ |- _ => rewrite !U in *; clear U end.

  (* [comment removed for export] *)
  #[using="PRE positive_digit_comp_d_spec negative_digit_comp_d_spec C_23e64"] Lemma uspd_DC : K_23cf4 c.
  Proof. LiaFast.lf_pins (fun (PRE positive_digit_comp_d_spec negative_digit_comp_d_spec C_23e64 : LiaFast.U) => LiaFast.u0).
    unfold K_23e64 in C_23e64.
    unfold K_23cf4. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm am ng k3 kI fp fL X TI PN Hq HX.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ. specialize (Hw eq_refl).
    assert (SQ2 : (bv_signed q = bv_unsigned q \/ bv_signed q = bv_unsigned q - 2^64)%Z)
      by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); lia).
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    (* [comment removed for export] *)
    assert (Jec : forall (T : Z) (v10 v11 v12 v13 v14 : word), (0 <= T <= 19)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 v10 v11 v12 v13 v14 x15 x16 x17
                 am (Zw X) (Zw (bv_signed q + T)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25d50) fc None m (seg_rom USEGS))).
    { intros T v10 v11 v12 v13 v14 HT.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      chunk_split FR 8%nat FRa FRb. chunk_split FRb 4%nat FRs FRc. chunk_split FRc 1%nat FR80 FRd.
      chunk_split FRd 1%nat FRo FRe. chunk_split FRe 1%nat DIG SAV.
      assert (LJ : length (firstn 504 r) = 504%nat) by exact (proj1 (proj1 (proj1 FRo))).
      pose proof (u8arr_of_rw_cells _ _ _ _ _ FRo) as OLD. clear FRo.
      pose_sp_lits. pose proof (unsigned_lit 504 ltac:(lia)) as U504.
      step. (* [comment removed for export] *)
      call memset_spec.
      { reflexivity. }
      { rewrite_sp_lits. exact_at OLD. }
      { rewrite U504, LJ. reflexivity. }
      { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
      rewrite_sp_lits_all. rewrite -> ?U504 in *.
      change (Z.to_nat 504) with 504%nat in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
        lazymatch goal with M : bytes_at _ m' _ (repeat _ _), Wt : wr_at _ m' _ _ |- _ =>
          pose proof (conj M Wt : u8arr USEGS m' _ _) as Z504; clear M Wt; rename m' into m1 end end.
      replace (repeat (Z_to_bv 8 0) 504) with (repeat (Z_to_bv 8 0) (8 * 62) ++ (repeat (Z_to_bv 8 0) 2 ++ repeat (Z_to_bv 8 0) 6))
        in Z504 by reflexivity.
      apply u8arr_app in Z504. destruct Z504 as [ZL Z26]. rewrite repeat_length in Z26.
      apply u8arr_app in Z26. destruct Z26 as [Z2 Z6]. rewrite repeat_length in Z6.
      pose proof (u64arr_of_u8arr USEGS _ _ 62 _ ZL (repeat_length _ _)) as LIMBS. clear ZL.
      rewrite words_of_bytes_zero in LIMBS.
      pose proof (rw_cells_of_u8arr USEGS _ _ _ Z2) as LENC. clear Z2. rewrite repeat_length in LENC.
      apply cb2_c2_zero in LENC.
      pose proof (rw_cells_of_u8arr USEGS _ _ _ Z6) as PAD. clear Z6. rewrite repeat_length in PAD.
      change (Z.of_nat (8 * 62)) with 496%Z in LENC, PAD. change (Z.of_nat 2) with 2%Z in PAD.
      replace (bv_unsigned sp + -704 + 88 + 496)%Z with (bv_unsigned sp + -120)%Z in LENC by lia.
      replace (bv_unsigned sp + -704 + 88 + 496 + 2)%Z with (bv_unsigned sp + -118)%Z in PAD by lia.
      (* [comment removed for export] *)
      set (ibs := firstn (Z.to_nat (kI - k3)) (skipn (Z.to_nat k3) bs)).
      set (fbs := firstn (Z.to_nat fL) (skipn (Z.to_nat (kI + 1)) bs)).
      assert (Libs : Z.of_nat (length ibs) = (kI - k3)%Z).
      { subst ibs. rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. }
      assert (Lfbs : Z.of_nat (length fbs) = fL).
      { subst fbs. destruct Hfp as [[-> ->]|[Hfp1 Hfp2]]; [reflexivity|].
        rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. }
      replace (Zw (kI - k3)) with (Zw (Z.of_nat (length ibs))) in FRs by (f_equal; lia).
      replace (Zw fL) with (Zw (Z.of_nat (length fbs))) in FRs by (f_equal; lia).
      assert (TXi : bytes_at USEGS m1 (bv_unsigned (Zw (P + k3))) ibs).
      { rewrite unsigned_lit by lia. subst ibs. replace (P + k3)%Z with (P + Z.of_nat (Z.to_nat k3))%Z by lia.
        apply bytes_at_slice; [assumption | lia]. }
      assert (TXf : bytes_at USEGS m1 (bv_unsigned (Zw fp)) fbs).
      { destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]].
        - subst fbs. rewrite Hfp1, Hfp2. rewrite unsigned_lit by lia. cbn [Z.to_nat firstn]. apply bytes_at_nil. lia.
        - rewrite unsigned_lit by lia. subst fbs. rewrite Hfp1.
          replace (P + kI + 1)%Z with (P + Z.of_nat (Z.to_nat (kI + 1)))%Z by lia.
          apply bytes_at_slice; [assumption | lia]. }
      replace (bv_unsigned sp + -656)%Z with (bv_unsigned sp + -704 + 16 + 32)%Z in FRs by lia.
      do 4 step. (* [comment removed for export] *)
      pose_sp_lits.
      pose proof (unsigned_lit (bv_unsigned sp + -704) ltac:(lia)) as USP.
      pose proof (unsigned_lit 769 ltac:(lia)) as U769.
      destruct (stk_split _ _ _ (bv_unsigned sp + -704 - 144)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
      assert (LL : length (repeat (Z_to_bv 64 0) 62) = 62%nat) by apply repeat_length.
      step. (* [comment removed for export] *)
      call (parse_mantissa_spec small_mul_spec small_add_spec).
      { rewrite ?USP. exact_at SThi. }
      { rewrite ?USP. Z.div_mod_to_equations. lia. }
      { exact PR1. }
      { rewrite_sp_lits. exact_at LIMBS. }
      { exact LL. }
      { rewrite_sp_lits. exact_at LENC. }
      { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
      { rewrite_sp_lits. exact_at FRs. }
      { exact TXi. }
      { rewrite unsigned_lit by lia. lia. }
      { rewrite unsigned_lit by lia. lia. }
      { lia. }
      { exact TXf. }
      { destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; rewrite Hfp1, ?unsigned_lit by lia; lia. }
      { lia. }
      { intros Hz. destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; [| rewrite Hfp1, unsigned_lit in Hz by lia; exfalso; lia].
        apply (f_equal Z.to_nat) in Lfbs. rewrite Nat2Z.id in Lfbs. rewrite Lfbs, Hfp2. reflexivity. }
      { rewrite U769. lia. }
      { rewrite_sp_lits. exact_at DIG. }
      { rewrite ?USP. lia. }
      { rewrite ?USP. rewrite_sp_lits. lia. }
      { rewrite_sp_lits. lia. }
      { rewrite_sp_lits. lia. }
      { rewrite_sp_lits. rewrite unsigned_lit by lia. lia. }
      { rewrite_sp_lits. intros Hz. destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; rewrite Hfp1, ?unsigned_lit in * by lia; lia. }
      rewrite_sp_lits_all. rewrite -> ?USP, -> ?U769 in *.
      clear LL U504 U769. try clear H.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename m' into m2 end.
      rename MI into ST2. rename PC into LIMBS. rename PC0 into L62. rename PC1 into LENC. rename PC2 into DIG.
      rename PC3 into Hlen. rename PC4 into Hdg. rename PC5 into NORM. rename POST into BVAL.
      lazymatch type of LIMBS with u64arr _ _ _ ?ws => rename ws into ws1 end.
      lazymatch type of Hlen with (0 <= ?l <= 62)%Z => rename l into len1 end.
      lazymatch type of Hdg with (0 <= ?d <= _)%Z => rename d into dg end.
      pose proof (stk_merge _ _ _ _ _ STlo ST2 ltac:(lia)) as ST. clear STlo ST2.
      apply c8_as_c4s in DIG; [|lia].
      step. (* [comment removed for export] *)
      rewrite ?(Z.add_0_r (bv_unsigned (Zw (bv_signed q + T)))). rewrite (swrap32_wordz (bv_signed q + T)) by lia.
      step. (* [comment removed for export] *)
      rewrite (swrap32_wordz_add (bv_signed q + T) 1) by lia.
      step. (* [comment removed for export] *)
      if_cases Hc1; [kill_chk Hc1|]. clear Hc1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?(usx32_small dg) by lia.
      lazymatch goal with |- context [Some (Zw (bv_swrap 32 ?t))] =>
        replace (bv_swrap 32 t) with (bv_signed q + T + 1 - dg)%Z
          by (symmetry; rewrite ?unsigned_lit_wrap; unfold bv_swrap, bv_wrap;
              replace (bv_half_modulus 32) with (2^31)%Z by reflexivity; replace (bv_modulus 32) with (2^32)%Z by reflexivity;
              Z.div_mod_to_equations; lia) end.
      set (e := (bv_signed q + T + 1 - dg)%Z) in |- *.
      assert (He : (-1111 <= e <= 328)%Z) by (subst e; lia).
      assert (Hedg : (0 <= e -> e + dg <= 329)%Z) by (subst e; lia).
      step. (* [comment removed for export] *)
      if_cases Hc2.
      { exfalso. cond_cleanup Hc2. apply Hc2. subst e. rewrite ?unsigned_lit_wrap. Z.div_mod_to_equations. lia. }
      clear Hc2. clearbody e.
      (* [comment removed for export] *)
      assert (Ja0 : forall (m3 : word -> option byte) (ws3 : list word) (len3 : Z)
                           (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
        bytes_at USEGS m3 P bs ->
        rw_cells USEGS m3 SP [CB 16 j16; C8 q; C8 w; C8 lm; C1 (Z_to_bv 8 ng); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); CB 5 j5] ->
        rw_cells USEGS m3 (SP + 16 + 32) [C8 (Zw (P + k3)); C8 (Zw (Z.of_nat (length ibs)));
                                          C8 (Zw fp); C8 (Zw (Z.of_nat (length fbs)))] ->
        rw_cells USEGS m3 (bv_unsigned sp + -624) [C8 (Zw 0)] ->
        u64arr USEGS m3 (bv_unsigned sp + -616) ws3 -> length ws3 = 62%nat ->
        rw_cells USEGS m3 (bv_unsigned sp + -120) [C2 (Zw len3)] ->
        rw_cells USEGS m3 (bv_unsigned sp + -118) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
        rw_cells USEGS m3 (bv_unsigned sp + -112) [C4 (Zw dg); C4 (Zw 0)] ->
        rw_cells USEGS m3 (bv_unsigned sp + -104) (usaves c) ->
        stk USEGS m3 (bv_unsigned sp - (704 + 1872)) SP ->
        rw_cells USEGS m3 V [C8 v] ->
        pristine m3 65536 139264 -> pristine m3 420760 (420760 + 4) ->
        munch [((bv_unsigned sp - (704 + 1872))%Z, bv_unsigned sp); (V, (V + 8)%Z)] mI m3 ->
        wmono USEGS mI m3 ->
        evt USEGS POST
          (MS (mkR v1 (Zw SP) gp tp v5 v6 v7 x8 x9 v10 v11 v12 v13 v14 v15 v16 v17
                   am (Zw X) (Zw (bv_signed q + T + 1)) x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
              F (Zw 0x25e00) fc None m3 (seg_rom USEGS))).
      { intros m3 ws3 len3 v1 v5 v6 v7 y10 y11 y12 y13 y14 y15 y16 y17 v28 v29 v30 v31
               TXT3 FRa3 FRs3 FR803 LIMBS3 L3 LENC3 PAD3 DIG3 SAV3 ST3 VAL3 PR13 PR23 MU3 WM3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (zxb_lit8 ng) by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb. { exfalso. cond_cleanup Hb. lia. }
        clear Hb.
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        pose proof (rw_cells_of_u64arr USEGS _ _ _ LIMBS3) as OBJ. rewrite L3 in OBJ. clear LIMBS3.
        apply c4s_as_c8 in DIG3; [|lia].
        chunk_join FRa3 FRs3 FRb. chunk_join FRb FR803 FRc. chunk_join FRc OBJ FRd.
        chunk_join FRd LENC3 FRe. chunk_join FRe PAD3 FRf. chunk_join FRf DIG3 FRg.
        cbn [app] in FRg.
        goto (eapply (C_23e64 m3 _ j16) with (ng := ng));
          [exact TXT3 | exact FRg | reflexivity | | exact ST3 | exact VAL3 | exact PR13 | exact PR23 | exact MU3 | exact WM3 | lia].
        replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact SAV3. }
      step. (* [comment removed for export] *)
      if_cases Hneg.
      - cond_cleanup Hneg. assert (Hen : (e < 0)%Z) by (rewrite ?signed_lit in Hneg by lia; Z.div_mod_to_equations; lia). clear Hneg.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose_sp_lits. pose proof (unsigned_lit (bv_unsigned sp + -704) ltac:(lia)) as USP.
        rewrite ?(unsigned_lit_wrap (X + 32768)%Z).
        step. (* [comment removed for export] *)
        call negative_digit_comp_d_spec.
        { rewrite ?USP. replace (bv_unsigned sp + -704 - 1872)%Z with (bv_unsigned sp - (704 + 1872))%Z by lia. exact ST. }
        { rewrite ?USP. Z.div_mod_to_equations. lia. }
        { rewrite ?USP. lia. }
        { exact PR1. }
        { rewrite_sp_lits. exact_at LIMBS. }
        { exact L62. }
        { rewrite_sp_lits. exact_at LENC. }
        { exact Hlen. }
        { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
        { rewrite_sp_lits. lia. }
        { exact NORM. }
        { match goal with |- bv_unsigned ?t = (?p mod 2^32)%Z => idtac | |- ?g => idtac "P2GOAL:"; idtac g end.
          instantiate (1 := (X + 32768)%Z).
          first [ apply zx32_shifts
                | rewrite <- (zx32_shifts (X + 32768)%Z); f_equal; apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
                | match goal with |- ?g => idtac "P2FAIL:"; idtac g end ]. }
        { lia. }
        { reflexivity. }
        { lia. }
        { rewrite ?USP. rewrite_sp_lits. lia. }
        rewrite_sp_lits_all. rewrite -> ?USP in *.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
          lazymatch goal with ST3 : stk _ m' _ _, LI : u64arr _ m' _ _, L3 : length _ = 62%nat, LE : rw_cells _ m' (bv_unsigned sp + -616 + 496) _ |- _ =>
            eapply (Ja0 m'); [exact TXT | exact FRa | exact FRs | exact FR80 | exact LI | exact L3 | exact_at LE | exact_at PAD | exact_at DIG | exact_at SAV | exact_at ST3 | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM]
          end end.
      - cond_cleanup Hneg. assert (Hen : (0 <= e)%Z) by (rewrite ?signed_lit in Hneg by lia; Z.div_mod_to_equations; lia). clear Hneg.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose_sp_lits. pose proof (unsigned_lit (bv_unsigned sp + -704) ltac:(lia)) as USP.
        pose proof (unsigned_lit e ltac:(lia)) as UE.
        destruct (stk_split _ _ _ (bv_unsigned sp + -704 - 1360)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
        step. (* [comment removed for export] *)
        call positive_digit_comp_d_spec.
        { rewrite ?USP. exact_at SThi. }
        { rewrite ?USP. Z.div_mod_to_equations. lia. }
        { rewrite ?USP. lia. }
        { exact PR1. }
        { rewrite_sp_lits. exact_at LIMBS. }
        { exact L62. }
        { rewrite_sp_lits. exact_at LENC. }
        { exact Hlen. }
        { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
        { rewrite_sp_lits. lia. }
        { exact NORM. }
        { rewrite UE. lia. }
        { rewrite UE. apply (cap_pos _ dg e); [lia | lia | lia | apply bval_nonneg | exact BVAL]. }
        { rewrite ?USP. rewrite_sp_lits. lia. }
        rewrite_sp_lits_all. rewrite -> ?USP, -> ?UE in *.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
          lazymatch goal with SThi' : stk _ m' (SP - 1360)%Z _, LI : u64arr _ m' _ _, L3 : length _ = 62%nat, LE : rw_cells _ m' (bv_unsigned sp + -616 + 496) _ |- _ =>
            pose proof (stk_merge _ _ _ _ _ STlo SThi' ltac:(lia)) as ST3;
            eapply (Ja0 m'); [exact TXT | exact FRa | exact FRs | exact FR80 | exact LI | exact L3 | exact_at LE | exact_at PAD | exact_at DIG | exact_at SAV | exact_at ST3 | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM]
          end end. }
    (* [comment removed for export] *)
    assert (Jbc : forall (mv d : Z) (v10 v12 v13 v14 : word),
      (1 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z -> (mv < 100)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 v10 (Zw mv) v12 v13 v14 x15 x16 x17
                 am (Zw X) (Zw (bv_signed q + d)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25d20) fc None m (seg_rom USEGS))).
    { intros mv d v10 v12 v13 v14 Hmv1 Hd Hmvd Hmv2.
      pose proof (sci_T_bound mv d (bv_unsigned w) Hmv1 Hd Hmvd ltac:(lia)) as HdT.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H10.
      - cond_cleanup H10. apply Jec. lia.
      - cond_cleanup H10.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite ?(Z.add_0_r (bv_unsigned (Zw (bv_signed q + d)))). rewrite (swrap32_wordz (bv_signed q + d)) by lia.
        step. (* [comment removed for export] *)
        rewrite (swrap32_wordz_add (bv_signed q + d) 1) by lia.
        step. (* [comment removed for export] *)
        if_cases Hc; [kill_chk Hc|]. clear Hc.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite ?(unsigned_lit mv) by lia. rewrite (magic_div10 mv) by lia.
        step. (* [comment removed for export] *)
        if_cases H99; [cond_cleanup H99; exfalso; lia|]. clear H99.
        pose proof (pow10_step mv d 1 (bv_unsigned w) Hd ltac:(lia) ltac:(lia) Hmvd) as HS.
        change (10 ^ 1)%Z with 10%Z in HS.
        goto (apply (Jec (d + 1)%Z)).
        split; [lia|]. eapply (sci_T_bound (mv / 10)); [Z.div_mod_to_equations; lia | lia | exact HS | lia]. }
    (* [comment removed for export] *)
    assert (J7c : forall (mv d : Z) (v11 v12 v13 v14 : word),
      (1 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z -> (mv < 10000)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 (Zw mv) v11 v12 v13 v14 x15 x16 x17
                 am (Zw X) (Zw (bv_signed q + d)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25ce0) fc None m (seg_rom USEGS))).
    { intros mv d v11 v12 v13 v14 Hmv1 Hd Hmvd Hmv4.
      pose proof (sci_T_bound mv d (bv_unsigned w) Hmv1 Hd Hmvd ltac:(lia)) as HdT.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H100.
      - cond_cleanup H100.
        step. (* [comment removed for export] *)
        apply (Jbc mv d); assumption.
      - cond_cleanup H100.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite ?(Z.add_0_r (bv_unsigned (Zw (bv_signed q + d)))). rewrite (swrap32_wordz (bv_signed q + d)) by lia.
        step. (* [comment removed for export] *)
        rewrite (swrap32_wordz_add (bv_signed q + d) 2) by lia.
        step. (* [comment removed for export] *)
        if_cases Hc; [kill_chk Hc|]. clear Hc.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite ?(unsigned_lit mv) by lia. rewrite (magic_div100 mv) by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (pow10_step mv d 2 (bv_unsigned w) Hd ltac:(lia) ltac:(lia) Hmvd) as HS.
        change (10 ^ 2)%Z with 100%Z in HS.
        step. (* [comment removed for export] *)
        if_cases H624.
        + cond_cleanup H624. rewrite ?Z.shiftr_div_pow2 in H624 by lia.
          goto (apply (Jbc (mv / 100)%Z (d + 2)%Z)).
          * Z.div_mod_to_equations; lia.
          * lia.
          * exact HS.
          * Z.div_mod_to_equations; lia.
        + cond_cleanup H624. exfalso. rewrite ?Z.shiftr_div_pow2 in H624 by lia.
          rewrite ?unsigned_lit in H624 by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
    idtac "MARK-J7c-done".
    (* [comment removed for export] *)
    assert (L1 : forall (k : nat) (mv d : Z) (v13 v14 : word),
      (mv < 10000 ^ Z.of_nat k)%Z -> (10000 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 (Zw mv) (Zw 3777893186295716171) (Zw 99999999) v13 v14 x15 x16 x17
                 am (Zw X) (Zw (bv_signed q + d)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x25cc4) fc None m (seg_rom USEGS))).
    { induction k as [|k IH]; intros mv d v13 v14 Hk Hmv4 Hd Hmvd.
      { exfalso. cbn in Hk. lia. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hk by lia.
      pose proof (sci_T_bound mv d (bv_unsigned w) ltac:(lia) Hd Hmvd ltac:(lia)) as HdT.
      assert (Rmv : (mv < 2^64)%Z).
      { assert (0 < 10 ^ d)%Z by (apply Z.pow_pos_nonneg; lia). nia. }
      step. (* [comment removed for export] *)
      rewrite ?(Z.add_0_r (bv_unsigned (Zw (bv_signed q + d)))). rewrite (swrap32_wordz (bv_signed q + d)) by lia.
      step. (* [comment removed for export] *)
      rewrite (swrap32_wordz_add (bv_signed q + d) 4) by lia.
      step. (* [comment removed for export] *)
      if_cases Hc; [kill_chk Hc|]. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit mv) by lia. rewrite (magic_div10000 mv) by lia.
      pose proof (pow10_step mv d 4 (bv_unsigned w) Hd ltac:(lia) ltac:(lia) Hmvd) as HS.
      change (10 ^ 4)%Z with 10000%Z in HS.
      step. (* [comment removed for export] *)
      if_cases Hbig.
      - cond_cleanup Hbig.
        goto (apply (IH (mv / 10000)%Z (d + 4)%Z)).
        + Z.div_mod_to_equations; nia.
        + Z.div_mod_to_equations; lia.
        + lia.
        + exact HS.
      - cond_cleanup Hbig.
        goto (apply (J7c (mv / 10000)%Z (d + 4)%Z)).
        + Z.div_mod_to_equations; lia.
        + lia.
        + exact HS.
        + Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsmall.
    - cond_cleanup Hsmall. rewrite Z.shiftr_div_pow2 in Hsmall by lia.
      goto (apply (J7c (bv_unsigned w) 0%Z)).
      + lia. + lia. + change (10 ^ 0)%Z with 1%Z. lia. + Z.div_mod_to_equations; lia.
    - cond_cleanup Hsmall. rewrite Z.shiftr_div_pow2 in Hsmall by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (apply (L1 5%nat (bv_unsigned w) 0%Z)).
      + change (10000 ^ Z.of_nat 5)%Z with (10^20)%Z. lia.
      + Z.div_mod_to_equations; lia.
      + lia.
      + change (10 ^ 0)%Z with 1%Z. lia.
  Qed.
End BLK.
