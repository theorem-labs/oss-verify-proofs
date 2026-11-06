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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_slow_path_float_stmt U_spf_common.

Module U_spf_commonT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export U_spf_common.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).
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
    /\ rw_cells USEGS m V [C4 v]
    /\ pristine m 0x10000 0x22000
    /\ pristine m U_FMIN (U_FMIN + 4)
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
  Definition K_2810c : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm : Z),
      tinv (frameT j16 q w lm ng tm j5 k3 kI fp fL [CB 520 r]) m -> pnsok ng k3 kI fp fL tm w ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w (Zw ng) (Zw 1) (Zw tm) x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a0c0) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_28128 : Prop :=
    forall m (cells : list cell)
           (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q : word) (ng : Z),
      bytes_at USEGS m P bs ->
      rw_cells USEGS m SP cells -> Z.of_nat (cells_size cells) = 600%Z ->
      rw_cells USEGS m (SP + 600)%Z (usaves c) ->
      stk USEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m V [C4 v] ->
      pristine m 0x10000 0x22000 -> pristine m U_FMIN (U_FMIN + 4) ->
      munch W mI m -> wmono USEGS mI m ->
      (0 <= ng <= 1)%Z -> (-10 <= bv_signed q <= 10)%Z -> (bv_unsigned w <= 2^24)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w (Zw ng) x12 x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a0dc) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_2819c : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm : Z),
      tinv (frameT j16 q w lm ng tm j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL tm w ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w (Zw ng) x12 (Zw tm) x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a150) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_283a4 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am ap : word) (ng k3 kI fp fL : Z),
      tinv (frameT j16 q w lm ng 1 j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (bv_signed q < -64 -> am = Zw 0 /\ ap = Zw 0)%Z ->
      (38 < bv_signed q -> am = Zw 0 /\ ap = Zw 255)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w (Zw ng) x12 x13 x14 x15 x16 x17
                 ap am q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a358) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_285f8 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL : Z),
      tinv (frameT j16 q w lm ng 1 j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (-64 <= bv_signed q <= 38)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w (Zw ng) x12 x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a5ac) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_28744 : Prop :=
    forall m (r : list byte) (j16 j5 : list byte)
           (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am : word) (ng k3 kI fp fL X : Z),
      tinv (frameT j16 q w lm ng 1 j5 k3 kI fp fL [C8 (Zw 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (-64 <= bv_signed q <= 38)%Z -> (-34100 <= X <= -31500)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 w x11 x12 x13 x14 x15 x16 x17
                 (Zw X) am q x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a6f8) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_288b4 : Prop :=
    forall m (cells : list cell) (j16 : list byte)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q : word),
      bytes_at USEGS m P bs ->
      rw_cells USEGS m SP ([CB 16 j16; C8 q; C8 w] ++ cells) -> Z.of_nat (cells_size cells) = 568%Z ->
      rw_cells USEGS m (SP + 600)%Z (usaves c) ->
      stk USEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m V [C4 v] ->
      pristine m 0x10000 0x22000 -> pristine m U_FMIN (U_FMIN + 4) ->
      munch W mI m -> wmono USEGS mI m ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a868) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_288f4 : Prop :=
    forall m (cells : list cell) (F' : bvmap 5 word) (fc' : bv 32) (v' : word)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      frm0 fc' ->
      rw_cells USEGS m SP cells -> Z.of_nat (cells_size cells) = 600%Z ->
      rw_cells USEGS m (SP + 600)%Z (usaves c) ->
      stk USEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m V [C4 v'] ->
      munch W mI m -> wmono USEGS mI m ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F' (Zw 0x2a8a8) fc' None m (seg_rom USEGS)).

End CTX.
End U_spf_commonT.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_positive_digit_comp_f_stmt U_negative_digit_comp_f_stmt U_spf_parse.

Module U_spf_T0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spf_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    cbv beta delta [frameT usaves app] in FR;
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
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_2810c : K_2810c c.

  (* [comment removed for export] *)
  #[using="PRE C_2810c"] Lemma uspf_T0 : K_28084 c.
  Proof. LiaFast.lf_pins (fun (PRE C_2810c : LiaFast.U) => LiaFast.u0).
    unfold K_2810c in C_2810c.
    unfold K_28084. intros junk m x1 x5 x6 x7 x8 x11 x16 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 w q k3 kI fp fL kq tm
      PINV K3I K31 FL0 KQ FP TM TW.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    pose proof (tx_range bs 0) as R0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite v_sltiu_b2z.
    lazymatch goal with |- context [Zw (Z.b2z ?b)] =>
      pose proof (b2z_range b) as NG; set (ng := Z.b2z b) in *; clearbody ng end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit ng), (unsigned_lit 1), (unsigned_lit tm) in FR by lia.
    eapply C_2810c with (ng := ng) (k3 := k3) (kI := kI) (fp := fp) (fL := fL) (tm := tm).
    - split; [exact TXT|]. split; [cbv beta delta [frameT usaves app]; exact FR|].
      split; [unfold slow_path_float_need; exact ST|]. split; [exact VAL|].
      split; [exact PR1|]. split; [unfold U_FMIN; exact PR2|]. split; [exact MU | exact WM].
    - unfold pnsok. repeat split; try lia; intros H1; apply TW; exact H1.
  Qed.
End BLK.
End U_spf_T0.


Module U_spf_TD.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spf_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    cbv beta delta [frameT usaves app] in FR;
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
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_28128 : K_28128 c.
  Hypothesis C_2819c : K_2819c c.

  (* [comment removed for export] *)
  #[using="PRE C_28128 C_2819c"] Lemma uspf_TD : K_2810c c.
  Proof. LiaFast.lf_pins (fun (PRE C_28128 C_2819c : LiaFast.U) => LiaFast.u0).
    unfold K_28128 in C_28128. unfold K_2819c in C_2819c.
    unfold K_2810c. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL tm TI PN.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      assert (TI2 : tinv c (frameT c j16 q w lm ng tm j5 k3 kI fp fL [C8 (Zw 0); CB 512 (skipn 8 r)]) m')
        by (split; [exact TXT|]; split; [cbv beta delta [frameT usaves app]; exact FR|];
            split; [unfold slow_path_float_need; exact ST|]; split; [exact VAL|];
            split; [exact PR1|]; split; [unfold U_FMIN; exact PR2|]; split; [exact MU | exact WM]) end.
    step. (* [comment removed for export] *)
    if_cases Htm3.
    { eapply C_2819c; [exact TI2 | exact PN]. }
    cond_cleanup Htm3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hq11.
    { eapply C_2819c; [exact TI2 | exact PN]. }
    cond_cleanup Hq11.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw24.
    { eapply C_2819c; [exact TI2 | exact PN]. }
    cond_cleanup Hw24.
    clear TI2. chunk_split FR 14%nat FRl FRh.
    eapply C_28128; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM
                    | lia | | lia].
    - replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh.
    - (* [comment removed for export] *)
      rewrite SQ. destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
  Qed.
End BLK.
End U_spf_TD.


Module U_spf_CL.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spf_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    cbv beta delta [frameT usaves app] in FR;
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
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_288f4 : K_288f4 c.

  (* [comment removed for export] *)
  #[using="PRE C_288f4"] Lemma uspf_CL : K_28128 c.
  Proof. LiaFast.lf_pins (fun (PRE C_288f4 : LiaFast.U) => LiaFast.u0).
    unfold K_288f4 in C_288f4.
    unfold K_28128. intros m cells x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q ng TXT FRl SZ FRh ST VAL PR1 PR2 MU WM NG Hq Hw.
    pre_facts. unfold slow_path_float_need in ST. unfold U_FMIN in PR2.
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU. cbv beta delta [usaves] in FRh.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- context [feq_s ?a ?b] => replace (feq_s a b) with true by (vm_compute; reflexivity) end.
    step. (* [comment removed for export] *)
    if_false.
    (* [comment removed for export] *)
    assert (TAIL : forall (m' : word -> option byte) (v' : word) (Fq : bvmap 5 word) (fcq : bv 32) (xa0 xa2 xa3 xs4 : word),
      frm0 fcq -> rw_cells USEGS m' SP cells -> rw_cells USEGS m' (bv_unsigned sp + -104)%Z (usaves c) ->
      stk USEGS m' (bv_unsigned sp - (704 + 1872)) SP -> rw_cells USEGS m' V [C4 v'] ->
      munch [((bv_unsigned sp - (704 + 1872))%Z, bv_unsigned sp); (V, (V + 4)%Z)] mI m' -> wmono USEGS mI m' ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 xa0 (Zw ng) xa2 xa3 x14 x15 x16 x17
                 x18 x19 xs4 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            Fq (Zw 0x2a820) fcq None m' (seg_rom USEGS))).
    { intros m' v' Fq fcq xa0 xa2 xa3 xs4 FRMq FRl' FRh' ST' VAL' MU' WM'. cbv beta delta [usaves] in FRh'.
      pose proof (rw_cells_bound _ _ _ _ VAL') as Bval'. cbn [cells_size csize Nat.add] in Bval'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsgn.
      - eapply C_288f4; [exact FRMq | exact FRl' | exact SZ | | exact ST' | | exact MU' | exact WM'].
        + replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh'.
        + match goal with H : rw_cells _ _ ?a [C4 _] |- rw_cells _ _ _ [C4 _] => replace a with V in H by lia; exact H end.
      - step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply C_288f4; [exact FRMq | exact FRl' | exact SZ | | exact ST' | | exact MU' | exact WM'].
        + replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh'.
        + match goal with H : rw_cells _ _ ?a [C4 _] |- rw_cells _ _ _ [C4 _] => replace a with V in H by lia; exact H end. }
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z in FRh by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hneg.
    - cond_cleanup Hneg.
      assert (QS : (bv_signed q = bv_unsigned q - 2^64)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.shiftl_mul_pow2 in Hov by lia; Z.div_mod_to_equations; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      replace (Zw (89384 + bv_unsigned (Zw (0 - bv_unsigned q)) * 2 ^ 2))
        with (Zw (89384 + 4 * (2^64 - bv_unsigned q)))
        by (rewrite unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
      lazymatch goal with H : pristine _ 65536 139264 |- _ =>
        pose proof (table_read USEGS _ _ _ _ _ _ _ TBLF_ok H ltac:(lia) ltac:(cbn; lia) (2^64 - bv_unsigned q)%Z ltac:(cbn; lia)) as RD end.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply TAIL; [exact FRM | exact FRl | exact FRh | exact ST | | exact MU | exact WM].
      match goal with H : rw_cells _ _ ?a [C4 _] |- rw_cells _ _ _ [C4 _] => replace a with V in H by lia; exact H end.
    - cond_cleanup Hneg.
      assert (QS : (bv_signed q = bv_unsigned q)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.shiftl_mul_pow2 in Hov by lia; Z.div_mod_to_equations; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      replace (Zw (89384 + bv_unsigned (Zw (bv_unsigned q * 2 ^ 2))))
        with (Zw (89384 + 4 * bv_unsigned q))
        by (rewrite unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
      lazymatch goal with H : pristine _ 65536 139264 |- _ =>
        pose proof (table_read USEGS _ _ _ _ _ _ _ TBLF_ok H ltac:(lia) ltac:(cbn; lia) (bv_unsigned q) ltac:(cbn; lia)) as RD end.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply TAIL; [exact FRM | exact FRl | exact FRh | exact ST | | exact MU | exact WM].
      match goal with H : rw_cells _ _ ?a [C4 _] |- rw_cells _ _ _ [C4 _] => replace a with V in H by lia; exact H end.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_288f4"] Lemma uspf_ERRCL : K_28114e c.
  Proof. LiaFast.lf_pins (fun (PRE C_288f4 : LiaFast.U) => LiaFast.u0).
    unfold K_28114e. intros junk m x1 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hr; [exfalso; revert Hr; vm_compute; congruence|]. clear Hr.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hm; [exfalso; revert Hm; vm_compute; congruence|]. clear Hm.
    chunk_split FR 1%nat FRl FRh.
    eapply (uspf_CL m [CB 600 junk]) with (ng := 0%Z);
      [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM
      | lia | rewrite signed_lit by lia; lia | rewrite unsigned_lit by lia; lia].
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh.
  Qed.
End BLK.
End U_spf_CL.


Module U_spf_PK.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spf_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    cbv beta delta [frameT usaves app] in FR;
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
    end.
  #[local] Ltac gstep := step; gen_big.

  #[using="PRE"] Lemma uspf_EPI : K_288f4 c.
  Proof. LiaFast.lf_pins (fun (PRE : LiaFast.U) => LiaFast.u0).
    unfold K_288f4. intros m cells F' fc' v' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 FRM' FRl SZ FRh ST VAL MU WM.
    pre_facts. cbv beta delta [usaves] in FRh. cbv beta delta [slow_path_float_W slow_path_float_need] in MU.
    unfold slow_path_float_need in ST.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z in FRh by lia.
    step. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply stk_release in FRl; [ | exact ST | lia ]. rewrite SZ in FRl. clear ST.
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z in FRl by lia.
    eapply stk_release in FRh; [ | exact FRl | lia ]. cbn [cells_size csize Nat.add] in FRh. clear FRl.
    replace (bv_unsigned sp + -104 + Z.of_nat 104)%Z with (bv_unsigned sp) in FRh by lia.
    unfold slow_path_float_post. finish.
    all: try (unfold slow_path_float_need; exact FRh).
    all: try exact VAL.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE"] Lemma uspf_PK : K_288b4 c.
  Proof. LiaFast.lf_pins (fun (PRE : LiaFast.U) => LiaFast.u0).
    unfold K_288b4. intros m cells j16 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 w q TXT FRl SZ FRh ST VAL PR1 PR2 MU WM.
    pre_facts. unfold slow_path_float_need in ST. unfold U_FMIN in PR2.
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    cbv beta delta [usaves] in FRh. cbn [app] in FRl.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      lazymatch goal with FR2 : rw_cells _ m' (bv_unsigned sp + -704) ?cs |- _ =>
        eapply (uspf_EPI m' cs); [exact FRM | exact FR2 | cbn [cells_size csize Nat.add app]; cbn [cells_size csize Nat.add] in SZ; lia
                                 | | exact ST | | exact MU | exact WM]
      end end.
    all: try (replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; first [exact FRh | assumption]).
    all: try assumption.
    all: match goal with H : rw_cells _ _ ?a [C4 _] |- rw_cells _ _ _ [C4 _] => replace a with V in H by lia; exact H end.
  Qed.
End BLK.
End U_spf_PK.


Module U_spf_CF1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spf_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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

  Hypothesis C_283a4 : K_283a4 c.
  Hypothesis C_288b4 : K_288b4 c.

  (* [comment removed for export] *)
  #[local] Ltac exitPK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -704) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 420760 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 14%nat FRl FRh;
    eapply C_288b4; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM];
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.

  (* [comment removed for export] *)
  #[using="PRE C_283a4 C_288b4"] Lemma uspf_CF1 : K_2819c c.
  Proof. LiaFast.lf_pins (fun (PRE C_283a4 C_288b4 : LiaFast.U) => LiaFast.u0).
    unfold K_283a4 in C_283a4. unfold K_288b4 in C_288b4.
    unfold K_2819c. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL tm TI PN.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    (* [comment removed for export] *)
    assert (XF2 : forall (v5 v6 v7 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 am ap : word), tm = 1%Z ->
      (bv_signed q < -64 -> am = Zw 0 /\ ap = Zw 0)%Z -> (38 < bv_signed q -> am = Zw 0 /\ ap = Zw 255)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 v13 v14 v15 v16 v17
                 ap am q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a358) fc None m (seg_rom USEGS))).
    { intros until am. intros ap Htm1 H1 H2. subst tm. eapply C_283a4; [exact TI | exact PN | exact H1 | exact H2]. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw0.
    { cond_cleanup Hw0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Htm1. { cond_cleanup Htm1. exfalso. lia. }
      step. (* [comment removed for export] *)
      exitPK. }
    cond_cleanup Hw0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqlo.
    { cond_cleanup Hqlo.
      step. (* [comment removed for export] *)
      if_cases Htm0.
      - exitPK.
      - cond_cleanup Htm0. apply XF2; [lia | intros _; split; reflexivity | intros HH; exfalso; lia]. }
    cond_cleanup Hqlo.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqhi.
    2:{ cond_cleanup Hqhi.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Htm1.
      - cond_cleanup Htm1. apply XF2; [lia | intros HH; exfalso; lia | intros _; split; reflexivity].
      - step. (* [comment removed for export] *)
        exitPK. }
    cond_cleanup Hqhi.
    (* [comment removed for export] *)
    assert (XF2' : forall (v5 v6 v7 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 am ap : word), tm = 1%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 v13 v14 v15 v16 v17
                 ap am q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a358) fc None m (seg_rom USEGS))).
    { intros. apply XF2; [assumption | intros HH; exfalso; lia | intros HH; exfalso; lia]. }
    clear XF2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (ucf_idx q) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 684) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5472)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    gstep. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 684)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    step. (* [comment removed for export] *)
    clear RD1.
    do 6 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J2c4 : forall v5 v6 v7 v12 v14 v15 v16 v17 v28 v29 v30 v31 : word,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 (Zw tm) v14 v15 v16 v17
                 (Zw 0) (Zw 0) q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a278) fc None m (seg_rom USEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnorm.
      - clear Hnorm. (* [comment removed for export] *)
        do 12 gstep. (* [comment removed for export] *)
        (* [comment removed for export] *)
        assert (J350 : forall u12 u14 u15 u16 u17 u5 : word,
          evt USEGS POST
            (MS (mkR x1 (Zw SP) gp tp u5 v6 v7 x8 x9 w (Zw ng) u12 (Zw tm) u14 u15 u16 u17
                     (Zw 0) (Zw 0) q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
                F (Zw 0x2a304) fc None m (seg_rom USEGS))).
        { intros.
          do 13 gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hinf.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_cases Htm0; [exitPK|]. cond_cleanup Htm0. apply XF2'. lia.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_cases Htm0; [exitPK|]. cond_cleanup Htm0. apply XF2'. lia. }
        step. (* [comment removed for export] *)
        if_cases Hre.
        + clear Hre. apply J350.
        + clear Hre.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          apply J350.
      - clear Hnorm. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh.
          step. (* [comment removed for export] *)
          do 7 gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htm1.
          * cond_cleanup Htm1. apply XF2'. lia.
          * step. (* [comment removed for export] *) exitPK.
        + clear Hsh.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htm1.
          * cond_cleanup Htm1. apply XF2'. lia.
          * step. (* [comment removed for export] *) exitPK. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply J2c4. }
    clear Hlow.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    replace (Z.lor (16 * bv_signed q + 5472) 8) with (16 * bv_signed q + 5480)%Z
      by (replace (16 * bv_signed q + 5472)%Z with (16 * (bv_signed q + 342))%Z by lia; rewrite lor_16k_8 by lia; lia).
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia.
    replace (Z.lor (2 * bv_signed q + 684) 1) with (2 * bv_signed q + 685)%Z
      by (replace (2 * bv_signed q + 684)%Z with (2 * (bv_signed q + 342))%Z by lia; rewrite lor_2k_1 by lia; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 685)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 685) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5480)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5480)%Z) by lia.
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 685)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    step. (* [comment removed for export] *)
    clear RD2.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply J2c4.
  Qed.
End BLK.
End U_spf_CF1.


Module U_spf_CF2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spf_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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

  Hypothesis C_285f8 : K_285f8 c.
  Hypothesis C_288b4 : K_288b4 c.

  #[local] Ltac exitPK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -704) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 420760 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 14%nat FRl FRh;
    eapply C_288b4; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM];
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.

  (* [comment removed for export] *)
  #[using="PRE C_285f8 C_288b4"] Lemma uspf_CF2 : K_283a4 c.
  Proof. LiaFast.lf_pins (fun (PRE C_285f8 C_288b4 : LiaFast.U) => LiaFast.u0).
    unfold K_285f8 in C_285f8. unfold K_288b4 in C_288b4.
    unfold K_283a4. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm am ap ng k3 kI fp fL TI PN Hlo Hhi.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ. specialize (Hw eq_refl).
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    (* [comment removed for export] *)
    assert (XCE : forall (v5 v6 v7 v12 v13 v14 v15 v16 v17 v18 v19 v28 v29 v30 v31 : word),
      (-64 <= bv_signed q <= 38)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 v13 v14 v15 v16 v17
                 v18 v19 q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a5ac) fc None m (seg_rom USEGS))).
    { intros. eapply C_285f8; [exact TI | exact PN | assumption]. }
    (* [comment removed for export] *)
    assert (CMP4 : forall (v5 v6 v7 v12 v15 v16 v17 v28 v29 v30 v31 bm bp : word),
      ((am <> bm \/ ap <> bp) -> -64 <= bv_signed q <= 38)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 bp bm v15 v16 v17
                 ap am q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a5a8) fc None m (seg_rom USEGS))).
    { intros until bm. intros bp Hrg.
      step. (* [comment removed for export] *)
      if_cases Heq.
      - exitPK.
      - cond_cleanup Heq. apply XCE. apply Hrg. right. intros E'. apply Heq. rewrite E'. reflexivity. }
    assert (CMP0 : forall (v5 v6 v7 v12 v15 v16 v17 v28 v29 v30 v31 bm bp : word),
      ((am <> bm \/ ap <> bp) -> -64 <= bv_signed q <= 38)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 bp bm v15 v16 v17
                 ap am q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a5a4) fc None m (seg_rom USEGS))).
    { intros until bm. intros bp Hrg.
      step. (* [comment removed for export] *)
      if_cases Hne.
      - cond_cleanup Hne. apply XCE. apply Hrg. left. intros E'. apply Hne. rewrite E'. reflexivity.
      - apply CMP4. exact Hrg. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw1. { cond_cleanup Hw1. exfalso. Z.div_mod_to_equations. lia. }
    cond_cleanup Hw1. rewrite ?(unsigned_lit (bv_unsigned w + 1)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqlo.
    { cond_cleanup Hqlo. destruct (Hlo ltac:(lia)) as [-> ->].
      apply CMP0. intros [HH|HH]; exfalso; apply HH; reflexivity. }
    cond_cleanup Hqlo.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqhi.
    2:{ cond_cleanup Hqhi. destruct (Hhi ltac:(lia)) as [-> ->].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; [| cond_cleanup Hz; exfalso; apply Hz; reflexivity].
      apply CMP4. intros [HH|HH]; exfalso; apply HH; reflexivity. }
    cond_cleanup Hqhi. clear Hlo Hhi.
    (* [comment removed for export] *)
    assert (W1 : (0 <= bv_unsigned w + 1 < 2^64)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (ucf_idx q) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 684) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5472)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    gstep. (* [comment removed for export] *)
    do 3 step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    step. step. (* [comment removed for export] *)
    do 3 gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 684)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    step. (* [comment removed for export] *)
    clear RD1.
    do 3 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J4c8 : forall v5 v6 v7 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 v13 v14 v15 v16 v17
                 ap am q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a47c) fc None m (seg_rom USEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnorm.
      - clear Hnorm. (* [comment removed for export] *)
        do 12 gstep.
        assert (J5a0 : forall u12 u13 u14 u15 u16 u17 u5 : word,
          evt USEGS POST
            (MS (mkR x1 (Zw SP) gp tp u5 v6 v7 x8 x9 w (Zw ng) u12 u13 u14 u15 u16 u17
                     ap am q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
                F (Zw 0x2a554) fc None m (seg_rom USEGS))).
        { intros.
          do 13 gstep.
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hinf.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            apply CMP0. intros; lia.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            apply CMP0. intros; lia. }
        step. (* [comment removed for export] *)
        if_cases Hre.
        + clear Hre. apply J5a0.
        + clear Hre.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          apply J5a0.
      - clear Hnorm. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh.
          step. (* [comment removed for export] *)
          do 7 gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases He1.
          * apply CMP4. intros; lia.
          * step. (* [comment removed for export] *) apply XCE. lia.
        + clear Hsh.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases He1.
          * apply CMP4. intros; lia.
          * step. (* [comment removed for export] *) apply XCE. lia. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply J4c8. }
    clear Hlow.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    replace (Z.lor (16 * bv_signed q + 5472) 8) with (16 * bv_signed q + 5480)%Z
      by (replace (16 * bv_signed q + 5472)%Z with (16 * (bv_signed q + 342))%Z by lia; rewrite lor_16k_8 by lia; lia).
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia.
    replace (Z.lor (2 * bv_signed q + 684) 1) with (2 * bv_signed q + 685)%Z
      by (replace (2 * bv_signed q + 684)%Z with (2 * (bv_signed q + 342))%Z by lia; rewrite lor_2k_1 by lia; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 685)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 685) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5480)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5480)%Z) by lia.
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 685)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    step. (* [comment removed for export] *)
    clear RD2.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply J4c8.
  Qed.
End BLK.
End U_spf_CF2.


Module U_spf_CE.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spf_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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

  Hypothesis C_28744 : K_28744 c.
  Hypothesis C_288b4 : K_288b4 c.

  #[local] Ltac exitPK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -704) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 420760 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 14%nat FRl FRh;
    eapply C_288b4; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM];
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.

  (* [comment removed for export] *)
  #[using="PRE C_28744 C_288b4"] Lemma uspf_CE : K_285f8 c.
  Proof. LiaFast.lf_pins (fun (PRE C_28744 C_288b4 : LiaFast.U) => LiaFast.u0).
    unfold K_28744 in C_28744. unfold K_288b4 in C_288b4.
    unfold K_285f8. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL TI PN Hq.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ. specialize (Hw eq_refl).
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *)
    if_cases Hw0; [cond_cleanup Hw0; exfalso; lia|]. clear Hw0.
    step. (* [comment removed for export] *)
    rewrite (q342_word q).
    step. (* [comment removed for export] *)
    if_cases Hc1; [kill_chk Hc1|]. clear Hc1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (bv_signed q + 342)%Z) by lia. rewrite (swrap32_small (bv_signed q + 342 + 1073741824)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hc2; [kill_chk Hc2|]. clear Hc2.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (bv_signed q + 342)%Z) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    rewrite (swrap32_small ((bv_signed q + 342) * 2 ^ 1)%Z) by lia.
    replace (Zw ((bv_signed q + 342) * 2 ^ 1)) with (Zw (2 * bv_signed q + 684)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc3; [cond_cleanup Hc3; exfalso; rewrite ?Z.mod_small in Hc3 by lia; lia|]. clear Hc3.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 684) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5472)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    gstep. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 684)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    step. (* [comment removed for export] *)
    clear RD1.
    do 5 gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- context [Some (Zw (Z.shiftr (bv_unsigned ?rv) 56))] =>
      pose proof (bv_unsigned_in_range 64 rv) as Rlz; unfold bv_modulus in Rlz;
      remember (Z.shiftr (bv_unsigned rv) 56) as lz eqn:Hlz end.
    assert (LZ : (0 <= lz < 256)%Z) by (subst lz; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    clear Hlz Rlz.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J704 : forall v5 v6 v7 v12 v13 v14 v15 v28 v29 v30 v31 hi : word,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw ng) v12 v13 v14 v15 hi (Zw lz)
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x2a6b8) fc None m (seg_rom USEGS))).
    { intros.
      pose proof (bv_unsigned_in_range 64 hi) as Rhi. unfold bv_modulus in Rhi.
      step. (* [comment removed for export] *)
      rewrite (Z.add_0_r (bv_unsigned q)). rewrite (swrap32_unsigned q) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc4.
      { exfalso. cond_cleanup Hc4. apply Hc4. unfold bv_swrap, bv_wrap.
        replace (bv_half_modulus 32) with (2^31)%Z by reflexivity. replace (bv_modulus 32) with (2^32)%Z by reflexivity.
        Z.div_mod_to_equations. lia. }
      clear Hc4.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Zw (bv_swrap 32 (Z.shiftr ?t 16)))] =>
        remember (bv_swrap 32 (Z.shiftr t 16)) as A eqn:HAe end.
      first [ pose proof (uce_A_range q ltac:(lia)) as HA; rewrite <- HAe in HA
            | pose proof (uce_A_range' q ltac:(lia)) as HA; rewrite <- HAe in HA
            | match type of HAe with ?ty => idtac "AFORM:" ty end ].
      clear HAe.
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit lz) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Zw (Z.shiftr (bv_unsigned ?rv) 63))] =>
        pose proof (bv_unsigned_in_range 64 rv) as Rhz; unfold bv_modulus in Rhz;
        remember (Z.shiftr (bv_unsigned rv) 63) as hz eqn:Hhz end.
      assert (HZ : (0 <= hz <= 1)%Z) by (subst hz; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
      clear Hhz Rhz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit hz) by lia.
      lazymatch goal with |- context [Some (Zw (bv_unsigned ?t - hz)%Z)] =>
        replace (Zw (bv_unsigned t - hz)%Z) with (Zw (A - lz - 32617 - hz))
          by (apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia)
      | |- ?g => idtac "SUB2FORM"; idtac g end.
      step. (* [comment removed for export] *)
      repeat match goal with |- context [Some (Zw (Z.shiftl ?a ?b))] => gen_val (Zw (Z.shiftl a b)) end.
      step. (* [comment removed for export] *)
      if_cases Hpos.
      - exitPK.
      - eapply C_28744; [exact TI | exact PN | exact Hq | lia]. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply J704. }
    clear Hlow.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    replace (Z.lor (16 * bv_signed q + 5472) 8) with (16 * bv_signed q + 5480)%Z
      by (replace (16 * bv_signed q + 5472)%Z with (16 * (bv_signed q + 342))%Z by lia; rewrite lor_16k_8 by lia; lia).
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia.
    replace (Z.lor (2 * bv_signed q + 684) 1) with (2 * bv_signed q + 685)%Z
      by (replace (2 * bv_signed q + 684)%Z with (2 * (bv_signed q + 342))%Z by lia; rewrite lor_2k_1 by lia; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 685)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 685) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5480)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5480)%Z) by lia.
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 685)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    step. (* [comment removed for export] *)
    clear RD2.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply J704.
  Qed.
End BLK.
End U_spf_CE.


Module U_spf_DC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spf_tbl U_memset.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_parse_mantissa.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_small_add U_parse_mantissa U_positive_digit_comp_f_stmt U_negative_digit_comp_f_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_tbl OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_small_mul OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_small_add OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_negative_digit_comp_f_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
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
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
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
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
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

  Hypothesis positive_digit_comp_f_spec : positive_digit_comp_f_stmt.
  Hypothesis negative_digit_comp_f_spec : negative_digit_comp_f_stmt.
  Hypothesis C_288b4 : K_288b4 c.

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
  #[using="PRE positive_digit_comp_f_spec negative_digit_comp_f_spec C_288b4"] Lemma uspf_DC : K_28744 c.
  Proof. LiaFast.lf_pins (fun (PRE positive_digit_comp_f_spec negative_digit_comp_f_spec C_288b4 : LiaFast.U) => LiaFast.u0).
    unfold K_288b4 in C_288b4.
    unfold K_28744. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
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
                 (Zw X) am (Zw (bv_signed q + T)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a7a0) fc None m (seg_rom USEGS))).
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
      pose proof (unsigned_lit 114 ltac:(lia)) as U114.
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
      { rewrite U114. lia. }
      { rewrite_sp_lits. exact_at DIG. }
      { rewrite ?USP. lia. }
      { rewrite ?USP. rewrite_sp_lits. lia. }
      { rewrite_sp_lits. lia. }
      { rewrite_sp_lits. lia. }
      { rewrite_sp_lits. rewrite unsigned_lit by lia. lia. }
      { rewrite_sp_lits. intros Hz. destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; rewrite Hfp1, ?unsigned_lit in * by lia; lia. }
      rewrite_sp_lits_all. rewrite -> ?USP, -> ?U114 in *.
      clear LL U504 U114. try clear H.
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
      assert (He : (-200 <= e <= 60)%Z) by (subst e; lia).
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
        rw_cells USEGS m3 V [C4 v] ->
        pristine m3 65536 139264 -> pristine m3 420760 (420760 + 4) ->
        munch [((bv_unsigned sp - (704 + 1872))%Z, bv_unsigned sp); (V, (V + 4)%Z)] mI m3 ->
        wmono USEGS mI m3 ->
        evt USEGS POST
          (MS (mkR v1 (Zw SP) gp tp v5 v6 v7 x8 x9 v10 v11 v12 v13 v14 v15 v16 v17
                   (Zw X) am (Zw (bv_signed q + T + 1)) x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
              F (Zw 0x2a854) fc None m3 (seg_rom USEGS))).
      { intros m3 ws3 len3 v1 v5 v6 v7 y10 y11 y12 y13 y14 y15 y16 y17 v28 v29 v30 v31
               TXT3 FRa3 FRs3 FR803 LIMBS3 L3 LENC3 PAD3 DIG3 SAV3 ST3 VAL3 PR13 PR23 MU3 WM3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb.
        { exfalso. cond_cleanup Hb. revert Hb. rewrite ?Z_to_bv_unsigned. unfold bv_wrap.
          change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z.
          rewrite ?Z.mod_small by lia. lia. }
        clear Hb.
        pose proof (rw_cells_of_u64arr USEGS _ _ _ LIMBS3) as OBJ. rewrite L3 in OBJ. clear LIMBS3.
        apply c4s_as_c8 in DIG3; [|lia].
        chunk_join FRa3 FRs3 FRb. chunk_join FRb FR803 FRc. chunk_join FRc OBJ FRd.
        chunk_join FRd LENC3 FRe. chunk_join FRe PAD3 FRf. chunk_join FRf DIG3 FRg.
        cbn [app] in FRg.
        eapply C_288b4; [exact TXT3 | exact FRg | reflexivity | | exact ST3 | exact VAL3 | exact PR13 | exact PR23 | exact MU3 | exact WM3].
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
        call negative_digit_comp_f_spec.
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
        call positive_digit_comp_f_spec.
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
                 (Zw X) am (Zw (bv_signed q + d)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a770) fc None m (seg_rom USEGS))).
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
                 (Zw X) am (Zw (bv_signed q + d)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a730) fc None m (seg_rom USEGS))).
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
                 (Zw X) am (Zw (bv_signed q + d)) x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2a714) fc None m (seg_rom USEGS))).
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
End U_spf_DC.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_negative_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_parse OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_T0 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_TD OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_CL OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_PK OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_CF1 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_CF2 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_CE OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float.U_spf_DC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Section Main.
  Hypothesis positive_digit_comp_f_spec : positive_digit_comp_f_stmt.
  Hypothesis negative_digit_comp_f_spec : negative_digit_comp_f_stmt.

  (* [comment removed for export] *)
  #[using="positive_digit_comp_f_spec negative_digit_comp_f_spec"] Lemma uspf_tail : forall c : spf_ctx, uspf_pre c -> K_28084 c /\ K_28114e c.
  Proof. LiaFast.lf_pins (fun (positive_digit_comp_f_spec negative_digit_comp_f_spec : LiaFast.U) => LiaFast.u0).
    intros c PRE.
    pose proof (uspf_EPI c PRE) as EPI.
    pose proof (uspf_PK c PRE) as PK.
    pose proof (uspf_CL c PRE EPI) as CL.
    pose proof (uspf_ERRCL c PRE EPI) as ERRCL.
    pose proof (uspf_DC c PRE positive_digit_comp_f_spec negative_digit_comp_f_spec PK) as DC.
    pose proof (uspf_CE c PRE DC PK) as CE.
    pose proof (uspf_CF2 c PRE CE PK) as CF2.
    pose proof (uspf_CF1 c PRE CF2 PK) as CF1.
    pose proof (uspf_TD c PRE CL CF1) as TD.
    pose proof (uspf_T0 c PRE TD) as T0.
    split; [exact T0 | exact ERRCL].
  Qed.

  #[using="positive_digit_comp_f_spec negative_digit_comp_f_spec"] Lemma slow_path_float_spec : slow_path_float_stmt.
  Proof. LiaFast.lf_pins (fun (positive_digit_comp_f_spec negative_digit_comp_f_spec : LiaFast.U) => LiaFast.u0).
    unfold slow_path_float_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v.
    intros TXT LEN RANGE ENW A5 VAL VAL4 ST AL LO P0 V0 VLO PR1 PR2 FRM SEP1 SEP2 SEP3.
    set (c := SPF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v).
    assert (PRE : uspf_pre c) by (constructor; assumption).
    destruct (uspf_tail c PRE) as [T0 ERRCL].
    exact (uspf_parse c PRE T0 ERRCL).
  Qed.
End Main.
