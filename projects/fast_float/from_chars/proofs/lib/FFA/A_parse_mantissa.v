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
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_parse_mantissa_1.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_parse_mantissa_1.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_parse_mantissa_3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_parse_mantissa_9.

Module A_parse_mantissa_5.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).

  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells ASEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95824) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ru_ok (pc : Z) (r9 r28 : word) : Prop :=
    forall (w8 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv r9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 SD BB x24 x25 x26 x27 r28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m (seg_rom ASEGS)).
  Definition ru1_ok : Prop := forall r28, ru_ok 0x9555c resv r28.
  Definition ru2_ok : Prop := forall r9, ru_ok 0x95760 r9 resv.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ftb1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv x9 p (Z_to_bv 64 48) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 x26 x27 resv x29 x30 x31)
            F (Z_to_bv 64 0x9572c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftb8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x9 x12 x16 x17 x18 x19 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x16 x17
                 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 x26 x27 resv x29 x30 x31)
            F (Z_to_bv 64 0x95670) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftb_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 x26 x27 resv x29 x30 x31)
            F (Z_to_bv 64 0x9564c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftaend_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95558) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fta1_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv p fw (Z_to_bv 64 48) p (Z_to_bv 64 (FP + flen)) x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95524) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fta8_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x7 x12 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp (Z_to_bv 64 7) (Z_to_bv 64 (flen - Z.of_nat off)) x7 dv resv p fw x12 p (Z_to_bv 64 flen) fptr
                 (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8))
                 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95464) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fta_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv (Z_to_bv 64 (NP + 48)) fw x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 numv x29 x30 x31)
            F (Z_to_bv 64 0x9540c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition itb_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 numv x29 x30 x31)
            F (Z_to_bv 64 0x953f0) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ita_ok : Prop :=
    forall (u : unit) (w8 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 numv x29 x30 x31)
            F (Z_to_bv 64 0x953c8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition it1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x18 x19 x20 x24 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv (Z_to_bv 64 48) x11 x12 (Z_to_bv 64 (bv_unsigned p + 1)) x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 x27 numv x29 x30 x31)
            F (Z_to_bv 64 0x9537c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition it8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x12 x16 x17 x18 x19 x20 x24 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv p (Z_to_bv 64 (ilen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x16 x17
                 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 x27 numv x29 x30 x31)
            F (Z_to_bv 64 0x952c0) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition it_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 x27 numv x29 x30 x31)
            F (Z_to_bv 64 0x9529c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition itadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 : word) (x1 x5 x6 x7 x8 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 y15 y16 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 m' -> FRHI m' -> stk ASEGS m' (SP + -176) (SP + -160) ->
          u64arr ASEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells ASEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at ASEGS m' IP ibs ->
          munch W m0 m' -> wmono ASEGS m0 m' ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt ASEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 resv y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 BB x24 x25 x26 yc x28 x29 x30 x31) F (Z_to_bv 64 0x9529c) fc None m' (seg_rom ASEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 resv p SHL (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x15 x16 x17 x18 x19 x20 x21 x22 BB x24 x25 x26 cw x28 x29 x30 x31)
            F (Z_to_bv 64 0x95090) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 : word) (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 y15 y16 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 m' -> FRHI m' -> stk ASEGS m' (SP + -176) (SP + -160) ->
          u64arr ASEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells ASEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at ASEGS m' IP ibs ->
          munch W m0 m' -> wmono ASEGS m0 m' ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt ASEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 BB x24 x25 yc x27 resv x29 x30 x31) F (Z_to_bv 64 0x9564c) fc None m' (seg_rom ASEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p SHL (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x15 x16 x17 x18 x19 x20 x21 x22 BB x24 x25 cw x27 resv x29 x30 x31)
            F (Z_to_bv 64 0x951d4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 vw x28 x29 x30 x31)
            F (Z_to_bv 64 0x9505c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 vw x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x951a4) fc None m (seg_rom ASEGS)).

  Lemma itrunc_proof : it_ok -> (forall k, itadd_ok k) -> itrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IT ADD. unfold itrunc_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB AV KB Hoff Hp; pre; shnow MU.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - (* [comment removed for export] *)
      eapply IT; try eassumption; try lia.
      unfold boxed in AV |- *. destruct AV as (BN & _ & BV & _). split; [exact BN| lia].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite zx16_lit by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 len) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len))) by (f_equal; lia).
      replace (Z_to_bv 64 (len + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len) - Z.of_nat 0 + 1)) by (f_equal; lia).
      eapply (ADD (Z.to_nat len) K 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
      + (* [comment removed for export] *)
        intros. eapply IT; try eassumption; try lia.
      + replace (Z.of_nat (Z.to_nat len)) with len by lia. exact XC.
      + unfold boxed. apply sad_inv_init.
  Qed.

  Lemma ftrunc_proof : ftb_ok -> (forall k, ftadd_ok k) -> ftrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FT ADD. unfold ftrunc_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB AV KB FBS FNZ Hoff Hp; pre; shnow MU.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - eapply FT; try eassumption; try lia.
      unfold boxed in AV |- *. destruct AV as (BN & _ & BV & _). split; [exact BN| lia].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite zx16_lit by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 len) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len))) by (f_equal; lia).
      replace (Z_to_bv 64 (len + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len) - Z.of_nat 0 + 1)) by (f_equal; lia).
      eapply (ADD (Z.to_nat len) K 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
      + intros. eapply FT; try eassumption; try lia. apply fbs_now; assumption.
      + replace (Z.of_nat (Z.to_nat len)) with len by lia. exact XC.
      + unfold boxed. apply sad_inv_init.
  Qed.
End Proof.
End A_parse_mantissa_5.


Module A_parse_mantissa_6a.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).

  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells ASEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95824) fc None m (seg_rom ASEGS)).


  (* [comment removed for export] *)
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 37)%Z -> ((off < length fbs)%nat -> 19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x95028) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d44) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94e94) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x6 x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp (Z_to_bv 64 17) x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 (Z_to_bv 64 1) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94ec8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fmul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 19 \/ off = length fbs \/ dg = maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94f3c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d88) fc None m (seg_rom ASEGS)).
  Notation LO7 w8 := [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ LF1 LF2 MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma fback_proof : forall kk, end_ok -> fout_ok kk -> fback_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk END FOUT. unfold fback_ok; intros until dg; introsF; intros V HK HK1 HK2 DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (FOUT off p K); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      eapply (END (LO7 w8)); try eassumption; try lia.
      { reflexivity. }
      all: enough (K <= (dg + 37) / 19 /\ (dg + 37) / 19 <= dg / 19 + 3)%Z by lia.
      all: split; [apply Z.div_le_lower_bound; lia|].
      all: Z.div_mod_to_equations; lia.
  Qed.

  Lemma f1e_proof : forall kk, fmul_ok kk -> (forall k, f1_ok kk k) -> f1e_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FM F1. unfold f1e_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd H0 Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hm; cond_cleanup Hm; rewrite ?unsigned_lit in Hm by lia. { exfalso. rewrite <- ?Hmaxd in Hm. lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    rewrite (unsigned_lit dg) in * by lia. rewrite <- Hmaxd in *. rewrite (unsigned_lit (cnt + maxd)) by lia.
    eapply (F1 (Z.to_nat (19 - cnt)) off p vw cnt (cnt + maxd - dg)%Z K w8); try eassumption; try lia.
  Qed.

  Lemma f1_proof : forall kk, fmul_ok kk -> forall k, f1_ok kk k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FM. induction k as [|k IH]; unfold f1_ok; intros until dg; introsF; intros V HK Hcnt Hk Hcd HKd Hc2 H0 Hoff Hp Hkk; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H1; cond_cleanup H1.
    { (* [comment removed for export] *)
      assert (Hdm : dg = maxd) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 c2) with (Z_to_bv 64 cnt) by (f_equal; lia).
      eapply (FM off p vw cnt K w8); try eassumption; try lia. }
    assert (Hdm : (dg < maxd)%Z) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
    pose proof (ro_block ASEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H19; cond_cleanup H19; rewrite ?unsigned_lit in H19 by lia.
    { eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    - replace (Z_to_bv 64 (dg + 2)) with (Z_to_bv 64 (dg + 1 + 1)) by (f_equal; lia).
      eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z c2 K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
    - step. (* [comment removed for export] *)
      eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.
End Proof.
End A_parse_mantissa_6a.


Module A_parse_mantissa_6b.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


  (* [comment removed for export] *)
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 37)%Z -> ((off < length fbs)%nat -> 19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x95028) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d44) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94e94) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x6 x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp (Z_to_bv 64 17) x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 (Z_to_bv 64 1) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94ec8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fmul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 19 \/ off = length fbs \/ dg = maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94f3c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d88) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 : word) (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 y15 y16 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 m' -> FRHI m' -> stk ASEGS m' (SP + -176) (SP + -160) ->
          u64arr ASEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells ASEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at ASEGS m' IP ibs ->
          munch W m0 m' -> wmono ASEGS m0 m' ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt ASEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 BB x24 x25 yc x27 x28 x29 x30 resv) F (Z_to_bv 64 0x95028) fc None m' (seg_rom ASEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p SHL (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x15 x16 x17 x18 x19 x20 x21 x22 BB x24 x25 cw x27 x28 x29 x30 resv)
            F (Z_to_bv 64 0x94fac) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 vw x28 x29 x30 x31)
            F (Z_to_bv 64 0x9505c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 vw x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x951a4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition TBL10V : list Z := Eval vm_compute in (map (fun k => 10 ^ Z.of_nat k)%Z (seq 0 20)).
  Lemma TBL10V_ok : table_b ASEGS TBL10 8 (fun v => le8 (Z_to_bv 64 v)) TBL10V = true.
  Proof. LiaFast.lf_pins LiaFast.lf_all. vm_compute. reflexivity. Qed.
  Lemma TBL10V_nth : forall c, (0 <= c <= 19)%Z -> (1 <= nth (Z.to_nat c) TBL10V 0 < 2^64)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros c Hc.
    assert (H : forall n, (n < 20)%nat -> (1 <= nth n TBL10V 0 < 2^64)%Z).
    { intros n Hn. do 20 (destruct n as [|n]; [cbn; lia|]). lia. }
    apply H. lia.
  Qed.
  Notation LO7 w8 := [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ LF1 LF2 MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma fmul_proof : forall kk, ftrunc_ok -> fback_ok kk -> (forall k, fadd_ok k) -> fmul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FT FB FADD. unfold fmul_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (Z_to_bv 64 (TBL10 + cnt * 2 ^ 3)) with (Z_to_bv 64 (TBL10 + 8 * cnt)) by (f_equal; lia).
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (table_read ASEGS _ _ _ _ m _ _ TBL10V_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10V_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10V 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    { rewrite ULs. replace (SP + -160 - 16)%Z with (SP + -176)%Z by lia. exact ST. }
    { exact PRG. } { exact BC. }
    { rewrite ULs. lia. } { rewrite ULs. lia. } { rewrite ULs. lia. } { rewrite ULs. lia. } { lia. } { lia. }
    { exact SHX. }
    lazymatch goal with
    | XL' : u64arr ASEGS ?m' A ?cur', XC' : rw_cells ASEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    lazymatch goal with ST' : stk ASEGS _ (bv_unsigned SP' - 16) _ |- _ =>
      rewrite ULs in ST'; replace (SP + -160 - 16)%Z with (SP + -176)%Z in ST' by lia; rename ST' into ST1 end.
    lazymatch goal with MU' : munch W m0 ?m' |- _ => rename MU' into MU1 end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    assert (AV : ADDV cur1 (Z.to_nat len1) (bv_unsigned vw) (K + 1)).
    { unfold boxed. split; [apply HN1; [lia| exact BN]|]. split; [lia|]. split; [| lia].
      rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht; rewrite ?unsigned_lit in Ht by lia.
    - eapply (FT off p vw w8); try eassumption; try lia.
      all: try (apply fbs_now; [assumption| exact FNZ]).
      all: try (enough (K + 1 <= (dg + 36) / 19 /\ (dg + 36) / 19 <= dg / 19 + 2)%Z by lia;
                split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia).
      all: show.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz.
      + eapply (FB off p (K + 1)%Z w8); try eassumption; try lia.
        all: try (apply fbs_now; [assumption| exact FNZ]).
        all: try (unfold boxed in AV |- *; destruct AV as (BN2 & _ & BV2 & _); split; [exact BN2| lia]).
        all: show.
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite zx16_lit by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        replace (Z_to_bv 64 len1) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1))) by (f_equal; lia).
        replace (Z_to_bv 64 (len1 + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1) - Z.of_nat 0 + 1)) by (f_equal; lia).
        eapply (FADD (Z.to_nat len1) (K + 1)%Z 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
        * intros. eapply (FB off p (K + 1)%Z w8); try eassumption; try lia. all: try (apply fbs_now; assumption). all: show.
        * replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1.
        * unfold boxed. apply sad_inv_init.
  Qed.
End Proof.
End A_parse_mantissa_6b.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_parse_mantissa_3.

Module A_parse_mantissa_6d.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).

  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells ASEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95824) fc None m (seg_rom ASEGS)).


  (* [comment removed for export] *)
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 37)%Z -> ((off < length fbs)%nat -> 19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x95028) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d44) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94e94) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x6 x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp (Z_to_bv 64 17) x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 (Z_to_bv 64 1) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94ec8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fmul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 19 \/ off = length fbs \/ dg = maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94f3c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d88) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 : word) (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 y15 y16 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 m' -> FRHI m' -> stk ASEGS m' (SP + -176) (SP + -160) ->
          u64arr ASEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells ASEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at ASEGS m' IP ibs ->
          munch W m0 m' -> wmono ASEGS m0 m' ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt ASEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 BB x24 x25 yc x27 x28 x29 x30 resv) F (Z_to_bv 64 0x95028) fc None m' (seg_rom ASEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p SHL (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x15 x16 x17 x18 x19 x20 x21 x22 BB x24 x25 cw x27 x28 x29 x30 resv)
            F (Z_to_bv 64 0x94fac) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 vw x28 x29 x30 x31)
            F (Z_to_bv 64 0x9505c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 vw x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x951a4) fc None m (seg_rom ASEGS)).
  Notation LO7 w8 := [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ LF1 LF2 MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma fout_proof :
    (forall kk, end_ok -> fout_ok kk -> fback_ok kk) ->
    (forall kk, ftrunc_ok -> fback_ok kk -> (forall k, fadd_ok k) -> fmul_ok kk) ->
    (forall kk, fmul_ok kk -> forall k, f1_ok kk k) ->
    (forall kk, fmul_ok kk -> (forall k, f1_ok kk k) -> f1e_ok kk) ->
    (forall kk, f1e_ok kk -> fmul_ok kk -> f8body_ok kk 0) ->
    (forall kk, f1e_ok kk -> fmul_ok kk -> f8body_ok kk 0 -> f8body_ok kk 1) ->
    end_ok -> ftrunc_ok -> (forall k, fadd_ok k) -> forall k, fout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros PFB PFM PF1 PFE PF80 PF81 END FT FADD.
    induction k as [|k IH]; unfold fout_ok; intros until dg; introsF; intros V HK HKd DGM Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (PFB k END IH) as FB.
    pose proof (PFM k FT FB FADD) as FM.
    pose proof (PF1 k FM) as F1.
    pose proof (PFE k FM F1) as FE.
    pose proof (PF80 k FE FM) as F80.
    pose proof (PF81 k FE FM F80) as F81.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (FP + flen)) by lia.
    replace (Z_to_bv 64 (FP + flen - bv_unsigned p)) with (Z_to_bv 64 (flen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. { exfalso. show. lia. }
      eapply (FE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
    - step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hw8. replace (Z_to_bv 64 (FP + flen - 8 - bv_unsigned p)) with (Z_to_bv 64 (flen - Z.of_nat off - 8)) by (f_equal; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit dg) in * by lia. rewrite <- Hmaxd in *.
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit in Hc by lia.
      + step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. { exfalso. show. lia. }
        eapply (FE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
      + show.
        eapply (F81 off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia. all: show.
  Qed.
End Proof.
End A_parse_mantissa_6d.


Module A_parse_mantissa_7.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).

  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells ASEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95824) fc None m (seg_rom ASEGS)).


  (* [comment removed for export] *)
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 37)%Z -> ((off < length fbs)%nat -> 19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x95028) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 x26 (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d44) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94e94) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x6 x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp (Z_to_bv 64 17) x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 (Z_to_bv 64 1) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94ec8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fmul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 19 \/ off = length fbs \/ dg = maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94f3c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition f8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs -> bytes_at ASEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) C_S2 C_S3 FENDW p SD BB C_S8 C_S9 vw (Z_to_bv 64 10) x28 x29 dv resv)
            F (Z_to_bv 64 0x94d88) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Notation FRLOJ j1 j2 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).

  (* [comment removed for export] *)
  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94cf4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p fendw (Z_to_bv 64 48) x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x95230) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x9521c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x12 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x950f4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 flen) x12 x13 x14 x15 x16 x17 x18 x19 FENDW fptr SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x950d4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94ca8) fc None m (seg_rom ASEGS)).
  Notation LOJ j1 j2 := [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].
  Ltac introsE := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V HK HKd.
  Ltac show := match goal with |- ?g => idtac g end.
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).
  Ltac end_tail K dg :=
    try reflexivity;
    try (enough (K <= (dg + 18) / 19 /\ (dg + 18) / 19 <= dg / 19 + 3)%Z by lia;
         split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia).

  Lemma fconst_proof : end_ok -> (forall k, fout_ok k) -> fconst_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FOUT. unfold fconst_ok; intros until dg; introsE; intros FBS FNZ LF1 LF2 Hoff Hp; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    { eapply (END (LOJ j1 j2)); try eassumption; try lia. all: end_tail K dg. all: show. }
    do 19 step.
    show.
    eapply (FOUT (length fbs - off)%nat off p K (Z_to_bv 64 (FP + flen + -8))); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.

  Lemma fz1_proof : fconst_ok -> forall k, fz1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FC. induction k as [|k IH]; unfold fz1_ok; intros until dg; introsE; intros FBS FNZ LF1 LF2 Hk Hoff Hp Hfe; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 fendw) as Rf; unfold bv_modulus in Rf.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    pose proof (ro_block ASEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (FC off p K j1 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?unsigned_lit in Hb by lia.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fendw K j1 j2); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (FC (length fbs) fendw K j1 j2); try eassumption; try lia.
  Qed.

  Lemma fzmid_proof : end_ok -> (forall k, fz1_ok k) -> fzmid_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FZ1. unfold fzmid_ok; intros until dg; introsE; intros FBS FNZ LF1 LF2 Hoff Hp; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    { eapply (END (LOJ j1 j2)); try eassumption; try lia. all: end_tail K dg. all: show. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (FZ1 (length fbs - off)%nat off p _ K j1 j2); try eassumption; try lia.
    all: rewrite ?(unsigned_lit (FP + flen)) by lia; rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.

  Lemma fz8_proof : fzmid_ok -> forall k, fz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FM. induction k as [|k IH]; unfold fz8_ok; intros until dg; introsE; intros FBS FNZ LF1 LF2 Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    pose proof (ro_block ASEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 22 step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (FM off p K j1 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    shptr_next p.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      replace (Z_to_bv 64 (flen - Z.of_nat off - 8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j1 j2); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (FM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j1 j2); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fz_proof : fzmid_ok -> (forall k, fz8_ok k) -> fz_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FM FZ8. unfold fz_ok; intros until dg; introsE; intros FBS FNZ LF1 LF2; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      eapply (FM 0%nat fptr K j1 j2); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 flen) with (Z_to_bv 64 (flen - Z.of_nat 0)) by (f_equal; lia).
      eapply (FZ8 (length fbs) 0%nat fptr K j1 j2); try eassumption; try lia.
  Qed.

  Lemma fset_proof : end_ok -> fz_ok -> fconst_ok -> fset_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FZ FC. unfold fset_ok; intros until dg; introsE; pre; shnow MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    { eapply (END (LOJ j1 j2)); try eassumption; try lia. all: end_tail K dg. all: show. }
    pose proof (fbs_now m MU Hz) as FBS. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    unfold boxed in LF. destruct (LF Hz) as [LF1 LF2].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd; cond_cleanup Hd; rewrite ?unsigned_lit in Hd by lia.
    - show. eapply (FZ tt K j1 j2); try eassumption; try lia. all: show.
    - show. eapply (FC 0%nat fptr K j1 j2); try eassumption; try lia. all: show.
  Qed.
End Proof.
End A_parse_mantissa_7.


Module A_parse_mantissa_8a.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


  (* [comment removed for export] *)
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).

  (* [comment removed for export] *)
  Notation FRLOJ j1 j2 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).

  (* [comment removed for export] *)
  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94cf4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p fendw (Z_to_bv 64 48) x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x95230) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x9521c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x12 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x950f4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 flen) x12 x13 x14 x15 x16 x17 x18 x19 FENDW fptr SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x950d4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94ca8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Notation IENDW := (Z_to_bv 64 (IP + ilen)).

  (* [comment removed for export] *)
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94c74) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x9498c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94ae0) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x6 x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp (Z_to_bv 64 17) x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 (Z_to_bv 64 1) C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94b14) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94b88) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x949d4) fc None m (seg_rom ASEGS)).
  Notation LO7 w8 := [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma frlo3_to_J : forall m a, FRLO3 a m -> FRLOJ (le8 a) (le8 (Z_to_bv 64 (A + 496))) m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m a [[WW B] R]. split; [split|].
    - cbn. repeat split; try reflexivity; try apply length_le8. all: exact I.
    - exact B.
    - exact R.
  Qed.

  Lemma iback_proof : forall kk, fset_ok -> iout_ok kk -> iback_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FSET IOUT. unfold iback_ok; intros until dg; introsF; intros V HK HK1 HK2 DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IOUT off p K); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      eapply (FSET tt K (le8 w8) (le8 (Z_to_bv 64 (A + 496)))); try eassumption; try lia.
      apply frlo3_to_J. exact FRLO.
  Qed.

  Lemma i1e_proof : forall kk, imul_ok kk -> (forall k, i1_ok kk k) -> i1e_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM I1. unfold i1e_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd H0 Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hm; cond_cleanup Hm; rewrite ?unsigned_lit in Hm by lia. { exfalso. rewrite <- ?Hmaxd in Hm. lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    rewrite (unsigned_lit dg) in * by lia. rewrite <- Hmaxd in *. rewrite (unsigned_lit (cnt + maxd)) by lia.
    eapply (I1 (Z.to_nat (19 - cnt)) off p vw cnt (cnt + maxd - dg)%Z K w8); try eassumption; try lia.
  Qed.

  Lemma i1_proof : forall kk, imul_ok kk -> forall k, i1_ok kk k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM. induction k as [|k IH]; unfold i1_ok; intros until dg; introsF; intros V HK Hcnt Hk Hcd HKd Hc2 H0 Hoff Hp Hkk; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H1; cond_cleanup H1.
    { (* [comment removed for export] *)
      assert (Hdm : dg = maxd) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 c2) with (Z_to_bv 64 cnt) by (f_equal; lia).
      eapply (IM off p vw cnt K w8); try eassumption; try lia. }
    assert (Hdm : (dg < maxd)%Z) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
    pose proof (ro_block ASEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H19; cond_cleanup H19; rewrite ?unsigned_lit in H19 by lia.
    { eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    - replace (Z_to_bv 64 (dg + 2)) with (Z_to_bv 64 (dg + 1 + 1)) by (f_equal; lia).
      eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z c2 K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
    - step. (* [comment removed for export] *)
      eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.
End Proof.
End A_parse_mantissa_8a.


Module A_parse_mantissa_8b.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


  (* [comment removed for export] *)
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).

  (* [comment removed for export] *)
  Notation IENDW := (Z_to_bv 64 (IP + ilen)).

  (* [comment removed for export] *)
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94c74) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x9498c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94ae0) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x6 x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp (Z_to_bv 64 17) x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 (Z_to_bv 64 1) C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94b14) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94b88) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x949d4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition iadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 : word) (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 y15 y16 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 m' -> FRHI m' -> stk ASEGS m' (SP + -176) (SP + -160) ->
          u64arr ASEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells ASEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at ASEGS m' IP ibs ->
          munch W m0 m' -> wmono ASEGS m0 m' ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt ASEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 BB x24 x25 x26 yc x28 x29 x30 resv) F (Z_to_bv 64 0x94c74) fc None m' (seg_rom ASEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p SHL (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x15 x16 x17 x18 x19 x20 x21 x22 BB x24 x25 x26 cw x28 x29 x30 resv)
            F (Z_to_bv 64 0x94bf8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 vw x28 x29 x30 x31)
            F (Z_to_bv 64 0x9505c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 vw x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x951a4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition TBL10V : list Z := Eval vm_compute in (map (fun k => 10 ^ Z.of_nat k)%Z (seq 0 20)).
  Lemma TBL10V_ok : table_b ASEGS TBL10 8 (fun v => le8 (Z_to_bv 64 v)) TBL10V = true.
  Proof. LiaFast.lf_pins LiaFast.lf_all. vm_compute. reflexivity. Qed.
  Lemma TBL10V_nth : forall c, (0 <= c <= 19)%Z -> (1 <= nth (Z.to_nat c) TBL10V 0 < 2^64)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros c Hc.
    assert (H : forall n, (n < 20)%nat -> (1 <= nth n TBL10V 0 < 2^64)%Z).
    { intros n Hn. do 20 (destruct n as [|n]; [cbn; lia|]). lia. }
    apply H. lia.
  Qed.
  Notation LO7 w8 := [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma imul_proof : forall kk, itrunc_ok -> iback_ok kk -> (forall k, iadd_ok k) -> imul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IT IB IADD. unfold imul_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (Z_to_bv 64 (TBL10 + cnt * 2 ^ 3)) with (Z_to_bv 64 (TBL10 + 8 * cnt)) by (f_equal; lia).
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (table_read ASEGS _ _ _ _ m _ _ TBL10V_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10V_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10V 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    { rewrite ULs. replace (SP + -160 - 16)%Z with (SP + -176)%Z by lia. exact ST. }
    { exact PRG. } { exact BC. }
    { rewrite ULs. lia. } { rewrite ULs. lia. } { rewrite ULs. lia. } { rewrite ULs. lia. } { lia. } { lia. }
    { exact SHX. }
    lazymatch goal with
    | XL' : u64arr ASEGS ?m' A ?cur', XC' : rw_cells ASEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    lazymatch goal with ST' : stk ASEGS _ (bv_unsigned SP' - 16) _ |- _ =>
      rewrite ULs in ST'; replace (SP + -160 - 16)%Z with (SP + -176)%Z in ST' by lia; rename ST' into ST1 end.
    lazymatch goal with MU' : munch W m0 ?m' |- _ => rename MU' into MU1 end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    assert (AV : ADDV cur1 (Z.to_nat len1) (bv_unsigned vw) (K + 1)).
    { unfold boxed. split; [apply HN1; [lia| exact BN]|]. split; [lia|]. split; [| lia].
      rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht; rewrite ?unsigned_lit in Ht by lia.
    - eapply (IT off p vw w8); try eassumption; try lia.
      
      all: try (enough (K + 1 <= (dg + 18) / 19 /\ (dg + 18) / 19 <= dg / 19 + 2)%Z by lia;
                split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia).
      all: show.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz.
      + eapply (IB off p (K + 1)%Z w8); try eassumption; try lia.
        
        all: try (unfold boxed in AV |- *; destruct AV as (BN2 & _ & BV2 & _); split; [exact BN2| lia]).
        all: show.
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite zx16_lit by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        replace (Z_to_bv 64 len1) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1))) by (f_equal; lia).
        replace (Z_to_bv 64 (len1 + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1) - Z.of_nat 0 + 1)) by (f_equal; lia).
        eapply (IADD (Z.to_nat len1) (K + 1)%Z 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
        * intros. eapply (IB off p (K + 1)%Z w8); try eassumption; try lia.  all: show.
        * replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1.
        * unfold boxed. apply sad_inv_init.
  Qed.
End Proof.
End A_parse_mantissa_8b.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_parse_mantissa_1.

Module A_parse_mantissa_8d.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_long_mul_stmt A_small_mul_stmt A_parse_mantissa_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.
  (* [comment removed for export] *)
  Lemma sh_now : forall m, munch W m0 m -> SHNOW m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU. bounds.
    pose proof (shz_bound _ _ _ _ SHX0) as B1. pose proof (shz_bound _ _ _ _ SHT0) as B2.
    repeat (lazymatch goal with |- _ /\ _ => split end).
    - eapply shz_transport; [exact SHX0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHD0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHN0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHI0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
    - eapply shz_transport; [exact SHT0 | exact MU | cbn [disjoint_from]; lia].
    - eapply pristine_transport; [exact PRG0 | exact MU | cbn [disjoint_from]; lia].
    - pose proof (ro_cells_bound _ _ _ _ BC0) as B3. cbn [cells_size csize Nat.add] in B3.
      eapply ro_cells_transport; [exact BC0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
    - eapply pristine_transport; [exact PR0 | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Ltac shnow MU := let H := fresh in pose proof (sh_now _ MU) as H;
    destruct H as (SHX & SHD & SHN & SHI & SHT & PRG & BC & PR).

  Lemma shf_now : forall m, munch W m0 m -> (FP <> 0)%Z ->
    shz ASEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at ASEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport ASEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


  (* [comment removed for export] *)
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).

  (* [comment removed for export] *)
  Notation FRLOJ j1 j2 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).

  (* [comment removed for export] *)
  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94cf4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p fendw (Z_to_bv 64 48) x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x95230) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x9521c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x12 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x16 x17 x18 x19 FENDW p SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x950f4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 flen) x12 x13 x14 x15 x16 x17 x18 x19 FENDW fptr SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x950d4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94ca8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Notation IENDW := (Z_to_bv 64 (IP + ilen)).

  (* [comment removed for export] *)
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x94c74) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 x27 x28 x29 dv resv)
            F (Z_to_bv 64 0x9498c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94ae0) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x6 x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp (Z_to_bv 64 17) x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 (Z_to_bv 64 1) C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94b14) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x94b88) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 (Z_to_bv 64 8) C_S1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) C_S2 (Z_to_bv 64 10) C_S3 p SD BB C_S8 IENDW C_S9 vw x28 x29 dv resv)
            F (Z_to_bv 64 0x949d4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition iadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 : word) (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 y15 y16 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 m' -> FRHI m' -> stk ASEGS m' (SP + -176) (SP + -160) ->
          u64arr ASEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells ASEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at ASEGS m' IP ibs ->
          munch W m0 m' -> wmono ASEGS m0 m' ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt ASEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 BB x24 x25 x26 yc x28 x29 x30 resv) F (Z_to_bv 64 0x94c74) fc None m' (seg_rom ASEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p SHL (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x15 x16 x17 x18 x19 x20 x21 x22 BB x24 x25 x26 cw x28 x29 x30 resv)
            F (Z_to_bv 64 0x94bf8) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 (IP + ilen)) x26 vw x28 x29 x30 x31)
            F (Z_to_bv 64 0x9505c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at ASEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (FP + flen)) p SD BB x24 x25 vw x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x951a4) fc None m (seg_rom ASEGS)).
  Notation LO7 w8 := [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma iout_proof :
    (forall kk, fset_ok -> iout_ok kk -> iback_ok kk) ->
    (forall kk, itrunc_ok -> iback_ok kk -> (forall k, iadd_ok k) -> imul_ok kk) ->
    (forall kk, imul_ok kk -> forall k, i1_ok kk k) ->
    (forall kk, imul_ok kk -> (forall k, i1_ok kk k) -> i1e_ok kk) ->
    (forall kk, i1e_ok kk -> imul_ok kk -> i8body_ok kk 0) ->
    (forall kk, i1e_ok kk -> imul_ok kk -> i8body_ok kk 0 -> i8body_ok kk 1) ->
    fset_ok -> itrunc_ok -> (forall k, iadd_ok k) -> forall k, iout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros PIB PIM PI1 PIE PI80 PI81 FSET IT IADD.
    induction k as [|k IH]; unfold iout_ok; intros until dg; introsF; intros V HK HKd DGM Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (PIB k FSET IH) as IB.
    pose proof (PIM k IT IB IADD) as IM.
    pose proof (PI1 k IM) as I1.
    pose proof (PIE k IM I1) as IE.
    pose proof (PI80 k IE IM) as I80.
    pose proof (PI81 k IE IM I80) as I81.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (IP + ilen)) by lia.
    replace (Z_to_bv 64 (IP + ilen - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. { exfalso. show. lia. }
      eapply (IE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
    - step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hw8. replace (Z_to_bv 64 (IP + ilen - 8 - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off - 8)) by (f_equal; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit dg) in * by lia. rewrite <- Hmaxd in *.
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit in Hc by lia.
      + step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. { exfalso. show. lia. }
        eapply (IE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
      + show.
        eapply (I81 off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia. all: show.
  Qed.
End Proof.
End A_parse_mantissa_8d.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_parse_mantissa_9.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1 OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2 OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_3 OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_9.A_parse_mantissa_4 OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_5 OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_6a OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_6b OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_3.A_parse_mantissa_6c OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_6d OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_7 OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_8a OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_8b OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_8c OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa.A_parse_mantissa_8d OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_9.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd FS THI GLO gi gin gf gfn : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis NAL : (bv_unsigned numv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at ASEGS m0 (bv_unsigned fptr) fbs).
  (* [comment removed for export] *)
  Hypothesis LAY0 : (IMG_END <= bv_unsigned sp - 176)%Z.
  Hypothesis KLO : (KHI <= bv_unsigned sp - 176)%Z.
  Hypothesis LD1 : (bv_unsigned sp <= bv_unsigned dv)%Z.
  Hypothesis LD2 : (bv_unsigned dv + 8 <= KTOP)%Z.
  Hypothesis KFS1 : (app2r (FS) (THI))%Z.
  Hypothesis KFS2 : (GLO <= bv_unsigned resv /\ (app2r (GLO) (GLO + FSSIZE)) /\ GLO + FSSIZE <= KTOP)%Z.
  Hypothesis LI1 : (FS <= bv_unsigned iptr)%Z.
  Hypothesis LI2 : (bv_unsigned iptr + ilen <= THI)%Z.
  Hypothesis LF : boxed (bv_unsigned fptr <> 0 -> FS <= bv_unsigned fptr /\ bv_unsigned fptr + flen <= THI)%Z.
  Hypothesis LA : (bv_unsigned resv + 498 <= bv_unsigned numv + 32)%Z.
  Hypothesis LN : (bv_unsigned numv + 64 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz ASEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz ASEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz ASEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz ASEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz ASEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz ASEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells ASEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).       (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells ASEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells ASEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells ASEGS m (SP + -160)
     [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz ASEGS m (ASAN_B + A / 8) 63 /\ shz ASEGS m (ASAN_B + D / 8) 1 /\ shz ASEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz ASEGS m (ASAN_B + gi) gin /\ shz ASEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 mdw) as RM; unfold bv_modulus in RM.

  (* [comment removed for export] *)
  Local Ltac inst L := exact (L small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_end_proof := (@A_parse_mantissa_1.end_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_diginc_proof := (@A_parse_mantissa_1.diginc_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_rupush1_proof := (@A_parse_mantissa_1.rupush1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_rupush2_proof := (@A_parse_mantissa_1.rupush2_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ruadd1_proof := (@A_parse_mantissa_1.ruadd1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ruadd2_proof := (@A_parse_mantissa_1.ruadd2_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ru1_proof := (@A_parse_mantissa_1.ru1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ru2_proof := (@A_parse_mantissa_1.ru2_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftb1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.ftb1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftb8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.ftb8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftb_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.ftb_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftaend_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.ftaend_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fta1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.fta1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fta8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.fta8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fta_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.fta_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_itb_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.itb_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ita_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.ita_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_it1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.it1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_it8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.it8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_it_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_2.it_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_itadd_proof := (@A_parse_mantissa_3.itadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftadd_proof := (@A_parse_mantissa_3.ftadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iadd_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_9.A_parse_mantissa_4.iadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fadd_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_9.A_parse_mantissa_4.fadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_itrunc_proof := (@A_parse_mantissa_5.itrunc_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftrunc_proof := (@A_parse_mantissa_5.ftrunc_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fback_proof := (@A_parse_mantissa_6a.fback_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f1e_proof := (@A_parse_mantissa_6a.f1e_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f1_proof := (@A_parse_mantissa_6a.f1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fmul_proof := (@A_parse_mantissa_6b.fmul_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f8body0_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_3.A_parse_mantissa_6c.f8body0_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f8body1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_3.A_parse_mantissa_6c.f8body1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fout_proof := (@A_parse_mantissa_6d.fout_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fconst_proof := (@A_parse_mantissa_7.fconst_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fz1_proof := (@A_parse_mantissa_7.fz1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fzmid_proof := (@A_parse_mantissa_7.fzmid_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fz8_proof := (@A_parse_mantissa_7.fz8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fz_proof := (@A_parse_mantissa_7.fz_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fset_proof := (@A_parse_mantissa_7.fset_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iback_proof := (@A_parse_mantissa_8a.iback_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i1e_proof := (@A_parse_mantissa_8a.i1e_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i1_proof := (@A_parse_mantissa_8a.i1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_imul_proof := (@A_parse_mantissa_8b.imul_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i8body0_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_8c.i8body0_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i8body1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_1.A_parse_mantissa_8c.i8body1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iout_proof := (@A_parse_mantissa_8d.iout_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iconst_proof := (@A_parse_mantissa_9.iconst_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iz1_proof := (@A_parse_mantissa_9.iz1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_izmid_proof := (@A_parse_mantissa_9.izmid_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_izpre_proof := (@A_parse_mantissa_9.izpre_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iz8_proof := (@A_parse_mantissa_9.iz8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_body_proof := (@A_parse_mantissa_9.body_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).

  (* [comment removed for export] *)
  Lemma main_ok :
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk ASEGS m0 (SP - 176) SP ->
      u64arr ASEGS m0 A ws -> rw_cells ASEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells ASEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at ASEGS m0 IP ibs -> rw_cells ASEGS m0 D [C8 dg0] ->
      evt ASEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x9474c) fc None m0 (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    pose proof L_end_proof as END.
    pose proof (L_diginc_proof END) as DIG.
    pose proof (L_rupush1_proof DIG) as PUSH1.
    pose proof (L_rupush2_proof DIG) as PUSH2.
    pose proof (L_ruadd1_proof DIG PUSH1) as RU1A.
    pose proof (L_ruadd2_proof DIG PUSH2) as RU2A.
    pose proof (L_ru1_proof RU1A) as RU1.
    pose proof (L_ru2_proof RU2A) as RU2.
    pose proof (L_ftb1_proof END RU2) as FTB1.
    pose proof (L_ftb8_proof END RU2 FTB1) as FTB8.
    pose proof (L_ftb_proof END FTB1 FTB8) as FTB.
    pose proof (L_ftaend_proof END RU1) as FE.
    pose proof (L_fta1_proof FE RU1) as FTA1.
    pose proof (L_fta8_proof FE RU1 FTA1) as FTA8.
    pose proof (L_fta_proof FE FTA1 FTA8) as FTA.
    pose proof (L_itb_proof FE FTA) as ITB.
    pose proof (L_ita_proof END FTA) as ITA.
    pose proof (L_it1_proof ITB) as IT1.
    pose proof (L_it8_proof ITB ITA IT1) as IT8.
    pose proof (L_it_proof ITA IT1 IT8) as IT.
    pose proof (L_itrunc_proof IT L_itadd_proof) as ITRUNC.
    pose proof (L_ftrunc_proof FTB L_ftadd_proof) as FTRUNC.
    pose proof (L_fout_proof L_fback_proof L_fmul_proof L_f1_proof L_f1e_proof L_f8body0_proof L_f8body1_proof END FTRUNC L_fadd_proof) as FOUT.
    pose proof (L_fconst_proof END FOUT) as FCONST.
    pose proof (L_fz1_proof FCONST) as FZ1.
    pose proof (L_fzmid_proof END FZ1) as FZMID.
    pose proof (L_fz8_proof FZMID) as FZ8.
    pose proof (L_fz_proof FZMID FZ8) as FZ.
    pose proof (L_fset_proof END FZ FCONST) as FSET.
    pose proof (L_iout_proof L_iback_proof L_imul_proof L_i1_proof L_i1e_proof L_i8body0_proof L_i8body1_proof FSET ITRUNC L_iadd_proof) as IOUT.
    pose proof (L_iconst_proof FSET IOUT) as ICONST.
    pose proof (L_iz1_proof ICONST) as IZ1.
    pose proof (L_izmid_proof IZ1) as IZMID.
    pose proof (L_izpre_proof FSET IZMID) as IZPRE.
    pose proof (L_iz8_proof IZPRE) as IZ8.
    exact (L_body_proof IZPRE IZ8).
  Qed.
End Proof.

Section Top.
  Hypothesis small_mul_spec : small_mul_stmt.

  Lemma parse_mantissa_spec : parse_mantissa_stmt.
  Proof.
    unfold parse_mantissa_stmt. intros until gfn.
    intros ST ALIGN PR XL Hxl XC XAL NUM IBS INZ IEND ILEN FBS FEND FLEN FNULL MAXD DG PRG BC LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN NAL SFS SHX SHD SHN SHI GI1 GI2 SHF SHT.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    eapply (main_ok small_mul_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc m ws iptr fptr ibs fbs
              (Z.of_nat (length ibs)) (Z.of_nat (length fbs)) (bv_unsigned a2) FS THI GLO gi gin gf gfn
              eq_refl eq_refl eq_refl Hxl MAXD XAL NAL ALIGN INZ IEND ltac:(lia) FEND ltac:(lia) FNULL FBS LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN SFS
              SHX SHD SHN SHI GI1 GI2 SHF SHT PRG BC PR);
      eassumption.
  Qed.
End Top.
