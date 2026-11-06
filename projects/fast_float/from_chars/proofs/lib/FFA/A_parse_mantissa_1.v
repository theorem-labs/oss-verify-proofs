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

Module A_parse_mantissa_2.
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
  Notation LO7 w8 := [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv].

  (* [comment removed for export] *)
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).

  Lemma ftb1_proof : end_ok -> ru2_ok -> forall k, ftb1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU2. induction k as [|k IH]; unfold ftb1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
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
    if_cases Hc.
    { clear Hc. eapply RU2; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { clear He. eapply (END (LO7 w8)); try eassumption; try lia. reflexivity. }
    step. (* [comment removed for export] *)
    eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma ftb8_proof : end_ok -> ru2_ok -> (forall k, ftb1_ok k) -> forall k, ftb8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU2 T1. induction k as [|k IH]; unfold ftb8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
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
    if_cases Hc.
    { clear Hc. eapply RU2; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    shptr_next p.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { clear He. eapply (END (LO7 w8)); try eassumption; try lia. reflexivity. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma ftb_proof : end_ok -> (forall k, ftb1_ok k) -> (forall k, ftb8_ok k) -> ftb_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END T1 T8. unfold ftb_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hoff Hp; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (FP + flen)) by lia.
    replace (Z_to_bv 64 (FP + flen - bv_unsigned p)) with (Z_to_bv 64 (flen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { clear He. eapply (END (LO7 w8)); try eassumption; try lia. reflexivity. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - off)%nat off p); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length fbs - off)%nat off p); try eassumption; try lia.
  Qed.

  Lemma ftaend_proof : end_ok -> ru1_ok -> ftaend_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU1. unfold ftaend_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB; pre.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    - eapply (END (LO7 w8)); try eassumption; try lia. reflexivity.
    - eapply RU1; try eassumption; lia.
  Qed.

  Lemma fta1_proof : ftaend_ok -> ru1_ok -> forall k, fta1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU1. induction k as [|k IH]; unfold fta1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
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
    if_cases Hc.
    { clear Hc. eapply RU1; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply FE; try eassumption; lia.
    - step. (* [comment removed for export] *)
      eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fta8_proof : ftaend_ok -> ru1_ok -> (forall k, fta1_ok k) -> forall k, fta8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU1 T1. induction k as [|k IH]; unfold fta8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
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
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU1; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    shptr_next p.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fta_proof : ftaend_ok -> (forall k, fta1_ok k) -> (forall k, fta8_ok k) -> fta_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE T1 T8. unfold fta_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs) 0%nat fptr fw); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 flen) with (Z_to_bv 64 (flen - Z.of_nat 0)) at 1 by (f_equal; lia).
      eapply (T8 (length fbs) 0%nat fptr fw); try eassumption; try lia.
  Qed.

  Lemma itb_proof : ftaend_ok -> fta_ok -> itb_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE FA. unfold itb_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB; pre; shnow MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - eapply FE; try eassumption; lia.
    - eapply FA; try eassumption; try lia. apply fbs_now; assumption.
  Qed.

  Lemma ita_proof : end_ok -> fta_ok -> ita_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FA. unfold ita_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB; pre; shnow MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - eapply (END (LO7 w8)); try eassumption; try lia. reflexivity.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply FA; try eassumption; try lia. apply fbs_now; assumption.
  Qed.

  Lemma it1_proof : itb_ok -> forall k, it1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TB. induction k as [|k IH]; unfold it1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block ASEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    - eapply TB; try eassumption; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb.
      + replace (Z_to_bv 64 (bv_unsigned p + 2)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned p + 1)) + 1)) by (f_equal; rewrite unsigned_lit by lia; lia).
        eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
      + step. (* [comment removed for export] *)
        eapply TB; try eassumption; lia.
  Qed.

  Lemma it8_proof : itb_ok -> ita_ok -> (forall k, it1_ok k) -> forall k, it8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TB TA T1. induction k as [|k IH]; unfold it8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block ASEGS m IP ibs off 8 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { step. (* [comment removed for export] *) eapply TB; try eassumption; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    shptr_next p.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (ilen - Z.of_nat off + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply TA; try eassumption; try lia. exact tt. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 (bv_unsigned p + 9)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) + 1)) by (f_equal; rewrite unsigned_lit by lia; lia).
      eapply (T1 (length ibs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma it_proof : ita_ok -> (forall k, it1_ok k) -> (forall k, it8_ok k) -> it_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TA T1 T8. unfold it_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB Hoff Hp; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (IP + ilen)) by lia.
    replace (Z_to_bv 64 (IP + ilen - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply TA; try eassumption; try lia. exact tt. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length ibs - off)%nat off p); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length ibs - off)%nat off p); try eassumption; try lia.
  Qed.
End Proof.
End A_parse_mantissa_2.

Module A_parse_mantissa_8c.
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

  (* [comment removed for export] *)
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).

  Ltac i8_body_steps p IBS off :=
    pose proof (ro_block ASEGS _ IP ibs off 8 IBS ltac:(lia)) as BLK;
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *) shr3;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    do 47 step; (* [comment removed for export] *)
    clear BLK.

  Lemma i8body0_proof : forall kk, i1e_ok kk -> imul_ok kk -> i8body_ok kk 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IE IM. unfold i8body_ok; intros until dg; introsF; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc. { exfalso. exact (f8flag0 _ Hc). } clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    - eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
    - step. (* [comment removed for export] *)
      eapply (IM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.

  Lemma i8body1_proof : forall kk, i1e_ok kk -> imul_ok kk -> i8body_ok kk 0 -> i8body_ok kk 1.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IE IM I80. unfold i8body_ok; intros until dg; introsF; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - pose proof (f8flag1 (ilen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb; rewrite ?unsigned_lit in Hb by lia.
      + step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. { exfalso. show. lia. }
        eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
      + shptr_next p.
        replace (Z_to_bv 64 (ilen - Z.of_nat off - 8 + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (ilen - Z.of_nat off - 16)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg + -8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg - 8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        replace (Z_to_bv 64 (dg + 16)) with (Z_to_bv 64 (dg + 8 + 8)) by (f_equal; lia).
        show.
        eapply (I80 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
    - pose proof (f8flag1' (ilen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
      + eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
      + step. (* [comment removed for export] *)
        eapply (IM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.
End Proof.
End A_parse_mantissa_8c.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)

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
  Definition diginc_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells ASEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 SD x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95810) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition rupush_ok (pc : Z) : Prop :=
    forall (w8 : word) (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K <= dg / 19 + 3)%Z ->
      length ws1 = 62%nat -> boxed (sad_inv ws1 cur 1 n1 1) -> ADDV ws1 n1 1 K ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv x10 SHL (Z_to_bv 64 (Z.of_nat n1)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition ruadd_ok (pc : Z) (k : nat) : Prop :=
    forall (j : nat) (w8 : word) (x1 x5 x6 x7 p x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (dg K : Z),
      (n1 - j = k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      FRLO3 w8 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A cur -> length cur = 62%nat -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K <= dg / 19 + 3)%Z ->
      length ws1 = 62%nat -> boxed (sad_inv ws1 cur 1 j 1) -> ADDV ws1 n1 1 K ->
      evt ASEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 dv resv p SHL (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x15 x16 x17
                 x18 x19 x20 x21 SD BB x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m (seg_rom ASEGS)).

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

  Lemma end_proof : end_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    unfold end_ok. intros until K. intros FRLO LOSZ FRH ST XL Hcur XC DG MU WM LEN DGB V KB. bounds.
    do 14 step.
    step. (* [comment removed for export] *)
    release_frame FRLO ST (bv_unsigned sp + -104)%Z.
    release_frame FRH ST (bv_unsigned sp).
    unfold parse_mantissa_post. finish.
    { exact XL. } { exact Hcur. } { exact XC. } { exact DG. } all: try lia.
    - unfold boxed in V. destruct V as [BN _]. exact BN.
    - unfold boxed in V. destruct V as [_ BV].
      eapply Z.lt_le_trans; [exact BV|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Lemma diginc_proof : end_ok -> diginc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END. unfold diginc_ok. intros until K. intros FRLO LOSZ FRH ST XL Hcur XC DG MU WM LEN DGB V KB. bounds. shnow MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply END; try eassumption; try lia.
    all: enough (dg / 19 <= (dg + 1) / 19)%Z by lia; apply Z.div_le_mono; lia.
  Qed.

  Lemma rupush1_proof : diginc_ok -> rupush_ok 0x955cc.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG. unfold rupush_ok. intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM DGB KB Hws1 SI AV; bounds; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    assert (ROOM : (n1 < 62)%nat).
    { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK). eapply (sad_room ws1 cur 1 n1 1 SI); [lia|].
      eapply cap_of_K; [exact BV| lia]. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (Z.of_nat n1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (A + Z.of_nat n1 * 2 ^ 3)) with (Z_to_bv 64 (A + 8 * Z.of_nat n1)) by (f_equal; lia).
    step. (* [comment removed for export] *) shr3.
    replace ((A + 8 * Z.of_nat n1) / 8)%Z with (A / 8 + Z.of_nat n1)%Z by (Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok ASEGS _ A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
    step. (* [comment removed for export] *)
    change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)).
    pose proof (u64arr_write ASEGS _ A cur (Z.of_nat n1) (Z_to_bv 64 1) XL ltac:(lia)) as XL'.
    rewrite Nat2Z.id in XL'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z.of_nat n1 + 1)%Z with (Z.of_nat (S n1)) by lia.
    eapply (DIG [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]); try eassumption; try lia.
    { reflexivity. }
    { rewrite upd_length. exact Hcur. }
    unfold boxed in SI, AV |- *. destruct AV as (BN & _ & BV & HK). replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia. split.
    - apply bnorm_push; [rewrite Hcur; lia|]. rewrite unsigned_lit by lia. lia.
    - rewrite (sad_inv_push ws1 cur 1 n1 1 SI) by (rewrite ?Hws1; lia). exact BV.
  Qed.

  Lemma rupush2_proof : diginc_ok -> rupush_ok 0x957d4.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG. unfold rupush_ok. intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM DGB KB Hws1 SI AV; bounds; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    assert (ROOM : (n1 < 62)%nat).
    { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK). eapply (sad_room ws1 cur 1 n1 1 SI); [lia|].
      eapply cap_of_K; [exact BV| lia]. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (Z.of_nat n1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (A + Z.of_nat n1 * 2 ^ 3)) with (Z_to_bv 64 (A + 8 * Z.of_nat n1)) by (f_equal; lia).
    step. (* [comment removed for export] *) shr3.
    replace ((A + 8 * Z.of_nat n1) / 8)%Z with (A / 8 + Z.of_nat n1)%Z by (Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok ASEGS _ A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
    step. (* [comment removed for export] *)
    change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)).
    pose proof (u64arr_write ASEGS _ A cur (Z.of_nat n1) (Z_to_bv 64 1) XL ltac:(lia)) as XL'.
    rewrite Nat2Z.id in XL'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z.of_nat n1 + 1)%Z with (Z.of_nat (S n1)) by lia.
    eapply (DIG [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]); try eassumption; try lia.
    { reflexivity. }
    { rewrite upd_length. exact Hcur. }
    unfold boxed in SI, AV |- *. destruct AV as (BN & _ & BV & HK). replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia. split.
    - apply bnorm_push; [rewrite Hcur; lia|]. rewrite unsigned_lit by lia. lia.
    - rewrite (sad_inv_push ws1 cur 1 n1 1 SI) by (rewrite ?Hws1; lia). exact BV.
  Qed.

  Lemma ruadd1_proof : diginc_ok -> rupush_ok 0x955cc -> forall k, ruadd_ok 0x9558c k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG PUSH. induction k as [|k IH]; unfold ruadd_ok; intros until K;
      intros Hk Hj Hn1 Hp FRLO FRH ST XL Hcur XC DG MU WM DGB KB Hws1 SI AV; bounds; shnow MU.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      eapply PUSH; eassumption.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH n1); try eassumption; lia. }
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia|]. clear Hz.
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      replace (bv_unsigned p / 8)%Z with (A / 8 + Z.of_nat j)%Z by (rewrite Hp; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_read ASEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write ASEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + 1)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc.
      + (* [comment removed for export] *)
        assert (Hwr : (bv_unsigned w + 1 = 2^64)%Z).
        { destruct (Z.eq_dec (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso. first [ rewrite Z.mod_small in Hc by lia; lia | lia ]. }
        clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH (S j) w8 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
        { rewrite unsigned_lit by lia. lia. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI |- *. rewrite <- Hlimb. apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia].
      + (* [comment removed for export] *)
        assert (Hnw : (bv_unsigned w + 1 < 2^64)%Z).
        { destruct (Z.lt_ge_cases (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          change 18446744073709551616%Z with (2^64)%Z in Hc.
          rewrite <- (Z.mod_unique_pos (bv_unsigned w + 1) (2^64) 1 (bv_unsigned w + 1 - 2^64)) in Hc by lia. lia. }
        clear Hc.
        step. (* [comment removed for export] *)
        eapply (DIG [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]); try eassumption; try lia.
        { reflexivity. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI, AV |- *. destruct AV as (BN & _ & BV & HK). rewrite Nat2Z.id, <- Hlimb. split.
        * apply (sad_bnorm_stop ws1 cur 1 j 1 n1 SI); rewrite ?Hws1; try lia. exact BN.
        * rewrite (sad_inv_stop ws1 cur 1 j 1 n1 SI) by (rewrite ?Hws1; lia). exact BV.
  Qed.

  Lemma ruadd2_proof : diginc_ok -> rupush_ok 0x957d4 -> forall k, ruadd_ok 0x95794 k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG PUSH. induction k as [|k IH]; unfold ruadd_ok; intros until K;
      intros Hk Hj Hn1 Hp FRLO FRH ST XL Hcur XC DG MU WM DGB KB Hws1 SI AV; bounds; shnow MU.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      eapply PUSH; eassumption.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH n1); try eassumption; lia. }
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia|]. clear Hz.
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      replace (bv_unsigned p / 8)%Z with (A / 8 + Z.of_nat j)%Z by (rewrite Hp; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_read ASEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write ASEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + 1)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc.
      + (* [comment removed for export] *)
        assert (Hnw : (bv_unsigned w + 1 < 2^64)%Z).
        { destruct (Z.lt_ge_cases (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          change 18446744073709551616%Z with (2^64)%Z in Hc.
          rewrite <- (Z.mod_unique_pos (bv_unsigned w + 1) (2^64) 1 (bv_unsigned w + 1 - 2^64)) in Hc by lia. lia. }
        clear Hc.
        eapply (DIG [C8 numv; C8 w8; C8 (Z_to_bv 64 (A + 496)); C8 (Z_to_bv 64 TBL10); C8 mdw; C8 resv; C8 dv]); try eassumption; try lia.
        { reflexivity. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI, AV |- *. destruct AV as (BN & _ & BV & HK). rewrite Nat2Z.id, <- Hlimb. split.
        * apply (sad_bnorm_stop ws1 cur 1 j 1 n1 SI); rewrite ?Hws1; try lia. exact BN.
        * rewrite (sad_inv_stop ws1 cur 1 j 1 n1 SI) by (rewrite ?Hws1; lia). exact BV.
      + (* [comment removed for export] *)
        assert (Hwr : (bv_unsigned w + 1 = 2^64)%Z).
        { destruct (Z.eq_dec (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso. first [ rewrite Z.mod_small in Hc by lia; lia | lia ]. }
        clear Hc.
        step. (* [comment removed for export] *)
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH (S j) w8 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
        { rewrite unsigned_lit by lia. lia. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI |- *. rewrite <- Hlimb. apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia].
  Qed.

  Lemma ru1_proof : (forall k, ruadd_ok 0x9558c k) -> ru1_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros ADD; unfold ru1_ok, ru_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM LEN DGB V KB; bounds; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { unfold boxed in V; destruct V as [_ BV]; rewrite unsigned_lit by lia.
      apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
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
    step. (* [comment removed for export] *)
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
    eapply (ADD (Z.to_nat len1) 0%nat w8 _ _ _ _ resv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 cur1 (Z.to_nat len1) dg (K + 1)%Z);
      try eassumption; try lia.
    { replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1. }
    { unfold boxed. apply sad_inv_init. }
    unfold boxed in V |- *. destruct V as [BN BV]. rewrite unsigned_lit in HV1, HN1 by lia.
    split; [apply HN1; [lia| exact BN] |]. split; [lia|]. split; [| lia].
    rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
    apply (addnative_bound (bval cur (Z.to_nat len)) 10 1 K); lia.
  Qed.

  Lemma ru2_proof : (forall k, ruadd_ok 0x95794 k) -> ru2_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros ADD; unfold ru2_ok, ru_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM LEN DGB V KB; bounds; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { unfold boxed in V; destruct V as [_ BV]; rewrite unsigned_lit by lia.
      apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
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
    step. (* [comment removed for export] *)
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
    eapply (ADD (Z.to_nat len1) 0%nat w8 _ _ _ _ resv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 cur1 (Z.to_nat len1) dg (K + 1)%Z);
      try eassumption; try lia.
    { replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1. }
    { unfold boxed. apply sad_inv_init. }
    unfold boxed in V |- *. destruct V as [BN BV]. rewrite unsigned_lit in HV1, HN1 by lia.
    split; [apply HN1; [lia| exact BN] |]. split; [lia|]. split; [| lia].
    rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
    apply (addnative_bound (bval cur (Z.to_nat len)) 10 1 K); lia.
  Qed.
End Proof.
