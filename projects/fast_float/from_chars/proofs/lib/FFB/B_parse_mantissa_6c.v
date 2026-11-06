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
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_add_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_stmt.

Module B_parse_mantissa_2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_add_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_stmt.
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
  Hypothesis small_add_spec : small_add_stmt.
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
  Hypothesis FBS0 : boxed (bytes_at BSEGS m0 (bv_unsigned fptr) fbs).
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
  Hypothesis LA : (bv_unsigned sp <= bv_unsigned numv + 32)%Z.          (* [comment removed for export] *)
  Hypothesis LN : (bv_unsigned numv + 64 <= bv_unsigned dv)%Z.
  Hypothesis LR : (bv_unsigned resv + 504 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz BSEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz BSEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz BSEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz BSEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz BSEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz BSEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells BSEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation TBLW := (Z_to_bv 64 TBL10).                          (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells BSEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells BSEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells BSEGS m (SP + -160)
     [C8 numv; C8 w8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv]).
  Notation FRLOJ j8 m := (rw_cells BSEGS m (SP + -160)
     [C8 numv; CB 8 j8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv]).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz BSEGS m (ASAN_B + A / 8) 63 /\ shz BSEGS m (ASAN_B + D / 8) 1 /\ shz BSEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz BSEGS m (ASAN_B + gi) gin /\ shz BSEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells BSEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

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
    shz BSEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at BSEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport BSEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr BSEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


  (* [comment removed for export] *)
  Ltac kill_trap := let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia] | clear Hc ].

  (* [comment removed for export] *)
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).

  Notation LO7 w8 := [C8 numv; C8 w8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv].
  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells BSEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95f20) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ru_ok : Prop :=
    forall (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 SD x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95eec) fc None m (seg_rom BSEGS)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ftb1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95cc0) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftb8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x17
                 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95bfc) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftb_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95bd4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftaend_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95ee8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta1_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p fw (Z_to_bv 64 48) (Z_to_bv 64 (FP + flen)) p (Z_to_bv 64 (-1)) x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95eac) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta8_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x7 x8 x9 x12 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x7 x8 x9 p fw x12 (Z_to_bv 64 (FP + flen)) p (Z_to_bv 64 (flen - Z.of_nat off))
                 (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8))
                 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95de8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95d64) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x14 x15 x16 x17 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95b4c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (ilen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x17
                 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x959b4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9598c) fc None m (seg_rom BSEGS)).
  Lemma ftb1_proof : end_ok -> ru_ok -> forall k, ftb1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU. induction k as [|k IH]; unfold ftb1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    pose proof (ro_block BSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { clear He. eapply (END (LO7 w8)); try eassumption; try lia. reflexivity. }
    step. (* [comment removed for export] *)
    eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma ftb8_proof : end_ok -> ru_ok -> (forall k, ftb1_ok k) -> forall k, ftb8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU T1. induction k as [|k IH]; unfold ftb8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    pose proof (ro_block BSEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
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
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *) kill_trap.
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
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - off)%nat off p); try eassumption; try lia.
    - step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length fbs - off)%nat off p); try eassumption; try lia.
  Qed.

  Lemma ftaend_proof : end_ok -> ru_ok -> ftaend_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU. unfold ftaend_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB; pre.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    - eapply (END (LO7 w8)); try eassumption; try lia. reflexivity.
    - eapply RU; try eassumption; lia.
  Qed.

  Lemma fta1_proof : ftaend_ok -> ru_ok -> forall k, fta1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU. induction k as [|k IH]; unfold fta1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    pose proof (ro_block BSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply FE; try eassumption; lia.
    - step. (* [comment removed for export] *)
      eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fta8_proof : ftaend_ok -> ru_ok -> (forall k, fta1_ok k) -> forall k, fta8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU T1. induction k as [|k IH]; unfold fta8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB FBS FNZ Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    pose proof (ro_block BSEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
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
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *) kill_trap.
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
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fta_proof : ftaend_ok -> (forall k, fta1_ok k) -> (forall k, fta8_ok k) -> fta_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE T1 T8. unfold fta_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB; pre; shnow MU.
    pose proof (rw_cells_bound _ _ _ _ NUM) as BN; cbn [cells_size csize Nat.add] in BN.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    { clear Hz. eapply FE; try eassumption; lia. }
    cond_cleanup Hz.
    pose proof (fbs_now _ MU Hz) as FBS. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    destruct (shf_now _ MU Hz) as (SHF & GF1 & GF2).
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
    rewrite ?(unsigned_lit flen) by lia.
    replace (Z_to_bv 64 (flen + FP)) with (Z_to_bv 64 (FP + flen)) by (f_equal; lia).
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) setcmp. decide_ltb.
    step. (* [comment removed for export] *) setcmp. decide_ltb.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    try kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs) 0%nat fptr fw); try eassumption; try lia.
    - step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 flen) with (Z_to_bv 64 (flen - Z.of_nat 0)) by (f_equal; lia).
      eapply (T8 (length fbs) 0%nat fptr fw); try eassumption; try lia.
  Qed.

  Lemma it1_proof : fta_ok -> forall k, it1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FTA. induction k as [|k IH]; unfold it1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block BSEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply FTA; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply FTA; try eassumption; lia. }
    step. (* [comment removed for export] *)
    eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma it8_proof : fta_ok -> (forall k, it1_ok k) -> forall k, it8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FTA T1. induction k as [|k IH]; unfold it8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block BSEGS m IP ibs off 8 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
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
    { clear Hc. step. (* [comment removed for export] *) eapply FTA; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *) kill_trap.
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
      { step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply FTA; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length ibs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma it_proof : fta_ok -> (forall k, it1_ok k) -> (forall k, it8_ok k) -> it_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FTA T1 T8. unfold it_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V KB Hoff Hp; pre; shnow MU.
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
      { step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply FTA; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length ibs - off)%nat off p); try eassumption; try lia.
    - step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length ibs - off)%nat off p); try eassumption; try lia.
  Qed.
End Proof.
End B_parse_mantissa_2.

Module B_parse_mantissa_3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_add_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_stmt.
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
  Hypothesis small_add_spec : small_add_stmt.
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
  Hypothesis FBS0 : boxed (bytes_at BSEGS m0 (bv_unsigned fptr) fbs).
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
  Hypothesis LA : (bv_unsigned sp <= bv_unsigned numv + 32)%Z.          (* [comment removed for export] *)
  Hypothesis LN : (bv_unsigned numv + 64 <= bv_unsigned dv)%Z.
  Hypothesis LR : (bv_unsigned resv + 504 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz BSEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz BSEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz BSEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz BSEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz BSEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz BSEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells BSEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation TBLW := (Z_to_bv 64 TBL10).                          (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells BSEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells BSEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells BSEGS m (SP + -160)
     [C8 numv; C8 w8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv]).
  Notation FRLOJ j8 m := (rw_cells BSEGS m (SP + -160)
     [C8 numv; CB 8 j8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv]).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz BSEGS m (ASAN_B + A / 8) 63 /\ shz BSEGS m (ASAN_B + D / 8) 1 /\ shz BSEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz BSEGS m (ASAN_B + gi) gin /\ shz BSEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells BSEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

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
    shz BSEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at BSEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport BSEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr BSEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


  (* [comment removed for export] *)
  Ltac kill_trap := let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia] | clear Hc ].

  (* [comment removed for export] *)
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).

  Notation LO7 w8 := [C8 numv; C8 w8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv].
  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells BSEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95f20) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ru_ok : Prop :=
    forall (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 SD x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95eec) fc None m (seg_rom BSEGS)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ftb1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95cc0) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftb8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x17
                 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95bfc) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftb_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95bd4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftaend_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95ee8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta1_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p fw (Z_to_bv 64 48) (Z_to_bv 64 (FP + flen)) p (Z_to_bv 64 (-1)) x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95eac) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta8_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x7 x8 x9 x12 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x7 x8 x9 p fw x12 (Z_to_bv 64 (FP + flen)) p (Z_to_bv 64 (flen - Z.of_nat off))
                 (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8))
                 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95de8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95d64) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x14 x15 x16 x17 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95b4c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (ilen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x17
                 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x959b4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9598c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition TBL10V : list Z := Eval vm_compute in (map (fun k => 10 ^ Z.of_nat k)%Z (seq 0 20)).
  Lemma TBL10V_ok : table_b BSEGS TBL10 8 (fun v => le8 (Z_to_bv 64 v)) TBL10V = true.
  Proof. LiaFast.lf_pins LiaFast.lf_all. vm_compute. reflexivity. Qed.
  Lemma TBL10V_nth : forall c, (0 <= c <= 19)%Z -> (1 <= nth (Z.to_nat c) TBL10V 0 < 2^64)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros c Hc.
    assert (H : forall n, (n < 20)%nat -> (1 <= nth n TBL10V 0 < 2^64)%Z).
    { intros n Hn. do 20 (destruct n as [|n]; [cbn; lia|]). lia. }
    apply H. lia.
  Qed.
  (* [comment removed for export] *)
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (cnt K : Z) (w8 : word) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 19)%Z -> (19 * (K + 1) <= dg + 36)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 x18 x19 vw SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95948) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (cnt K : Z) (w8 : word) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 19)%Z -> (19 * (K + 1) <= dg + 36)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 x18 vw p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95b90) fc None m (seg_rom BSEGS)).
  (* [comment removed for export] *)
  Ltac muladd_seq XL Hcur XC V cur len K cnt vw ST MU :=
    let RD := fresh "RD" in let Hy := fresh "Hy" in let BN := fresh "BN" in let BV := fresh "BV" in
    step; (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3)%Z with 8%Z;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    kill_trap;
    step; (* [comment removed for export] *)
    replace (Z_to_bv 64 (TBL10 + cnt * 8)) with (Z_to_bv 64 (TBL10 + 8 * cnt)) by (f_equal; lia);
    step; (* [comment removed for export] *) shr3;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    lazymatch goal with PR : pristine ?mq IMG_LO ROD_HI |- _ =>
      pose proof (table_read BSEGS _ _ _ _ mq _ _ TBL10V_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD end;
    step; (* [comment removed for export] *)
    clear RD;
    pose proof (TBL10V_nth cnt ltac:(lia)) as Hy; set (y := nth (Z.to_nat cnt) TBL10V 0%Z) in *;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    unfold boxed in V; destruct V as [BN BV];
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len);
    [ exact XL | exact Hcur | exact XC | lia
    | rewrite unsigned_lit by lia; apply (cap_mul _ _ K); try lia; pose proof (bval_nonneg cur (Z.to_nat len)); lia
    | rewrite (unsigned_lit (SP + -160)) by lia; replace (SP + -160 - 16)%Z with (SP + -176)%Z by lia; exact ST
    | eassumption | eassumption
    | rewrite (unsigned_lit (SP + -160)) by lia; lia | rewrite (unsigned_lit (SP + -160)) by lia; lia
    | rewrite (unsigned_lit (SP + -160)) by lia; lia | rewrite (unsigned_lit (SP + -160)) by lia; lia | lia | lia
    | eassumption | ].

  Ltac after_mul cur len XL1 XC1 HB1 HV1 HN1 cur1 len1 Hcur1 BdX1 ST1 m1 MU1 :=
    lazymatch goal with
    | XL' : u64arr BSEGS ?m' A ?cur', XC' : rw_cells BSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end;
    lazymatch goal with ST' : stk BSEGS _ (bv_unsigned SP' - 16) _ |- _ =>
      rewrite (unsigned_lit (SP + -160)) in ST' by lia; replace (SP + -160 - 16)%Z with (SP + -176)%Z in ST' by lia; rename ST' into ST1 end;
    rewrite unsigned_lit in HV1, HN1 by lia;
    pose proof (u64arr_bound _ _ _ _ XL1) as BdX1; lazymatch goal with H : length cur1 = 62%nat |- _ => rename H into Hcur1 end; rewrite Hcur1 in BdX1;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end;
    match goal with H : munch _ m0 m1 |- _ => rename H into MU1 end.

  Ltac add_call XL1 Hcur1 XC1 HV1 cur cur1 len len1 K ST1 BV :=
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    call (small_add_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 len1);
    [ exact XL1 | exact Hcur1 | exact XC1 | lia
    | rewrite HV1; pose proof (bval_nonneg cur (Z.to_nat len));
      eapply cap_of_K with (K := (K + 1)%Z); [| lia]; apply addnative_bound; lia
    | rewrite (unsigned_lit (SP + -160)) by lia; replace (SP + -160 - 16)%Z with (SP + -176)%Z by lia; exact ST1
    | eassumption | eassumption
    | rewrite (unsigned_lit (SP + -160)) by lia; lia | rewrite (unsigned_lit (SP + -160)) by lia; lia
    | rewrite (unsigned_lit (SP + -160)) by lia; lia | rewrite (unsigned_lit (SP + -160)) by lia; lia | lia | lia
    | eassumption | ].

  Ltac after_add cur1 len1 XL2 XC2 HB2 HV2 HN2 cur2 len2 ST2 m2 MU2 :=
    lazymatch goal with
    | XL' : u64arr BSEGS ?m' A ?cur', XC' : rw_cells BSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len1 <= ?len' <= len1 + 1 /\ _)%Z, HV : bval _ _ = (bval cur1 (Z.to_nat len1) + _)%Z, HN : (bnorm cur1 _ -> bnorm _ _) |- _ =>
      rename XL' into XL2; rename XC' into XC2; rename HB into HB2; rename HV into HV2; rename HN into HN2;
      set (cur2 := cur') in *; set (len2 := len') in *
    end;
    lazymatch goal with ST' : stk BSEGS _ (bv_unsigned SP' - 16) _ |- _ =>
      rewrite (unsigned_lit (SP + -160)) in ST' by lia; replace (SP + -160 - 16)%Z with (SP + -176)%Z in ST' by lia; rename ST' into ST2 end;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end;
    match goal with H : munch _ m0 m2 |- _ => rename H into MU2 end.

  Lemma itrunc_proof : it_ok -> itrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IT. unfold itrunc_ok; intros until dg; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V HK Hcnt HKd Hoff Hp; pre; shnow MU.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) kill_trap.
    muladd_seq XL Hcur XC V cur len K cnt vw ST MU.
    after_mul cur len XL1 XC1 HB1 HV1 HN1 cur1 len1 Hcur1 BdX1 ST1 m1 MU1.
    clear SHX SHD SHN SHI SHT PRG BC PR. shnow MU1.
    add_call XL1 Hcur1 XC1 HV1 cur cur1 len len1 K ST1 BV.
    after_add cur1 len1 XL2 XC2 HB2 HV2 HN2 cur2 len2 ST2 m2 MU2.
    rewrite ?unsigned_lit in HV2 by lia.
    eapply (IT off p w8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur2 len2 dg (K + 1)%Z); try eassumption; try lia.
    { unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
      rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    all: enough ((dg + 36) / 19 <= dg / 19 + 2)%Z; [ assert (K + 1 <= (dg + 36) / 19)%Z by (apply Z.div_le_lower_bound; lia); lia | Z.div_mod_to_equations; lia ].
  Qed.

  Lemma ftrunc_proof : ftb_ok -> ftrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FT. unfold ftrunc_ok; intros until dg; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V HK Hcnt HKd FBS FNZ Hoff Hp; pre; shnow MU.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) kill_trap.
    muladd_seq XL Hcur XC V cur len K cnt vw ST MU.
    after_mul cur len XL1 XC1 HB1 HV1 HN1 cur1 len1 Hcur1 BdX1 ST1 m1 MU1.
    clear SHX SHD SHN SHI SHT PRG BC PR. shnow MU1.
    add_call XL1 Hcur1 XC1 HV1 cur cur1 len len1 K ST1 BV.
    after_add cur1 len1 XL2 XC2 HB2 HV2 HN2 cur2 len2 ST2 m2 MU2.
    rewrite ?unsigned_lit in HV2 by lia.
    eapply (FT off p w8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur2 len2 dg (K + 1)%Z); try eassumption; try lia.
    { unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
      rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    { apply fbs_now; assumption. }
    all: enough ((dg + 36) / 19 <= dg / 19 + 2)%Z; [ assert (K + 1 <= (dg + 36) / 19)%Z by (apply Z.div_le_lower_bound; lia); lia | Z.div_mod_to_equations; lia ].
  Qed.
End Proof.
End B_parse_mantissa_3.

Module B_small_add.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_add_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
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

(* [comment removed for export] *)
Definition sadd_inv (ws cur : list word) (y : Z) (i : nat) (cv : Z) : Prop :=
  (bval cur i + cv * 2 ^ (64 * Z.of_nat i) = bval ws i + y)%Z
  /\ (forall j, (i <= j)%nat -> nth j cur w0 = nth j ws w0)
  /\ length cur = length ws.

Lemma sadd_inv_init : forall ws y, sadd_inv ws ws y 0 y.
Proof. intros. split; [cbn; lia|]. split; [intros; reflexivity| reflexivity]. Qed.

Lemma sadd_inv_step_val : forall ws cur y i cv,
  sadd_inv ws cur y i cv -> (i < length ws)%nat -> (0 <= cv < 2^64)%Z ->
  let x := limbZ ws i in
  (bval (upd cur i (Z_to_bv 64 (x + cv))) (S i) + (if (x + cv <? 2^64)%Z then 0 else 1) * 2 ^ (64 * Z.of_nat (S i))
   = bval ws (S i) + y)%Z
  /\ (forall j, (S i <= j)%nat -> nth j (upd cur i (Z_to_bv 64 (x + cv))) w0 = nth j ws w0)
  /\ length (upd cur i (Z_to_bv 64 (x + cv))) = length ws.
Proof.
  intros ws cur y i cv (Hv & Hag & Hl) Hi Hcv x.
  pose proof (limbZ_range ws i) as Hx. fold x in Hx.
  split; [| split; [intros j Hj; rewrite nth_upd_other by lia; apply Hag; lia | rewrite upd_length; exact Hl]].
  rewrite bval_push by (rewrite Hl; exact Hi). rewrite bval_S, pow64_S.
  rewrite unsigned_lit_wrap.
  replace (limbZ ws i) with x by reflexivity.
  destruct (Z.ltb_spec (x + cv) (2 ^ 64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. nia.
  - rewrite <- (Z.mod_unique_pos (x + cv) (2^64) 1 (x + cv - 2^64)) by lia. nia.
Qed.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word).
  Variables (vec : word) (y : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (j8 : list byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 <= len <= 62)%Z.
  Hypothesis Hy : (0 < y < 2^64)%Z.
  Hypothesis CAP : (bval ws (Z.to_nat len) + y < BIG_CAP)%Z.
  Hypothesis SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z.
  Hypothesis KA1 : (bv_unsigned vec + 504 <= KTOP)%Z.

  Notation A := (bv_unsigned vec).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation A5 := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation POST := (small_add_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc A y ws len m0).
  Notation NOTA := (Z_to_bv 64 (Z.lxor A 18446744073709551615)).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p cw x29 x30 : word) (cv : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i <= Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (i = 0%nat -> cv = y) -> ((0 < i)%nat -> cv = 1%Z) ->
      u64arr BSEGS m A cur -> length cur = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      sadd_inv ws cur y i cv ->
      munch (small_add_W A sp) m0 m -> wmono BSEGS m0 m ->
      rw_cells BSEGS m (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
      stk BSEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16) ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      evt BSEGS POST
        (MS (mkR ra SP' gp tp NOTA (Z_to_bv 64 (-512 + 8 * Z.of_nat i)) (Z_to_bv 64 (len - Z.of_nat i)) s0 s1 (Z_to_bv 64 1) cw
                 (Z_to_bv 64 (A + 496)) vec p A5 BB (Z_to_bv 64 len)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p x29 x30 t6)
            F (Z_to_bv 64 0x96a8c) fc None m (seg_rom BSEGS)).

  #[using="Hlen LEN Hy SEP KSP KSP2 KA0"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hy SEP KSP KSP2 KA0 : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p cw x29 x30 cv cur m Hk Hi Hp Hcw Hcv Hcv0 Hcv1 CUR Hcur LC INV MU WM FR ST SHZ.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 cw) as Rcw. unfold bv_modulus in Rcw.
    pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
    cbv delta [small_add_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
    assert (Hil : (i < Z.to_nat len)%nat) by lia.
    destruct INV as (Hv & Hag & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    try if_not_taken.
    step. (* [comment removed for export] *) shr3.
    replace (bv_unsigned p / 8)%Z with (A / 8 + Z.of_nat i)%Z by (rewrite Hp; Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read BSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok BSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write BSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (sadd_inv_step_val ws cur y i cv (conj Hv (conj Hag Hlc)) ltac:(rewrite Hlen; lia) ltac:(lia)) as (Hv' & Hag' & Hlc').
    unfold limbZ in Hv', Hag', Hlc'. rewrite <- Hw, Hcw in *.
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb. rewrite ?v_sltu_b2z in Hb. rewrite ?unsigned_lit_wrap in Hb. decide_ltb_in Hb.
      pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hb) as Hge.
      replace (bv_unsigned w + cv <? 2 ^ 64)%Z with false in Hv' by (symmetry; apply Z.ltb_ge; lia).
      replace (-512 + 8 * Z.of_nat i + 8)%Z with (-512 + 8 * Z.of_nat (S i))%Z by lia.
      replace (len - Z.of_nat i + -1)%Z with (len - Z.of_nat (S i))%Z by lia.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) _ _ 1%Z); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. reflexivity.
      + split; [exact Hv'| split; [exact Hag'| exact Hlc']].
    - (* [comment removed for export] *)
      cond_cleanup Hb. rewrite ?v_sltu_b2z in Hb. rewrite ?unsigned_lit_wrap in Hb. decide_ltb_in Hb.
      pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hb) as Hlt.
      replace (bv_unsigned w + cv <? 2 ^ 64)%Z with true in Hv' by (symmetry; apply Z.ltb_lt; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      unfold small_add_post. finish.
      { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia. all: try eassumption.
      + (* [comment removed for export] *)
        replace ((if true then 0 else 1) : Z) with 0%Z in Hv' by reflexivity.
        pose proof (bval_agree_above _ _ (S i) (Z.to_nat len) ltac:(lia) Hag') as E. lia.
      + (* [comment removed for export] *)
        intros BN. right. unfold limbZ.
        destruct (Nat.eq_dec (Z.to_nat len - 1) i) as [E|E].
        * rewrite E, nth_upd_same by (rewrite Hcur; lia). rewrite unsigned_lit by lia. lia.
        * rewrite Hag' by lia. apply (bnorm_top ws (Z.to_nat len) ltac:(lia) BN).
  Qed.

  (* [comment removed for export] *)
  #[using="Hlen LEN Hy CAP SEP KSP KSP2 KA0 KA1"] Lemma loop_exit : forall k, loop_ok k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hy CAP SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; [| apply loop_body; exact IH].
    unfold loop_ok. intros i p cw x29 x30 cv cur m Hk Hi Hp Hcw Hcv Hcv0 Hcv1 CUR Hcur LC INV MU WM FR ST SHZ.
    assert (Hil : i = Z.to_nat len) by lia.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 cw) as Rcw. unfold bv_modulus in Rcw.
    cbv delta [small_add_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
    destruct INV as (Hv & Hag & Hlc).
    (* [comment removed for export] *)
    assert (ROOM : (len <= 61)%Z).
    { subst i. pose proof (bval_nonneg cur (Z.to_nat len)) as B0.
      destruct (Z.le_gt_cases len 61) as [|Hgt]; [assumption|]. exfalso.
      assert (E62 : Z.to_nat len = 62%nat) by lia. rewrite E62 in Hv, B0, CAP.
      unfold BIG_CAP in CAP. change (64 * Z.of_nat 62)%Z with 3968%Z in Hv.
      pose proof (Z.pow_pos_nonneg 2 3968 ltac:(lia) ltac:(lia)) as P0.
      assert (2 ^ 3968 <= cv * 2 ^ 3968)%Z by nia. lia. }
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit len) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
    step. (* [comment removed for export] *)
    try if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    replace ((A + 8 * len) / 8)%Z with (A / 8 + len)%Z by (Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok BSEGS m A cur len (Z_to_bv 64 (A + 8 * len)) CUR ltac:(lia) eq_refl) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write BSEGS m A cur len cw CUR ltac:(lia)) as CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold small_add_post. finish.
    { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia. all: try eassumption.
    + replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. rewrite <- Hil.
      rewrite bval_push by (rewrite Hlc, Hlen; lia). rewrite Hcw. subst i. lia.
    + intros _. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. rewrite <- Hil.
      apply bnorm_push; [rewrite Hcur; lia|]. rewrite Hcw. exact Hcv.
  Qed.
End Loop.

Lemma small_add_spec : small_add_stmt.
Proof.
  unfold small_add_stmt. intros until len. intros LIMBS Hlen LC LEN CAP ST PRG BC SEP RO3 KSP KSP2 KA0 KA1 SHZ.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 a1) as Ry. unfold bv_modulus in Ry.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
  pose proof (munch_refl (small_add_W (bv_unsigned a0) sp) m) as MU. cbv delta [small_add_W] in MU.
  pose proof (wmono_refl BSEGS m) as WM.
  carve_frame 16%nat ST.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hy0.
  - (* [comment removed for export] *)
    cond_cleanup Hy0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold small_add_post. finish.
    { exact LIMBS. } { exact Hlen. } { exact LC. } all: try lia. all: try eassumption.
    intros BN; exact BN.
  - cond_cleanup Hy0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
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
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    change (Z_to_bv 64 (-512)) with (Z_to_bv 64 (-512 + 8 * Z.of_nat 0)).
    replace (Z_to_bv 64 len) with (Z_to_bv 64 (len - Z.of_nat 0)) at 1 by (f_equal; lia).
    match goal with |- ?g => idtac g end.
    eapply (loop_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 a0 (bv_unsigned a1) F fc m _ ws len
              Hlen LEN ltac:(lia) CAP SEP KSP KSP2 KA0 KA1 (Z.to_nat len) 0%nat a0 a1); try eassumption; try lia.
    all: try apply sadd_inv_init.
    all: match goal with |- ?g => idtac g end.
Qed.
End B_small_add.

Module B_small_mul.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
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

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word).
  Variables (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z) (j8 : list byte).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z.
  Hypothesis SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z.
  Hypothesis RO3 : (IMG_END <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z.
  Hypothesis KA1 : (bv_unsigned vec + 504 <= KTOP)%Z.

  Notation A := (bv_unsigned vec).
  Notation y := (bv_unsigned yw).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation A5 := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation POST := (small_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A y ws len m0).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p q cnt x29 x30 x31 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned q = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned cnt = (63 - Z.of_nat i)%Z ->
      u64arr BSEGS m A cur -> length cur = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      smul_inv ws cur y i c ->
      munch (small_mul_W A sp) m0 m -> wmono BSEGS m0 m ->
      rw_cells BSEGS m (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
      stk BSEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16) ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      evt BSEGS POST
        (MS (mkR ra SP' gp tp (Z_to_bv 64 c) (Z_to_bv 64 63) p s0 s1 (Z_to_bv 64 (A + 496)) yw vec (Z_to_bv 64 1) q A5 BB (Z_to_bv 64 len)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cnt x29 x30 x31)
            F (Z_to_bv 64 0x96970) fc None m (seg_rom BSEGS)).

  #[using="Hlen LEN CAP SEP KSP KSP2 KA0 KA1"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p q cnt x29 x30 x31 c cur m Hk Hi Hp Hq Hcnt CUR Hcur LC INV MU WM FR ST SHZ.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    cbv delta [small_mul_W] in MU.
    pose proof (bv_unsigned_in_range 64 yw) as Ry. unfold bv_modulus in Ry.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *) shr3. rewrite Hq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read BSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok BSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write BSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    first [ rewrite (smul_carry_word (bv_unsigned w) y c) by lia | rewrite (smul_carry_word' (bv_unsigned w) y c) by lia ].
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite Hlen; lia |].
      unfold limbZ. rewrite <- Hw. apply smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 (bv_unsigned q + 8)) (Z_to_bv 64 (bv_unsigned cnt + -1)));
        try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      pose proof (proj1 (proj2 (proj2 INV'))) as Hc'. cbn beta in Hc'.
      remember (mul_cout (limbZ ws i) y c) as c' eqn:Ec'.
      step. (* [comment removed for export] *)
      if_cases Hz.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold small_mul_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        * rewrite <- Hil. rewrite (Z.mul_comm (bval ws _) y). apply (smul_inv_finish_nocarry ws _ y (S i)). rewrite <- Hz. exact INV'.
        * intros Hy BN. rewrite <- Hil in BN |- *. right. cbn [Nat.sub]. rewrite Nat.sub_0_r.
          unfold limbZ. rewrite nth_upd_same by (rewrite Hcur; lia).
          rewrite (smul_lo_word (bv_unsigned w) y c) by lia.
          unfold limbZ in Ec'. rewrite <- Hw in Ec'.
          apply smul_top_nonzero; try lia.
          destruct BN as [BN|BN]; [lia|]. cbn [Nat.sub] in BN. rewrite Nat.sub_0_r in BN. unfold limbZ in BN. rewrite <- Hw in BN. lia.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        pose proof (smul_carry_room ws _ y _ _ INV' ltac:(lia) ltac:(rewrite Hil; lia)) as ROOM.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit len) by lia. rewrite Z.shiftl_mul_pow2 by lia.
        replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Ht; [ cond_cleanup Ht; rewrite ?zb_lxor_ones in Ht by lia; rewrite ?unsigned_lit in Ht by lia; exfalso; lia | clear Ht ].
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (u64arr_store_ok BSEGS m1 A _ len (Z_to_bv 64 (A + 8 * len)) CUR' ltac:(rewrite upd_length; lia) eq_refl) as SOK2.
        step. (* [comment removed for export] *)
        pose proof (u64arr_write BSEGS m1 A _ len (Z_to_bv 64 c') CUR' ltac:(rewrite upd_length; lia)) as CUR''.
        store_done.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold small_mul_post. finish.
        { exact CUR''. } { rewrite !upd_length. exact Hcur. } { exact LC. } all: try lia.
        * replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. replace (Z.to_nat len) with (S i) by lia.
          rewrite (Z.mul_comm (bval ws _) y). subst c'. apply (smul_inv_finish_carry ws _ y (S i)); [exact INV'| rewrite Hlen; lia].
        * intros Hy BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          apply bnorm_push; [rewrite upd_length, Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
          (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z) (j8 : list byte)
          (Hlen : length ws = 62%nat) (LEN : (0 < len <= 62)%Z)
          (CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z)
          (SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z)
          (RO3 : (IMG_END <= bv_unsigned sp + -16)%Z)
          (KSP : (KHI <= bv_unsigned sp + -16)%Z)
          (KSP2 : (bv_unsigned sp <= KTOP)%Z)
          (KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z)
          (KA1 : (bv_unsigned vec + 504 <= KTOP)%Z).
  #[using="Hlen LEN CAP SEP KSP KSP2 KA0 KA1"] Lemma sm_loop : forall k, loop_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 vec yw F fc m0 ws len j8 k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH].
    - unfold loop_ok. intros. exfalso. lia.
    - apply loop_body; assumption.
  Qed.
End Loop2.

Lemma small_mul_spec : small_mul_stmt.
Proof.
  unfold small_mul_stmt. intros until len. intros LIMBS Hlen LC LEN CAP ST PRG BC SEP RO3 KSP KSP2 KA0 KA1 SHZ.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
  pose proof (munch_refl (small_mul_W (bv_unsigned a0) sp) m) as MU. cbv delta [small_mul_W] in MU.
  pose proof (wmono_refl BSEGS m) as WM.
  carve_frame 16%nat ST.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *) shr3.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hz.
  - (* [comment removed for export] *)
    cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold small_mul_post. finish.
    { exact LIMBS. } { exact Hlen. } { exact LC. } all: try lia.
    + subst len. change (Z.to_nat 0) with 0%nat. rewrite bval_0. lia.
    + intros _ BN. exact BN.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply sm_loop with (k := Z.to_nat len) (i := 0%nat); try eassumption; try lia.
    + rewrite unsigned_lit by lia. lia.
    + apply smul_inv_init.
Qed.
End B_small_mul.

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
  Hypothesis small_add_spec : small_add_stmt.
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
  Hypothesis FBS0 : boxed (bytes_at BSEGS m0 (bv_unsigned fptr) fbs).
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
  Hypothesis LA : (bv_unsigned sp <= bv_unsigned numv + 32)%Z.          (* [comment removed for export] *)
  Hypothesis LN : (bv_unsigned numv + 64 <= bv_unsigned dv)%Z.
  Hypothesis LR : (bv_unsigned resv + 504 <= GLO + FSSIZE)%Z.
  Hypothesis SFS : ((THI <= bv_unsigned resv \/ bv_unsigned resv + 498 <= FS) /\ GLO + FSSIZE <= bv_unsigned sp - 176 /\ THI <= bv_unsigned sp - 176)%Z.
  (* [comment removed for export] *)
  Hypothesis SHX0 : shz BSEGS m0 (ASAN_B + bv_unsigned resv / 8) 63.
  Hypothesis SHD0 : shz BSEGS m0 (ASAN_B + bv_unsigned dv / 8) 1.
  Hypothesis SHN0 : shz BSEGS m0 (ASAN_B + (bv_unsigned numv + 32) / 8) 4.
  Hypothesis SHI0 : shz BSEGS m0 (ASAN_B + gi) gin.
  Hypothesis GI1 : (0 <= gi <= bv_unsigned iptr / 8)%Z.
  Hypothesis GI2 : (bv_unsigned iptr + ilen <= 8 * (gi + gin) <= KTOP)%Z.
  Hypothesis SHF0 : boxed (bv_unsigned fptr <> 0 ->
     shz BSEGS m0 (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\ bv_unsigned fptr + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Hypothesis SHT0 : shz BSEGS m0 TBL10_SH TBL10_SHN.
  Hypothesis PRG0 : pristine m0 RELRO_LO RELRO_HI.
  Hypothesis BC0 : ro_cells BSEGS m0 BCELL [C8 (Z_to_bv 64 ASAN_B)].
  Hypothesis PR0 : pristine m0 IMG_LO ROD_HI.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SD := (Z_to_bv 64 (D / 8 + ASAN_B)).                (* [comment removed for export] *)
  Notation TBLW := (Z_to_bv 64 TBL10).                          (* [comment removed for export] *)
  Notation SP' := (Z_to_bv 64 (SP + -160)).
  Notation W := [((SP - 176)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells BSEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells BSEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).
  (* [comment removed for export] *)
  Notation FRLO3 w8 m := (rw_cells BSEGS m (SP + -160)
     [C8 numv; C8 w8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv]).
  Notation FRLOJ j8 m := (rw_cells BSEGS m (SP + -160)
     [C8 numv; CB 8 j8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv]).
  (* [comment removed for export] *)
  Notation SHNOW m := (shz BSEGS m (ASAN_B + A / 8) 63 /\ shz BSEGS m (ASAN_B + D / 8) 1 /\ shz BSEGS m (ASAN_B + (NP + 32) / 8) 4
     /\ shz BSEGS m (ASAN_B + gi) gin /\ shz BSEGS m TBL10_SH TBL10_SHN
     /\ pristine m RELRO_LO RELRO_HI /\ ro_cells BSEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] /\ pristine m IMG_LO ROD_HI).

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
    shz BSEGS m (ASAN_B + gf) gfn /\ (0 <= gf <= FP / 8)%Z /\ (FP + flen <= 8 * (gf + gfn) <= KTOP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in SHF0. destruct (SHF0 FNZ) as (S0 & G1 & G2).
    pose proof (shz_bound _ _ _ _ S0) as B1.
    split; [| split; [exact G1 | exact G2]].
    eapply shz_transport; [exact S0 | exact MU | cbn [disjoint_from]; Z.div_mod_to_equations; lia].
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at BSEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LF. destruct (LF FNZ) as [L1 L2].
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport BSEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr BSEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


  (* [comment removed for export] *)
  Ltac kill_trap := let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia] | clear Hc ].

  (* [comment removed for export] *)
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).

  Notation LO7 w8 := [C8 numv; C8 w8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv].
  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells BSEGS m (SP + -160) lo -> Z.of_nat (cells_size lo) = 56%Z ->
      FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95f20) fc None m (seg_rom BSEGS)).


  (* [comment removed for export] *)
  Definition TBL10V : list Z := Eval vm_compute in (map (fun k => 10 ^ Z.of_nat k)%Z (seq 0 20)).
  Lemma TBL10V_ok : table_b BSEGS TBL10 8 (fun v => le8 (Z_to_bv 64 v)) TBL10V = true.
  Proof. LiaFast.lf_pins LiaFast.lf_all. vm_compute. reflexivity. Qed.
  Lemma TBL10V_nth : forall c, (0 <= c <= 19)%Z -> (1 <= nth (Z.to_nat c) TBL10V 0 < 2^64)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros c Hc.
    assert (H : forall n, (n < 20)%nat -> (1 <= nth n TBL10V 0 < 2^64)%Z).
    { intros n Hn. do 20 (destruct n as [|n]; [cbn; lia|]). lia. }
    apply H. lia.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ftb1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95cc0) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftb8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x17
                 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95bfc) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftb_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95bd4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftaend_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95ee8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta1_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p fw (Z_to_bv 64 48) (Z_to_bv 64 (FP + flen)) p (Z_to_bv 64 (-1)) x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95eac) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta8_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 : word) (x1 x7 x8 x9 x12 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x7 x8 x9 p fw x12 (Z_to_bv 64 (FP + flen)) p (Z_to_bv 64 (flen - Z.of_nat off))
                 (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8))
                 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95de8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fta_ok : Prop :=
    forall (fw : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 fw x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95d64) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x14 x15 x16 x17 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95b4c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (ilen - Z.of_nat off)) x12 (Z_to_bv 64 3472328296227680304)
                 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x17
                 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x959b4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition it_ok : Prop :=
    forall (off : nat) (p : word) (w8 : word) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9598c) fc None m (seg_rom BSEGS)).
  (* [comment removed for export] *)
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (cnt K : Z) (w8 : word) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x23 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 19)%Z -> (19 * (K + 1) <= dg + 36)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 x18 x19 vw SD BB x23 p (Z_to_bv 64 (IP + ilen)) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95948) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (cnt K : Z) (w8 : word) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 19)%Z -> (19 * (K + 1) <= dg + 36)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 x18 vw p SD BB x23 (Z_to_bv 64 (FP + flen)) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95b90) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Notation K0 := (Z_to_bv 64 1095216660735).
  Notation K1 := (Z_to_bv 64 100000000).
  Notation K2 := (Z_to_bv 64 42949672960001).
  Notation K7 := (Z_to_bv 64 4294967296000100).
  Notation K9 := (Z_to_bv 64 14974415777481871312).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation E8 := (Z_to_bv 64 8).
  Notation E10 := (Z_to_bv 64 10).
  Notation EM1 := (Z_to_bv 64 (-1)).
  Notation E17 := (Z_to_bv 64 17).
  Notation E1 := (Z_to_bv 64 1).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).
  Notation IENDW := (Z_to_bv 64 (IP + ilen)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs -> bytes_at BSEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 37)%Z -> ((off < length fbs)%nat -> 19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 x17 K2 x19 p x21 BB K7 FENDW K9 E8 E10 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95928) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x7 x10 x11 x12 x13 x14 x15 x16 x19 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs -> bytes_at BSEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp EM1 E17 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 E1 K2 x19 p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x956c0) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition f1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x7 x10 x12 x13 x14 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs -> bytes_at BSEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 E1 K2 vw p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95820) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition f1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs -> bytes_at BSEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 E1 K2 vw p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9584c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fmul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs -> bytes_at BSEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 19 \/ off = length fbs \/ dg = maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 K2 vw p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x958d4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition f8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs -> bytes_at BSEGS m FP fbs -> (FP <> 0)%Z ->
      (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) (Z_to_bv 64 cnt0) K2 vw p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95708) fc None m (seg_rom BSEGS)).
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ LF1 LF2 MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Ltac f8_body_steps p FBS off :=
    pose proof (ro_block BSEGS _ FP fbs off 8 FBS ltac:(lia)) as BLK;
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    kill_trap;
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

  Lemma f8body0_proof : forall kk, f1e_ok kk -> fmul_ok kk -> f8body_ok kk 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FE FM. unfold f8body_ok; intros until dg; introsF; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    f8_body_steps p FBS off.
    step. (* [comment removed for export] *)
    if_cases Hc. { exfalso. exact (f8flag0 _ Hc). } clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    - eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
    - step. (* [comment removed for export] *)
      eapply (FM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.

  Lemma f8body1_proof : forall kk, f1e_ok kk -> fmul_ok kk -> f8body_ok kk 0 -> f8body_ok kk 1.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FE FM F80. unfold f8body_ok; intros until dg; introsF; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    destruct (shf_now _ MU FNZ) as (SHF & GF1 & GF2).
    f8_body_steps p FBS off.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - pose proof (f8flag1 (flen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb; rewrite ?unsigned_lit in Hb by lia.
      + step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. 2:{ exfalso. show. lia. }
        eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
      + shptr_next p.
        replace (Z_to_bv 64 (flen - Z.of_nat off - 8 + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (flen - Z.of_nat off - 16)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg + -8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg - 8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        replace (Z_to_bv 64 (dg + 16)) with (Z_to_bv 64 (dg + 8 + 8)) by (f_equal; lia).
        show.
        eapply (F80 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
    - pose proof (f8flag1' (flen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
      + eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
      + step. (* [comment removed for export] *)
        eapply (FM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.
End Proof.
