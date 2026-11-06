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

Module A_parse_mantissa_6c.
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

  (* [comment removed for export] *)
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).

  Ltac f8_body_steps p FBS off :=
    pose proof (ro_block ASEGS _ FP fbs off 8 FBS ltac:(lia)) as BLK;
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
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
      + step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. { exfalso. show. lia. }
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
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
      + eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
      + step. (* [comment removed for export] *)
        eapply (FM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.
End Proof.
End A_parse_mantissa_6c.

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

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr ASEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).


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

  Lemma itadd_proof : forall k, itadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold itadd_ok; intros until dg;
      intros CONT Hk Hj Hn1 Hp Hcw Hcv Hcv0 Hcv1 FRLO FRH ST XL Hcur XC DG NUM IBS MU WM DGB HK Hws1 AV SI; pre; shnow MU.
    all: pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    all: pose proof (bv_unsigned_in_range 64 cw) as Rcw; unfold bv_modulus in Rcw.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      (* [comment removed for export] *)
      assert (ROOM : (n1 < 62)%nat).
      { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK2). eapply (sad_room ws1 cur y n1 cv SI); [lia|].
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
      pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write ASEGS m A cur (Z.of_nat n1) cw XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      rewrite <- (Z_to_bv_bv_unsigned cw), Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply CONT; try eassumption; try lia.
      all: lazymatch goal with
           | |- length _ = _ => rewrite upd_length; exact Hcur
           | |- boxed _ =>
             unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia; split;
             [ apply bnorm_push; [rewrite Hcur; lia|]; rewrite unsigned_lit by lia; exact Hcv
             | rewrite (sad_inv_push ws1 cur y n1 cv SI) by (rewrite ?Hws1; lia); exact BV ]
           end.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH K n1 p cw cv); try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia| clear Hz].
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
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write ASEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      rewrite Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hcw.
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc.
      + pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH K (S j) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) 1%Z); try eassumption; try lia.
        all: lazymatch goal with
             | |- bv_unsigned _ = _ => rewrite unsigned_lit by lia; first [reflexivity | lia]
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ => unfold boxed in SI |- *; rewrite <- Hlimb; apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia]
             end.
      + pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hlt. clear Hc.
        step. (* [comment removed for export] *)
        eapply CONT; try eassumption; try lia.
        all: lazymatch goal with
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ =>
               unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); rewrite Nat2Z.id, <- Hlimb; split;
               [ apply (sad_bnorm_stop ws1 cur y j cv n1 SI); rewrite ?Hws1; try lia; exact BN
               | rewrite (sad_inv_stop ws1 cur y j cv n1 SI) by (rewrite ?Hws1; lia); exact BV ]
             end.
  Qed.

  Lemma ftadd_proof : forall k, ftadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold ftadd_ok; intros until dg;
      intros CONT Hk Hj Hn1 Hp Hcw Hcv Hcv0 Hcv1 FRLO FRH ST XL Hcur XC DG NUM IBS MU WM DGB HK Hws1 AV SI; pre; shnow MU.
    all: pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    all: pose proof (bv_unsigned_in_range 64 cw) as Rcw; unfold bv_modulus in Rcw.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      (* [comment removed for export] *)
      assert (ROOM : (n1 < 62)%nat).
      { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK2). eapply (sad_room ws1 cur y n1 cv SI); [lia|].
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
      pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write ASEGS m A cur (Z.of_nat n1) cw XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      rewrite <- (Z_to_bv_bv_unsigned cw), Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply CONT; try eassumption; try lia.
      all: lazymatch goal with
           | |- length _ = _ => rewrite upd_length; exact Hcur
           | |- boxed _ =>
             unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia; split;
             [ apply bnorm_push; [rewrite Hcur; lia|]; rewrite unsigned_lit by lia; exact Hcv
             | rewrite (sad_inv_push ws1 cur y n1 cv SI) by (rewrite ?Hws1; lia); exact BV ]
           end.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH K n1 p cw cv); try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia| clear Hz].
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
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write ASEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      rewrite Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hcw.
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc.
      + pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH K (S j) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) 1%Z); try eassumption; try lia.
        all: lazymatch goal with
             | |- bv_unsigned _ = _ => rewrite unsigned_lit by lia; first [reflexivity | lia]
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ => unfold boxed in SI |- *; rewrite <- Hlimb; apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia]
             end.
      + pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hlt. clear Hc.
        step. (* [comment removed for export] *)
        eapply CONT; try eassumption; try lia.
        all: lazymatch goal with
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ =>
               unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); rewrite Nat2Z.id, <- Hlimb; split;
               [ apply (sad_bnorm_stop ws1 cur y j cv n1 SI); rewrite ?Hws1; try lia; exact BN
               | rewrite (sad_inv_stop ws1 cur y j cv n1 SI) by (rewrite ?Hws1; lia); exact BV ]
             end.
  Qed.
End Proof.
