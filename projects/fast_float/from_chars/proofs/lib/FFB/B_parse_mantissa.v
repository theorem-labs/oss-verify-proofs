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

Module B_parse_mantissa_1.
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

  Lemma ru_proof : end_ok -> ru_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END; unfold ru_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM LEN DGB V KB; bounds; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
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
    | XL' : u64arr BSEGS ?m' A ?cur', XC' : rw_cells BSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    lazymatch goal with ST' : stk BSEGS _ (bv_unsigned SP' - 16) _ |- _ =>
      rewrite ULs in ST'; replace (SP + -160 - 16)%Z with (SP + -176)%Z in ST' by lia; rename ST' into ST1 end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    pose proof (u64arr_bound _ _ _ _ XL1) as BdX1. lazymatch goal with H : length cur1 = 62%nat |- _ => rename H into Hcur1 end. rewrite Hcur1 in BdX1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    match goal with H : munch _ m0 m1 |- _ => rename H into MU1 end. clear SHX SHD SHN SHI SHT PRG BC PR. shnow MU1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_add_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 len1).
    { exact XL1. } { exact Hcur1. } { exact XC1. } { lia. }
    { rewrite unsigned_lit by lia. rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
      unfold boxed in V; destruct V as [_ BV].
      eapply cap_of_K with (K := (K + 1)%Z); [| lia]. apply addnative_bound; lia. }
    { rewrite ULs. replace (SP + -160 - 16)%Z with (SP + -176)%Z by lia. exact ST1. }
    { eassumption. } { eassumption. }
    { rewrite ULs. lia. } { rewrite ULs. lia. } { rewrite ULs. lia. } { rewrite ULs. lia. } { lia. } { lia. }
    { eassumption. }
    lazymatch goal with
    | XL' : u64arr BSEGS ?m' A ?cur', XC' : rw_cells BSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len1 <= ?len' <= len1 + 1 /\ _)%Z, HV : bval _ _ = (bval cur1 (Z.to_nat len1) + _)%Z, HN : (bnorm cur1 _ -> bnorm _ _) |- _ =>
      rename XL' into XL2; rename XC' into XC2; rename HB into HB2; rename HV into HV2; rename HN into HN2;
      set (cur2 := cur') in *; set (len2 := len') in *
    end.
    lazymatch goal with ST' : stk BSEGS _ (bv_unsigned SP' - 16) _ |- _ =>
      rewrite ULs in ST'; replace (SP + -160 - 16)%Z with (SP + -176)%Z in ST' by lia; rename ST' into ST2 end.
    rewrite unsigned_lit in HV2 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    match goal with H : munch _ m0 m2 |- _ => rename H into MU2 end.
    clear SHX SHD SHN SHI SHT PRG BC PR. shnow MU2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (END [C8 numv; C8 w8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur2 len2 (dg + 1)%Z (K + 1)%Z);
      try eassumption; try reflexivity; try lia.
    all: try (unfold boxed in V |- *; destruct V as [BN BV]; split; [ apply HN2; apply HN1; [lia| exact BN] |];
              rewrite HV2, HV1; pose proof (bval_nonneg cur (Z.to_nat len)); apply addnative_bound; lia).
    all: try (enough (dg / 19 <= (dg + 1) / 19)%Z by lia; apply Z.div_le_mono; lia).
  Qed.
End Proof.
End B_parse_mantissa_1.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_6c.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_6c.

Module B_parse_mantissa_6a.
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

  Lemma fback_proof : forall kk, end_ok -> fout_ok kk -> fback_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk END FOUT. unfold fback_ok; intros until dg; introsF; intros V HK HK1 HK2 DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
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
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit dg) in * by lia. rewrite <- Hmaxd in *. rewrite ?(unsigned_lit (cnt + maxd)) by lia.
    eapply (F1 (Z.to_nat (19 - cnt)) off p vw cnt (cnt + maxd - dg)%Z K w8); try eassumption; try lia.
    all: show.
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
    { assert (Hdm : dg = maxd) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 c2) with (Z_to_bv 64 cnt) by (f_equal; lia).
      eapply (FM off p vw cnt K w8); try eassumption; try lia. }
    assert (Hdm : (dg < maxd)%Z) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
    pose proof (ro_block BSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) kill_trap.
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
End B_parse_mantissa_6a.


Module B_parse_mantissa_6b.
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

  Lemma fmul_proof : forall kk, ftrunc_ok -> fback_ok kk -> fmul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FT FB. unfold fmul_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht; rewrite ?unsigned_lit in Ht by lia.
    { rewrite <- ?Hmaxd in Ht. eapply (FT off p vw cnt K w8); try eassumption; try lia. }
    rewrite <- ?Hmaxd in Ht.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) kill_trap.
    muladd_seq XL Hcur XC V cur len K cnt vw ST MU.
    after_mul cur len XL1 XC1 HB1 HV1 HN1 cur1 len1 Hcur1 BdX1 ST1 m1 MU1.
    clear SHX SHD SHN SHI SHT PRG BC PR. shnow MU1.
    add_call XL1 Hcur1 XC1 HV1 cur cur1 len len1 K ST1 BV.
    after_add cur1 len1 XL2 XC2 HB2 HV2 HN2 cur2 len2 ST2 m2 MU2.
    rewrite ?unsigned_lit in HV2 by lia.
    eapply (FB off p (K + 1)%Z w8); try eassumption; try lia.
    all: try (apply fbs_now; [assumption| exact FNZ]).
    unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
    rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia.
  Qed.
End Proof.
End B_parse_mantissa_6b.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_6c.

Module B_parse_mantissa_6d.
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

  Lemma fout_proof :
    (forall kk, end_ok -> fout_ok kk -> fback_ok kk) ->
    (forall kk, ftrunc_ok -> fback_ok kk -> fmul_ok kk) ->
    (forall kk, fmul_ok kk -> forall k, f1_ok kk k) ->
    (forall kk, fmul_ok kk -> (forall k, f1_ok kk k) -> f1e_ok kk) ->
    (forall kk, f1e_ok kk -> fmul_ok kk -> f8body_ok kk 0) ->
    (forall kk, f1e_ok kk -> fmul_ok kk -> f8body_ok kk 0 -> f8body_ok kk 1) ->
    end_ok -> ftrunc_ok -> forall k, fout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros PFB PFM PF1 PFE PF80 PF81 END FT.
    induction k as [|k IH]; unfold fout_ok; intros until dg; introsF; intros V HK HKd DGM Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (PFB k END IH) as FB.
    pose proof (PFM k FT FB) as FM.
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
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit dg) in * by lia. rewrite <- Hmaxd in *.
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit in Hc by lia.
      + step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. 2:{ exfalso. show. lia. }
        eapply (FE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
      + show.
        eapply (F81 off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia. all: show.
  Qed.
End Proof.
End B_parse_mantissa_6d.


Module B_parse_mantissa_7.
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

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9566c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p fendw (Z_to_bv 64 48) EM1 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d18) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d00) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 E8 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a88) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 flen) x12 x13 x14 x15 x16 x17 x18 x19 fptr SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a68) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95618) fc None m (seg_rom BSEGS)).
  Notation LOJ j8 := [C8 numv; CB 8 j8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv].
  Ltac introsE := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB V HK HKd.
  Ltac show := match goal with |- ?g => idtac g end.
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
    { eapply (END (LOJ j8)); try eassumption; try lia. all: end_tail K dg. all: show. }
    do 20 step. (* [comment removed for export] *)
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
    pose proof (ro_block BSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (FC off p K j8); try eassumption; try lia. }
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?unsigned_lit in Hb by lia.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fendw K j8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (FC (length fbs) fendw K j8); try eassumption; try lia.
  Qed.

  Lemma fzmid_proof : end_ok -> (forall k, fz1_ok k) -> fzmid_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FZ1. unfold fzmid_ok; intros until dg; introsE; intros FBS FNZ LF1 LF2 Hoff Hp; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    { eapply (END (LOJ j8)); try eassumption; try lia. all: end_tail K dg. all: show. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (FZ1 (length fbs - off)%nat off p _ K j8); try eassumption; try lia.
    all: rewrite ?(unsigned_lit (FP + flen)) by lia; rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.

  Lemma fz8_proof : fzmid_ok -> forall k, fz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FM. induction k as [|k IH]; unfold fz8_ok; intros until dg; introsE; intros FBS FNZ LF1 LF2 Hk Hoff Hp; pre; shnow MU.
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
    if_cases Hc; clear Hc.
    { eapply (FM off p K j8); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    shptr_next p.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      replace (Z_to_bv 64 (flen - Z.of_nat off - 8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (FM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j8); try eassumption; try lia.
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
      eapply (FM 0%nat fptr K j8); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 flen) with (Z_to_bv 64 (flen - Z.of_nat 0)) by (f_equal; lia).
      eapply (FZ8 (length fbs) 0%nat fptr K j8); try eassumption; try lia.
  Qed.

  Lemma fset_proof : end_ok -> fz_ok -> fconst_ok -> fset_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FZ FC. unfold fset_ok; intros until dg; introsE; pre; shnow MU.
    pose proof (rw_cells_bound _ _ _ _ NUM) as BN; cbn [cells_size csize Nat.add] in BN.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    { eapply (END (LOJ j8)); try eassumption; try lia. all: end_tail K dg. all: show. }
    pose proof (fbs_now m MU Hz) as FBS. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    unfold boxed in LF. destruct (LF Hz) as [LF1 LF2].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit flen) by lia.
    step. (* [comment removed for export] *)
    if_cases Hd; cond_cleanup Hd; rewrite ?unsigned_lit in Hd by lia.
    - show. eapply (FZ tt K j8); try eassumption; try lia. all: show.
    - show. eapply (FC 0%nat fptr K j8); try eassumption; try lia. all: show.
  Qed.
End Proof.
End B_parse_mantissa_7.


Module B_parse_mantissa_8a.
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) (Z_to_bv 64 cnt0) K2 vw p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95708) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9566c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p fendw (Z_to_bv 64 48) EM1 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d18) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d00) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 E8 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a88) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 flen) x12 x13 x14 x15 x16 x17 x18 x19 fptr SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a68) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95618) fc None m (seg_rom BSEGS)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 x17 K2 E10 x19 x21 BB K7 p IENDW K9 E8 x28 x29 x30 x31)
            F (Z_to_bv 64 0x955f8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x7 x10 x11 x12 x13 x14 x15 x16 x19 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 E1 K2 E10 x19 SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95398) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x7 x10 x12 x13 x14 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 E1 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x954f0) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 E1 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9551c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x955a4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) (Z_to_bv 64 cnt0) K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x953dc) fc None m (seg_rom BSEGS)).
  Ltac introsI := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma frlo3_to_J : forall m a, FRLO3 a m -> FRLOJ (le8 a) m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m a [[WW B] R]. split; [split|].
    - cbn. repeat split; try reflexivity; try apply length_le8. all: exact I.
    - exact B.
    - exact R.
  Qed.

  Lemma iback_proof : forall kk, fset_ok -> iout_ok kk -> iback_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FSET IOUT. unfold iback_ok; intros until dg; introsI; intros V HK HK1 HK2 DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IOUT off p K); try eassumption; try lia.
    - eapply (FSET tt K (le8 w8)); try eassumption; try lia.
      apply frlo3_to_J. exact FRLO.
  Qed.

  Lemma i1e_proof : forall kk, imul_ok kk -> (forall k, i1_ok kk k) -> i1e_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM I1. unfold i1e_ok; intros until dg; introsI; intros V HK Hcnt Hcd HKd H0 Hoff Hp Hkk; pre; shnow MU.
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
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit dg) in * by lia. rewrite <- Hmaxd in *. rewrite ?(unsigned_lit (cnt + maxd)) by lia.
    eapply (I1 (Z.to_nat (19 - cnt)) off p vw cnt (cnt + maxd - dg)%Z K w8); try eassumption; try lia.
    all: show.
  Qed.

  Lemma i1_proof : forall kk, imul_ok kk -> forall k, i1_ok kk k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM. induction k as [|k IH]; unfold i1_ok; intros until dg; introsI; intros V HK Hcnt Hk Hcd HKd Hc2 H0 Hoff Hp Hkk; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H1; cond_cleanup H1.
    { assert (Hdm : dg = maxd) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 c2) with (Z_to_bv 64 cnt) by (f_equal; lia).
      eapply (IM off p vw cnt K w8); try eassumption; try lia. }
    assert (Hdm : (dg < maxd)%Z) by (revert H1; rewrite ?unsigned_lit by lia; intros H1; Z.div_mod_to_equations; lia).
    pose proof (ro_block BSEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) kill_trap.
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
End B_parse_mantissa_8a.


Module B_parse_mantissa_8b.
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) (Z_to_bv 64 cnt0) K2 vw p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95708) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9566c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p fendw (Z_to_bv 64 48) EM1 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d18) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d00) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 E8 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a88) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 flen) x12 x13 x14 x15 x16 x17 x18 x19 fptr SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a68) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95618) fc None m (seg_rom BSEGS)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 x17 K2 E10 x19 x21 BB K7 p IENDW K9 E8 x28 x29 x30 x31)
            F (Z_to_bv 64 0x955f8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x7 x10 x11 x12 x13 x14 x15 x16 x19 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 E1 K2 E10 x19 SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95398) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x7 x10 x12 x13 x14 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 E1 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x954f0) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 E1 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9551c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x955a4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) (Z_to_bv 64 cnt0) K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x953dc) fc None m (seg_rom BSEGS)).
  Ltac introsI := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma imul_proof : forall kk, itrunc_ok -> iback_ok kk -> imul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IT IB. unfold imul_ok; intros until dg; introsI; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (unsigned_lit (SP + -160) ltac:(lia)) as ULs.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht; rewrite ?unsigned_lit in Ht by lia.
    { rewrite <- ?Hmaxd in Ht. eapply (IT off p vw cnt K w8); try eassumption; try lia. }
    rewrite <- ?Hmaxd in Ht.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) kill_trap.
    muladd_seq XL Hcur XC V cur len K cnt vw ST MU.
    after_mul cur len XL1 XC1 HB1 HV1 HN1 cur1 len1 Hcur1 BdX1 ST1 m1 MU1.
    clear SHX SHD SHN SHI SHT PRG BC PR. shnow MU1.
    add_call XL1 Hcur1 XC1 HV1 cur cur1 len len1 K ST1 BV.
    after_add cur1 len1 XL2 XC2 HB2 HV2 HN2 cur2 len2 ST2 m2 MU2.
    rewrite ?unsigned_lit in HV2 by lia.
    eapply (IB off p (K + 1)%Z w8); try eassumption; try lia.
        unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
    rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia.
  Qed.
End Proof.
End B_parse_mantissa_8b.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_9.

Module B_parse_mantissa_8d.
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
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
      (FS <= FP)%Z -> (FP + flen <= A)%Z ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) (Z_to_bv 64 cnt0) K2 vw p SD BB K7 FENDW K9 E8 E10 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95708) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9566c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p fendw (Z_to_bv 64 48) EM1 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d18) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95d00) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (flen - Z.of_nat off)) x12 E8 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x17 x18 x19 p SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a88) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at BSEGS m FP fbs -> (FP <> 0)%Z -> (FS <= FP)%Z -> (FP + flen <= THI)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 flen) x12 x13 x14 x15 x16 x17 x18 x19 fptr SD BB x23 FENDW x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95a68) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j8 : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 x24 x25 x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95618) fc None m (seg_rom BSEGS)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 x17 K2 E10 x19 x21 BB K7 p IENDW K9 E8 x28 x29 x30 x31)
            F (Z_to_bv 64 0x955f8) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x7 x10 x11 x12 x13 x14 x15 x16 x19 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 x10 x11 x12 x13 x14 x15 x16 E1 K2 E10 x19 SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95398) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i1e_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x7 x10 x12 x13 x14 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 E1 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x954f0) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt c2 : Z) (K : Z) (w8 : word) (x7 x15 x16 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (c2 = cnt + maxd - dg)%Z -> (cnt = 0 -> dg < maxd)%Z ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp EM1 E17 x7 K0 K1 p (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 (0 - maxd)) (Z_to_bv 64 (dg + 1)) x15 x16 E1 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9551c) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17 K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x955a4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x5 x6 x7 x28 x29 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A cur -> length cur = 62%nat -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 K0 K1 p (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 (dg + 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) (Z_to_bv 64 cnt0) K2 E10 vw SD BB K7 p IENDW K9 E8 x28 x29 dv mdw)
            F (Z_to_bv 64 0x953dc) fc None m (seg_rom BSEGS)).
  Ltac introsI := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM LEN DGB Hw8.
  Ltac show := match goal with |- ?g => idtac g end.

  Lemma iout_proof :
    (forall kk, fset_ok -> iout_ok kk -> iback_ok kk) ->
    (forall kk, itrunc_ok -> iback_ok kk -> imul_ok kk) ->
    (forall kk, imul_ok kk -> forall k, i1_ok kk k) ->
    (forall kk, imul_ok kk -> (forall k, i1_ok kk k) -> i1e_ok kk) ->
    (forall kk, i1e_ok kk -> imul_ok kk -> i8body_ok kk 0) ->
    (forall kk, i1e_ok kk -> imul_ok kk -> i8body_ok kk 0 -> i8body_ok kk 1) ->
    fset_ok -> itrunc_ok -> forall k, iout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros PIB PIM PI1 PIE PI80 PI81 FSET IT.
    induction k as [|k IH]; unfold iout_ok; intros until dg; introsI; intros V HK HKd DGM Hk Hoff Hp; pre; shnow MU.
    { exfalso; lia. }
    pose proof (PIB k FSET IH) as IB.
    pose proof (PIM k IT IB) as IM.
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
      + step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. 2:{ exfalso. show. lia. }
        eapply (IE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
      + show.
        eapply (I81 off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia. all: show.
  Qed.
End Proof.
End B_parse_mantissa_8d.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_9.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_1 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_3 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_6a OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_6b OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_6d OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_7 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_8a OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_8b OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_9.B_parse_mantissa_8c OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa.B_parse_mantissa_8d OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_9.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
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
  #[local] Definition L_end_proof := (@B_parse_mantissa_1.end_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ru_proof := (@B_parse_mantissa_1.ru_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftb1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.ftb1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftb8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.ftb8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftb_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.ftb_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftaend_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.ftaend_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fta1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.fta1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fta8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.fta8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fta_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.fta_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_it1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.it1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_it8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.it8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_it_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_2.it_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_itrunc_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_3.itrunc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_ftrunc_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_parse_mantissa_3.ftrunc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fback_proof := (@B_parse_mantissa_6a.fback_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f1e_proof := (@B_parse_mantissa_6a.f1e_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f1_proof := (@B_parse_mantissa_6a.f1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fmul_proof := (@B_parse_mantissa_6b.fmul_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f8body0_proof := (@B_parse_mantissa_6c.f8body0_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_f8body1_proof := (@B_parse_mantissa_6c.f8body1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fout_proof := (@B_parse_mantissa_6d.fout_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fconst_proof := (@B_parse_mantissa_7.fconst_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fz1_proof := (@B_parse_mantissa_7.fz1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fzmid_proof := (@B_parse_mantissa_7.fzmid_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fz8_proof := (@B_parse_mantissa_7.fz8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fz_proof := (@B_parse_mantissa_7.fz_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_fset_proof := (@B_parse_mantissa_7.fset_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iback_proof := (@B_parse_mantissa_8a.iback_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i1e_proof := (@B_parse_mantissa_8a.i1e_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i1_proof := (@B_parse_mantissa_8a.i1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_imul_proof := (@B_parse_mantissa_8b.imul_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i8body0_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_9.B_parse_mantissa_8c.i8body0_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_i8body1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_9.B_parse_mantissa_8c.i8body1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iout_proof := (@B_parse_mantissa_8d.iout_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iconst_proof := (@B_parse_mantissa_9.iconst_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iz1_proof := (@B_parse_mantissa_9.iz1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_izpre_proof := (@B_parse_mantissa_9.izpre_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_iz8_proof := (@B_parse_mantissa_9.iz8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).
  #[local] Definition L_body_proof := (@B_parse_mantissa_9.body_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd FS THI GLO gi gin gf gfn Hilen Hflen Hmaxd Hws MAXD XAL NAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS SHX0 SHD0 SHN0 SHI0 GI1 GI2 SHF0 SHT0 PRG0 BC0 PR0).

  (* [comment removed for export] *)
  Lemma main_ok :
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk BSEGS m0 (SP - 176) SP ->
      u64arr BSEGS m0 A ws -> rw_cells BSEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells BSEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at BSEGS m0 IP ibs -> rw_cells BSEGS m0 D [C8 dg0] ->
      evt BSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x9514c) fc None m0 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    pose proof L_end_proof as END.
    pose proof (L_ru_proof END) as RU.
    pose proof (L_ftb1_proof END RU) as FTB1.
    pose proof (L_ftb8_proof END RU FTB1) as FTB8.
    pose proof (L_ftb_proof END FTB1 FTB8) as FTB.
    pose proof (L_ftaend_proof END RU) as FE.
    pose proof (L_fta1_proof FE RU) as FTA1.
    pose proof (L_fta8_proof FE RU FTA1) as FTA8.
    pose proof (L_fta_proof FE FTA1 FTA8) as FTA.
    pose proof (L_it1_proof FTA) as IT1.
    pose proof (L_it8_proof FTA IT1) as IT8.
    pose proof (L_it_proof FTA IT1 IT8) as IT.
    pose proof (L_itrunc_proof IT) as ITRUNC.
    pose proof (L_ftrunc_proof FTB) as FTRUNC.
    pose proof (L_fout_proof L_fback_proof L_fmul_proof L_f1_proof L_f1e_proof L_f8body0_proof L_f8body1_proof END FTRUNC) as FOUT.
    pose proof (L_fconst_proof END FOUT) as FCONST.
    pose proof (L_fz1_proof FCONST) as FZ1.
    pose proof (L_fzmid_proof END FZ1) as FZMID.
    pose proof (L_fz8_proof FZMID) as FZ8.
    pose proof (L_fz_proof FZMID FZ8) as FZ.
    pose proof (L_fset_proof END FZ FCONST) as FSET.
    pose proof (L_iout_proof L_iback_proof L_imul_proof L_i1_proof L_i1e_proof L_i8body0_proof L_i8body1_proof FSET ITRUNC) as IOUT.
    pose proof (L_iconst_proof FSET IOUT) as ICONST.
    pose proof (L_iz1_proof ICONST) as IZ1.
    pose proof (L_izpre_proof FSET IZ1) as IZPRE.
    pose proof (L_iz8_proof IZPRE) as IZ8.
    exact (L_body_proof IZPRE IZ8).
  Qed.
End Proof.

Section Top.
  Hypothesis small_mul_spec : small_mul_stmt.
  Hypothesis small_add_spec : small_add_stmt.

  Lemma parse_mantissa_spec : parse_mantissa_stmt.
  Proof.
    unfold parse_mantissa_stmt. intros until gfn.
    intros ST ALIGN PR XL Hxl XC XAL NUM IBS INZ IEND ILEN FBS FEND FLEN FNULL MAXD DG PRG BC LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR NAL SFS SHX SHD SHN SHI GI1 GI2 SHF SHT.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    eapply (main_ok small_mul_spec small_add_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc m ws iptr fptr ibs fbs
              (Z.of_nat (length ibs)) (Z.of_nat (length fbs)) (bv_unsigned a2) FS THI GLO gi gin gf gfn
              eq_refl eq_refl eq_refl Hxl MAXD XAL NAL ALIGN INZ IEND ltac:(lia) FEND ltac:(lia) FNULL FBS LAY0 KLO LD1 LD2 KFS1 KFS2 LI1 LI2 LF LA LN LR SFS
              SHX SHD SHN SHI GI1 GI2 SHF SHT PRG BC PR);
      eassumption.
  Qed.
End Top.
