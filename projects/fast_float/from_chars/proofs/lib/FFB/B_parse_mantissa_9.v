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

Module B_parse_mantissa_8c.
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

  Ltac i8_body_steps p IBS off :=
    pose proof (ro_block BSEGS _ IP ibs off 8 IBS ltac:(lia)) as BLK;
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
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

  Lemma i8body0_proof : forall kk, i1e_ok kk -> imul_ok kk -> i8body_ok kk 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IE IM. unfold i8body_ok; intros until dg; introsI; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc. { exfalso. exact (f8flag0 _ Hc). } clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
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
    intros kk IE IM I80. unfold i8body_ok; intros until dg; introsI; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - pose proof (f8flag1 (ilen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb; rewrite ?unsigned_lit in Hb by lia.
      + step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia. 2:{ exfalso. show. lia. }
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
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
      + eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
      + step. (* [comment removed for export] *)
        eapply (IM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.
End Proof.
End B_parse_mantissa_8c.

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

  (* [comment removed for export] *)
  Notation FRLOA ja m := (rw_cells BSEGS m (SP + -160) [C8 numv; CB 40 ja; C8 resv]).

  (* [comment removed for export] *)
  Definition iconst_ok : Prop :=
    forall (off : nat) (p : word) (j8 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 : word) (m : word -> option byte),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A ws -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 p IENDW x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95344) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition iz1_ok (k : nat) : Prop :=
    forall (off : nat) (p pendw : word) (j8 : list byte) (x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 : word) (m : word -> option byte),
      FRLOJ j8 m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A ws -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> bv_unsigned pendw = (IP + ilen)%Z ->
      evt BSEGS POST
        (MS (mkR TBLW SP' gp tp x5 x6 x7 x8 x9 p pendw (Z_to_bv 64 48) EM1 x14 x15 x16 x17 x18 x19 x20 SD BB x23 p IENDW x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x95304) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition izpre_ok : Prop :=
    forall (off : nat) (p : word) (ja : list byte) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x26 x27 x28 x29 : word) (m : word -> option byte),
      FRLOA ja m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A ws -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SD BB x23 p IENDW x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x952d4) fc None m (seg_rom BSEGS)).

  (* [comment removed for export] *)
  Definition iz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (ja : list byte) (x1 x5 x6 x7 x8 x9 x12 x17 x18 x19 x20 x23 x26 x27 x28 x29 : word) (m : word -> option byte),
      FRLOA ja m -> FRHI m -> stk BSEGS m (SP + -176) (SP + -160) ->
      u64arr BSEGS m A ws -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells BSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at BSEGS m IP ibs ->
      munch W m0 m -> wmono BSEGS m0 m ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt BSEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 p (Z_to_bv 64 (ilen - Z.of_nat off)) x12 E8 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) x17 x18 x19 x20 SD BB x23 p IENDW x26 x27 x28 x29 dv mdw)
            F (Z_to_bv 64 0x9521c) fc None m (seg_rom BSEGS)).
  Ltac introsZ := intros FRLO FRH ST XL XC DG NUM IBS MU WM.
  Ltac show := match goal with |- ?g => idtac g end.
  Notation LOJ j8 := [C8 numv; CB 8 j8; C8 mdw; C8 SD; C8 TBLW; C8 dv; C8 resv].

  Lemma val0 : VAL ws 0 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all. unfold boxed. split. { apply bnorm_0. } change (Z.to_nat 0) with 0%nat. rewrite bval_0. cbn. lia. Qed.

  Lemma iconst_proof : fset_ok -> (forall k, iout_ok k) -> iconst_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FSET IOUT. unfold iconst_ok; intros until m; introsZ; intros Hoff Hp; pre; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX'. rewrite Hws in BdX'.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    { eapply (FSET tt 0%Z j8); try eassumption; try lia. all: try apply val0. all: show. }
    do 20 step.
    show.
    eapply (IOUT (length ibs - off)%nat off p 0%Z (Z_to_bv 64 (IP + ilen + -8))); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; try lia. all: try apply val0. all: show.
  Qed.

  Lemma iz1_proof : iconst_ok -> forall k, iz1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IC. induction k as [|k IH]; unfold iz1_ok; intros until m; introsZ; intros Hk Hoff Hp Hpe; pre; shnow MU.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 pendw) as Rpe; unfold bv_modulus in Rpe.
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
    if_cases Hc; clear Hc.
    { eapply (IC off p j8); try eassumption; try lia. }
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?unsigned_lit in Hb by lia.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) pendw j8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (IC (length ibs) pendw j8); try eassumption; try lia.
  Qed.

  Lemma izpre_proof : fset_ok -> (forall k, iz1_ok k) -> izpre_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FSET IZ1. unfold izpre_ok; intros until m; introsZ; intros Hoff Hp; pre; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX'. rewrite Hws in BdX'.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    show.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    { eapply (FSET tt 0%Z); try eassumption; try lia. all: try apply val0. all: show. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IZ1 (length ibs - off)%nat off p _); try eassumption; try lia.
    all: rewrite ?(unsigned_lit (IP + ilen)) by lia; rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.

  Lemma iz8_proof : izpre_ok -> forall k, iz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IZP. induction k as [|k IH]; unfold iz8_ok; intros until m; introsZ; intros Hk Hoff Hp; pre; shnow MU.
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
    if_cases Hc; clear Hc.
    { eapply (IZP off p ja); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    shptr_next p.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (ilen - Z.of_nat off + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      replace (Z_to_bv 64 (ilen - Z.of_nat off - 8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) ja); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (IZP (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) ja); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Definition body_ok : Prop :=
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk BSEGS m0 (SP - 176) SP ->
      u64arr BSEGS m0 A ws -> rw_cells BSEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells BSEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at BSEGS m0 IP ibs -> rw_cells BSEGS m0 D [C8 dg0] ->
      evt BSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x9514c) fc None m0 (seg_rom BSEGS)).

  Lemma body_proof : izpre_ok -> (forall k, iz8_ok k) -> body_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IZP IZ8. unfold body_ok. intros until dg0. intros ST XL XC NUM IBS DG. bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hws in BdX.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (rw_cells_bound _ _ _ _ NUM) as BN. cbn [cells_size csize Nat.add] in BN.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl BSEGS m0) as WM.
    pose proof SHX0 as SHX. pose proof SHD0 as SHD. pose proof SHN0 as SHN. pose proof SHI0 as SHI. pose proof SHT0 as SHT.
    pose proof PRG0 as PRG. pose proof BC0 as BC. pose proof PR0 as PR.
    pose proof (shz_bound _ _ _ _ SHD) as BSD.
    destruct (stk_split BSEGS _ _ (SP - 160)%Z _ ST ltac:(lia)) as [STlo ST1].
    replace (SP - 176)%Z with (SP + -176)%Z in STlo by lia. replace (SP - 160)%Z with (SP + -160)%Z in STlo by lia.
    carve_frame 160%nat ST1.
    do 14 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (D / 8 + ASAN_B)) with SD by reflexivity.
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
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit ilen) by lia.
    step. (* [comment removed for export] *) kill_trap.
    step. (* [comment removed for export] *) setcmp. decide_ltb.
    step. (* [comment removed for export] *) setcmp. decide_ltb.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    try kill_trap.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells BSEGS ?m1 (SP + -160) ?cs |- _ => show; chunk_split FR 3%nat FRLO FRH end.
    change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)) in DG |- *.
    show.
    step. (* [comment removed for export] *)
    if_cases H8; cond_cleanup H8; rewrite ?signed_lit in H8 by lia.
    - step. (* [comment removed for export] *)
      eapply (IZP 0%nat iptr); try eassumption; try lia. all: show.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 ilen) with (Z_to_bv 64 (ilen - Z.of_nat 0)) by (f_equal; lia).
      show.
      eapply (IZ8 (length ibs) 0%nat iptr); try eassumption; try lia. all: show.
  Qed.
End Proof.
