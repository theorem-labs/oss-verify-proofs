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

Module A_parse_mantissa_4.
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

  Lemma iadd_proof : forall k, iadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold iadd_ok; intros until dg;
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

  Lemma fadd_proof : forall k, fadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold fadd_ok; intros until dg;
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
End A_parse_mantissa_4.

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
  Notation C_S1 := (Z_to_bv 64 42949672960001).
  Notation C_S2 := (Z_to_bv 64 1095216660735).
  Notation C_S3 := (Z_to_bv 64 14974415777481871312).
  Notation C_S8 := (Z_to_bv 64 4294967296000100).
  Notation C_S9 := (Z_to_bv 64 100000000).
  Notation C_Z8 := (Z_to_bv 64 3472328296227680304).
  Notation FENDW := (Z_to_bv 64 (FP + flen)).
  Notation IENDW := (Z_to_bv 64 (IP + ilen)).

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
  Notation FRLO0 j0 m := (rw_cells ASEGS m (SP + -160) [CB 56 j0]).

  (* [comment removed for export] *)
  Definition iconst_ok : Prop :=
    forall (off : nat) (p : word) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x27 x28 : word) (m : word -> option byte),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A ws -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 IENDW x26 x27 x28 numv dv resv)
            F (Z_to_bv 64 0x9493c) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition iz1_ok (k : nat) : Prop :=
    forall (off : nat) (p pendw : word) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x27 x28 : word) (m : word -> option byte),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A ws -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> bv_unsigned pendw = (IP + ilen)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p pendw (Z_to_bv 64 48) x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 IENDW x26 x27 x28 numv dv resv)
            F (Z_to_bv 64 0x94904) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition izmid_ok : Prop :=
    forall (off : nat) (p : word) (j1 j2 : list byte) (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x27 x28 : word) (m : word -> option byte),
      FRLOJ j1 j2 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A ws -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 IENDW x26 x27 x28 numv dv resv)
            F (Z_to_bv 64 0x948f4) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition izpre_ok : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x26 x27 x28 : word) (m : word -> option byte),
      FRLO0 j0 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A ws -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p iptr x12 x13 x14 x15 x16 x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 ilen) x26 x27 x28 numv dv resv)
            F (Z_to_bv 64 0x948d0) fc None m (seg_rom ASEGS)).

  (* [comment removed for export] *)
  Definition iz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (x5 x6 x7 x8 x9 x12 x17 x18 x19 x20 x24 x26 x27 x28 : word) (m : word -> option byte),
      FRLO0 j0 m -> FRHI m -> stk ASEGS m (SP + -176) (SP + -160) ->
      u64arr ASEGS m A ws -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells ASEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at ASEGS m IP ibs ->
      munch W m0 m -> wmono ASEGS m0 m ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt ASEGS POST
        (MS (mkR mdw SP' gp tp x5 x6 x7 x8 x9 p iptr x12 C_Z8 (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8)) (Z_to_bv 64 7) (Z_to_bv 64 (ilen - Z.of_nat off)) x17 x18 x19 x20 p SD BB x24 (Z_to_bv 64 ilen) x26 x27 x28 numv dv resv)
            F (Z_to_bv 64 0x94820) fc None m (seg_rom ASEGS)).
  Ltac introsZ := intros FRLO FRH ST XL XC DG NUM IBS MU WM.
  Ltac show := match goal with |- ?g => idtac g end.
  Ltac shptr_next p :=
    replace (Z_to_bv 64 (ASAN_B + bv_unsigned p / 8 + 1)) with (Z_to_bv 64 (ASAN_B + bv_unsigned (Z_to_bv 64 (bv_unsigned p + 8)) / 8))
      by (f_equal; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia).

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
    { eapply (FSET tt 0%Z j1 j2); try eassumption; try lia. all: try apply val0. all: show. }
    do 19 step.
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
    pose proof (ro_block ASEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (IC off p j1 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?unsigned_lit in Hb by lia.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) pendw j1 j2); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (IC (length ibs) pendw j1 j2); try eassumption; try lia.
  Qed.

  Lemma izmid_proof : (forall k, iz1_ok k) -> izmid_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IZ1. unfold izmid_ok; intros until m; introsZ; intros Hoff Hp; pre; shnow MU.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IZ1 (length ibs - off)%nat off p _ j1 j2); try eassumption; try lia.
    all: rewrite ?(unsigned_lit (IP + ilen)) by lia; rewrite ?unsigned_lit by lia; try lia. all: show.
  Qed.

  Lemma izpre_proof : fset_ok -> izmid_ok -> izpre_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FSET IM. unfold izpre_ok; intros until m; introsZ; intros Hoff Hp; pre; shnow MU.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX'. rewrite Hws in BdX'.
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
    show.
    (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells ASEGS ?m1 (SP + -160) (C8 numv :: CB 16 ?j :: ?rest) |- _ =>
      pose proof (rw_cells_split_CB ASEGS m1 (SP + -160) [C8 numv] 16 j rest [8; 8]%nat FR eq_refl) as FRJ;
      cbn [mk_CB_cells app] in FRJ; clear FR
    end.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He; rewrite ?unsigned_lit in He by lia.
    { eapply (FSET tt 0%Z); try eassumption; try lia. all: try apply val0. all: show. }
    eapply (IM off p); try eassumption; try lia. all: show.
  Qed.

  Lemma iz8_proof : izpre_ok -> forall k, iz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IZP. induction k as [|k IH]; unfold iz8_ok; intros until m; introsZ; intros Hk Hoff Hp; pre; shnow MU.
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
    do 22 step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (IZP off p j0); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    shptr_next p.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (ilen - Z.of_nat off + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      replace (Z_to_bv 64 (ilen - Z.of_nat off - 8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) j0); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (IZP (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) j0); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Definition body_ok : Prop :=
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk ASEGS m0 (SP - 176) SP ->
      u64arr ASEGS m0 A ws -> rw_cells ASEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells ASEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at ASEGS m0 IP ibs -> rw_cells ASEGS m0 D [C8 dg0] ->
      evt ASEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x9474c) fc None m0 (seg_rom ASEGS)).

  Lemma body_proof : izpre_ok -> (forall k, iz8_ok k) -> body_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IZP IZ8. unfold body_ok. intros until dg0. intros ST XL XC NUM IBS DG. bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hws in BdX.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl ASEGS m0) as WM.
    pose proof SHX0 as SHX. pose proof SHD0 as SHD. pose proof SHN0 as SHN. pose proof SHI0 as SHI. pose proof SHT0 as SHT.
    pose proof PRG0 as PRG. pose proof BC0 as BC. pose proof PR0 as PR.
    destruct (stk_split ASEGS _ _ (SP - 160)%Z _ ST ltac:(lia)) as [STlo ST1].
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
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells ASEGS ?m1 (SP + -160) ?cs |- _ => chunk_split FR 1%nat FRLO FRH end.
    change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)) in DG |- *.
    show.
    step. (* [comment removed for export] *)
    if_cases H8; cond_cleanup H8; rewrite ?signed_lit in H8 by lia.
    - eapply (IZP 0%nat iptr); try eassumption; try lia. all: show.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 ilen) with (Z_to_bv 64 (ilen - Z.of_nat 0)) at 2 by (f_equal; lia).
      show.
      eapply (IZ8 (length ibs) 0%nat iptr); try eassumption; try lia. all: show.
  Qed.
End Proof.
