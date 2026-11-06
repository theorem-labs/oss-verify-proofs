(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_compare_stmt.
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
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word).
  Variables (xv yv : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (j8 : list byte).
  Variables (xs ys : list word) (len : Z).
  Hypothesis Hxl : length xs = 62%nat.
  Hypothesis Hyl : length ys = 62%nat.
  Hypothesis LEN : (0 <= len <= 62)%Z.
  Hypothesis XL : u64arr BSEGS m (bv_unsigned xv) xs.
  Hypothesis YL : u64arr BSEGS m (bv_unsigned yv) ys.
  Hypothesis KX0 : (app2r (bv_unsigned xv) (bv_unsigned xv + 504))%Z.  Hypothesis KX1 : (bv_unsigned xv + 504 <= KTOP)%Z.
  Hypothesis KY0 : (app2r (bv_unsigned yv) (bv_unsigned yv + 504))%Z.  Hypothesis KY1 : (bv_unsigned yv + 504 <= KTOP)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis MU : munch (compare_W sp) m0 m.
  Hypothesis WM : wmono BSEGS m0 m.
  Hypothesis FR : rw_cells BSEGS m (bv_unsigned sp + -16) [CB 8 j8; C8 ra].
  Hypothesis ST : stk BSEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16).
  Hypothesis SHX : shz BSEGS m (ASAN_B + bv_unsigned xv / 8) 63.
  Hypothesis SHY : shz BSEGS m (ASAN_B + bv_unsigned yv / 8) 63.

  Notation X := (bv_unsigned xv).
  Notation Y := (bv_unsigned yv).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation POST := (compare_post ra sp gp tp s0 s1 yv s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m0).
  Notation NOTX := (Z_to_bv 64 (18446744073709551615 - X)).
  Notation NOTY := (Z_to_bv 64 (18446744073709551615 - Y)).

  (* [comment removed for export] *)
  #[using="xv j8 xs ys Hxl Hyl KX0 KY0 MU WM FR ST"] Lemma cmp_exit : forall (x5 x6 x7 x10 r x13 x14 x15 x16 x17 x28 x29 : word),
    evt BSEGS POST (MS (mkR ra SP' gp tp x5 x6 x7 s0 s1 x10 yv r x13 x14 x15 x16 x17
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
                       F (Z_to_bv 64 0x98c6c) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (xv j8 xs ys Hxl Hyl KX0 KY0 MU WM FR ST : LiaFast.U) => LiaFast.u0).
    intros. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof MU as MU'. cbv delta [compare_W] in MU'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold compare_post. finish. all: try eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (idx : Z) (x13 x28 x29 : word),
      (Z.to_nat idx = k)%nat -> (0 <= idx <= len)%Z ->
      evt BSEGS POST
        (MS (mkR ra SP' gp tp NOTY (Z_to_bv 64 (-16)) (Z_to_bv 64 64) s0 s1 xv yv (Z_to_bv 64 1) x13 (Z_to_bv 64 (8 * idx - 8)) BB (Z_to_bv 64 len) NOTX
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
            F (Z_to_bv 64 0x98c10) fc None m (seg_rom BSEGS)).

  #[using="j8 xs ys Hxl Hyl LEN XL YL KX0 KX1 KY0 KY1 MU WM FR ST SHX SHY"] Lemma cmp_loop : forall k, loop_ok k.
  Proof. LiaFast.lf_pins (fun (j8 xs ys Hxl Hyl LEN XL YL KX0 KX1 KY0 KY1 MU WM FR ST SHX SHY : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold loop_ok; intros idx x13 x28 x29 Hk Hidx.
    - (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; [| exfalso; lia].
      step. (* [comment removed for export] *)
      apply cmp_exit.
    - pose proof (bv_unsigned_in_range 64 xv) as RA. unfold bv_modulus in RA.
      pose proof (bv_unsigned_in_range 64 yv) as RB. unfold bv_modulus in RB.
      pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hxl in BdX.
      pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; [exfalso; lia|].
      step. (* [comment removed for export] *)
      try if_not_taken.
      step. (* [comment removed for export] *)
      try if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      replace ((X + (8 * idx - 8)) / 8)%Z with (X / 8 + (idx - 1))%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      try if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      replace ((Y + (8 * idx - 8)) / 8)%Z with (Y / 8 + (idx - 1))%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      destruct (nth_error xs (Z.to_nat (idx - 1))) as [wx|] eqn:Hnx. 2:{ exfalso. apply nth_error_None in Hnx. lia. }
      destruct (nth_error ys (Z.to_nat (idx - 1))) as [wy|] eqn:Hny. 2:{ exfalso. apply nth_error_None in Hny. lia. }
      pose proof (u64arr_read BSEGS m X xs (idx - 1) wx _ XL Hnx ltac:(lia) eq_refl) as RDX.
      replace (wa (X + 8 * (idx - 1))) with (Z_to_bv 64 (X + (8 * idx - 8))) in RDX by (unfold wa; f_equal; lia).
      step. (* [comment removed for export] *)
      clear RDX.
      pose proof (u64arr_read BSEGS m Y ys (idx - 1) wy _ YL Hny ltac:(lia) eq_refl) as RDY.
      replace (wa (Y + 8 * (idx - 1))) with (Z_to_bv 64 (Y + (8 * idx - 8))) in RDY by (unfold wa; f_equal; lia).
      step. (* [comment removed for export] *)
      clear RDY.
      step. (* [comment removed for export] *)
      if_cases Hgt.
      { apply cmp_exit. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hge.
      + replace (8 * idx - 8 + -8)%Z with (8 * (idx - 1) - 8)%Z by lia.
        eapply (IH (idx - 1)%Z); lia.
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        apply cmp_exit.
  Qed.
End Loop.

Lemma compare_spec : compare_stmt.
Proof.
  unfold compare_stmt. intros until ylen. intros XL Hxl XC XLEN YL Hyl YC YLEN ST PRG BC SEPX SEPY RO3 KSP KSP2 KX0 KX1 KY0 KY1 SHX SHY.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 a1) as RB. unfold bv_modulus in RB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (munch_refl (compare_W sp) m) as MU. cbv delta [compare_W] in MU.
  pose proof (wmono_refl BSEGS m) as WM.
  carve_frame 16%nat ST.
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
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases H1.
  { eapply cmp_exit; try eassumption; try lia. }
  cond_cleanup H1.
  step. (* [comment removed for export] *)
  if_cases H2.
  { step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply cmp_exit; try eassumption; try lia. }
  cond_cleanup H2.
  assert (EQL : ylen = xlen) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit xlen) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite !zb_lxor_ones by lia.
  replace (xlen * 2 ^ 3 + -8)%Z with (8 * xlen - 8)%Z by lia.
  rewrite EQL.
  eapply (cmp_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m _ _ xs ys xlen) with (k := Z.to_nat xlen); try eassumption; try lia.
  all: match goal with |- ?g => idtac g end.
Qed.
