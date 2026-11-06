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
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_nonzero_stmt.
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

Lemma b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof. intros [|]; cbn; lia. Qed.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word).
  Variables (vec : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (j8 : list byte).
  Variables (ws : list word) (len : Z).
  Hypothesis LIMBS : u64arr BSEGS m (bv_unsigned vec) ws.
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z.
  Hypothesis KA1 : (bv_unsigned vec + 504 <= KTOP)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis MU : munch (nonzero_W sp) m0 m.
  Hypothesis WM : wmono BSEGS m0 m.
  Hypothesis FR : rw_cells BSEGS m (bv_unsigned sp + -16) [CB 8 j8; C8 ra].
  Hypothesis ST : stk BSEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16).
  Hypothesis SHZ : shz BSEGS m (ASAN_B + bv_unsigned vec / 8) 63.

  Notation A := (bv_unsigned vec).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation POST := (nonzero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m0).

  (* [comment removed for export] *)
  #[using="vec j8 ws L62 KA0 MU WM FR ST"] Lemma nz_exit : forall (x5 x6 x7 x10 y x13 x14 x15 x16 x17 x28 x29 : word),
    evt BSEGS POST (MS (mkR ra SP' gp tp x5 x6 x7 s0 s1 x10 y (Z_to_bv 64 len) x13 x14 x15 x16 x17
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
                       F (Z_to_bv 64 0x98a20) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (vec j8 ws L62 KA0 MU WM FR ST : LiaFast.U) => LiaFast.u0).
    intros. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof MU as MU'. cbv delta [nonzero_W] in MU'.
    step. (* [comment removed for export] *) rewrite v_sltu_b2z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold nonzero_post. finish. all: try eassumption. all: try apply b2z_range.
  Qed.

  (* [comment removed for export] *)
  #[using="j8 ws LIMBS L62 Hlen KA0 KA1 MU WM FR ST SHZ"] Lemma nz_loop : forall (k : nat) (i : Z) (x7 x28 x29 : word),
    (Z.to_nat (len - i) <= k)%nat -> (0 <= i < len)%Z ->
    evt BSEGS POST
      (MS (mkR ra SP' gp tp (Z_to_bv 64 63) (Z_to_bv 64 (8 * (len - i))) x7 s0 s1
               vec (Z_to_bv 64 i) (Z_to_bv 64 len) BB (Z_to_bv 64 len)
               (Z_to_bv 64 (18446744073709551615 - A)) (Z_to_bv 64 (A - 8)) (Z_to_bv 64 (len - 1 - i))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0x989e8) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (j8 ws LIMBS L62 Hlen KA0 KA1 MU WM FR ST SHZ : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros i x7 x28 x29 Hk Hi; [lia|].
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    step. (* [comment removed for export] *) try if_not_taken.
    step. (* [comment removed for export] *)
    replace (8 * (len - i) + -8)%Z with (8 * (len - 1 - i))%Z by lia.
    step. (* [comment removed for export] *) try if_not_taken.
    step. (* [comment removed for export] *)
    replace (A - 8 + 8 * (len - i))%Z with (A + 8 * (len - 1 - i))%Z by lia.
    step. (* [comment removed for export] *) shr3.
    replace ((A + 8 * (len - 1 - i)) / 8)%Z with (A / 8 + (len - 1 - i))%Z by (Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    destruct (nth_error ws (Z.to_nat (len - 1 - i))) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
    pose proof (u64arr_read BSEGS m A ws (len - 1 - i) w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - apply nz_exit.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hne.
      + cond_cleanup Hne. rewrite ?unsigned_lit in Hne by lia.
        replace (8 * (len - 1 - i))%Z with (8 * (len - (i + 1)))%Z by lia.
        replace (len - 1 - i + -1)%Z with (len - 1 - (i + 1))%Z by lia.
        apply IH; lia.
      + apply nz_exit.
  Qed.
End Loop.

Lemma nonzero_spec : nonzero_stmt.
Proof.
  unfold nonzero_stmt. intros until len. intros LIMBS L62 LENC Hlen ST PRG BC SEP RO3 KSP KSP2 KA0 KA1 SHZ.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (munch_refl (nonzero_W sp) m) as MU. cbv delta [nonzero_W] in MU.
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
  rewrite (zx16_lit_small len) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hli.
  - cond_cleanup Hli.
    step. (* [comment removed for export] *)
    try if_taken.
    eapply nz_exit; try eassumption; try lia.
  - cond_cleanup Hli.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hge.
    + cond_cleanup Hge. eapply nz_exit; try eassumption; try lia.
    + cond_cleanup Hge.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      set (i := bv_unsigned a1) in *.
      rewrite !zb_lxor_ones by lia.
      rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      rewrite (unsigned_lit len) by lia. rewrite (unsigned_lit (len * 8)) by lia. rewrite (unsigned_lit (i * 8)) by lia.
      replace (Z_to_bv 64 (len * 8 - i * 8)) with (Z_to_bv 64 (8 * (len - i))) by (f_equal; lia).
      replace (Z_to_bv 64 (bv_unsigned a0 + -8)) with (Z_to_bv 64 (bv_unsigned a0 - 8)) by (f_equal; lia).
      replace (Z_to_bv 64 (18446744073709551615 - i + len)) with (Z_to_bv 64 (len - 1 - i))
        by (apply Z_to_bv_eqm; replace (18446744073709551615 - i + len)%Z with ((len - 1 - i) + 1 * 2 ^ 64)%Z by lia; rewrite Z_mod_plus_full; reflexivity).
      rewrite <- (Z_to_bv_bv_unsigned a1). change (bv_unsigned a1) with i.
      eapply (nz_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 F fc m _ _ ws len) with (k := Z.to_nat (len - i)); try eassumption; try lia.
Qed.
