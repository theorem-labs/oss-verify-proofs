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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_rt_stmt A_rt_lemmas A_long_mul_stmt A_pow10_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_positive_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt.A_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt.A_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_positive_digit_comp_d_stmt.

Module A_ctlz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt.A_ctlz_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2.
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
Ltac forget_vals :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 ?e)] =>
        lazymatch e with
        | Z.add (bv_unsigned _) _ => fail
        | Zpos _ => fail | Z0 => fail | Zneg _ => fail
        | bv_unsigned _ => fail
        | _ => let w := fresh "v" in let Ew := fresh "Ev" in remember (Z_to_bv 64 e) as w eqn:Ew in |- *; clear Ew
        end
      end
  end.

Lemma shiftr56_bound : forall w : word, (0 <= Z.shiftr (bv_unsigned w) 56 < 256)%Z.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia|]. change (2 ^ Z.of_N 64)%Z with (2^56 * 256)%Z in H. lia.
Qed.

Lemma ctlz_spec : ctlz_stmt.
Proof.
  unfold ctlz_stmt. intros until len. intros LIMBS L62 LENC Hlen NORM ST PR SPLO SEP PRG BC KSP KSP2 KA0 KA1 SHZ.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ASEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
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
  rewrite (zx16_lit_small len) by lia.
  step. (* [comment removed for export] *)
  if_cases Hz.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. step. step. step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    finish. all: first [lia | assumption].
  - cond_cleanup Hz.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite (Z.shiftl_mul_pow2 len 3) by lia. change (2 ^ 3)%Z with 8%Z.
    zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (nth_error ws (Z.to_nat (len - 1))) as [top|] eqn:Htop.
    2:{ apply nth_error_None in Htop. lia. }
    assert (TOPNZ : bv_unsigned top <> 0%Z).
    { pose proof (bnorm_top ws (Z.to_nat len) ltac:(lia) NORM) as T. unfold limbZ in T.
      replace (Z.to_nat len - 1)%nat with (Z.to_nat (len - 1)) in T by lia.
      rewrite (nth_error_nth _ _ _ Htop) in T. exact T. }
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u64arr_read ASEGS mc (bv_unsigned a0) ws (len - 1) top _ LIMBS Htop ltac:(lia) eq_refl) as RD end.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    if_not_taken.
    do 32 (step; forget_vals).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. step. step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    finish; try apply shiftr56_bound.
Qed.
End A_ctlz.

Module A_hi64.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt.A_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2.
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

Ltac forget_vals :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 ?e)] =>
        lazymatch e with
        | Z.add (bv_unsigned _) _ => fail
        | Z.add (Z.add (bv_unsigned _) _) _ => fail
        | Z.add _ ASAN_B => fail
        | Zpos _ => fail | Z0 => fail | Zneg _ => fail
        | bv_unsigned _ => fail
        | _ => tryif is_var e then fail else
               (let w := fresh "v" in let Ew := fresh "Ev" in remember (Z_to_bv 64 e) as w eqn:Ew in |- *; clear Ew)
        end
      end
  end.

(* [comment removed for export] *)
Ltac with_mem tac := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => tac mc end.

Lemma unsigned_zxb8 : forall c, (0 <= c < 256)%Z -> bv_unsigned (zxb (Z_to_bv 8 c)) = c.
Proof.
  intros c Hc. unfold zxb.
  assert (E : bv_unsigned (Z_to_bv 8 c) = c).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z. lia. }
  rewrite E. apply unsigned_lit. lia.
Qed.

Lemma v_sltu_range : forall a b, (0 <= bv_unsigned (v_sltu a b) <= 1)%Z.
Proof. intros. unfold v_sltu. destruct (c_ltu a b); rewrite unsigned_lit by lia; lia. Qed.

Lemma lor_bit_range : forall x y, (0 <= x <= 1)%Z -> (0 <= y <= 1)%Z -> (0 <= Z.lor x y <= 1)%Z.
Proof.
  intros x y Hx Hy.
  destruct (Z.eq_dec x 0) as [->|X1]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec y 0) as [->|Y1]; [rewrite Z.lor_0_r; lia|].
  assert (x = 1)%Z by lia. assert (y = 1)%Z by lia. subst x y. rewrite Z.lor_diag. lia.
Qed.

Section Tail.
  Variables (ra sp gp tp t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m mm : word -> option byte)
            (ws : list word) (len : Z) (c2 : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis Hc2 : (0 <= c2 <= 1)%Z.
  Hypothesis LIMBS : u64arr ASEGS mm (bv_unsigned a0) ws.
  Hypothesis TB : rw_cells ASEGS mm (bv_unsigned a1) [C1 (Z_to_bv 8 c2)].
  Hypothesis ST : stk ASEGS mm (bv_unsigned sp + -16) (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells ASEGS mm (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis MU : munch [((bv_unsigned sp + -16)%Z, bv_unsigned sp); (bv_unsigned a1, (bv_unsigned a1 + 1)%Z)] m mm.
  Hypothesis WM : wmono ASEGS m mm.
  Hypothesis SHA : shz ASEGS mm (ASAN_B + bv_unsigned a0 / 8) 63.
  Hypothesis SHT : shz ASEGS mm (ASAN_B + bv_unsigned a1 / 8) 1.
  Hypothesis SEPA : (bv_unsigned a0 + 498 <= bv_unsigned sp + -16 \/ bv_unsigned sp <= bv_unsigned a0)%Z.
  Hypothesis SEPT : (bv_unsigned a1 + 1 <= bv_unsigned sp + -16 \/ bv_unsigned sp <= bv_unsigned a1)%Z.
  Hypothesis SEPTA : (bv_unsigned a1 + 1 <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned a1)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z.
  Hypothesis KA1 : (bv_unsigned a0 + 504 <= KTOP)%Z.
  Hypothesis KB0 : (KHI <= bv_unsigned a1)%Z.
  Hypothesis KB1 : (bv_unsigned a1 + 1 <= KTOP)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis Bl : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.
  Hypothesis Bt : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + 1 <= 2 ^ 64)%Z.

  Notation POST := (hi64_post ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation A6 := (Z_to_bv 64 (bv_unsigned a1 / 8 + ASAN_B)).

  (* [comment removed for export] *)
  #[using="a0 ws c2 L62 Hc2 LIMBS TB ST FR MU WM SHA SHT SEPA SEPT SEPTA KSP KSP2 KA0 KB0 KB1 Bl"] Lemma hi_tail : forall (r x5 x6 a2 a5 a7 c4 : word), (0 <= bv_unsigned c4 <= 1)%Z ->
    evt ASEGS POST (MS (mkR ra SP' gp tp x5 x6 t2 s0 s1 r a1 a2 BB c4 a5 A6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9668c) fc None mm (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (a0 ws c2 L62 Hc2 LIMBS TB ST FR MU WM SHA SHT SEPA SEPT SEPTA KSP KSP2 KA0 KB0 KB1 Bl : LiaFast.U) => LiaFast.u0).
    intros r x5 x6 a2 a5 a7 c4 Hc4.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_zxb8 c2) by lia.
    pose proof (lor_bit_range _ _ Hc2 Hc4) as Ht.
    remember (Z.lor c2 (bv_unsigned c4)) as t eqn:Et; clear Et.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit t) in TB by lia.
    step. step. step. step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    finish. all: first [exact TB | idtac]. all: lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ws c2 L62 Hlen Hc2 LIMBS TB ST FR MU WM SHA SHT SEPA SEPT SEPTA KSP KSP2 KA0 KB0 KB1 Bl"] Lemma hi_loop : forall (k : nat) (kz : Z) (r x5 x6 a4 : word),
    (Z.to_nat kz <= k)%nat -> (0 <= kz <= len - 3)%Z ->
    evt ASEGS POST (MS (mkR ra SP' gp tp x5 x6 t2 s0 s1 r a1 (Z_to_bv 64 (bv_unsigned a0 + 8 * kz)) BB a4
                             (Z_to_bv 64 (bv_unsigned a0 + 8 * kz)) A6 (Z_to_bv 64 kz)
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x96654) fc None mm (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (ws c2 L62 Hlen Hc2 LIMBS TB ST FR MU WM SHA SHT SEPA SEPT SEPTA KSP KSP2 KA0 KB0 KB1 Bl : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros kz r x5 x6 a4 Hk Hkz.
    - (* [comment removed for export] *)
      assert (kz = 0)%Z as -> by lia.
      destruct (nth_error ws 0) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_read ASEGS mm (bv_unsigned a0) ws 0 w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *) clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnz.
      + apply hi_tail. apply v_sltu_range.
      + step. step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        apply hi_tail. apply v_sltu_range.
    - destruct (Z.eq_dec kz 0) as [->|NZ].
      { apply (IH 0%Z); lia. }
      destruct (nth_error ws (Z.to_nat kz)) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_read ASEGS mm (bv_unsigned a0) ws kz w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *) clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnz.
      + apply hi_tail. apply v_sltu_range.
      + step. step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_taken.
        replace (bv_unsigned a0 + 8 * kz + -8)%Z with (bv_unsigned a0 + 8 * (kz + -1))%Z by lia.
        apply IH; lia.
  Qed.
End Tail.

Section Scan.
  Variables (ra sp gp tp t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte)
            (ws : list word) (len : Z) (tb : byte).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis LIMBS : u64arr ASEGS m0 (bv_unsigned a0) ws.
  Hypothesis TB : rw_cells ASEGS m0 (bv_unsigned a1) [C1 tb].
  Hypothesis ST : stk ASEGS m0 (bv_unsigned sp + -16) (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells ASEGS m0 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis MU : munch [((bv_unsigned sp + -16)%Z, bv_unsigned sp); (bv_unsigned a1, (bv_unsigned a1 + 1)%Z)] m m0.
  Hypothesis WM : wmono ASEGS m m0.
  Hypothesis SHA : shz ASEGS m0 (ASAN_B + bv_unsigned a0 / 8) 63.
  Hypothesis SHT : shz ASEGS m0 (ASAN_B + bv_unsigned a1 / 8) 1.
  Hypothesis SEPA : (bv_unsigned a0 + 498 <= bv_unsigned sp + -16 \/ bv_unsigned sp <= bv_unsigned a0)%Z.
  Hypothesis SEPT : (bv_unsigned a1 + 1 <= bv_unsigned sp + -16 \/ bv_unsigned sp <= bv_unsigned a1)%Z.
  Hypothesis SEPTA : (bv_unsigned a1 + 1 <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned a1)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z.
  Hypothesis KA1 : (bv_unsigned a0 + 504 <= KTOP)%Z.
  Hypothesis KB0 : (KHI <= bv_unsigned a1)%Z.
  Hypothesis KB1 : (bv_unsigned a1 + 1 <= KTOP)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis Bl : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.
  Hypothesis Bt : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + 1 <= 2 ^ 64)%Z.

  Notation POST := (hi64_post ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).

  (* [comment removed for export] *)
  #[using="ws tb L62 Hlen LIMBS TB ST FR MU WM SHA SHT SEPA SEPT SEPTA KSP KSP2 KA0 KB0 KB1 Bl"] Lemma hi_scan : forall (r x5 x6 a2 a6 a7 : word), (2 <= len)%Z ->
    evt ASEGS POST (MS (mkR ra SP' gp tp x5 x6 t2 s0 s1 r a1 a2 BB (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned a0 + 8 * len)) a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x96628) fc None m0 (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (ws tb L62 Hlen LIMBS TB ST FR MU WM SHA SHT SEPA SEPT SEPTA KSP KSP2 KA0 KB0 KB1 Bl : LiaFast.U) => LiaFast.u0).
    intros r x5 x6 a2 a6 a7 H2.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (v_sltu_range (Z_to_bv 64 0) a2) as Hc2.
    remember (v_sltu (Z_to_bv 64 0) a2) as c2w eqn:Ec2; clear Ec2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H3.
    - cond_cleanup H3.
      step. (* [comment removed for export] *)
      eapply hi_tail; try eassumption; rewrite ?unsigned_lit by lia; try lia.
    - cond_cleanup H3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (bv_unsigned a0 + 8 * len + -24)%Z with (bv_unsigned a0 + 8 * (len - 3))%Z by lia.
      replace (len + -3)%Z with (len - 3)%Z by lia.
      eapply (hi_loop ra sp gp tp t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ ws len (bv_unsigned c2w))
        with (k := Z.to_nat (len - 3)); try eassumption; try lia.
  Qed.
End Scan.

Lemma hi64_spec : hi64_stmt.
Proof.
  unfold hi64_stmt. intros until tb. intros LIMBS L62 LENC Hlen NORM TB ST PR SPLO SEPA SEPT SEPTA PRG BC KSP KSP2 KA0 KA1 KB0 KB1 SHA SHT.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 1)]%Z m) as MU.
  pose proof (wmono_refl ASEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
  pose proof (rw_cells_bound _ _ _ _ TB) as Bt. cbn [cells_size csize Nat.add] in Bt.
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
  rewrite (zx16_lit_small len) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases H1.
  - cond_cleanup H1. subst len.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    destruct (nth_error ws 0) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
    assert (WNZ : bv_unsigned w <> 0%Z).
    { pose proof (bnorm_top ws 1 ltac:(lia) NORM) as T. unfold limbZ in T. cbn [Nat.sub] in T.
      rewrite (nth_error_nth _ _ _ Hw) in T. exact T. }
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    with_mem ltac:(fun mc => pose proof (u64arr_read ASEGS mc (bv_unsigned a0) ws 0 w _ LIMBS Hw ltac:(lia) eq_refl) as RD).
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    do 33 (step; forget_vals).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish. all: first [exact TB | idtac]. all: rewrite ?unsigned_lit by lia; lia.
  - cond_cleanup H1.
    step. (* [comment removed for export] *)
    if_cases H0.
    + cond_cleanup H0.
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite (Z.shiftl_mul_pow2 len 3) by lia. change (2 ^ 3)%Z with 8%Z.
      replace (len * 8 + bv_unsigned a0)%Z with (bv_unsigned a0 + 8 * len)%Z by lia.
      zstep. (* [comment removed for export] *)
      destruct (nth_error ws (Z.to_nat (len - 1))) as [top|] eqn:Htop.
      2:{ apply nth_error_None in Htop. lia. }
      assert (TOPNZ : bv_unsigned top <> 0%Z).
      { pose proof (bnorm_top ws (Z.to_nat len) ltac:(lia) NORM) as T. unfold limbZ in T.
        replace (Z.to_nat len - 1)%nat with (Z.to_nat (len - 1)) in T by lia.
        rewrite (nth_error_nth _ _ _ Htop) in T. exact T. }
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      with_mem ltac:(fun mc => pose proof (u64arr_read ASEGS mc (bv_unsigned a0) ws (len - 1) top _ LIMBS Htop ltac:(lia) eq_refl) as RD).
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      if_not_taken.
      do 30 (step; forget_vals).
      destruct (nth_error ws (Z.to_nat (len - 2))) as [nxt|] eqn:Hnxt.
      2:{ apply nth_error_None in Hnxt. lia. }
      with_mem ltac:(fun mc => pose proof (u64arr_read ASEGS mc (bv_unsigned a0) ws (len - 2) nxt _ LIMBS Hnxt ltac:(lia) eq_refl) as RD).
      step. (* [comment removed for export] *)
      clear RD.
      step; forget_vals. step; forget_vals. step; forget_vals. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsh.
      * eapply hi_scan; try eassumption; lia.
      * do 6 (step; forget_vals).
        eapply hi_scan; try eassumption; lia.
    + cond_cleanup H0.
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      finish. all: first [exact TB | idtac]. all: rewrite ?unsigned_lit by lia; lia.
Qed.
End A_hi64.

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
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length in *) else idtac.      (* [comment removed for export] *)

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

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)
Ltac open_fk5 H :=
  let a := fresh "FK1" in let b := fresh "FK2" in let c := fresh "FK3" in let d := fresh "FK4" in let e := fresh "FK5" in
  destruct H as (a & b & c & d & e); unfold fs_cells_ok in a.
Ltac close_fk5 := unfold fk5_inv, fs_cells_ok; repeat match goal with |- _ /\ _ => split end; eassumption.
Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

(* [comment removed for export] *)
Ltac gen_val e := let X := fresh "rv" in set (X := e) in *; clearbody X.
Ltac gen_big :=
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
  | |- context [Some (zx8 ?a)] => gen_val (zx8 a)
  | |- context [Some (zx16 ?a)] => gen_val (zx16 a)
  | |- context [Some (sx32 ?a)] => gen_val (sx32 a)
  end.
Ltac gstep := step; gen_big.

Lemma cb1_c1 : forall m A l, rw_cells ASEGS m A [CB 1 l] -> exists b, rw_cells ASEGS m A [C1 b].
Proof.
  intros m A l [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
  destruct l as [|b [|]]; cbn in Hl; try discriminate.
  exists b. split; [split|]; [cbn; tauto | exact Hb | exact Hw].
Qed.

Section Main.
  Hypothesis pow10_spec : pow10_stmt.
  Hypothesis hi64_spec : hi64_stmt.
  Hypothesis ctlz_spec : ctlz_stmt.

  Notation SP' sp := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation BB := (Z_to_bv 64 ASAN_B).

  #[using="pow10_spec hi64_spec ctlz_spec"] Lemma positive_digit_comp_d_spec : positive_digit_comp_d_stmt.
  Proof. LiaFast.lf_pins (fun (pow10_spec hi64_spec ctlz_spec : LiaFast.U) => LiaFast.u0).
    unfold positive_digit_comp_d_stmt. intros until h5. cbv zeta.
    intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM He CAP CAP2 SEP TP PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF SHS RTX0.
    pose proof (munch_refl (positive_digit_comp_d_W (bv_unsigned sp) (bv_unsigned a0) (rt_FS v)) m) as MU.
    cbv delta [positive_digit_comp_d_W] in MU.
    pose proof (wmono_refl ASEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Kc1 & Kc2 & Kt1 & Kt2 & Kb1 & Kb2).
    assert (BC : ro_cells ASEGS m 937400 [C8 (Z_to_bv 64 ASAN_B)]).
    { change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
      apply (proj1 (proj1 (ro_cells_app ASEGS m 937400 _ _) RT1)). }
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    open_fk5 FK.
    carve_frame 48%nat ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply pow10_spec with (v := v) (h5 := h5) (ws := ws) (len := len) | post_call ASEGS mc ] end.
    1:{ rewrite ULs. replace (bv_unsigned sp + -48 - 2624)%Z with (bv_unsigned sp - 2672)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NORM. }
    1:{ exact He. } 1:{ exact CAP. } 1:{ exact CAP2. }
    1:{ rewrite ULs. lia. }
    1:{ exact TP. } 1:{ exact PRG. } 1:{ exact PRT. }
    1:{ eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
    1:{ close_fk5. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ rewrite ULs. lia. } 1:{ exact SEPF. }
    1:{ rewrite ULs. eapply rt_disj_sub; [exact RD1 | lia | lia]. }
    1:{ exact RD2. } 1:{ exact RD3. }
    1:{ exact SHX. } 1:{ exact SHT. } 1:{ exact RBX. } 1:{ exact RBF. } 1:{ exact RTX0. }
    rewrite ?ULs in *.
    clear CAP CAP2 NORM.
    match goal with H : u64arr ASEGS _ (bv_unsigned a0) ?w |- _ => rename H into XA5; rename w into ws5 end.
    match goal with H : length ws5 = 62%nat |- _ => rename H into L62' end.
    match goal with H : rw_cells ASEGS _ (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename H into LENC5; rename l into len5 end.
    match goal with H : (0 <= len5 <= 62)%Z |- _ => rename H into Hlen5 end.
    match goal with H : bnorm ws5 _ |- _ => rename H into BN5 end.
    match goal with H : stk ASEGS _ (bv_unsigned sp + -48 - 2624) _ |- _ => rename H into ST5 end.
    match goal with H : RT _ v |- _ => rename H into RTH5 end.
    match goal with H : pristine _ IMG_LO ROD_HI |- _ => rename H into PR5 end.
    match goal with H : fk5_inv _ (rt_FS v) ?hh |- _ => rename H into FK5'; rename hh into h5b end.
    try clear FK1; try clear FK2; try clear FK3; try clear FK4; try clear FK5. open_fk5 FK5'.
    name_mem m1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 2672, bv_unsigned sp)]%Z m1) as MU1.
    (* [comment removed for export] *)
    eapply (rw_cells_split_CB ASEGS m1 _ [] 16 _ _ [15; 1]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    chunk_split FR 1%nat FR15 FRr. chunk_split FRr 1%nat TB FRs.
    destruct (cb1_c1 _ _ _ TB) as [tb TB1]. clear TB.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -33) ltac:(lia)) as UL15.
    replace (bv_unsigned sp + -48 - 2624)%Z with (bv_unsigned sp - 2672)%Z in ST5 by lia.
    destruct (stk_split _ _ _ (bv_unsigned sp + -48 - 16)%Z _ ST5 ltac:(lia)) as [STlo SThi]. clear ST5.
    match goal with H : shz ASEGS m1 (ASAN_B + (bv_unsigned sp - 2672) / 8) 334 |- _ => rename H into SHS1 end.
    assert (SHB : shz ASEGS m1 (ASAN_B + (bv_unsigned sp + -33) / 8) 1).
    { eapply shz_sub; [exact SHS1 | | lia | ]; Z.div_mod_to_equations; lia. }
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply hi64_spec with (ws := ws5) (len := len5) (tb := tb) | post_call ASEGS mc ] end.
    1:{ exact XA5. } 1:{ exact L62'. } 1:{ exact LENC5. } 1:{ exact Hlen5. } 1:{ exact BN5. }
    1:{ rewrite UL15. exact TB1. }
    1:{ rewrite ULs. exact SThi. }
    1:{ exact PR5. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite UL15, ULs. lia. }
    1:{ rewrite UL15. lia. }
    1:{ exact PRG. } 1:{ exact BC. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ rewrite UL15. lia. } 1:{ rewrite UL15. lia. }
    1:{ exact SHX. }
    1:{ rewrite UL15. exact SHB. }
    rewrite ?ULs, ?UL15 in *.
    rename MI into Ht. rename PC into TB.
    first [ clear SThi; rename POST into SThi | rename POST into SThi ].
    name_mem m2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply ctlz_spec with (ws := ws5) (len := len5) | post_call ASEGS mc ] end.
    1:{ exact XA5. } 1:{ exact L62'. } 1:{ exact LENC5. } 1:{ exact Hlen5. } 1:{ exact BN5. }
    1:{ rewrite ULs. exact SThi. }
    1:{ exact PR5. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PRG. } 1:{ exact BC. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ exact SHX. }
    rewrite ?ULs in *.
    rename MI into Hz. first [ clear SThi; rename POST into SThi | rename POST into SThi ].
    name_mem m3.
    try clear ST. pose proof (stk_merge _ _ _ _ _ STlo SThi ltac:(lia)) as ST. clear STlo SThi.
    (* [comment removed for export] *)
    assert (EPI : forall x1 x5 x6 x7 v8 v10 v11 v12 v13 v14 v15 x16 x17 x28 x29 x30 x31 : word,
      evt ASEGS (positive_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) v m)
        (MS (mkR x1 (SP' sp) gp tp x5 x6 x7 v8 a0 v10 v11 v12 v13 v14 v15 x16 x17
                 BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x95b9c) fc None m3 (seg_rom ASEGS))).
    2:{
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hden.
    - clear Hden.
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (J04 : forall x1 x5 x6 x7 v8 v10 v11 v12 x14 x15 x16 x17 x28 x29 x30 x31 : word,
        evt ASEGS (positive_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) v m)
          (MS (mkR x1 (SP' sp) gp tp x5 x6 x7 v8 a0 v10 v11 v12 (Z_to_bv 64 64) x14 x15 x16 x17
                   BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x95b40) fc None m3 (seg_rom ASEGS))).
      { intros.
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        do 11 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb1.
        { clear Hb1. do 3 gstep. apply EPI. }
        clear Hb1.
        step. (* [comment removed for export] *)
        if_cases Hb2.
        - clear Hb2. do 4 gstep. (* [comment removed for export] *) do 3 gstep. apply EPI.
        - clear Hb2. step. (* [comment removed for export] *)
          if_cases Hb3.
          + clear Hb3. do 3 gstep. apply EPI.
          + clear Hb3. do 4 gstep. do 3 gstep. apply EPI. }
      if_cases Hsh.
      + clear Hsh. apply J04.
      + clear Hsh. step. (* [comment removed for export] *) apply J04.
    - clear Hden.
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (Jac : forall x1 x5 x6 x7 v8 v10 v11 v12 v13 v14 x16 x17 x28 x29 x30 x31 : word,
        evt ASEGS (positive_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) v m)
          (MS (mkR x1 (SP' sp) gp tp x5 x6 x7 v8 a0 v10 v11 v12 v13 v14 (Z_to_bv 64 1024) x16 x17
                   BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x95ae8) fc None m3 (seg_rom ASEGS))).
      { intros.
        do 8 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hinf.
        - clear Hinf. step. step. step. gstep. step. (* [comment removed for export] *) apply EPI.
        - clear Hinf. step. (* [comment removed for export] *) step. step. step. gstep. step. apply EPI. }
      step. (* [comment removed for export] *)
      if_cases Hb1. { clear Hb1. apply Jac. }
      clear Hb1.
      step. (* [comment removed for export] *)
      if_cases Hb2.
      + clear Hb2. do 6 gstep. (* [comment removed for export] *) apply Jac.
      + clear Hb2. step. (* [comment removed for export] *)
        if_cases Hb3.
        * clear Hb3. apply Jac.
        * clear Hb3. do 6 gstep. apply Jac. }
    (* [comment removed for export] *)
    intros.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    chunk_join FR15 TB FRa. chunk_join FRa FRs FR.
    release_frame FR ST (bv_unsigned sp).
    unfold positive_digit_comp_d_post. finish.
    all: try eassumption. all: try lia.
    all: try (eapply RT_transport; [exact RTH5 | exact MU1 | solve_W_ok_rt]).
    all: try close_fk5.
  Qed.
End Main.
