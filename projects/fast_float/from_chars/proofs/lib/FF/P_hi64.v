(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs ImgFacts P_hi64_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac forget_vals :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 ?e)] =>
        lazymatch e with
        | Z.add (bv_unsigned _) _ => fail
        | Zpos _ => fail | Z0 => fail | Zneg _ => fail
        | bv_unsigned _ => fail
        | _ => tryif is_var e then fail else
               (let w := fresh "v" in let Ew := fresh "Ev" in remember (Z_to_bv 64 e) as w eqn:Ew in |- *; clear Ew)
        end
      end
  end.

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
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte)
            (ws : list word) (len : Z) (tb : byte) (junk : list byte).
  Hypothesis LIMBS : u64arr PSEGS m0 (bv_unsigned a0) ws.
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis TB : rw_cells PSEGS m0 (bv_unsigned a1) [C1 tb].
  Hypothesis ST : stk PSEGS m0 (bv_unsigned sp + -16) (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells PSEGS m0 (bv_unsigned sp + -16) [CB 8 (firstn 8 junk); C8 ra].
  Hypothesis MU : munch [((bv_unsigned sp + -16)%Z, bv_unsigned sp); (bv_unsigned a1, (bv_unsigned a1 + 1)%Z)] m m0.
  Hypothesis WM : wmono PSEGS m m0.
  Hypothesis SPLO : (139264 <= bv_unsigned sp + -16)%Z.
  Hypothesis SEPA : (bv_unsigned a0 + 498 <= bv_unsigned sp + -16 \/ bv_unsigned sp <= bv_unsigned a0)%Z.
  Hypothesis SEPT : (bv_unsigned a1 + 1 <= bv_unsigned sp + -16 \/ bv_unsigned sp <= bv_unsigned a1)%Z.
  Hypothesis SEPTA : (bv_unsigned a1 + 1 <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned a1)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis Bl : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.
  Hypothesis Bt : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + 1 <= 2 ^ 64)%Z.

  Notation POST := (hi64_post ra sp gp tp t0 t1 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).

  #[using="a0 ws tb junk LIMBS L62 TB ST FR MU WM SEPA SEPT SEPTA Bl Bt"] Lemma hi_tail : forall (r a3 a4 a5 a6 a7 c2 : word), (0 <= bv_unsigned c2 <= 1)%Z ->
    evt PSEGS POST (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 r a1 c2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x26238) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (a0 ws tb junk LIMBS L62 TB ST FR MU WM SEPA SEPT SEPTA Bl Bt : LiaFast.U) => LiaFast.u0).
    intros r a3 a4 a5 a6 a7 c2 Hc2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (lor_bit_range _ _ (v_sltu_range (Z_to_bv 64 0) a4) Hc2) as Ht.
    lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => remember (Z.lor x y) as t eqn:Et; clear Et end.
    step. (* [comment removed for export] *)
    rewrite unsigned_lit in TB by lia.
    step. step. step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    finish. all: first [exact TB | idtac]. all: lia.
  Qed.

  #[using="ws tb junk LIMBS L62 Hlen TB ST FR MU WM SEPA SEPT SEPTA Bl Bt"] Lemma hi_loop : forall (k : nat) (kz : Z) (r a2 a4 a6 a7 : word),
    (Z.to_nat kz <= k)%nat -> (0 <= kz <= len - 3)%Z ->
    evt PSEGS POST (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 r a1 a2 (Z_to_bv 64 (bv_unsigned a0 + 8 * kz)) a4 (Z_to_bv 64 kz) a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x26214) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (ws tb junk LIMBS L62 Hlen TB ST FR MU WM SEPA SEPT SEPTA Bl Bt : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros kz r a2 a4 a6 a7 Hk Hkz.
    - (* [comment removed for export] *)
      assert (kz = 0)%Z as -> by lia.
      destruct (nth_error ws 0) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
      pose proof (u64arr_read PSEGS m0 (bv_unsigned a0) ws 0 w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *) clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnz.
      + apply hi_tail. apply v_sltu_range.
      + step. step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_false.
        step. (* [comment removed for export] *)
        apply hi_tail. apply v_sltu_range.
    - destruct (Z.eq_dec kz 0) as [->|NZ].
      { apply (IH 0%Z); lia. }
      destruct (nth_error ws (Z.to_nat kz)) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
      pose proof (u64arr_read PSEGS m0 (bv_unsigned a0) ws kz w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
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

  #[using="ws tb junk LIMBS L62 Hlen TB ST FR MU WM SEPA SEPT SEPTA Bl Bt"] Lemma hi_scan : forall (r a4 a5 a6 a7 : word), (2 <= len)%Z ->
    evt PSEGS POST (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 r a1 (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned a0 + 8 * len)) a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x26204) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (ws tb junk LIMBS L62 Hlen TB ST FR MU WM SEPA SEPT SEPTA Bl Bt : LiaFast.U) => LiaFast.u0).
    intros r a4 a5 a6 a7 H2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H3.
    - cond_cleanup H3.
      step. (* [comment removed for export] *)
      apply hi_tail. rewrite unsigned_lit by lia. lia.
    - cond_cleanup H3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (bv_unsigned a0 + 8 * len + -24)%Z with (bv_unsigned a0 + 8 * (len + -3))%Z by lia.
      apply (hi_loop (Z.to_nat (len - 3))); lia.
  Qed.
End Tail.

Lemma hi64_spec : hi64_stmt.
Proof.
  unfold hi64_stmt. intros until tb. intros LIMBS L62 LENC Hlen NORM TB ST PR SPLO SEPA SEPT SEPTA.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 1)]%Z m) as MU.
  pose proof (wmono_refl PSEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
  pose proof (rw_cells_bound _ _ _ _ TB) as Bt. cbn [cells_size csize Nat.add] in Bt.
  pose proof (rw_cells_outside_rodata_P m _ _ PR TB ltac:(cbn; lia)) as TROD. cbn [cells_size csize Nat.add] in TROD.
  carve_frame 16%nat ST.
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
    destruct (nth_error ws 0) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
    pose proof (u64arr_read PSEGS m0 (bv_unsigned a0) ws 0 w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
    assert (WNZ : bv_unsigned w <> 0%Z).
    { pose proof (bnorm_top ws 1 ltac:(lia) NORM) as T. unfold limbZ in T. cbn [Nat.sub] in T.
      rewrite (nth_error_nth _ _ _ Hw) in T. exact T. }
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    do 33 (step; forget_vals).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish. all: first [exact TB | idtac]. all: rewrite ?unsigned_lit by lia; lia.
  - cond_cleanup H1.
    step. (* [comment removed for export] *)
    if_cases H0.
    + cond_cleanup H0.
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      replace (len * 8 + bv_unsigned a0)%Z with (bv_unsigned a0 + 8 * len)%Z by lia.
      destruct (nth_error ws (Z.to_nat (len - 1))) as [top|] eqn:Htop.
      2:{ apply nth_error_None in Htop. lia. }
      pose proof (u64arr_read PSEGS m0 (bv_unsigned a0) ws (len - 1) top _ LIMBS Htop ltac:(lia) eq_refl) as RD.
      assert (TOPNZ : bv_unsigned top <> 0%Z).
      { pose proof (bnorm_top ws (Z.to_nat len) ltac:(lia) NORM) as T. unfold limbZ in T.
        replace (Z.to_nat len - 1)%nat with (Z.to_nat (len - 1)) in T by lia.
        rewrite (nth_error_nth _ _ _ Htop) in T. exact T. }
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      if_not_taken.
      do 30 (step; forget_vals).
      destruct (nth_error ws (Z.to_nat (len - 2))) as [nxt|] eqn:Hnxt.
      2:{ apply nth_error_None in Hnxt. lia. }
      pose proof (u64arr_read PSEGS m0 (bv_unsigned a0) ws (len - 2) nxt _ LIMBS Hnxt ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step; forget_vals. step; forget_vals. step; forget_vals. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsh.
      * eapply hi_scan; try eassumption; lia.
      * do 6 (step; forget_vals).
        eapply hi_scan; try eassumption; lia.
    + cond_cleanup H0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. step. step.
      release_frame FR ST (bv_unsigned sp).
      finish. all: first [exact TB | idtac]. all: rewrite ?unsigned_lit by lia; lia.
Qed.
