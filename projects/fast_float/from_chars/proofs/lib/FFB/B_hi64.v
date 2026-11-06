(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_nonzero_stmt B_hi64_stmt.
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

Ltac with_mem tac := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => tac mc end.

Lemma unsigned_zxb8 : forall c, (0 <= c < 256)%Z -> bv_unsigned (zxb (Z_to_bv 8 c)) = c.
Proof.
  intros c Hc. unfold zxb.
  assert (E : bv_unsigned (Z_to_bv 8 c) = c).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z. lia. }
  rewrite E. apply unsigned_lit. lia.
Qed.

Lemma unsigned_lit8 : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z. lia.
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

Lemma stk_subH : forall m lo hi lo' hi',
  stk BSEGS m lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> (lo' <= hi')%Z -> stk BSEGS m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split BSEGS m lo lo' hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split BSEGS m lo' hi' hi ST1 ltac:(lia)) as [ST2 _]. exact ST2.
Qed.

Section Main.
  Hypothesis nonzero_spec : nonzero_stmt.

  Section Fixed.
  Variables (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws : list word) (len : Z) (j0 : list byte).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis SEPA : (bv_unsigned a0 + 498 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z.
  Hypothesis SEPT : (bv_unsigned a1 + 1 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a1)%Z.
  Hypothesis SEPTA : (bv_unsigned a1 + 1 <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned a1)%Z.
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 64)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp - 64)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z.
  Hypothesis KA1 : (bv_unsigned a0 + 504 <= KTOP)%Z.
  Hypothesis KB0 : (KHI <= bv_unsigned a1)%Z.
  Hypothesis KB1 : (bv_unsigned a1 + 1 <= KTOP)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis Bl : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.
  Hypothesis Bt : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + 1 <= 2 ^ 64)%Z.

  Notation POST := (hi64_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation FRAME mm := (rw_cells BSEGS mm (bv_unsigned sp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  #[using="a0 ws L62 KA0 Bl"] Lemma hi_exit : forall (t : Z) (r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 : word) (mm : word -> option byte),
    rw_cells BSEGS mm (bv_unsigned a1) [C1 (Z_to_bv 8 t)] ->
    (0 <= t <= 1)%Z ->
    FRAME mm ->
    stk BSEGS mm (bv_unsigned sp + -64) (bv_unsigned sp + -48) ->
    munch [((bv_unsigned sp - 64)%Z, bv_unsigned sp); (bv_unsigned a1, (bv_unsigned a1 + 1)%Z)] m mm ->
    wmono BSEGS m mm ->
    evt BSEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 a1 r x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
                       F (Z_to_bv 64 0x96e30) fc None mm (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (a0 ws L62 KA0 Bl : LiaFast.U) => LiaFast.u0).
    intros * TB Ht FR ST MU WM.
    step. (* [comment removed for export] *)
    do 7 step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold hi64_post. finish. all: first [exact TB | idtac]. all: try lia.
    all: try (replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia; exact ST).
  Qed.
  End Fixed.

  #[using="nonzero_spec"] Lemma hi64_spec : hi64_stmt.
  Proof. LiaFast.lf_pins (fun (nonzero_spec : LiaFast.U) => LiaFast.u0).
    unfold hi64_stmt. intros until tb. intros LIMBS L62 LENC Hlen NORM TB ST PR SPLO SEPA SEPT SEPTA PRG BC KSP KSP2 KA0 KA1 KB0 KB1 SHA SHT.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 1)]%Z m) as MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ TB) as Bt. cbn [cells_size csize Nat.add] in Bt.
    carve_frame 48%nat ST.
    step. (* [comment removed for export] *)
    do 5 step. (* [comment removed for export] *)
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
    rewrite (zx16_lit_small len) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H1.
    - cond_cleanup H1. subst len.
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Ht; [ cond_cleanup Ht; rewrite ?zb_lxor_ones in Ht by lia; rewrite ?unsigned_lit in Ht by lia; exfalso; lia | clear Ht ].
      zstep. (* [comment removed for export] *)
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
      with_mem ltac:(fun mc => pose proof (u64arr_read BSEGS mc (bv_unsigned a0) ws 0 w _ LIMBS Hw ltac:(lia) ltac:(f_equal; lia)) as RD).
      step. (* [comment removed for export] *) clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      do 33 (step; forget_vals).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply hi_exit; try eassumption; try lia.
      all: try (rewrite ?unsigned_lit by lia; lia).
      all: try match goal with H : rw_cells BSEGS _ _ [C1 ?x] |- rw_cells BSEGS _ _ [C1 _] => first [exact H | change (Z_to_bv 8 0) with x; exact H] end.
      all: try lia.
      all: match goal with |- ?g => idtac "REMAIN-1" g end.
    - cond_cleanup H1.
      step. (* [comment removed for export] *)
      if_cases H0.
      + (* [comment removed for export] *)
        cond_cleanup H0.
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        rewrite (Z.shiftl_mul_pow2 (len + -1) 3) by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        rewrite ?zb_lxor_ones by lia.
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        replace (bv_unsigned a0 + (len + -1) * 8)%Z with (bv_unsigned a0 + 8 * (len - 1))%Z by lia.
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
        zstep. (* [comment removed for export] *)
        rewrite (Z.shiftl_mul_pow2 (len + -2) 3) by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        replace (bv_unsigned a0 + (len + -2) * 8)%Z with (bv_unsigned a0 + 8 * (len - 2))%Z by lia.
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        with_mem ltac:(fun mc => pose proof (u64arr_read BSEGS mc (bv_unsigned a0) ws (len - 1) top _ LIMBS Htop ltac:(lia) eq_refl) as RD).
        step. (* [comment removed for export] *)
        clear RD.
        step. (* [comment removed for export] *)
        if_not_taken.
        do 30 (step; forget_vals).
        destruct (nth_error ws (Z.to_nat (len - 2))) as [nxt|] eqn:Hnxt.
        2:{ apply nth_error_None in Hnxt. lia. }
        with_mem ltac:(fun mc => pose proof (u64arr_read BSEGS mc (bv_unsigned a0) ws (len - 2) nxt _ LIMBS Hnxt ltac:(lia) eq_refl) as RD).
        step. (* [comment removed for export] *)
        clear RD.
        step; forget_vals. step; forget_vals. step; forget_vals. (* [comment removed for export] *)
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (JFC : forall (y9 y11 y12 y14 y15 y16 : word),
          evt BSEGS (hi64_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m)
                    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a1 y9 a0 y11 y12 (Z_to_bv 64 ASAN_B) y14 y15 y16 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x96dec) fc None mc (seg_rom BSEGS))) end.
        { intros.
          step. (* [comment removed for export] *) shr3.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose proof (v_sltu_range (Z_to_bv 64 0) y11) as Hc2.
          remember (v_sltu (Z_to_bv 64 0) y11) as c2w eqn:Ec2; clear Ec2.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as ULs.
          step. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            eapply evt_cut; [ eapply nonzero_spec with (ws := ws) (len := len) | post_call BSEGS mc ] end.
          all: try lazymatch goal with
               | |- evt _ _ _ => idtac
               | |- u64arr _ _ _ _ => eassumption
               | |- rw_cells _ _ _ [C2 _] => eassumption
               | |- pristine _ _ _ => exact PRG
               | |- ro_cells _ _ _ _ => exact BC
               | |- shz _ _ _ _ => eassumption
               | |- stk _ _ _ _ => rewrite ?ULs; match goal with H : stk BSEGS _ _ _ |- _ => eapply stk_subH; [exact H | lia | lia | lia] end
               | |- _ => rewrite ?ULs; first [eassumption | lia]
               end.
          rewrite ?ULs in *.
          match goal with H : (0 <= ?b <= 1)%Z |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename H into Hb; rename b into nb end.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          try rewrite (unsigned_zxb8 (bv_unsigned c2w)) by lia.
          step. (* [comment removed for export] *)
          if_cases Ht; [ cond_cleanup Ht; rewrite ?unsigned_lit8 in Ht by lia; rewrite ?unsigned_lit in Ht by lia; exfalso; lia | clear Ht ].
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          rewrite ?(unsigned_zxb8 (bv_unsigned c2w)) by lia. rewrite ?unsigned_lit8 by lia. rewrite ?unsigned_lit by lia.
          pose proof (lor_bit_range _ _ Hc2 Hb) as Htt.
          remember (Z.lor (bv_unsigned c2w) nb) as t eqn:Et; clear Et.
          step. (* [comment removed for export] *)
          eapply hi_exit; try eassumption; try lia.
          all: try match goal with H : rw_cells BSEGS _ _ [C1 ?x] |- rw_cells BSEGS _ _ [C1 _] =>
                 first [exact H | rewrite (unsigned_lit t) in H by lia; exact H] end.
          all: rewrite ?unsigned_lit by lia; try lia.
          all: try (replace (bv_unsigned sp + -64)%Z with (bv_unsigned sp + -48 - 16)%Z by lia; assumption).
          all: match goal with |- ?g => idtac "REMAIN-2" g end. }
        step. (* [comment removed for export] *)
        if_cases Hsh.
        * apply JFC.
        * do 6 (step; forget_vals). apply JFC.
      + (* [comment removed for export] *)
        cond_cleanup H0.
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply hi_exit; try eassumption; try lia.
        all: try match goal with H : rw_cells BSEGS _ _ [C1 ?x] |- rw_cells BSEGS _ _ [C1 _] => first [exact H | change (Z_to_bv 8 0) with x; exact H] end.
        all: try (rewrite ?unsigned_lit by lia; lia).
        all: match goal with |- ?g => idtac "REMAIN-0" g end.
  Qed.
End Main.
