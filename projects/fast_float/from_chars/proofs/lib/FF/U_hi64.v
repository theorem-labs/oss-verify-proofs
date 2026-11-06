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
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs ImgFacts.

Module U_nonzero_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition nonzero_entry : Z := 0x27be4.

Definition nonzero_post
    (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (b : Z) (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 b) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch [] m m'
    /\ wmono USEGS m m'
    /\ (0 <= b <= 1)%Z.

Definition nonzero_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    evt USEGS (nonzero_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27be4) fc None m (seg_rom USEGS)).
End U_nonzero_stmt.


Module U_nonzero.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64.U_nonzero_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof. intros [|]; cbn; lia. Qed.

Section Loop.
  Variables (ra sp gp tp t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws : list word) (len : Z).
  Hypothesis LIMBS : u64arr USEGS m (bv_unsigned a0) ws.
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis Bl : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.
  Notation POST := (nonzero_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).

  #[using="Type"] Lemma nz_exit : forall (t0 y x a3 a4 a5 a6 a7 : word),
    evt USEGS POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 y x (Z_to_bv 64 len) a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x27c44) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros. step. (* [comment removed for export] *) rewrite v_sltu_b2z. step. (* [comment removed for export] *)
    finish. 1: apply munch_refl. 1: apply wmono_refl. all: apply b2z_range.
  Qed.

  #[using="ws LIMBS L62 Hlen Bl"] Lemma nz_loop : forall (k : nat) (i : Z) (t0 : word),
    (Z.to_nat (len - i) <= k)%nat -> (0 <= i < len)%Z ->
    evt USEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 (8 * (len - 1 - i))) (Z_to_bv 64 i) (Z_to_bv 64 len) (Z_to_bv 64 len)
               (Z_to_bv 64 (18446744073709551615 - bv_unsigned a0)) (Z_to_bv 64 (len - 1 - i))
               (Z_to_bv 64 (bv_unsigned a0 + 8 * (len - 1 - i))) (Z_to_bv 64 63)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x27c20) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (ws LIMBS L62 Hlen Bl : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros i t0 Hk Hi; [lia|].
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *) if_not_taken.
    destruct (nth_error ws (Z.to_nat (len - 1 - i))) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
    pose proof (u64arr_read USEGS m (bv_unsigned a0) ws (len - 1 - i) w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - apply nz_exit.
    - step. step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hne.
      + cond_cleanup Hne.
        replace (8 * (len - 1 - i) + -8)%Z with (8 * (len - 1 - (i + 1)))%Z by lia.
        replace (bv_unsigned a0 + 8 * (len - 1 - i) + -8)%Z with (bv_unsigned a0 + 8 * (len - 1 - (i + 1)))%Z by lia.
        replace (len - 1 - i + -1)%Z with (len - 1 - (i + 1))%Z by lia.
        apply IH; lia.
      + apply nz_exit.
  Qed.
End Loop.

Lemma nonzero_spec : nonzero_stmt.
Proof.
  unfold nonzero_stmt. intros until len. intros LIMBS L62 LENC Hlen.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
  step. (* [comment removed for export] *)
  rewrite (zx16_lit_small len) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hli.
  - cond_cleanup Hli.
    step. (* [comment removed for export] *)
    if_taken.
    eapply nz_exit; eassumption.
  - cond_cleanup Hli.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hge.
    + cond_cleanup Hge. eapply nz_exit; eassumption.
    + cond_cleanup Hge.
      do 10 zstep.
      rewrite !zb_lxor_ones by lia.
      set (i := bv_unsigned a1) in *.
      assert (Ej : ((18446744073709551615 - i + len) mod 18446744073709551616 = len - 1 - i)%Z).
      { replace (18446744073709551615 - i + len)%Z with ((len - 1 - i) + 1 * 18446744073709551616)%Z by lia.
        rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
      rewrite !Ej.
      rewrite <- (Z_to_bv_mod64 (18446744073709551615 - i + len)). change (2 ^ 64)%Z with 18446744073709551616%Z. rewrite Ej.
      rewrite (Z.shiftl_mul_pow2 (len - 1 - i)) by lia. change (2 ^ 3)%Z with 8%Z.
      replace ((len - 1 - i) * 8)%Z with (8 * (len - 1 - i))%Z by lia.
      lazymatch goal with |- context [Z_to_bv 64 (?x + -8)%Z] =>
        replace (Z_to_bv 64 (x + -8)%Z) with (Z_to_bv 64 (bv_unsigned a0 + 8 * (len - 1 - i)))%Z
          by (apply Z_to_bv_eqm; rewrite !Z.shiftl_mul_pow2 by lia; change (2 ^ 3)%Z with 8%Z; Z.div_mod_to_equations; lia)
      end.
      rewrite <- (Z_to_bv_bv_unsigned a1). change (bv_unsigned a1) with i.
      eapply (nz_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ws len LIMBS L62 Hlen Bl (Z.to_nat (len - i))); lia.
Qed.
End U_nonzero.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_hi64_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64.U_nonzero_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64.U_nonzero OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac forget_vals :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 ?e)] =>
        lazymatch e with
        | Z.add (bv_unsigned _) _ => fail
        | bv_unsigned _ => fail
        | _ => lazymatch e with context [bv_unsigned _] =>
                 let w := fresh "v" in let Ew := fresh "Ev" in remember (Z_to_bv 64 e) as w eqn:Ew in |- *; clear Ew
               end
        end
      end
  end.

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Lemma v_sltu_range : forall a b, (0 <= bv_unsigned (v_sltu a b) <= 1)%Z.
Proof. intros. unfold v_sltu. destruct (c_ltu a b); rewrite unsigned_lit by lia; lia. Qed.

Lemma lor_bit_range : forall x y, (0 <= x <= 1)%Z -> (0 <= y <= 1)%Z -> (0 <= Z.lor x y <= 1)%Z.
Proof.
  intros x y Hx Hy.
  destruct (Z.eq_dec x 0) as [->|X1]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec y 0) as [->|Y1]; [rewrite Z.lor_0_r; lia|].
  assert (x = 1)%Z by lia. assert (y = 1)%Z by lia. subst x y. rewrite Z.lor_diag. lia.
Qed.

Lemma unsigned_byte_lit : forall t, (0 <= t < 256)%Z -> bv_unsigned (Z_to_bv 8 t) = t.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Section Tail.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte)
            (ws : list word) (len : Z) (tb : byte).
  Hypothesis LIMBS : u64arr USEGS m0 (bv_unsigned a0) ws.
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LENC : rw_cells USEGS m0 (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)].
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis TB : rw_cells USEGS m0 (bv_unsigned a1) [C1 tb].
  Hypothesis ST : stk USEGS m0 (bv_unsigned sp + -32) (bv_unsigned sp + -32).
  Hypothesis FR : rw_cells USEGS m0 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis MU : munch [((bv_unsigned sp + -32)%Z, bv_unsigned sp); (bv_unsigned a1, (bv_unsigned a1 + 1)%Z)] m m0.
  Hypothesis WM : wmono USEGS m m0.
  Hypothesis SPLO : (139264 <= bv_unsigned sp + -32)%Z.
  Hypothesis SEPA : (bv_unsigned a0 + 498 <= bv_unsigned sp + -32 \/ bv_unsigned sp <= bv_unsigned a0)%Z.
  Hypothesis SEPT : (bv_unsigned a1 + 1 <= bv_unsigned sp + -32 \/ bv_unsigned sp <= bv_unsigned a1)%Z.
  Hypothesis SEPTA : (bv_unsigned a1 + 1 <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned a1)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis Bl : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.
  Hypothesis Bt : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + 1 <= 2 ^ 64)%Z.
  Hypothesis TROD : (bv_unsigned a1 + 1 <= 65536 \/ 139264 <= bv_unsigned a1)%Z.

  Notation POST := (hi64_post ra sp gp tp t1 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).

  (* [comment removed for export] *)
  #[using="ws len tb LIMBS L62 LENC Hlen TB ST FR MU WM SPLO SEPA SEPT SEPTA Bl Bt"] Lemma uhi_tail : forall (r x a2 a3 a4 a5 a6 a7 : word),
    evt USEGS POST (MS (mkR ra SP' gp tp t0 t1 t2 a1 r a0 x a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x26fa8) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (ws len tb LIMBS L62 LENC Hlen TB ST FR MU WM SPLO SEPA SEPT SEPTA Bl Bt : LiaFast.U) => LiaFast.u0).
    intros.
    step. (* [comment removed for export] *)
    pose proof (v_sltu_range (Z_to_bv 64 0) x) as Ht1.
    remember (v_sltu (Z_to_bv 64 0) x) as c1 eqn:Ec1; clear Ec1.
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call nonzero_spec.
    all: try eassumption.
    step. (* [comment removed for export] *)
    unfold zxb. rewrite (unsigned_byte_lit (bv_unsigned c1)) by lia.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?u ?v)] =>
      assert (Ht : (0 <= Z.lor u v <= 1)%Z) by (apply lor_bit_range; rewrite ?unsigned_lit by lia; lia);
      remember (Z.lor u v) as t eqn:Et; clear Et end.
    step. (* [comment removed for export] *)
    rewrite unsigned_lit in TB by lia.
    step. (* [comment removed for export] *)
    do 6 step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    finish. all: first [exact TB | idtac]. all: rewrite ?unsigned_lit by lia; lia.
  Qed.
End Tail.

Lemma hi64_spec : hi64_stmt.
Proof.
  unfold hi64_stmt. intros until tb. intros LIMBS L62 LENC Hlen NORM TB ST PR SPLO SEPA SEPT SEPTA.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 1)]%Z m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
  pose proof (rw_cells_bound _ _ _ _ TB) as Bt. cbn [cells_size csize Nat.add] in Bt.
  pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
  pose proof (rw_cells_outside_rodata_U m _ _ PR TB ltac:(cbn; lia)) as TROD. cbn [cells_size csize Nat.add] in TROD.
  carve_frame 32%nat ST.
  do 5 step. (* [comment removed for export] *)
  name_mem m0.
  step. (* [comment removed for export] *)
  rewrite (zx16_lit_small len) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases H1.
  - cond_cleanup H1. subst len.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *)
    destruct (nth_error ws 0) as [w|] eqn:Hw. 2:{ apply nth_error_None in Hw. lia. }
    pose proof (u64arr_read USEGS m0 (bv_unsigned a0) ws 0 w _ LIMBS Hw ltac:(lia) eq_refl) as RD.
    assert (WNZ : bv_unsigned w <> 0%Z).
    { pose proof (bnorm_top ws 1 ltac:(lia) NORM) as T. unfold limbZ in T. cbn [Nat.sub] in T.
      rewrite (nth_error_nth _ _ _ Hw) in T. exact T. }
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_not_taken.
    do 33 (step; forget_vals).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. do 6 step.
    release_frame FR ST (bv_unsigned sp).
    finish. all: first [exact TB | idtac]. all: rewrite ?unsigned_lit by lia; lia.
  - cond_cleanup H1.
    step. (* [comment removed for export] *)
    if_cases H0.
    + cond_cleanup H0.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      step. (* [comment removed for export] *) if_not_taken.
      zstep. (* [comment removed for export] *)
      replace (bv_unsigned a0 + (len + -1) * 8)%Z with (bv_unsigned a0 + 8 * (len - 1))%Z by lia.
      destruct (nth_error ws (Z.to_nat (len - 1))) as [top|] eqn:Htop.
      2:{ apply nth_error_None in Htop. lia. }
      pose proof (u64arr_read USEGS m0 (bv_unsigned a0) ws (len - 1) top _ LIMBS Htop ltac:(lia) eq_refl) as RD.
      assert (TOPNZ : bv_unsigned top <> 0%Z).
      { pose proof (bnorm_top ws (Z.to_nat len) ltac:(lia) NORM) as T. unfold limbZ in T.
        replace (Z.to_nat len - 1)%nat with (Z.to_nat (len - 1)) in T by lia.
        rewrite (nth_error_nth _ _ _ Htop) in T. exact T. }
      step. (* [comment removed for export] *) clear RD.
      step. (* [comment removed for export] *) if_not_taken.
      do 30 (step; forget_vals).
      zstep. (* [comment removed for export] *)
      destruct (nth_error ws (Z.to_nat (len - 2))) as [nxt|] eqn:Hnxt.
      2:{ apply nth_error_None in Hnxt. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (u64arr_read USEGS mc (bv_unsigned a0) ws (len - 2) nxt _ LIMBS Hnxt ltac:(lia) eq_refl) as RD end.
      step. (* [comment removed for export] *) clear RD.
      step; forget_vals. step; forget_vals. step; forget_vals. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsh.
      * eapply uhi_tail; try eassumption; lia.
      * do 6 (step; forget_vals).
        eapply uhi_tail; try eassumption; lia.
    + cond_cleanup H0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. do 6 step.
      release_frame FR ST (bv_unsigned sp).
      finish. all: first [exact TB | idtac]. all: rewrite ?unsigned_lit by lia; lia.
Qed.
