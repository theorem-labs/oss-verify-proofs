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
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_small_mul_stmt.
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
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word).
  Variables (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z) (j8 : list byte).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z.
  Hypothesis SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z.
  Hypothesis RO3 : (IMG_END <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z.
  Hypothesis KA1 : (bv_unsigned vec + 504 <= KTOP)%Z.

  Notation A := (bv_unsigned vec).
  Notation y := (bv_unsigned yw).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation A5 := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation POST := (small_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A y ws len m0).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p sh cnt x14 x29 x30 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned sh = (ASAN_B + A / 8 + Z.of_nat i)%Z ->
      bv_unsigned cnt = (len - Z.of_nat i)%Z ->
      u64arr ASEGS m A cur -> length cur = 62%nat ->
      rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      smul_inv ws cur y i c ->
      munch (small_mul_W A sp) m0 m -> wmono ASEGS m0 m ->
      rw_cells ASEGS m (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
      stk ASEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16) ->
      shz ASEGS m (ASAN_B + A / 8) 63 ->
      evt ASEGS POST
        (MS (mkR ra SP' gp tp (Z_to_bv 64 c) sh p s0 s1 (Z_to_bv 64 (A + 496)) yw vec (Z_to_bv 64 1) x14 A5 BB (Z_to_bv 64 len)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cnt x29 x30 t6)
            F (Z_to_bv 64 0x96324) fc None m (seg_rom ASEGS)).

  #[using="Hlen LEN CAP SEP KSP KSP2 KA0 KA1"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p sh cnt x14 x29 x30 c cur m Hk Hi Hp Hsh Hcnt CUR Hcur LC INV MU WM FR ST SHZ.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    cbv delta [small_mul_W] in MU.
    pose proof (bv_unsigned_in_range 64 yw) as Ry. unfold bv_modulus in Ry.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read ASEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write ASEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    rewrite (smul_carry_word (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite Hlen; lia |].
      unfold limbZ. rewrite <- Hw. apply smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 (bv_unsigned sh + 1)) (Z_to_bv 64 (bv_unsigned cnt + -1)));
        try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      pose proof (proj1 (proj2 (proj2 INV'))) as Hc'. cbn beta in Hc'.
      remember (mul_cout (limbZ ws i) y c) as c' eqn:Ec'.
      step. (* [comment removed for export] *)
      if_cases Hz.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold small_mul_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        * rewrite <- Hil. rewrite (Z.mul_comm (bval ws _) y). apply (smul_inv_finish_nocarry ws _ y (S i)). rewrite <- Hz. exact INV'.
        * intros Hy BN. rewrite <- Hil in BN |- *. right. cbn [Nat.sub]. rewrite Nat.sub_0_r.
          unfold limbZ. rewrite nth_upd_same by (rewrite Hcur; lia).
          rewrite (smul_lo_word (bv_unsigned w) y c) by lia.
          unfold limbZ in Ec'. rewrite <- Hw in Ec'.
          apply smul_top_nonzero; try lia.
          destruct BN as [BN|BN]; [lia|]. cbn [Nat.sub] in BN. rewrite Nat.sub_0_r in BN. unfold limbZ in BN. rewrite <- Hw in BN. lia.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        pose proof (smul_carry_room ws _ y _ _ INV' ltac:(lia) ltac:(rewrite Hil; lia)) as ROOM.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit len) by lia. rewrite Z.shiftl_mul_pow2 by lia.
        replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (u64arr_store_ok ASEGS m1 A _ len (Z_to_bv 64 (A + 8 * len)) CUR' ltac:(rewrite upd_length; lia) eq_refl) as SOK2.
        step. (* [comment removed for export] *)
        pose proof (u64arr_write ASEGS m1 A _ len (Z_to_bv 64 c') CUR' ltac:(rewrite upd_length; lia)) as CUR''.
        store_done.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold small_mul_post. finish.
        { exact CUR''. } { rewrite !upd_length. exact Hcur. } { exact LC. } all: try lia.
        * replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. replace (Z.to_nat len) with (S i) by lia.
          rewrite (Z.mul_comm (bval ws _) y). subst c'. apply (smul_inv_finish_carry ws _ y (S i)); [exact INV'| rewrite Hlen; lia].
        * intros Hy BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          apply bnorm_push; [rewrite upd_length, Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
          (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z) (j8 : list byte)
          (Hlen : length ws = 62%nat) (LEN : (0 < len <= 62)%Z)
          (CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z)
          (SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z)
          (RO3 : (IMG_END <= bv_unsigned sp + -16)%Z)
          (KSP : (KHI <= bv_unsigned sp + -16)%Z)
          (KSP2 : (bv_unsigned sp <= KTOP)%Z)
          (KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z)
          (KA1 : (bv_unsigned vec + 504 <= KTOP)%Z).
  #[using="Hlen LEN CAP SEP KSP KSP2 KA0 KA1"] Lemma sm_loop : forall k, loop_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 vec yw F fc m0 ws len j8 k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH].
    - unfold loop_ok. intros. exfalso. lia.
    - apply loop_body; assumption.
  Qed.
End Loop2.

Lemma small_mul_spec : small_mul_stmt.
Proof.
  unfold small_mul_stmt. intros until len. intros LIMBS Hlen LC LEN CAP ST PRG BC SEP RO3 KSP KSP2 KA0 KA1 SHZ.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
  pose proof (munch_refl (small_mul_W (bv_unsigned a0) sp) m) as MU. cbv delta [small_mul_W] in MU.
  pose proof (wmono_refl ASEGS m) as WM.
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
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hz.
  - (* [comment removed for export] *)
    cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold small_mul_post. finish.
    { exact LIMBS. } { exact Hlen. } { exact LC. } all: try lia.
    + subst len. change (Z.to_nat 0) with 0%nat. rewrite bval_0. lia.
    + intros _ BN. exact BN.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply sm_loop with (k := Z.to_nat len) (i := 0%nat); try eassumption; try lia.
    + rewrite unsigned_lit by lia. lia.
    + rewrite unsigned_lit by lia. lia.
    + apply smul_inv_init.
Qed.
