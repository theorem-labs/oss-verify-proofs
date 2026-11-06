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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_shl_bits_stmt.
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
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z) (j8 : list byte).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hn : (1 <= bv_unsigned nw <= 63)%Z.
  Hypothesis SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z.
  Hypothesis KA1 : (bv_unsigned vec + 504 <= KTOP)%Z.

  Notation A := (bv_unsigned vec).
  Notation r := (bv_unsigned nw).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation A5 := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation POST := (shl_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A r ws len m0).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p prev sh cnt x14 x30 x31 : word) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned sh = (ASAN_B + A / 8 + Z.of_nat i)%Z ->
      bv_unsigned cnt = (len - Z.of_nat i)%Z ->
      u64arr ASEGS m A cur -> length cur = 62%nat ->
      rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      shl_inv ws cur r i (bv_unsigned prev) ->
      (i <> 0%nat -> prev = nth (i - 1) ws w0) ->
      munch (shl_bits_W A sp) m0 m -> wmono ASEGS m0 m ->
      rw_cells ASEGS m (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
      stk ASEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16) ->
      shz ASEGS m (ASAN_B + A / 8) 63 ->
      evt ASEGS POST
        (MS (mkR ra SP' gp tp (Z_to_bv 64 (64 - r)) sh p s0 s1 (Z_to_bv 64 (A + 496)) nw vec (Z_to_bv 64 1) x14 A5 BB (Z_to_bv 64 len)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cnt prev x30 x31)
            F (Z_to_bv 64 0x97b08) fc None m (seg_rom ASEGS)).

  #[using="Hlen LEN Hn SEP KSP KSP2 KA0 KA1"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p prev sh cnt x14 x30 x31 cur m Hk Hi Hp Hsh Hcnt CUR Hcur LC INV PREV MU WM FR ST SHZ.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    cbv delta [shl_bits_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (bv_unsigned_in_range 64 prev) as Rp. unfold bv_modulus in Rp.
    destruct INV as (Hv & Hag & Hpr & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hnw. 2:{ exfalso. apply nth_error_None in Hnw. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hnw. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read ASEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hnw) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (64 - r)) by lia.
    rewrite (Z.mod_small (64 - r) 64) by lia. rewrite (Z.mod_small r 64) by lia.
    rewrite (shlb_limb_word (bv_unsigned w) (bv_unsigned prev) r) by lia.
    pose proof (shlb_limb_range (bv_unsigned w) (bv_unsigned prev) r Rw Rp Hn) as Rz.
    pose proof (u64arr_store_ok ASEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write ASEGS m A cur (Z.of_nat i) (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (INV' : shl_inv ws (upd cur i (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r))) r (S i) (bv_unsigned w)).
    { replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply (shl_inv_step ws _ (bv_unsigned nw) i (bv_unsigned prev)); [split; [exact Hv| split; [exact Hag| split; [exact Hpr| exact Hlc]]] | rewrite Hlen; lia | exact Hn |].
      rewrite unsigned_lit by (unfold limbZ; rewrite <- Hw; lia). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) w (Z_to_bv 64 (bv_unsigned sh + 1)) (Z_to_bv 64 (bv_unsigned cnt + -1)));
        try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
      + intros _. rewrite Hw. f_equal. lia.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (64 - r)) by lia. rewrite (Z.mod_small (64 - r) 64) by lia.
      pose proof (shr_small (bv_unsigned w) r Rw Hn) as Rc.
      assert (R2r : (2 ^ r <= 2 ^ 63)%Z) by (apply Z.pow_le_mono_r; lia).
      rewrite Z.shiftr_div_pow2 by lia.
      remember (bv_unsigned w / 2 ^ (64 - r))%Z as c eqn:Ec.
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold shl_bits_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        * intros _. split; [| split; [lia|]].
          -- rewrite <- Hil. apply (shl_inv_finish_nocarry ws _ r (S i) (bv_unsigned w)); [exact INV'| lia].
          -- intros BN. rewrite <- Hil in BN |- *. right. cbn [Nat.sub]. rewrite Nat.sub_0_r.
             unfold limbZ. rewrite nth_upd_same by (rewrite Hcur; lia). rewrite unsigned_lit by lia.
             apply shlb_top_nonzero; try lia.
             destruct BN as [BN|BN]; [lia|]. cbn [Nat.sub] in BN. rewrite Nat.sub_0_r in BN. unfold limbZ in BN. rewrite <- Hw in BN. lia.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hroom.
        * (* [comment removed for export] *)
          cond_cleanup Hroom.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          release_frame FR ST (bv_unsigned sp).
          unfold shl_bits_post. finish.
          { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
          intros CAP. exfalso.
          pose proof (shl_carry_room ws _ r (S i) (bv_unsigned w) INV' Hn ltac:(lia)) as ROOM. rewrite Hil in ROOM. lia.
        * cond_cleanup Hroom.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          rewrite (unsigned_lit len) by lia. rewrite (Z.shiftl_mul_pow2 len 3) by lia.
          replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
          step. (* [comment removed for export] *) shr3.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose proof (u64arr_store_ok ASEGS m1 A _ len (Z_to_bv 64 (A + 8 * len)) CUR' ltac:(rewrite upd_length; lia) eq_refl) as SOK2.
          step. (* [comment removed for export] *)
          pose proof (u64arr_write ASEGS m1 A _ len (Z_to_bv 64 c) CUR' ltac:(rewrite upd_length; lia)) as CUR''.
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
          unfold shl_bits_post. finish.
          { exact CUR''. } { rewrite !upd_length. exact Hcur. } { exact LC. } all: try lia.
          intros _. split; [| split; [lia|]].
          -- replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. rewrite <- Hil. subst c.
             apply (shl_inv_finish_carry ws _ r (S i) (bv_unsigned w)); [exact INV'| rewrite Hlen; lia | exact Hn].
          -- intros BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
             apply bnorm_push; [rewrite upd_length, Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
          (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z) (j8 : list byte)
          (Hlen : length ws = 62%nat) (LEN : (0 < len <= 62)%Z) (Hn : (1 <= bv_unsigned nw <= 63)%Z)
          (SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z)
          (KSP : (KHI <= bv_unsigned sp + -16)%Z)
          (KSP2 : (bv_unsigned sp <= KTOP)%Z)
          (KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z)
          (KA1 : (bv_unsigned vec + 504 <= KTOP)%Z).
  #[using="Hlen LEN Hn SEP KSP KSP2 KA0 KA1"] Lemma sb_loop : forall k, loop_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 vec nw F fc m0 ws len j8 k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH].
    - unfold loop_ok. intros. exfalso. lia.
    - apply loop_body; assumption.
  Qed.
End Loop2.

Lemma shl_bits_spec : shl_bits_stmt.
Proof.
  unfold shl_bits_stmt. intros until len. intros LIMBS L62 LENC Hlen Hn ST PRG BC SEP RO3 KSP KSP2 KA0 KA1 SHZ.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite L62 in Bd.
  pose proof (munch_refl (shl_bits_W (bv_unsigned a0) sp) m) as MU. cbv delta [shl_bits_W] in MU.
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
  rewrite zx16_lit_small by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hz.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold shl_bits_post. finish.
    { exact LIMBS. } { exact L62. } { exact LENC. } all: try lia.
    intros _. subst len. change (Z.to_nat 0) with 0%nat. rewrite !bval_0. split; [lia| split; [lia| intros B; exact B]].
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply sb_loop with (k := Z.to_nat len) (i := 0%nat); try eassumption; try lia.
    all: try (rewrite unsigned_lit by lia; lia).
    + rewrite unsigned_lit by lia. apply shl_inv_init. exact Hn.
Qed.
