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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_shl_bits_stmt.
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
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 <= len <= 62)%Z.
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
  Notation A4 := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation POST := (shl_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A r ws len m0).

  (* [comment removed for export] *)
  #[using="Hlen LEN Hn SEP KSP KSP2 KA0 KA1"] Lemma sb_tail : forall (prev x5 x6 x7 x8 x11 x13 x28 x29 x30 : word) (cur : list word) (m : word -> option byte),
    u64arr BSEGS m A cur -> length cur = 62%nat ->
    rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
    shl_inv ws cur r (Z.to_nat len) (bv_unsigned prev) ->
    ((0 < len)%Z -> prev = nth (Z.to_nat len - 1) ws w0) ->
    munch (shl_bits_W A sp) m0 m -> wmono BSEGS m0 m ->
    rw_cells BSEGS m (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    stk BSEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16) ->
    shz BSEGS m (ASAN_B + A / 8) 63 ->
    evt BSEGS POST
      (MS (mkR ra SP' gp tp x5 x6 x7 x8 s1 (Z_to_bv 64 (A + 496)) x11 vec x13 A4 BB (Z_to_bv 64 len) (Z_to_bv 64 (64 - r))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 prev)
          F (Z_to_bv 64 0x98684) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    intros prev x5 x6 x7 x8 x11 x13 x28 x29 x30 cur m CUR Hcur LC INV PREV MU WM FR ST SHZ.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 prev) as Rp. unfold bv_modulus in Rp.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    cbv delta [shl_bits_W] in MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (64 - r)) by lia. rewrite (Z.mod_small (64 - r) 64) by lia.
    pose proof (shr_small (bv_unsigned prev) r Rp Hn) as Rc.
    assert (R2r : (2 ^ r <= 2 ^ 63)%Z) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.shiftr_div_pow2 by lia.
    remember (bv_unsigned prev / 2 ^ (64 - r))%Z as c eqn:Ec.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hcz.
    - cond_cleanup Hcz.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      unfold shl_bits_post. finish.
      { exact CUR. } { exact Hcur. } { exact LC. } all: try lia.
      intros _. split; [| split; [lia|]].
      + apply (shl_inv_finish_nocarry ws _ r _ (bv_unsigned prev)); [exact INV| lia].
      + intros BN.
        destruct (Nat.eq_dec (Z.to_nat len) 0) as [E0|NE]. { left; exact E0. }
        apply bnorm_of_value; [lia|].
        pose proof (bnorm_lower ws (Z.to_nat len) BN ltac:(lia)) as LO.
        rewrite (shl_inv_finish_nocarry ws _ r _ _ INV) by lia.
        assert (1 <= 2 ^ r)%Z by (pose proof (Z.pow_le_mono_r 2 0 r); lia).
        pose proof (bval_nonneg ws (Z.to_nat len)). nia.
    - cond_cleanup Hcz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hroom.
      + cond_cleanup Hroom.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold shl_bits_post. finish.
        { exact CUR. } { exact Hcur. } { exact LC. } all: try lia.
        intros CAP. exfalso.
        pose proof (shl_carry_room ws _ r (Z.to_nat len) (bv_unsigned prev) INV Hn ltac:(lia) CAP) as ROOM. lia.
      + cond_cleanup Hroom.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Ht; [ cond_cleanup Ht; rewrite ?zb_lxor_ones in Ht by lia; rewrite ?unsigned_lit in Ht by lia; exfalso; lia | clear Ht ].
        zstep. (* [comment removed for export] *)
        replace (A + len * 8)%Z with (A + 8 * len)%Z by lia.
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (u64arr_store_ok BSEGS m A _ len (Z_to_bv 64 (A + 8 * len)) CUR ltac:(rewrite Hcur; lia) eq_refl) as SOK.
        step. (* [comment removed for export] *)
        pose proof (u64arr_write BSEGS m A _ len (Z_to_bv 64 c) CUR ltac:(rewrite Hcur; lia)) as CUR'.
        store_done.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold shl_bits_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        intros _. split; [| split; [lia|]].
        * replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. subst c.
          apply (shl_inv_finish_carry ws _ r _ (bv_unsigned prev)); [exact INV| rewrite Hlen; lia | exact Hn].
        * intros BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          apply bnorm_push; [rewrite Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (cnt rem : Z) (p q prev x8 x31 : word) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      (cnt = 63 - Z.of_nat i)%Z -> (rem = len - Z.of_nat i)%Z ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned q = (A + 8 * Z.of_nat i)%Z ->
      u64arr BSEGS m A cur -> length cur = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      shl_inv ws cur r i (bv_unsigned prev) ->
      (i <> 0%nat -> prev = nth (i - 1) ws w0) ->
      munch (shl_bits_W A sp) m0 m -> wmono BSEGS m0 m ->
      rw_cells BSEGS m (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      stk BSEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16) ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      evt BSEGS POST
        (MS (mkR ra SP' gp tp (Z_to_bv 64 (Z.lor (64 - r) r)) (Z_to_bv 64 cnt) (Z_to_bv 64 64) x8 s1
                 (Z_to_bv 64 (A + 496)) nw vec q A4 BB (Z_to_bv 64 len) (Z_to_bv 64 (64 - r))
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rem) p prev x31)
            F (Z_to_bv 64 0x98638) fc None m (seg_rom BSEGS)).

  #[using="Hlen LEN Hn SEP KSP KSP2 KA0 KA1"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i cnt rem p q prev x8 x31 cur m Hk Hi Hcnt Hrem Hp Hq CUR Hcur LC INV PREV MU WM FR ST SHZ. subst cnt rem.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    cbv delta [shl_bits_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (bv_unsigned_in_range 64 prev) as Rp. unfold bv_modulus in Rp.
    pose proof (lor_lt_64 (64 - r) r ltac:(lia) ltac:(lia)) as Hlor.
    destruct INV as (Hv & Hag & Hpr & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hnw. 2:{ exfalso. apply nth_error_None in Hnw. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hnw. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *) shr3. rewrite Hq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read BSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hnw) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (64 - r)) by lia.
    rewrite ?(Z.mod_small (64 - r) 64) by lia. rewrite ?(Z.mod_small r 64) by lia.
    rewrite (shlb_limb_word (bv_unsigned w) (bv_unsigned prev) r) by lia.
    pose proof (shlb_limb_range (bv_unsigned w) (bv_unsigned prev) r Rw Rp Hn) as Rz.
    pose proof (u64arr_store_ok BSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write BSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (INV' : shl_inv ws (upd cur i (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r))) r (S i) (bv_unsigned w)).
    { replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply (shl_inv_step ws _ r i (bv_unsigned prev)); [split; [exact Hv| split; [exact Hag| split; [exact Hpr| exact Hlc]]] | rewrite Hlen; lia | exact Hn |].
      rewrite unsigned_lit by (unfold limbZ; rewrite <- Hw; lia). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      eapply sb_tail; try eassumption.
      all: first [ rewrite upd_length; exact Hcur
                 | rewrite <- Hil; exact INV'
                 | intros _; rewrite <- Hil; replace (S i - 1)%nat with i by lia; exact Hw
                 | cbv delta [shl_bits_W]; exact MU ].
    - cond_cleanup Hb.
      step. (* [comment removed for export] *)
      eapply (IH (S i) _ _ (Z_to_bv 64 (bv_unsigned p + 8)) _ w); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
      + intros _. rewrite Hw. f_equal. lia.
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
          (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z)
          (Hlen : length ws = 62%nat) (LEN : (0 <= len <= 62)%Z) (Hn : (1 <= bv_unsigned nw <= 63)%Z)
          (SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z)
          (KSP : (KHI <= bv_unsigned sp + -16)%Z)
          (KSP2 : (bv_unsigned sp <= KTOP)%Z)
          (KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z)
          (KA1 : (bv_unsigned vec + 504 <= KTOP)%Z).
  #[using="Hlen LEN Hn SEP KSP KSP2 KA0 KA1"] Lemma sb_loop : forall k, loop_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 vec nw F fc m0 ws len k.
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
  pose proof (wmono_refl BSEGS m) as WM.
  carve_frame 16%nat ST.
  step. (* [comment removed for export] *)
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
  step. (* [comment removed for export] *)
  if_cases Hz.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    eapply (sb_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m ws len L62 ltac:(lia) Hn SEP KSP KSP2 KA0 KA1
              (Z_to_bv 64 0)); try eassumption; try lia.
    all: first [ rewrite Hz; rewrite unsigned_lit by lia; apply shl_inv_init; exact Hn | intros H; exfalso; lia ].
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (64 - bv_unsigned a1)) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (sb_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m ws len
              L62 ltac:(lia) Hn SEP KSP KSP2 KA0 KA1 (Z.to_nat len) 0%nat 63%Z len a0 a0 (Z_to_bv 64 0)); try eassumption; try lia.
    all: try (rewrite unsigned_lit by lia; apply shl_inv_init; exact Hn).
Qed.
