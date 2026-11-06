(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 121 of its 142 lines of code are new or changed and 123 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_agree
  codec_main_inv codec_main_oweb_lib LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** 0x146c0 addi a2, zero, -1; sllw a1, a2, a1; not a1, a1: the mask (1 << b) - 1 for b <= 14. *)
Lemma meter_mask : forall b, 0 <= b <= 14 ->
  Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (b mod 32)) mod 18446744073709551616) 18446744073709551615 =
  (2 ^ b - 1) mod 2 ^ 32.
Proof.
  intros b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/
              b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; reflexivity |]). subst b. vm_compute. reflexivity.
Qed.

(** 0x146f4 snez a1, a2; slli a1, a1, 5; or a0, a1, a0: the channel a | (c ? 0x20 : 0). *)
Lemma meter_ch : forall a c, 0 <= c < 2 ^ 32 ->
  Z.lor (Z.shiftl (Z.b2z (0 <? bv_unsigned (sx32 (Z_to_bv 64 c)))) 5 mod 18446744073709551616) a =
  Z.lor a (bit_or_0 (negb (c =? 0)) 0x20).
Proof.
  intros a c Hc. rewrite sx32_u by lia.
  assert (Ec : (0 <? (if c <? 2 ^ 31 then c else c + (2 ^ 64 - 2 ^ 32))) = negb (c =? 0)).
  { destruct (Z.ltb_spec c (2 ^ 31)); destruct (Z.eqb_spec c 0); cbn [negb];
      first [ apply Z.ltb_ge; lia | apply Z.ltb_lt; lia ]. }
  rewrite Ec. rewrite Z.lor_comm. destruct (c =? 0); reflexivity.
Qed.

Lemma meter_key : forall x, 0 <= x < 64 -> Z.lor x 262144 = KEY 4 (u8 x).
Proof.
  intros x Hx. unfold KEY, u8. rewrite (Z.mod_small x 256) by lia.
  change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. rewrite (Z.mod_small x (2 ^ 16)) by lia.
  rewrite Z.lor_comm. reflexivity.
Qed.

(** owe()'s METER case (fuzz_codec.c:189-197). *)
Lemma owe6_rng : forall d a b c delta bytes n, 0x20 <= a \/ 14 < b ->
  fst (owe_spec 6 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
  destruct (Z.leb_spec 0x20 a); destruct (Z.ltb_spec 14 b); try reflexivity; lia.
Qed.

Lemma owe6_ok : forall d a b c delta bytes n, a < 0x20 -> b <= 14 ->
  owe_spec 6 (Some d) a b c delta bytes n =
  (0, (fst (owe_sx (d_dev d) 0x10 [u8 (Z.lor a (bit_or_0 (negb (c =? 0)) 0x20));
                                    u8 (Z.shiftr ((2 ^ b - 1) mod 2 ^ 32) 7);
                                    u8 (Z.land ((2 ^ b - 1) mod 2 ^ 32) 0x7f)]),
       KEY 4 (u8 (Z.lor a (bit_or_0 (negb (c =? 0)) 0x20))), 0)).
Proof.
  intros d a b c delta bytes n Ha Hb. unfold owe_spec. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
  replace (0x20 <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (14 <? b) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(** 0x146a8 lw a0, a; bltu 0x1f, a0 -> E_RANGE; lw a1, b; bltu 14, a1 -> E_RANGE; mask = ~(-1 << b);
    ch = a | (c ? 0x20 : 0); want = F0 13 dev 10 ch mask>>7 mask&0x7f F7, want_len = 8, want_key = 0x40000|ch,
    want_display = 0; j CHK. *)
Lemma codec_main_owe6 : S_owe6.
Proof.
  unfold S_owe6, owe_ok, st, body_regs.
  intros e fuel HE CHK ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HRC HK HOD HRCk HWR HWL HWK HWD HC FR HFR.
  replace (owe_pc 6) with 0x146a8 by reflexivity.
  pose proof HRC as (_ & HPD & HRD & _ & _).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _ & _ & HPB & _ & HDJ). unfold LLVM_CODEC_STACK in HLO.
  pose proof HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  pose proof (relro_of_fr e m1 HE HFR) as HRI.
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & _ & _ & _).
  destruct od as [d|]; [| exfalso; destruct (HOD eq_refl) as [X | [X | X]]; discriminate X].
  destruct (desk_ro m1 (k_p k) (k_desk k) d HRI HPD) as (Hd & Dr & Hdv & np & pad & DK).
  pose proof Dr as (Ddev & Dstr & Dch & Dctr).
  unfold desk_cells in DK.
  unfold disj, RELRO_BASE, RELRO_LEN in HDJ.
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep. zstep. zstep.
  if_cases E1.
  - (* a > 0x1f *)
    zify_cond E1.
    assert (Ha : 0x20 <= k_a k) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
    zstep.
    assert (FB : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FR.
    eapply (owe_err_tail e fuel HE CHK) with (rc := E_RANGE);
      [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FB | exact HFR ].
    + unfold owe_k. rewrite HK. apply owe6_rng. lia.
    + unfold E_RANGE. lia.
    + first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
  - zify_cond E1.
    assert (Ha : k_a k <= 0x1f) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
    rewrite (sx32_small (k_a k)) by lia.
    zstep. zstep. zstep.
    if_cases E2.
    + (* b > 14 *)
      zify_cond E2.
      assert (Hb : 14 < k_b k) by (rewrite sx32_u in E2 by lia; destruct (Z.ltb_spec (k_b k) (2 ^ 31)); lia).
      zstep.
      assert (FB : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FR.
      eapply (owe_err_tail e fuel HE CHK) with (rc := E_RANGE);
        [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FB | exact HFR ].
      * unfold owe_k. rewrite HK. apply owe6_rng. lia.
      * unfold E_RANGE. lia.
      * first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
    + zify_cond E2.
      assert (Hb : k_b k <= 14) by (rewrite sx32_u in E2 by lia; destruct (Z.ltb_spec (k_b k) (2 ^ 31)); lia).
      rewrite (sx32_small (k_b k)) by lia.
      zstep. zstep. zstep. zstep. cbv beta. rewrite (u8_unsigned (d_dev d)) by lia.
      do 23 zstep.
      match goal with H : rw_cells rsegs ?mm (bv_unsigned (e_sp e) + -400) _ |- _ =>
        pose proof (rw_cells_merge_at mm _ _ 16 8 H) as FM; clear H end.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in FM.
      rewrite HWR in FM.
      rewrite (meter_ch (k_a k) (k_c k)) in FM by lia.
      rewrite (meter_mask (k_b k)) in FM by lia.
      set (CH := Z.lor (k_a k) (bit_or_0 (negb (k_c k =? 0)) 0x20)) in FM.
      assert (CHr : 0 <= CH < 64).
      { unfold CH. change 64 with (2 ^ 6). apply lor_lt_pow2; [change (2 ^ 6) with 64; lia |].
        destruct (negb (k_c k =? 0)); cbn [bit_or_0]; change (2 ^ 6) with 64; lia. }
      rewrite (meter_key CH) in FM by exact CHr.
      match type of FM with context [CB 24 ?W :: C8 (Z_to_bv 64 8) :: _] => set (Wv := W) in FM end.
      set (MK := (2 ^ k_b k - 1) mod 2 ^ 32) in *.
      set (BS := fst (owe_sx (d_dev d) 0x10 [u8 CH; u8 (Z.shiftr MK 7); u8 (Z.land MK 0x7f)])).
      assert (FR' : rw_cells rsegs m0 (bv_unsigned (e_sp e) + -400)
                      (body_cells e (set_owe k 0 Wv (Z.of_nat (length BS)) (KEY 4 (u8 CH)) 0) c rem tl))
        by exact FM.
      eapply (owe_ok_tail e fuel CHK) with (bs := BS) (key := KEY 4 (u8 CH)) (dp := 0);
        [ exact HF | exact HRC | exact HRCk | | | exact HC | exact FR' | ].
      * unfold owe_k. rewrite HK. apply owe6_ok; lia.
      * unfold Wv, BS, owe_sx. cbn [fst length app].
        replace (le2 (Z_to_bv 64 5104)) with [b8 0xf0; b8 0x13]
          by (apply bytes_eq_of_unsigned; vm_compute; reflexivity).
        cbn [firstn app bz map]. rewrite !b8_lit, !b8_u8.
        replace (b8 (-9)) with (b8 0xf7) by (apply bv_eq; vm_compute; reflexivity). reflexivity.
      * split; [eassumption|]. split; [eassumption|]. split; [unfold LLVM_CODEC_STACK; eassumption|].
        split; eassumption.
Qed.
