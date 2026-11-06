(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the control path from 0x1402c (status neither 0x9x nor
   0xF0): a status other than 0xBx (kind 13), the jog (d1 = 0x5C), the V-Pots (0x40 <= d1 < 0x58), any
   other controller (kind 13), and the faders (d1 < 0x20, diginet_decoder_next_fader.v)
   (diginet_decode.c:127-157).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_msg_next_c diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib
  diginet_decoder_next_fader.
Import ListNotations.
Open Scope Z_scope.

Lemma s16_small : forall x, -32768 <= x < 32768 -> s16 x = x.
Proof. intros x Hx. unfold s16. rewrite Z.mod_small by lia. lia. Qed.

(* addi -0x40 / andi 0xff / bltu 0x17: d1 is not a V-Pot controller *)
Lemma dn_vpot_cond : forall x, 0 <= x < 256 ->
  bv_ltu (Z_to_bv 64 23) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (x + -64))) 255)) =
  negb ((64 <=? x) && (x <? 88)).
Proof.
  intros x Hx. apply Bool.eqb_prop. revert x Hx.
  apply (byte_forall (fun x => Bool.eqb (bv_ltu (Z_to_bv 64 23)
                                           (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (x + -64))) 255)))
                                        (negb ((64 <=? x) && (x <? 88))))).
  vm_compute. reflexivity.
Qed.

Section Ctl.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_ctl : diginet_msg_next_contract ->
  forall (ra' t0 t1 t2 s1' a1 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 : word) (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra (dn_e0 msg) ->
  Z.land (dm_status msg) 240 <> 144 -> dm_status msg <> 240 ->
  0 <= dm_d1 msg < 128 -> 0 <= dm_d2 msg < 128 -> (pos1 <= length bb)%nat -> st_ok st1 ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) s1'
             (Z_to_bv 64 (Z.land (dm_status msg) 240)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 d) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1402c) fc None m1 (seg_rom rsegs)).
Proof.
  intros MN ra' t0 t1 t2 s1' a1 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 m1 HCTX HAT N90 NF0 R1 R2 HPOS1 HST1.
  pose proof HCTX as HCTX0. pose proof HAT as HAT0. dn_ctx_open HCTX. dn_open HAT.
  pose proof (byte_land_le (dm_status msg) 240 RST ltac:(lia)) as RL.
  (* a1 = 0xb0; s1 = 1; bne a0, a1 *)
  step. step. step.
  rewrite (dn_eqb_u64 (Z.land (dm_status msg) 240) 176) by lia.
  destruct (Z.eq_dec (Z.land (dm_status msg) 240) 176) as [CB0|CB0].
  2: {
    (* not a control change: kind 13 *)
    if_true.
    assert (HR : res = (1, dn_e0 msg, {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
    { rewrite HRES. unfold dn_tail.
      rewrite (proj2 (Z.eqb_neq _ _) N90), (proj2 (Z.eqb_neq _ _) NF0), (proj2 (Z.eqb_neq _ _) CB0).
      reflexivity. }
    dn_fin HR HDc HD2 HE HEM.
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  if_false.
  (* lbu d1; bltu 0x1f, d1 *)
  step.
  rewrite (dn_zxb_b8 (dm_d1 msg)) by lia.
  step. step.
  rewrite (ltu_lit 31 (dm_d1 msg)) by lia.
  destruct (Z.ltb_spec 31 (dm_d1 msg)) as [D1|D1].
  2: {
    (* a fader *)
    eapply dn_fader; [exact MN | exact HCTX0 | exact HAT0 | exact CB0 | lia | lia | exact HPOS1 | exact HST1]. }
  (* bne d1, 0x5c *)
  step. step.
  rewrite (dn_eqb_u64 (dm_d1 msg) 92) by lia.
  destruct (Z.eq_dec (dm_d1 msg) 92) as [J|J].
  - (* the jog wheel: kind 6, delta d2 - 0x40 *)
    if_false.
    step.
    rewrite (dn_zxb_b8 (dm_d2 msg)) by lia.
    do 5 step.
    assert (HR : res = (1, de_set_delta (s16 (dm_d2 msg - 64)) (de_set_kind DIGINET_EV_JOG (dn_e0 msg)),
                        {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
    { rewrite HRES. unfold dn_tail, DIGINET_JOG_CC.
      rewrite (proj2 (Z.eqb_neq _ _) N90), (proj2 (Z.eqb_neq _ _) NF0), CB0, J. reflexivity. }
    dn_fin HR HDc HD2 HE HEM.
    + dmsg_eq.
    + ev_head_lit. unfold DIGINET_EV_JOG. rewrite s16_small by lia. reflexivity.
  - if_true.
    (* addi -0x40; andi 0xff; bltu 0x17: a V-Pot? *)
    do 4 step.
    rewrite (dn_vpot_cond (dm_d1 msg)) by lia.
    destruct ((64 <=? dm_d1 msg) && (dm_d1 msg <? 88)) eqn:V; cbn [negb].
    + (* a V-Pot: kind 5, strip d1 - 0x40, delta d2 - 0x40 *)
      apply andb_true_iff in V as [V1 V2]. apply Z.leb_le in V1. apply Z.ltb_lt in V2.
      step.
      rewrite (dn_zxb_b8 (dm_d2 msg)) by lia.
      do 6 step.
      assert (HR : res = (1, de_set_delta (s16 (dm_d2 msg - 64))
                               (de_set_strip (u8 (dm_d1 msg - 64)) (de_set_kind DIGINET_EV_VPOT (dn_e0 msg))),
                          {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
      { rewrite HRES. unfold dn_tail, DIGINET_JOG_CC, DIGINET_ZONE_FIRST.
        rewrite (proj2 (Z.eqb_neq _ _) N90), (proj2 (Z.eqb_neq _ _) NF0), CB0.
        rewrite (proj2 (Z.ltb_ge (dm_d1 msg) 32)) by lia. rewrite (proj2 (Z.eqb_neq (dm_d1 msg) 92)) by lia.
        rewrite (proj2 (Z.leb_le 64 (dm_d1 msg))) by lia. rewrite (proj2 (Z.ltb_lt (dm_d1 msg) (64 + 24))) by lia.
        reflexivity. }
      dn_fin HR HDc HD2 HE HEM.
      * dmsg_eq.
      * ev_head_lit. unfold DIGINET_EV_VPOT. rewrite s16_small, u8_small by lia. reflexivity.
    + (* another controller: kind 13 *)
      assert (HR : res = (1, dn_e0 msg, {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
      { rewrite HRES. unfold dn_tail, DIGINET_JOG_CC, DIGINET_ZONE_FIRST.
        rewrite (proj2 (Z.eqb_neq _ _) N90), (proj2 (Z.eqb_neq _ _) NF0), CB0.
        rewrite (proj2 (Z.ltb_ge (dm_d1 msg) 32)) by lia. rewrite (proj2 (Z.eqb_neq (dm_d1 msg) 92)) by lia.
        change (64 + 24) with 88. rewrite V. reflexivity. }
      dn_fin HR HDc HD2 HE HEM.
      * dmsg_eq.
      * ev_head_lit. reflexivity.
Qed.

End Ctl.
