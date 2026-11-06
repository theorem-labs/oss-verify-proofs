(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the meter case of the sysex switch (fn 0x10, from the jump target 0x141a0): address,
   strip, right, mask and the call of diginet_meter_segments (0x141ec) (diginet_decode.c:63-72).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_meter_segments_c diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib.
Import ListNotations.
Open Scope Z_scope.

(* bit 5 of a byte, as slli 58 / srli 63 takes it *)
Lemma dn_bit5 : forall x, 0 <= x < 256 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 58))) 63 = u8 (int_of_bool (negb (Z.land x 32 =? 0))).
Proof.
  intros x Hx. apply Z.eqb_eq. revert x Hx.
  apply (byte_forall (fun x => Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 58))) 63 =?
                               u8 (int_of_bool (negb (Z.land x 32 =? 0))))).
  vm_compute. reflexivity.
Qed.

(* sb keeps the low byte: an int8_t conversion does not change it *)
Lemma b8_s8 : forall x, b8 (s8 x) = b8 x.
Proof.
  intros x. unfold b8, s8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. Z.div_mod_to_equations. lia.
Qed.

(* the mask of two bytes as andi / slli 7 / andi / or compute it: the uint16_t of the model *)
Lemma dn_mask_val : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land x 127))) 7)))
        (bv_unsigned (Z_to_bv 64 (Z.land y 127))) =
  u16 (Z.lor (Z.shiftl (Z.land x 127) 7) (Z.land y 127)).
Proof.
  intros x y Hx Hy. apply Z.eqb_eq.
  assert (H : forallb (fun a => forallb (fun b =>
              Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (Z.of_nat a) 127))) 7)))
                    (bv_unsigned (Z_to_bv 64 (Z.land (Z.of_nat b) 127))) =?
              u16 (Z.lor (Z.shiftl (Z.land (Z.of_nat a) 127) 7) (Z.land (Z.of_nat b) 127)))
            (seq 0 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  specialize (H (Z.to_nat y) ltac:(apply in_seq; lia)).
  rewrite !Z2Nat.id in H by lia. exact H.
Qed.

(* decode_sysex with the body bytes read as at8 (as diginet_decoder_next_sysex.v) *)
Ltac sx_model :=
  unfold decode_sysex, DIGINET_SYSEX_MAKER, DIGINET_FN_RING, DIGINET_FN_METER, DIGINET_FN_LEDS,
    DIGINET_FN_SCRIBBLE, DIGINET_FN_COUNTER, DIGINET_FN_SYSTEM; cbv zeta;
  rewrite !byte_at_map_Z by lia.

Section Meter.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_meter : diginet_meter_segments_contract ->
  forall (ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 : word) (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra
    (de_set_device (at8 bb (Z.to_nat (dm_sysex msg + 1))) (dn_e0 msg)) ->
  dm_status msg = 240 -> 1 <= dm_sysex msg -> 3 <= dm_sysex_len msg ->
  dm_sysex msg + dm_sysex_len msg < Z.of_nat (length bb) ->
  at8 bb (Z.to_nat (dm_sysex msg)) = 19 -> at8 bb (Z.to_nat (dm_sysex msg + 2)) = 16 ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1)
             (Z_to_bv 64 (dm_sysex_len msg + -3)) (Z_to_bv 64 (body + dm_sysex msg)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (dm_sysex_len msg)) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141a0) fc None m1 (seg_rom rsegs)).
Proof.
  intros SEG ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 m1 HCTX HAT HF0 HS1 HN3 HSN MK Hfn.
  dn_ctx_open HCTX. dn_open HAT.
  assert (HR : res = (1, decode_sysex (map bz bb) msg (dn_e0 msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
  { rewrite HRES. unfold dn_tail. rewrite HF0. reflexivity. }
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 3))) as RB3.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 4))) as RB4.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 5))) as RB5.
  (* addi a2 = 3; bne pn, 3 *)
  step. step.
  rewrite (dn_eqb_u64 (dm_sysex_len msg + -3) 3) by lia.
  destruct (Z.eq_dec (dm_sysex_len msg + -3) 3) as [P3|P3].
  2: {
    (* another payload length: kind 13 and the device *)
    if_true.
    dn_fin HR HDc HD2 HE HEM; sx_model;
      rewrite Hfn, MK, (proj2 (Z.ltb_ge _ _) HN3); cbn [Z.eqb Pos.eqb orb negb];
      rewrite (proj2 (Z.eqb_neq (dm_sysex_len msg - 3) 3)) by lia; cbn [negb].
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  if_false.
  (* kind 8; lbu s[3]: strip = s[3] & 0x1f, addr = s[3] *)
  step. step.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 3 HBB ltac:(lia)) as RD3.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  step. step. step.
  (* lbu s[3] again: right = bit 5 *)
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 3 HBB ltac:(lia)) as RD3'.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  step. step. step.
  (* lbu s[4], s[5]: the mask *)
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 4 HBB ltac:(lia)) as RD4.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 5 HBB ltac:(lia)) as RD5.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 4)))) by lia.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 5)))) by lia.
  step. step. step. step.
  rewrite (unsigned_lit (at8 bb (Z.to_nat (dm_sysex msg + 3)))) in HE |- * by lia.
  rewrite (unsigned_lit (at8 bb (Z.to_nat (dm_sysex msg + 4)))) by lia.
  rewrite (unsigned_lit (at8 bb (Z.to_nat (dm_sysex msg + 5)))) by lia.
  rewrite (dn_mask_val (at8 bb (Z.to_nat (dm_sysex msg + 4))) (at8 bb (Z.to_nat (dm_sysex msg + 5)))) by lia.
  rewrite (dn_bit5 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) in HE by lia.
  remember (u16 (Z.lor (Z.shiftl (Z.land (at8 bb (Z.to_nat (dm_sysex msg + 4))) 127) 7)
                       (Z.land (at8 bb (Z.to_nat (dm_sysex msg + 5))) 127))) as M eqn:HMk.
  assert (MR : 0 <= M < 2^16) by (rewrite HMk; unfold u16; change (2^16) with 65536; apply Z.mod_pos_bound; lia).
  (* sh the mask; jal diginet_meter_segments *)
  step. step.
  eapply evt_cut; [eapply SEG; exact MR|].
  intros ms' (a1' & a2' & ->).
  replace (ret_pc (Z_to_bv 64 82416)) with (Z_to_bv 64 82416) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* sb the segments; j 0x140f8 *)
  step. step.
  pose proof (byte_land_le (at8 bb (Z.to_nat (dm_sysex msg + 3))) 31 ltac:(lia) ltac:(lia)) as RL.
  dn_fin HR HDc HD2 HE HEM; sx_model;
    rewrite Hfn, MK, (proj2 (Z.ltb_ge _ _) HN3); cbn [Z.eqb Pos.eqb orb negb];
    rewrite (proj2 (Z.eqb_eq (dm_sysex_len msg - 3) 3)) by lia; cbn [negb];
    replace (dm_sysex msg + 3 + 1) with (dm_sysex msg + 4) by lia;
    replace (dm_sysex msg + 3 + 2) with (dm_sysex msg + 5) by lia;
    rewrite <- HMk.
  - dmsg_eq.
  - ev_head_lit. unfold DIGINET_EV_METER.
    rewrite b8_s8, (u8_small (Z.land (at8 bb (Z.to_nat (dm_sysex msg + 3))) 31)) by lia.
    reflexivity.
Qed.

End Meter.
