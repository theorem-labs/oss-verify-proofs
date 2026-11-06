(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the note path (0x13ef8 .. 0x13f2c, 0x1401c .. 0x14028,
   0x140e8 .. 0x140f4): status & 0xf0 = 0x90, decode_note inlined (diginet_decode.c:20-35).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib.
Import ListNotations.
Open Scope Z_scope.

(* bit 6 of a byte, as slli 57 / srli 63 takes it *)
Lemma dn_bit6 : forall x, 0 <= x < 256 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 57))) 63 = u8 (int_of_bool (negb (Z.land x 64 =? 0))).
Proof.
  intros x Hx. apply Z.eqb_eq. revert x Hx.
  apply (byte_forall (fun x => Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 57))) 63 =?
                               u8 (int_of_bool (negb (Z.land x 64 =? 0))))).
  vm_compute. reflexivity.
Qed.

Section Note.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_note : forall (ra' t0 t1 t2 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 : word)
    (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra (dn_e0 msg) ->
  Z.land (dm_status msg) 240 = 144 -> 0 <= dm_d1 msg < 256 -> 0 <= dm_d2 msg < 256 ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) s1' a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ef8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0 t1 t2 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m1 HCTX HAT H90 R1 R2.
  dn_ctx_open HCTX. dn_open HAT.
  assert (HR : res = (1, decode_note msg (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero)),
                      {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
  { rewrite HRES. unfold dn_tail. rewrite H90. reflexivity. }
  pose proof (byte_land_le (dm_d2 msg) 63 R2 ltac:(lia)) as RL.
  (* lbu d2, lbu d1; id = d2 & 0x3f, on = bit 6 of d2; button and on stored *)
  step. step.
  rewrite (dn_zxb_b8 (dm_d2 msg)) by lia. rewrite (dn_zxb_b8 (dm_d1 msg)) by lia.
  do 5 step.
  step. step.
  (* bltu 5, id - 0x18: not a zone key *)
  step.
  rewrite (unsigned_lit (dm_d2 msg)) in HE |- * by lia.
  rewrite (dn_bit6 (dm_d2 msg)) in HE by lia.
  if_cases HB; zify_cond HB.
  - assert (Z1 : (24 <=? u8 (Z.land (dm_d2 msg) 63)) && (u8 (Z.land (dm_d2 msg) 63) <=? 29) = false).
    { rewrite u8_small by lia. replace (2^64) with 18446744073709551616 in HB by reflexivity.
      apply andb_false_iff. Z.div_mod_to_equations.
      destruct (Z.leb_spec 24 (Z.land (dm_d2 msg) 63)); [right; apply Z.leb_gt; lia | left; reflexivity]. }
    step. step.
    rewrite (dn_eqb_int64 (dm_d1 msg) 9) by lia.
    destruct (Z.eq_dec (dm_d1 msg) 9) as [T|T].
    + (* the touch button: TOUCH, strip id *)
      if_false. do 5 step.
      dn_fin HR HDc HD2 HE HEM;
        unfold decode_note, DIGINET_ZONE_FIRST, DIGINET_ZONE_LAST, DIGINET_BTN_TOUCH; cbv zeta;
        rewrite Z1, T; cbn [Z.eqb Pos.eqb].
      * dmsg_eq.
      * ev_head_lit. unfold DIGINET_EV_TOUCH.
        rewrite (u8_small (Z.land (dm_d2 msg) 63)) by lia. reflexivity.
    + (* another button: STRIP_BUTTON, strip id *)
      if_true. do 4 step.
      dn_fin HR HDc HD2 HE HEM;
        unfold decode_note, DIGINET_ZONE_FIRST, DIGINET_ZONE_LAST, DIGINET_BTN_TOUCH; cbv zeta;
        rewrite Z1, (proj2 (Z.eqb_neq _ _) T).
      * dmsg_eq.
      * ev_head_lit. unfold DIGINET_EV_STRIP_BUTTON.
        rewrite (u8_small (Z.land (dm_d2 msg) 63)) by lia. reflexivity.
  - (* a zone key: SECTION_BUTTON, zone id *)
    assert (Z1 : (24 <=? u8 (Z.land (dm_d2 msg) 63)) && (u8 (Z.land (dm_d2 msg) 63) <=? 29) = true).
    { rewrite u8_small by lia. replace (2^64) with 18446744073709551616 in HB by reflexivity.
      apply andb_true_iff. Z.div_mod_to_equations. split; apply Z.leb_le; lia. }
    do 5 step.
    dn_fin HR HDc HD2 HE HEM;
      unfold decode_note, DIGINET_ZONE_FIRST, DIGINET_ZONE_LAST, DIGINET_BTN_TOUCH; cbv zeta; rewrite Z1.
    + dmsg_eq.
    + ev_head_lit. unfold DIGINET_EV_SECTION_BUTTON.
      rewrite (u8_small (Z.land (dm_d2 msg) 63)) by lia. reflexivity.
Qed.

End Note.
