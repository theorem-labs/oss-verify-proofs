(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: segment C of the UBSan walk of diginet_decoder_next (lib/U/Prog/
   diginet_decoder_next_seg.v cuts the walk at DN_DECODE = 0x14054): the statuses that are neither a note
   (status & 0xf0 = 0x90) nor a sysex (0xf0), less the fader (status & 0xf0 = 0xb0 with d1 < 0x20), from DN_DECODE to
   DN_RET = 0x1429c (src/diginet_decode.c:115-157).
   - 0x14054-0x14068: lbu status (msg at sp + 0x48), kind = OTHER (0x14064 `sw a2, 0(s0)`, a2 = 13), and
     status & 0xf0 != 0x90 goes to 0x140a4;
   - 0x140a4-0x140a8: status != 0xf0 goes to 0x141d0;
   - 0x141d0-0x141d8: s1 = 1; status & 0xf0 != 0xb0 goes to DN_RET with the event as it is (:127-128);
   - 0x141dc-0x141e4: lbu d1 (sp + 0x4a); 0x1f < d1 goes to 0x142b8 (d1 < 0x20 is the fader, not this segment);
   - 0x142b8-0x142d4: d1 == 0x5c (jog, :146-150): lbu d2 (sp + 0x4b), kind = JOG (6), delta = d2 - 0x40
     (`sh a0, 0xe(s0)`), `j` to DN_RET;
   - 0x142e0-0x142ec: (d1 - 0x40) & 0xff > 0x17 goes to DN_RET with kind OTHER (:157); for a byte d1 that test is
     0x40 <= d1 < 0x58, the model's V-Pot range (DIGINET_ZONE_FIRST = 0x18);
   - 0x142f0-0x14308: the V-Pot (:151-156): kind = VPOT (5), strip = d1 - 0x40 (`sb a0, 4(s0)`), delta = d2 - 0x40,
     `j` to DN_RET.
   33 instructions; the paths of this segment reach no other pc of the function: 0x1406c (the note) needs
   status & 0xf0 = 0x90, 0x140ac (the sysex) status = 0xf0, 0x141e8 (the fader, with 0x142d8-0x142dc) d1 < 0x20;
   the path condition excludes each. The stores write only the event: memory changes only in [ev, ev + 80).
   The int16_t / uint8_t conversions of the model (s16 (d2 - 64), u8 (d1 - 0x40)) are the identity on a byte d2
   and on 0x40 <= d1 < 0x58, so the 64-bit register values the code stores give the model's cells. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step
  Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout diginet_decoder_next_c
  diginet_decoder_next_seg.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model's step under the path condition of this segment ---- *)

(* the tail of DgnLib.v diginet_decoder_next after its note, sysex and fader tests: the model's event *)
Definition dn_cc_ev (msg : dgn_msg) : dgn_event :=
  let e := de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero) in
  if negb (Z.land (dm_status msg) 0xf0 =? 0xb0) then e
  else if dm_d1 msg =? DIGINET_JOG_CC then de_set_delta (s16 (dm_d2 msg - 64)) (de_set_kind DIGINET_EV_JOG e)
  else if (0x40 <=? dm_d1 msg) && (dm_d1 msg <? 0x40 + DIGINET_ZONE_FIRST) then
    de_set_delta (s16 (dm_d2 msg - 64)) (de_set_strip (u8 (dm_d1 msg - 0x40)) (de_set_kind DIGINET_EV_VPOT e))
  else e.

Lemma dn_cc_step : forall bb dc msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  dm_status msg <> 0xf0 /\ Z.land (dm_status msg) 0xf0 <> 0x90 /\
  (Z.land (dm_status msg) 0xf0 <> 0xb0 \/ 0x20 <= dm_d1 msg) ->
  dn_step bb dc = (1, dn_cc_ev msg, {| dd_c := c1; dd_p := dd_p dc |}).
Proof.
  intros bb dc msg c1 H (Pf0 & P90 & Pb0).
  unfold dn_step, diginet_decoder_next. rewrite H. cbv beta iota zeta.
  rewrite Z.eqb_refl. cbn [negb].
  rewrite (proj2 (Z.eqb_neq _ _) P90), (proj2 (Z.eqb_neq _ _) Pf0).
  unfold dn_cc_ev. cbv zeta.
  destruct (Z.land (dm_status msg) 0xf0 =? 0xb0) eqn:E; cbn [negb]; [|reflexivity].
  apply Z.eqb_eq in E. destruct Pb0 as [Pb0|Pb0]; [contradiction|].
  rewrite (proj2 (Z.ltb_ge _ _) Pb0).
  destruct (dm_d1 msg =? DIGINET_JOG_CC); [reflexivity|].
  destruct ((0x40 <=? dm_d1 msg) && (dm_d1 msg <? 0x40 + DIGINET_ZONE_FIRST)); reflexivity.
Qed.

Lemma dn_cc_r : forall bb dc msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  dm_status msg <> 0xf0 /\ Z.land (dm_status msg) 0xf0 <> 0x90 /\
  (Z.land (dm_status msg) 0xf0 <> 0xb0 \/ 0x20 <= dm_d1 msg) ->
  dn_r bb dc = 1.
Proof. intros bb dc msg c1 H P. unfold dn_r. rewrite (dn_cc_step bb dc msg c1 H P). reflexivity. Qed.

Lemma dn_cc_e : forall bb dc msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  dm_status msg <> 0xf0 /\ Z.land (dm_status msg) 0xf0 <> 0x90 /\
  (Z.land (dm_status msg) 0xf0 <> 0xb0 \/ 0x20 <= dm_d1 msg) ->
  dn_e bb dc = dn_cc_ev msg.
Proof. intros bb dc msg c1 H P. unfold dn_e. rewrite (dn_cc_step bb dc msg c1 H P). reflexivity. Qed.

Lemma dn_cc_d : forall bb dc msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  dm_status msg <> 0xf0 /\ Z.land (dm_status msg) 0xf0 <> 0x90 /\
  (Z.land (dm_status msg) 0xf0 <> 0xb0 \/ 0x20 <= dm_d1 msg) ->
  dn_d bb dc = {| dd_c := c1; dd_p := dd_p dc |}.
Proof. intros bb dc msg c1 H P. unfold dn_d. rewrite (dn_cc_step bb dc msg c1 H P). reflexivity. Qed.

(* ---- word and byte facts of the walk ---- *)

(* lbu of a model byte *)
Lemma zxb_b8 : forall x, 0 <= x < 256 -> zxb (b8 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hx.
Qed.

(* 0x142e4 `andi a1, a0, 0xff` *)
Lemma land255_wrap : forall x, Z.land (bv_unsigned (Z_to_bv 64 x)) 255 = x mod 256.
Proof.
  intros x. rewrite unsigned_lit_wrap. change 255 with (2 ^ 8 - 1). rewrite zb_land_mask by lia.
  change (2 ^ 8) with 256. Z.div_mod_to_equations. lia.
Qed.

(* 0x14300 `sb a0, 4(s0)` *)
Lemma le1_lit_b8 : forall x, le1 (Z_to_bv 64 x) = [b8 x].
Proof.
  intros x. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. change (2 ^ 8) with 256. Z.div_mod_to_equations. lia.
Qed.

(* :148 / :154, (int16_t)(d2 - 64) of a byte d2 *)
Lemma s16_byte_sub64 : forall x, 0 <= x < 256 -> s16 (x - 64) = x + -64.
Proof. intros x Hx. unfold s16. rewrite Z.mod_small by lia. lia. Qed.

(* :153, (uint8_t)(d1 - 0x40) on the V-Pot range *)
Lemma u8_vpot : forall x, 0x40 <= x < 0x58 -> u8 (x - 0x40) = x + -64.
Proof. intros x Hx. unfold u8. rewrite Z.mod_small by lia. lia. Qed.

(* the registers after a load: a model byte, and bv_unsigned of an in-range literal *)
Ltac fix_regs :=
  repeat match goal with
  | |- context [zxb (b8 ?x)] => rewrite (zxb_b8 x) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
  end.

(* ---- the walk ---- *)

Lemma diginet_decoder_next_cc_seg : forall (ra s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
    (spf d ev body : Z) (bb cpad mpad junk : list byte) (dc : dgn_decoder) (msg : dgn_msg) (c1 : dgn_cursor)
    (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word),
  dn_seg_pre m spf d ev body bb cpad mpad junk dc msg c1 ->
  dm_status msg <> 0xf0 /\ Z.land (dm_status msg) 0xf0 <> 0x90 /\
  (Z.land (dm_status msg) 0xf0 <> 0xb0 \/ 0x20 <= dm_d1 msg) ->
  dn_seg_cont Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DN_DECODE) fc None m (seg_rom rsegs)).
Proof.
  intros ra s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp F fc m Q spf d ev body bb cpad mpad junk dc msg c1
    a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 Hpre Hpath K.
  destruct Hpre as (Hmn & Hd0 & Hev0 & Hdal & Heval & Hspal & Hbody & Hlen & Hpos & Hst & Hbb & HD & HE & HM & HJ &
                    Hdev & Hdb & Heb & Hds & Hes & Hbs & HI).
  pose proof (dn_cc_step bb dc msg c1 Hmn Hpath) as Hstep.
  destruct Hpath as (Pf0 & P90 & Pb0).
  pose proof (msg_next_one bb (dd_c dc) dgn_msg_zero msg c1 Hlen ltac:(lia) Hst Hmn) as Hone.
  destruct Hone as (Rst & Rd1 & Rd2 & _).
  unfold dn_seg_cont in K.
  (* DN_RET with the event E written at ev and nothing else written: the decoder is the one of dn_seg_pre *)
  assert (K' : forall (E : dgn_event) (ra' s0' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      dn_cc_ev msg = E -> munch [(ev, ev + 80)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
      rw_cells rsegs m' ev (event_cells body mpad E) ->
      evt rsegs Q (MS (mkR ra' (Z_to_bv 64 spf) gp tp t0' t1' t2' s0' (Z_to_bv 64 1) a0' a1' a2' a3' a4' a5' a6' a7'
                           s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x1429c) fc None m' (seg_rom rsegs))).
  { intros E ra' s0' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' m' HEq HMU HWM HMI HEV.
    apply K.
    - eapply munch_weaken; [|exact HMU]. unfold sub_fp. cbn [outside]. intros x Hx. tauto.
    - exact HWM.
    - exact HMI.
    - unfold dn_e. rewrite Hstep. cbn [fst snd]. rewrite HEq. exact HEV.
    - unfold dn_d. rewrite Hstep. cbn [snd].
      eapply rw_cells_transport; [exact HD | exact HMU | exact HWM |].
      cbn [disjoint_from]. rewrite decoder_cells_size. change (Z.of_nat 40) with 40. split; [lia | exact I]. }
  clear K Hstep HJ Hbb HD Hmn Hlen Hpos Hst Hdev Hdb Heb Hds Hbs Hd0 Hdal Hbody.
  unfold dmsg_cells in HM.
  unfold event_cells, dmsg_cells, arr_cells in HE. cbn [map seq app] in HE.
  pose proof (munch_refl [(ev, ev + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold DN_DECODE.
  (* 0x14054-0x14068: status, kind = OTHER, not a note *)
  step. fix_regs.
  step. step. step. step. fix_regs.
  step. if_cases B1; zify_cond B1; [|exfalso; lia].
  (* 0x140a4-0x140a8: not a sysex *)
  step. step. if_cases B2; zify_cond B2; [|exfalso; lia].
  (* 0x141d0-0x141d8: s1 = 1; a control change? *)
  step. step. step. if_cases B3; zify_cond B3.
  - (* status & 0xf0 != 0xb0: DN_RET, kind OTHER (:127-128) *)
    eapply (K' (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero)));
      [ | exact MU | exact WM | exact HI | exact HE ].
    unfold dn_cc_ev. rewrite (proj2 (Z.eqb_neq _ _) B3). reflexivity.
  - (* 0x141dc-0x141e4: d1 > 0x1f (d1 < 0x20 is the fader) *)
    step. fix_regs. step. step. if_cases B4; zify_cond B4; [| exfalso; destruct Pb0; lia].
    (* 0x142b8-0x142bc: the jog? *)
    step. step. if_cases B5; zify_cond B5.
    + (* 0x142e0-0x142ec: the V-Pot range test *)
      step. fix_regs. step. rewrite land255_wrap.
      step. step. if_cases B6; zify_cond B6.
      * (* not a V-Pot: DN_RET, kind OTHER (:157) *)
        eapply (K' (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero)));
          [ | exact MU | exact WM | exact HI | exact HE ].
        unfold dn_cc_ev, DIGINET_JOG_CC, DIGINET_ZONE_FIRST.
        rewrite (proj2 (Z.eqb_eq _ _) B3), (proj2 (Z.eqb_neq _ _) B5). cbn [negb].
        replace ((0x40 <=? dm_d1 msg) && (dm_d1 msg <? 0x40 + 0x18)) with false; [reflexivity|].
        symmetry. apply Bool.andb_false_iff.
        destruct (Z.ltb_spec (dm_d1 msg) 0x40) as [L|L]; [left; apply Z.leb_gt; lia|].
        right. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
      * (* 0x142f0-0x14308: the V-Pot (:151-156) *)
        assert (V : 0x40 <= dm_d1 msg < 0x58) by (Z.div_mod_to_equations; lia).
        step. fix_regs. step. step. step.
        step. rewrite le1_lit_b8. mem_after_store.
        step. step.
        eapply (K' (de_set_delta (dm_d2 msg + -64) (de_set_strip (dm_d1 msg + -64)
                     (de_set_kind DIGINET_EV_VPOT (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero))))));
          [ | exact MU | exact WM | exact HI | exact HE ].
        unfold dn_cc_ev, DIGINET_JOG_CC, DIGINET_ZONE_FIRST.
        rewrite (proj2 (Z.eqb_eq _ _) B3), (proj2 (Z.eqb_neq _ _) B5). cbn [negb].
        change (0x40 + 0x18) with 0x58.
        rewrite (proj2 (Z.leb_le _ _) (proj1 V)), (proj2 (Z.ltb_lt _ _) (proj2 V)). cbn [andb].
        rewrite s16_byte_sub64, u8_vpot by lia. reflexivity.
    + (* 0x142c0-0x142d4: the jog (:146-150) *)
      step. fix_regs. step. step. step. step. step.
      eapply (K' (de_set_delta (dm_d2 msg + -64)
                   (de_set_kind DIGINET_EV_JOG (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero)))));
        [ | exact MU | exact WM | exact HI | exact HE ].
      unfold dn_cc_ev, DIGINET_JOG_CC.
      rewrite (proj2 (Z.eqb_eq _ _) B3), (proj2 (Z.eqb_eq _ _) B5). cbn [negb].
      rewrite s16_byte_sub64 by lia. reflexivity.
Qed.
