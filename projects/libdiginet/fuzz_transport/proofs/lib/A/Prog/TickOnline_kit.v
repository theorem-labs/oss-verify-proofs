(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths, module names and numbers changed; 1019 of its 1158 lines of code are new or changed and 626 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_sl1.v, with its module names and numbers changed; 246 of its 343 lines of code are new or changed and 1061 lines of the source are left out. *)
(* TickOnline_kit: the lemmas the online piece of the image-A walk of diginet_session_tick uses beyond the kit
   (lib/A/Prog/TickOnline.v proves tick_online_stmt of lib/A/Prog/TickCut.v). Three groups:
   - the model on the two arms of the silence test (to_model_step, to_model_lost) and what the two stores of 0 at
     s + 212 and s + 168 keep (to_w1_facts); SlostNtcKit.v's sn_model, sn_notify, sn_gfn' do the rest;
   - the 72 bytes of the notice the arm builds at p = frame + 32 (to_val_split2, to_nb);
   - the written range tick_wr (to_wr_G: every byte of it is a byte of G; to_wr_lo: below the shadow band) and what
     that gives at the call of notice: notice_apart (to_apart) and trans_ntc_at of the notice in the class-5 frame
     (to_ntc_at, from TickSrcKit.v trans_src_ok_fake and TransportGNotice.v frame_ra_zero / frame_hull_vis).
   Nothing here names a symbolic state or a run. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportImg DgnTransportCg YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
TransportGCg TransportGFrame CanKit TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  diginet_session_tick_cg TickCut TransportGNotice SlostNtcKit TickSrcKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The offsets the piece runs, and the shadow bytes it reads        *)
(* ------------------------------------------------------------------ *)

(* The silence test's branch (`bgeu a1, a0`, +0x3c4), the first instruction of the lost arm (+0x558), the
   instruction after the memset call (+0x5c0) and the one after the notice call (+0x61c). *)
Definition TO_BR : Z := AF_diginet_session_tick + 0x3c4.
Definition TO_LOST : Z := AF_diginet_session_tick + 0x558.
Definition TO_AFTER_MS : Z := AF_diginet_session_tick + 0x5c0.
Definition TO_AFTER_NTC : Z := AF_diginet_session_tick + 0x61c.
(* The shadow bytes of the g_s fields the piece reads or writes (the code forms each as (s + k) >> 3 + s8). *)
Definition TO_SH40 : Z := 2148220733.
Definition TO_SH96 : Z := 2148220740.
Definition TO_SH112 : Z := 2148220742.
Definition TO_SH168 : Z := 2148220749.
Definition TO_SH176 : Z := 2148220750.
Definition TO_SH212 : Z := 2148220754.
Lemma to_sh_eq :
  TO_SH40 = SHADOW_OFF + (TICK_S + 40) / 8 /\ TO_SH96 = SHADOW_OFF + (TICK_S + 96) / 8 /\
  TO_SH112 = SHADOW_OFF + (TICK_S + 112) / 8 /\ TO_SH168 = SHADOW_OFF + (TICK_S + 168) / 8 /\
  TO_SH176 = SHADOW_OFF + (TICK_S + 176) / 8 /\ TO_SH212 = SHADOW_OFF + (TICK_S + 212) / 8 /\
  TO_SH40 = FCells.shadow_addr (TICK_S + 40) /\ TO_SH96 = FCells.shadow_addr (TICK_S + 96) /\
  TO_SH112 = FCells.shadow_addr (TICK_S + 112) /\ TO_SH168 = FCells.shadow_addr (TICK_S + 168) /\
  TO_SH176 = FCells.shadow_addr (TICK_S + 176) /\ TO_SH212 = FCells.shadow_addr (TICK_S + 208).
Proof. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model at the silence test                                    *)
(* ------------------------------------------------------------------ *)

Lemma to_state_range : forall Bw, - 2 ^ 31 <= TW.S_state Bw < 2 ^ 31.
Proof.
intros Bw. pose proof (bv_swrap_in_range 32 (TW.u_at Bw TW.A_S_state 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bw TW.A_S_state 4)) with (TW.S_state Bw) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

(* No silence: the dispatch of :418-427 takes neither a return nor a lost arm, so what is left is tick_go. *)
Lemma to_model_step : forall (TF : option TI.tframe) Bw now Bw' r,
  TW.S_state Bw = TS0.DIGINET_S_ONLINE ->
  (TS0.ms_m (TW.S_cfg_offline_ms Bw) <=? TS0.u64 (now - TW.S_last_rx_us Bw)) = false ->
  TSS.diginet_session_tick_m timg_A TF Bw now = Some (Bw', r) ->
  tick_go timg_A TF Bw now = Some (Bw', r).
Proof.
intros TF Bw now Bw' r Hst Hto Hm. rewrite tick_model in Hm. cbv zeta in Hm. rewrite Hst in Hm.
change ((TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_CLOSED) || (TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_IDLE))%bool
  with false in Hm.
change ((TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_WAKING))%bool with false in Hm.
change ((TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_ONLINE))%bool with true in Hm.
rewrite Hto in Hm. cbn [andb] in Hm. exact Hm.
Qed.

(* Silence: the model is session_lost at R_SILENCE, and the result is DIGINET_OK. *)
Lemma to_model_lost : forall (TF : option TI.tframe) Bw now Bw' r,
  TW.S_state Bw = TS0.DIGINET_S_ONLINE ->
  (TS0.ms_m (TW.S_cfg_offline_ms Bw) <=? TS0.u64 (now - TW.S_last_rx_us Bw)) = true ->
  TSS.diginet_session_tick_m timg_A TF Bw now = Some (Bw', r) ->
  TSS.session_lost_m timg_A TF Bw TS0.DIGINET_R_SILENCE = Some (Bw', tt) /\ r = DLib.DIGINET_OK.
Proof.
intros TF Bw now Bw' r Hst Hto Hm. rewrite tick_model in Hm. cbv zeta in Hm. rewrite Hst in Hm.
change ((TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_CLOSED) || (TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_IDLE))%bool
  with false in Hm.
change ((TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_WAKING))%bool with false in Hm.
change ((TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_ONLINE))%bool with true in Hm.
rewrite Hto in Hm. cbn [andb] in Hm.
destruct (TSS.session_lost_m timg_A TF Bw TS0.DIGINET_R_SILENCE) as [[B0 u]|]; [|discriminate Hm].
destruct u. destruct (tick_some_inv _ _ _ _ Hm) as [EB Er]. subst B0. split; [reflexivity | exact (eq_sym Er)].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. What the two stores of 0 of the lost arm keep                   *)
(* ------------------------------------------------------------------ *)

(* The two stores of 0 at s + 212 and s + 168 keep g_s's state and g_fail_next. *)
Lemma to_w1_facts : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_state (slost_w1 Bw) = TW.S_state Bw /\ TW.g_fail_next (slost_w1 Bw) = TW.g_fail_next Bw.
Proof.
intros Bw HL.
assert (LZ : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
assert (L1 : Z.of_nat (length (TW.upd Bw TW.A_S_inflight (TW.put 4 0))) = TW.W_LEN).
{ rewrite TWL.length_upd_put; [exact LZ | unfold TW.A_S_inflight, TW.OFF_g_s; lia |].
  rewrite LZ. unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN. lia. }
unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight, TW.S_state, TW.g_fail_next.
split.
- rewrite TWL.s32_at_upd_out;
    [| unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put; unfold TW.A_S_desk_counter_valid, TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put, L1; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; lia].
  rewrite TWL.s32_at_upd_out;
    [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put; unfold TW.A_S_inflight, TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put, LZ; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out;
    [| unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put, L1; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; lia].
  rewrite TWL.u_at_upd_out;
    [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put; unfold TW.A_S_inflight, TW.OFF_g_s, TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put, LZ; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The 72 bytes of the notice                                      *)
(* ------------------------------------------------------------------ *)

(* The 8 bytes 0x400000002 the code stores at p + 8 (`addi a1, zero, 1`, `slli a1, a1, 0x22`, `addi a1, a1, 2`,
   `sd a1, 8(s5)`), read as the notice's old (S_ONLINE) and reason (R_SILENCE) fields. *)
Lemma to_val_split2 : forall (m : word -> option byte) a,
  val_mem tfibsegs m a 8 17179869186 ->
  val_mem tfibsegs m a 4 2 /\ val_mem tfibsegs m (a + 4) 4 4.
Proof.
intros m a H. split; intros k Hk.
- destruct k as [|[|[|[|k]]]]; try lia;
  [ exact (H 0%nat ltac:(lia)) | exact (H 1%nat ltac:(lia)) | exact (H 2%nat ltac:(lia))
  | exact (H 3%nat ltac:(lia)) ].
- destruct k as [|[|[|[|k]]]]; try lia;
  [ replace (a + 4 + Z.of_nat 0) with (a + Z.of_nat 4) by (cbn; lia); exact (H 4%nat ltac:(lia))
  | replace (a + 4 + Z.of_nat 1) with (a + Z.of_nat 5) by (cbn; lia); exact (H 5%nat ltac:(lia))
  | replace (a + 4 + Z.of_nat 2) with (a + Z.of_nat 6) by (cbn; lia); exact (H 6%nat ltac:(lia))
  | replace (a + 4 + Z.of_nat 3) with (a + Z.of_nat 7) by (cbn; lia); exact (H 7%nat ltac:(lia)) ].
Qed.

(* The 72 bytes of the notice at p = F + 32: the 8 bytes 2 at p (kind N_STATE, state S_IDLE), old and reason
   (4 bytes each) and the memset's 56 zeros, read as WalkNotify.v ntc_state_bytes. *)
Lemma to_nb : forall (H : word -> bool) (m : word -> option byte) F old why,
  val_mem tfibsegs (mrestrict H m) (F + 32) 8 2 ->
  val_mem tfibsegs (mrestrict H m) (F + 40) 4 old ->
  val_mem tfibsegs (mrestrict H m) (F + 44) 4 why ->
  (forall a, F + 48 <= a < F + 104 -> aview tfibsegs H m a = Some 0) ->
  garr8 tfibsegs (mrestrict H m) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 0 old why)).
Proof.
intros H m F old why V0 V8 V12 Z0.
unfold WN.ntc_state_bytes.
change (TW.put 4 2 ++ TW.put 4 0 ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56)
  with (TW.put 8 2 ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56).
rewrite !map_app. apply garr8_app. split; [exact (garr8_of_put tfibsegs _ _ 8 2 V0) |].
rewrite length_map, TWL.length_put. replace (F + 32 + Z.of_nat 8) with (F + 40) by lia.
apply garr8_app. split; [exact (garr8_of_put tfibsegs _ _ 4 old V8) |].
rewrite length_map, TWL.length_put. replace (F + 40 + Z.of_nat 4) with (F + 44) by lia.
apply garr8_app. split; [exact (garr8_of_put tfibsegs _ _ 4 why V12) |].
rewrite length_map, TWL.length_put. replace (F + 44 + Z.of_nat 4) with (F + 48) by lia.
rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
apply garr8_zeros. intros a Ha.
pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Every byte of tick_wr is a byte of G                             *)
(* ------------------------------------------------------------------ *)

(* A field of a row of TWorldA.v TMAP_A, inside the row's payload, is a byte of G. *)
Lemma to_row_inG : forall o b sz A n a, In (o, b, sz) TMAP_A -> twa_fld o b A n a ->
  0 <= A - o -> A - o + n <= sz -> inG TG.G_HARNESS a.
Proof.
intros o b sz A n a Hin Hx H1 H2. unfold inG. apply Exists_exists. exists (b, sz).
split; [exact (TMAP_A_in_G _ _ _ Hin) | unfold in_zr, twa_fld in *; cbn [fst snd]; lia].
Qed.
Lemma to_row_inG_b : forall o b sz A n a, In (o, b, sz) TMAP_A -> twa_fld o b A n a ->
  ((0 <=? A - o) && (A - o + n <=? sz))%bool = true -> inG TG.G_HARNESS a.
Proof.
intros o b sz A n a Hin Hx Hb. apply andb_prop in Hb as [B1 B2].
apply Z.leb_le in B1. apply Z.leb_le in B2. exact (to_row_inG o b sz A n a Hin Hx B1 B2).
Qed.

Ltac to_gs H := apply (to_row_inG_b TW.OFF_g_s TA_g_s TW.SZ_g_s _ _ _ TMAP_A_g_s H); vm_compute; reflexivity.
Ltac to_got H := apply (to_row_inG_b TW.OFF_GOT TA_GOT TW.SZ_GOT _ _ _ TMAP_A_GOT H); vm_compute; reflexivity.
Ltac to_m H := apply (to_row_inG_b TW.OFF_M TA_M TW.SZ_M _ _ _ TMAP_A_M H); vm_compute; reflexivity.

(* Every byte io_send stores is a byte of G. *)
Lemma to_iosend_wr_G : forall n a, 0 <= n -> iosend_wr n a -> inG TG.G_HARNESS a.
Proof.
intros n a Hn H. unfold iosend_wr in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(s & Hs & H)|[H|H]]]]]]]]]]]]]]]]]].
- apply (to_row_inG_b TW.OFF_g_fail_next TA_g_fail_next 1 _ _ _ TMAP_A_g_fail_next H);
  vm_compute; reflexivity.
- to_got H.
- to_got H.
- to_got H.
- apply (to_row_inG_b TW.OFF_g_last_counter TA_g_last_counter TW.SZ_g_last_counter _ _ _
    TMAP_A_g_last_counter H); vm_compute; reflexivity.
- to_m H.
- to_m H.
- to_m H.
- to_m H.
- to_m H.
- to_m H.
- to_m H.
- to_m H.
- to_m H.
- to_m H.
- apply (to_row_inG TW.OFF_M TA_M TW.SZ_M TW.A_M_fly_frame (Z.min n TC.SPEC_MAX_FRAME) a TMAP_A_M H);
    [unfold TW.A_M_fly_frame, TW.OFF_M; lia
     | unfold TW.A_M_fly_frame, TW.OFF_M, TW.SZ_M, TC.SPEC_MAX_FRAME; lia].
- apply (to_row_inG TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (TW.A_Cmd_st s) 4 a TMAP_A_g_cmd H);
    [unfold TW.A_Cmd_st, TW.OFF_g_cmd in *; unfold TC.CMDS_MAX in Hs; lia
     | unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd in *; unfold TC.CMDS_MAX in Hs; lia].
- apply (to_row_inG_b TW.OFF_g_q TA_g_q TW.SZ_g_q _ _ _ TMAP_A_g_q H); vm_compute; reflexivity.
- apply (to_row_inG_b TW.OFF_g_nq TA_g_nq TW.SZ_g_nq _ _ _ TMAP_A_g_nq H); vm_compute; reflexivity.
Qed.

(* Every byte send_data stores outside its own frames is a byte of G. *)
Lemma to_senddata_wr_G : forall a, senddata_wr a -> inG TG.G_HARNESS a.
Proof.
intros a H. unfold senddata_wr in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; try (to_gs H).
exact (to_iosend_wr_G SENDDATA_CAP a ltac:(unfold SENDDATA_CAP; lia) H).
Qed.

(* Every byte some path of the call stores outside its own frames is a byte of G. *)
Lemma to_wr_G : forall Bw a, tick_wr Bw a -> inG TG.G_HARNESS a.
Proof.
intros Bw a H. unfold tick_wr in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(q & Hq & H)|[H|H]]]]]]]]]]]]]]]]]]].
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- to_gs H.
- exact (notice_wr_G _ _ a H).
- exact (notice_wr_G _ _ a H).
- exact (notice_wr_G _ _ a H).
- exact (to_iosend_wr_G TC.SPEC_MAX_FRAME a ltac:(unfold TC.SPEC_MAX_FRAME; lia) H).
- apply (to_row_inG TW.OFF_g_s TA_g_s TW.SZ_g_s (TW.A_S_queue_bytes q) TW.S_queue_ESZ a TMAP_A_g_s H);
    [unfold TW.A_S_queue_bytes, TW.OFF_g_s in *; unfold TW.S_queue_N in Hq; lia
     | unfold TW.A_S_queue_bytes, TW.S_queue_ESZ, TW.OFF_g_s, TW.SZ_g_s in *; unfold TW.S_queue_N in Hq; lia].
- to_gs H.
- exact (to_senddata_wr_G a H).
Qed.

(* The store of 0 at s + 112 is a byte of tick_wr. *)
Lemma to_wr_state : forall Bw a, TICK_S + 112 <= a < TICK_S + 116 -> tick_wr Bw a.
Proof.
intros Bw a Ha. right; right; left. unfold TICK_S, twa_fld, TW.A_S_state, TW.OFF_g_s, TA_g_s in *. lia.
Qed.
Lemma to_wr_inflight : forall Bw a, TICK_S + 212 <= a < TICK_S + 216 -> tick_wr Bw a.
Proof.
intros Bw a Ha. left. unfold TICK_S, twa_fld, TW.A_S_inflight, TW.OFF_g_s, TA_g_s in *. lia.
Qed.
Lemma to_wr_dcv : forall Bw a, TICK_S + 168 <= a < TICK_S + 172 -> tick_wr Bw a.
Proof.
intros Bw a Ha. right; left. unfold TICK_S, twa_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s, TA_g_s in *. lia.
Qed.
(* The notice this arm makes is the fifteenth row of tick_wr. *)
Lemma to_wr_ntc : forall Bw a, notice_wr (slost_w2 Bw) (slost_ntc Bw TS0.DIGINET_R_SILENCE) a -> tick_wr Bw a.
Proof. intros Bw a H. do 14 right. left. exact H. Qed.

(* ------------------------------------------------------------------ *)
(* 6. The facts the call of notice asks                               *)
(* ------------------------------------------------------------------ *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* The notice at p = F + 32, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma to_ntc_at : forall lyc S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bw why F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W memN mdN -> In (TICK_CID, pos) (frames S2) ->
  F = frame_addr lyc TICK_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + TICK_FBYTES <= alloc_ceiling ->
  in_app F TICK_FBYTES -> F + TICK_FBYTES <= spZ regsC - NOTICE_STK -> 0 <= why < 2 ^ 31 ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 0 (TW.S_state (slost_w1 Bw)) why)) ->
  trans_ntc_at B lyc S2 W memN regsC NOTICE_STK (F + 32) (slost_ntc Bw why).
Proof.
intros lyc S2 W memN mdN regsC Bw why F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin Hwhy ZS HNB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TICK_FBYTES in HFc, HFapp, Hwin.
destruct (al_frames _ _ LAWS lyc S2 W memN mdN TICK_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF in HFb, HFsh. change (fs_frame_bytes TICK_CID) with 2048 in HFb.
change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
set (old := TW.S_state (slost_w1 Bw)) in *.
assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
unfold trans_ntc_at.
split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
split.
{ apply (trans_src_ok_fake B lyc S2 W memN (F + 32) NTC_SIZE).
  - exists TICK_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048.
    unfold NTC_SIZE. lia.
  - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
    + apply (frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
    + apply (frame_hull_vis _ F 2048 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
    + apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia].
    + lia.
    + lia. }
split; [left; unfold NTC_SIZE; lia|].
exists (WN.ntc_state_bytes 0 old why).
split; [exact HNB|].
unfold slost_ntc. fold old.
cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
  TI.n_body TI.n_ann length].
unfold WN.ntc_state_bytes, TW.s32_at.
assert (Z0 : TW.u_at (TW.put 4 2 ++ TW.put 4 0 ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56) 48 8 = 0)
  by WN.ntc_field.
rewrite Z0.
split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
split; [WN.ntc_field |].
split; [WN.ntc_field |].
split; [WN.ntc_field; apply WN.swrap32_mod; exact Hold |].
split; [WN.ntc_field; apply WN.swrap32_mod; lia |].
split; [WN.ntc_field |].
split; [WN.ntc_field |].
split; [WN.ntc_field |].
split; [WN.ntc_field |].
split; [WN.ntc_field |].
split; [apply garr8_nil |].
split; [exact (trans_src_ok_null B lyc S2 W memN) |].
split; [left; lia |].
WN.ntc_field.
Qed.

(* notice's stores (an N_STATE notice: bytes of GOT) are apart from the notice's own bytes (a frame is not image),
   from its empty body, and from TF (tick_apart: they are bytes of tick_wr). *)
Lemma to_apart : forall lyc S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W2 mem2 md2 -> In (TICK_CID, pos) (frames S2) ->
  F = frame_addr lyc TICK_CID pos -> tick_apart TF Bw ->
  notice_apart W memN (F + 32) (slost_ntc Bw TS0.DIGINET_R_SILENCE) TF (slost_w2 Bw).
Proof.
intros lyc S2 W2 mem2 md2 W memN TF Bw F pos LAWS HAR Hin EF Hap x Hx.
assert (Hw : tick_wr Bw x) by exact (to_wr_ntc Bw x Hx).
split; [|split].
- intros Hr. apply (frm_img segs B LAWS lyc S2 W2 mem2 md2 TICK_CID pos x HAR Hin);
    [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; unfold NTC_SIZE in Hr; lia|].
  exact (trans_g_img x (to_wr_G Bw x Hw)).
- intros NB _ _. split.
  + unfold slost_ntc. cbn [TI.n_body length Z.of_nat]. lia.
  + intros Hn. exfalso. apply Hn. reflexivity.
- intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* Every byte of tick_wr lies below the shadow band: the premise TickSrcKit.v trans_tframe_at_top asks of the
   walk's written range. *)
Lemma to_wr_lo : gx_ok segs B TG.G_HARNESS -> forall Bw a, tick_wr Bw a -> a < SHADOW_OFF.
Proof.
intros HGX Bw a Hw.
pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX (to_wr_G Bw a Hw)) as Hl.
unfold kLowMemEnd, SHADOW_OFF in *. lia.
Qed.

End k.
