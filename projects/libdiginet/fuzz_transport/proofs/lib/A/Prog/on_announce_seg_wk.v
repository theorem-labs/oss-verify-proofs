(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names changed; 771 of its 856 lines of code are new or changed and 680 lines of the source are left out. *)
(* on_announce_seg_wk: the wake piece of on_announce's image-A G-form walk, onann_piece_wk : onann_wk_stmt
   (lib/A/Prog/OnannCut.v), code +0x518 .. +0x544 (0x87f8c .. 0x87fb8), ending at the cut onann_nrel_at (+0x764).
     +0x518  `bnez a0` on the state the e0 arm loaded (a0 = S_state B4, onann_regs_wk): a state that is not S_IDLE
             is the model's else branch (onann_k_wk gives Bw' = B4) and goes to +0x764;
     +0x51c .. +0x534  the checked 4-byte load of g_s.cfg.auto_wake (s + 16; its shadow byte is 0, the record's
             trans_onann_cells) and `beqz a0`: auto_wake = 0 is the model's else branch again, to +0x764;
     +0x538 .. +0x540  a0 = s, a1 = now (the 8-byte load at s1 + 0, the cut's onann_slot), and the call of
             diginet_session_wake (0x87fb4, return 0x87fb8) through the statement's premise
             transport_diginet_session_wake_cg, in the SAME G journal (as SlostNtc.v applies notice);
     +0x544  `j` to +0x764 with the world B5 the call left.
   The call's facts: wake_apart from onann_apart (wake_wr Bx lies in the row `exists Bx, wake_wr Bx` of onann_wr),
   trans_tframe_at at WAKE_STK by wk_tf_call (the own class-4 frame is live; TF lies outside G by trans_tf_off_g, so
   the G placement of trans_src_ok cannot hold of a non-empty TF), trans_rom_view_rd by wk_rom_call, the run
   invariants and g_fail_next at B4 from the cut, the counts and the event budget from onann_fix. Its post folds into
   the walk's acall_kept_g with TransportGCg.v dk_kept_trans_nf_g (wake_wr B4 is a row of onann_wr), which keeps the
   13 saved words above sp1 and the frame's last word.
   Lemmas of note: wk_wr_G (every byte of onann_wr is a byte of G: the g_s fields, notice_seg_base.v nt_wr_G,
   SlostNtcKit.v sn_wr_G, and wake's and maybe_online's ranges), wk_tf_call, wk_rom_call, wk_cur_move. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg SlostNtcKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The code points and the symbolic states                          *)
(* ------------------------------------------------------------------ *)

(* The return address of the call of diginet_session_wake (+0x544, the `j` to the release cut). *)
Definition WK_C3 : Z := AF_on_announce + 0x544.
Lemma wk_c3_num : WK_C3 = 27988.
Proof. reflexivity. Qed.
(* The shadow byte of g_s.cfg.auto_wake (s + 16). *)
Definition WK_SH : Z := 2148220730.
Lemma WK_SH_eq : WK_SH = SHADOW_OFF + (ONANN_S + 16) / 8.
Proof. reflexivity. Qed.
Definition WK_Bx : sv := SLit 0.
Definition WK_B0 : Z * Z := (0, 0).

(* The three regions the piece reads: g_s.cfg.auto_wake (4 bytes, atom 32), its shadow byte (0), and the spill slot
   at s1 + 0 holding now (atom 33). None of them is written. *)
Definition WK_R_gs : YP09.region :=
  YP09.mkRegion None (ONANN_S + 16) (ONANN_S + 20) 0 0
    [YP09.mkChunk (ONANN_S + 16) (YP09.CVal 4 (SOff 32 0))].
Definition WK_R_sh : YP09.region :=
  YP09.mkRegion None WK_SH (WK_SH + 1) 0 0 [YP09.mkChunk WK_SH (YP09.CVal 1 (SLit 0))].
Definition WK_R_now : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 33 0))].
Definition WK_FACTS : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
(* s4 = s and s8 = the shadow base are pinned as literals, so the instrumented check's address is a numeral. *)
Definition WK_REGS : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_wk : sstate := mkSS ONANN_WK WK_REGS [WK_R_gs; WK_R_sh; WK_R_now] None WK_FACTS.
(* After the call returns: one `j` to the cut, from a state with no region. *)
Definition ss_wk3 : sstate := mkSS WK_C3 sr_atoms [] None (mkFacts [] [] []).

(* The own class-4 frame is not of class WAKE_CID, so the call's count is the walk's. *)
Lemma wk_count : forall p l, count_cid WAKE_CID ((ONANN_CID, p) :: l) = count_cid WAKE_CID l.
Proof. intros p l. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. Arithmetic of the two tests                                      *)
(* ------------------------------------------------------------------ *)

(* A byte of the shadow read as 0 is a stored 0. *)
Lemma wk_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* `bnez a0` / `beqz a0` on a sign-extended 4-byte field: the model's = 0 test. *)
Lemma wk_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma wk_state_range : forall Bx, - 2 ^ 31 <= TW.S_state Bx < 2 ^ 31.
Proof.
intros Bx. pose proof (bv_swrap_in_range 32 (TW.u_at Bx TW.A_S_state 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bx TW.A_S_state 4)) with (TW.S_state Bx) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

Lemma wk_awake_range : forall Bx, - 2 ^ 31 <= TW.S_cfg_auto_wake Bx < 2 ^ 31.
Proof.
intros Bx. pose proof (bv_swrap_in_range 32 (TW.u_at Bx TW.A_S_cfg_auto_wake 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bx TW.A_S_cfg_auto_wake 4)) with (TW.S_cfg_auto_wake Bx) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

Lemma wk_awake_off : TW.A_S_cfg_auto_wake = TW.OFF_g_s + 16.
Proof. reflexivity. Qed.

(* The sign-extended 4-byte load of g_s.cfg.auto_wake is the model's S_cfg_auto_wake. *)
Lemma wk_sext : forall E Bx, ew E 32 = Z_to_bv 64 (TW.u_at Bx TW.A_S_cfg_auto_wake 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_cfg_auto_wake Bx).
Proof.
intros E Bx H. pose proof (TWL.u_at_range Bx TW.A_S_cfg_auto_wake 4) as R.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
cbn [sv_denot]. rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The model after the two tests                                    *)
(* ------------------------------------------------------------------ *)

Lemma wk_model_keep : forall TF (B4 Bw' : list byte) now,
  onann_k_wk timg_A TF B4 now = Some (Bw', tt) ->
  (TW.S_state B4 <> TS0.DIGINET_S_IDLE \/ TW.S_cfg_auto_wake B4 = 0) -> Bw' = B4.
Proof.
intros TF B4 Bw' now Hm Hd. unfold onann_k_wk in Hm.
assert (Hc : ((TW.S_state B4 =? TS0.DIGINET_S_IDLE) && negb (TW.S_cfg_auto_wake B4 =? 0))%bool = false).
{ destruct Hd as [H | H].
  - rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
  - rewrite H, Z.eqb_refl. cbn [negb]. apply andb_false_r. }
rewrite Hc in Hm. cbv iota in Hm. exact (eq_sym (onann_some_inv _ _ Hm)).
Qed.

Lemma wk_model_call : forall TF (B4 Bw' : list byte) now,
  onann_k_wk timg_A TF B4 now = Some (Bw', tt) ->
  TW.S_state B4 = TS0.DIGINET_S_IDLE -> TW.S_cfg_auto_wake B4 <> 0 ->
  exists r', TSS.diginet_session_wake_m timg_A TF B4 now = Some (Bw', r').
Proof.
intros TF B4 Bw' now Hm Hst Haw. unfold onann_k_wk in Hm.
rewrite Hst, Z.eqb_refl in Hm. rewrite (proj2 (Z.eqb_neq _ _) Haw) in Hm. cbn [negb andb] in Hm.
destruct (TSS.diginet_session_wake_m timg_A TF B4 now) as [[B5 r']|] eqn:E; [|discriminate Hm].
exists r'. rewrite (onann_some_inv B5 Bw' Hm). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The written range lies in G                                      *)
(* ------------------------------------------------------------------ *)

Lemma wk_inG_row : forall o bb n a, In (o, bb, n) TMAP_A -> bb <= a < bb + n -> inG TG.G_HARNESS a.
Proof.
intros o bb n a Hin Ha. unfold inG. apply Exists_exists. exists (bb, n).
split; [exact (TMAP_A_in_G o bb n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma wk_inG_gs : forall a, TA_g_s <= a < TA_g_s + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_g_s Ha). Qed.
Lemma wk_inG_GOT : forall a, TA_GOT <= a < TA_GOT + TW.SZ_GOT -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_GOT Ha). Qed.
Lemma wk_inG_M : forall a, TA_M <= a < TA_M + TW.SZ_M -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_M Ha). Qed.
Lemma wk_inG_fn : forall a, TA_g_fail_next <= a < TA_g_fail_next + 1 -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_g_fail_next Ha). Qed.
Lemma wk_inG_lc : forall a, TA_g_last_counter <= a < TA_g_last_counter + TW.SZ_g_last_counter ->
  inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_g_last_counter Ha). Qed.
Lemma wk_inG_cmd : forall a, TA_g_cmd <= a < TA_g_cmd + TW.SZ_g_cmd -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_g_cmd Ha). Qed.
Lemma wk_inG_q : forall a, TA_g_q <= a < TA_g_q + TW.SZ_g_q -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_g_q Ha). Qed.
Lemma wk_inG_nq : forall a, TA_g_nq <= a < TA_g_nq + TW.SZ_g_nq -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (wk_inG_row _ _ _ a TMAP_A_g_nq Ha). Qed.

(* Split every disjunction of a written range. *)
Ltac wk_or := repeat (match goal with HH : _ \/ _ |- _ => destruct HH as [HH | HH] end).
(* The field addresses and the globals' bases and sizes, as numerals. *)
Ltac wk_num := cbv [twa_fld TA_g_s TA_GOT TA_M TA_g_fail_next TA_g_last_counter TA_g_cmd TA_g_q TA_g_nq
  TW.OFF_g_s TW.SZ_g_s TW.OFF_GOT TW.SZ_GOT TW.OFF_M TW.SZ_M TW.OFF_g_fail_next
  TW.OFF_g_last_counter TW.SZ_g_last_counter TW.OFF_g_cmd TW.SZ_g_cmd TW.OFF_g_q TW.SZ_g_q
  TW.OFF_g_nq TW.SZ_g_nq
  TW.A_S_stats_rx_ignored TW.A_S_personality TW.A_S_foreign TW.A_S_e1_named_us TW.A_S_state
  TW.A_S_stats_refused TW.A_S_wake_acked TW.A_S_wake_sent_us TW.A_S_inflight_frame TW.A_S_inflight_len
  TW.A_S_stats_tx_wakes TW.A_S_inflight TW.A_S_inflight_counter TW.A_S_inflight_retries
  TW.A_S_inflight_sent_us TW.A_S_stats_tx_frames TW.A_S_next_keepalive_us
  TW.A_GOT_e2 TW.A_GOT_e3 TW.A_GOT_acks TW.A_GOT_n TW.A_GOT_t_state TW.GOT_t_ESZ
  TW.A_M_host_counter TW.A_M_next_ka TW.A_M_last_display TW.A_M_display_sent
  TW.A_M_fly_on TW.A_M_fly_cmd TW.A_M_fly_counter TW.A_M_fly_retries TW.A_M_fly_sent
  TW.A_M_fly_len TW.A_M_fly_frame TW.A_Cmd_st
  TC.SPEC_MAX_FRAME TC.CMDS_MAX TC.TRANS_MAX SENDCTL_F] in *.
(* A twa_fld of one of the eight globals. *)
Ltac wk_close :=
  first [ apply wk_inG_gs; wk_num; lia | apply wk_inG_GOT; wk_num; lia
        | apply wk_inG_M; wk_num; lia | apply wk_inG_fn; wk_num; lia
        | apply wk_inG_lc; wk_num; lia | apply wk_inG_cmd; wk_num; lia
        | apply wk_inG_q; wk_num; lia | apply wk_inG_nq; wk_num; lia ].

Lemma wk_io_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS a.
Proof.
intros n a H.
pose proof (Z.le_min_r n TC.SPEC_MAX_FRAME) as Hmin. pose proof (Z.le_min_l n TC.SPEC_MAX_FRAME) as Hmin2.
unfold iosend_wr in H. wk_or.
all: try (destruct H as (ss & Hss & H)).
all: wk_close.
Qed.

(* The state branch of wake_wr: g_s.state or an N_STATE notice's stores. *)
Lemma wk_wake_last : forall Bx a,
  (TW.S_state Bx <> TS0.DIGINET_S_WAKING /\
   (twa_fld TW.OFF_g_s TA_g_s TW.A_S_state 4 a \/ notice_wr Bx (wake_ntc Bx) a)) ->
  inG TG.G_HARNESS a.
Proof.
intros Bx a Hw. destruct Hw as (_ & [H | H]); [wk_close | exact (nt_wr_G Bx (wake_ntc Bx) a H)].
Qed.

Lemma wk_wake_wr_G : forall Bx a, wake_wr Bx a -> inG TG.G_HARNESS a.
Proof.
intros Bx a H. unfold wake_wr in H. wk_or.
all: first [ exact (wk_io_wr_G SENDCTL_F a H) | exact (wk_wake_last Bx a H) | wk_close ].
Qed.

Lemma wk_maybeon_wr_G : forall Bx a, maybeon_wr Bx a -> inG TG.G_HARNESS a.
Proof.
intros Bx a Hw. destruct Hw as (_ & H). wk_or.
all: first [ wk_close
           | (destruct H as (_ & [H | H]);
              [wk_close | exact (nt_wr_G (maybeon_w2 Bx) (maybeon_ntc Bx) a H)]) ].
Qed.

(* Every byte the call stores is a byte of G. *)
Lemma wk_wr_G : forall (Bw b : list byte) a, onann_wr Bw b a -> inG TG.G_HARNESS a.
Proof.
intros Bw b a H. unfold onann_wr in H. wk_or.
all: first [ exact (nt_wr_G _ _ a H)
           | exact (sn_wr_G Bw TS0.DIGINET_R_DESK_OFFLINE a H)
           | exact (sn_wr_G Bw TS0.DIGINET_R_FOREIGN a H)
           | (destruct H as (Bx & H); exact (wk_wake_wr_G Bx a H))
           | exact (wk_maybeon_wr_G _ a H)
           | wk_close ].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Section wk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation: the 32 registers, g_s.cfg.auto_wake (atom 32) and now (atom 33). *)
Definition wk_E (regs : bvmap 5 word) (B4 : list byte) (now : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 (TW.u_at B4 TW.A_S_cfg_auto_wake 4); Z_to_bv 64 now]).

Lemma wk_ew_reg : forall regs B4 now n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (wk_E regs B4 now) n = YK11.getr regs r.
Proof. intros regs B4 now n r Hn. unfold wk_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma wk_ew_32 : forall regs B4 now,
  ew (wk_E regs B4 now) 32 = Z_to_bv 64 (TW.u_at B4 TW.A_S_cfg_auto_wake 4).
Proof.
intros regs B4 now. unfold wk_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs _ 0).
Qed.
Lemma wk_ew_33 : forall regs B4 now, ew (wk_E regs B4 now) 33 = Z_to_bv 64 now.
Proof.
intros regs B4 now. unfold wk_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs _ 1).
Qed.
Lemma wk_env_img : forall regs B4 now, img_env VAL A_LIM (wk_E regs B4 now).
Proof. intros regs B4 now. unfold wk_E. apply Eimg_env. Qed.
(* The denotation of a register atom and of now, stated so that `exact` goes through the valuation's name. *)
Lemma wk_dr : forall regs B4 now n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (wk_E regs B4 now) (SOff n 0) = YK11.getr regs r.
Proof.
intros regs B4 now n r Hn. cbn [sv_denot]. rewrite (wk_ew_reg regs B4 now n r Hn).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma wk_d33 : forall regs B4 now, 0 <= now < 2 ^ 64 ->
  sv_denot (wk_E regs B4 now) (SOff 33 0) = w64 now.
Proof.
intros regs B4 now Hn. cbn [sv_denot]. rewrite (wk_ew_33 regs B4 now), unsigned_lit_small, Z.add_0_r by lia.
reflexivity.
Qed.

(* The entry state at +0x518, before the two registers are pinned. *)
Lemma wk_entry0 : forall ly S (W : world segs) regs mem md B4 now sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B4 ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 0) = Some now ->
  st_ok_pi segs VAL (wk_E regs B4 now)
    (mkSS ONANN_WK sr_atoms [WK_R_gs; WK_R_sh; WK_R_now] None WK_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_WK)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
intros ly S W regs mem md B4 now sp1 HSC HAR Htw R9 Hsp Hsp32 Hnow Hslot.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := wk_E regs B4 now).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (wk_ew_reg regs B4 now 9%nat 9%bv eq_refl), R9; unfold w64;
      apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at B4 TW.A_S_cfg_auto_wake 4)) by (unfold E; apply wk_ew_32).
assert (E33 : ew E 33 = Z_to_bv 64 now) by (unfold E; apply wk_ew_33).
assert (R32 : 0 <= TW.u_at B4 TW.A_S_cfg_auto_wake 4 < 2 ^ 32).
{ pose proof (TWL.u_at_range B4 TW.A_S_cfg_auto_wake 4) as R.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. lia. }
assert (ZSH : val_mem segs (mrestrict (w_H W) mem) WK_SH 1 0).
{ apply wk_vm0.
  replace WK_SH with (FCells.shadow_addr (ONANN_S + 16)).
  - apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (ONANN_S + 16) HAR);
      [reflexivity | lia | unfold TW.SZ_g_s; lia | exact HSC].
  - unfold FCells.shadow_addr, FCells.ASAN_K, WK_SH, ONANN_S, TA_g_s.
    replace (6158784 + 16) with (769850 * 8) by lia. rewrite Z.div_mul by lia. lia. }
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks WK_R_gs WK_R_sh WK_R_now base_val].
  + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 (ONANN_S + 16) 4 (SOff 32 0) (TW.u_at B4 TW.A_S_cfg_auto_wake 4));
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity
      | exact R32 | lia |].
    replace (0 + (ONANN_S + 16)) with (TA_g_s + 16) by (unfold ONANN_S; lia).
    rewrite wk_awake_off.
    exact (tw_read_val segs _ TMAP_A B4 TW.OFF_g_s TA_g_s TW.SZ_g_s 16 4 TMAP_A_ok Htw TMAP_A_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + split; [unfold WK_SH; lia|]. split; [unfold WK_SH; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 WK_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_l. exact ZSH.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 0 8 (SOff 33 0) now);
      [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
    exact (val_mem_of_rdword _ _ _ _ _ Hslot).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, WK_R_gs, WK_R_sh, WK_R_now.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold WK_SH, ONANN_S, TA_g_s in *. repeat split; first [exact I | lia].
- unfold WK_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hsp32; lia.
Qed.

Lemma wk_entry : forall ly S (W : world segs) regs mem md B4 now sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B4 ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 0) = Some now ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (wk_E regs B4 now) ss_wk
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_WK)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md B4 now sp1 HSC HAR Htw R9 Hsp Hsp32 Hnow Hslot R20 R24.
rewrite restrict_mkst_fx.
pose proof (wk_entry0 ly S W regs mem md B4 now sp1 HSC HAR Htw R9 Hsp Hsp32 Hnow Hslot) as H0.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
exact H2.
Qed.

(* The state at +0x544 (after the call), with no region. *)
Lemma wk_entry3 : forall (W : world segs) regs mem B4 now,
  st_ok_pi segs VAL (wk_E regs B4 now) ss_wk3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WK_C3)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem B4 now. rewrite restrict_mkst_fx. unfold ss_wk3.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The cut's facts at a later memory of the same view. *)
Lemma wk_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (Bw b : list byte) pos F
    ly2 S2 (W2 : world segs) mem2 md2 mem3 md3 e,
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  HCUR HJ3 KD GR.
destruct HCUR as (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL).
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros bb m i Hb Hi Hn. rewrite KD. exact (K2 bb m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

(* The read-only image bytes at the call state. *)
Lemma wk_rom_call : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  trans_rom_view_rd W memc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, trans_in_ro_rd a -> ~ E a) ->
  trans_rom_view_rd W2 mem2.
Proof.
intros HRU HRE lyc Sc W memc W2 mem2 slo shi E Hrom HKP HnE a Ha.
destruct HKP as (_ & _ & K3 & _).
rewrite <- (Hrom a Ha).
destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
unfold TG.G_HARNESS_LO in Gh. lia.
Qed.

(* The current heap frame at the call of diginet_session_wake: the own class-4 frame is on top of the call's frames,
   TF lies outside G (trans_tf_off_g), so the G placement of trans_src_ok cannot hold of a non-empty TF. *)
Lemma wk_tf_call : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 (regs regsC : bvmap 5 word)
    (TF : option TI.tframe) (Bw b : list byte) pos,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (ONANN_CID, pos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc -> ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) ->
  onann_apart TF Bw b -> trans_tf_off_g TF ->
  spZ regs - ONANN_STK <= spZ regsC - WAKE_STK -> spZ regsC <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs ONANN_STK TF ->
  trans_tframe_at B ly2 S2 W2 mem2 regsC WAKE_STK TF.
Proof.
intros LAWS0 HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 regs regsC TF Bw b pos
  HARc HAR2 Hfr Hbl ELF Elo Ehi Hstklt HKP Hap HTFG Hw1 Hw2 HT.
pose proof HKP as (K1 & K2 & K3 & K4 & K5 & K6).
destruct TF as [fr|]; [|exact I].
pose proof HT as (Ha0 & Hg8 & Hsrc & Hoff).
set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (HnE : forall a, q <= a < q + n -> ~ onann_wr Bw b a) by (intros a Ha Hx; exact (Hap a Hx fr eq_refl Ha)).
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; right; exact Hf).
assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha. destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS0 lyc Sc W memc mdc bA nA HARc HinA) as (_ & _ & _ & _ & _ & _ & Hn1).
    pose proof (req_size_pos nA (proj1 Hn1)) as [_ Hreq].
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) HinA ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
  - destruct HL as [(c & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
    + exfalso. exact (HTFG fr eq_refl a Ha (HG a Ha)).
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HARc) as [T1 T2].
      apply K1; [lia | unfold decode_off_win in Hoff; lia].
    + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
      apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
      intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
      unfold TG.G_HARNESS_LO in Gh. lia. }
assert (KS : forall c p s, In (c, p) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8) ->
   aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
{ intros c p s Hin Hs. apply (K4 c p s Hin (or_intror Hs)). intros Hw.
  pose proof (inG_G_HARNESS_hull s (wk_wr_G Bw b s Hw)) as Hl.
  destruct (frames_bounds segs B LAWS0 lyc Sc W memc mdc c p HARc Hin) as (F1 & F2 & _).
  pose proof (Z.div_pos (frame_addr lyc c p) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs. cbn [fst snd] in Hs.
  unfold shadow_addr, SHADOW_OFF, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
split; [exact Ha0|]. split.
{ eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview segs). apply KV. exact Ha. }
split.
2: { unfold decode_off_win in *. lia. }
destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & Hrd)].
- left. exists bA, nA. split; [exact (Hbl _ HinA) | lia].
- right. split.
  + destruct HL as [(c & p & Hin & F1 & F2) | [HG | [HS | HR]]].
    * left. exists c, p. rewrite !Efa. split; [exact (Hfin _ Hin) | lia].
    * right; left; exact HG.
    * right; right; left. rewrite Elo, Ehi. exact HS.
    * right; right; right; exact HR.
  + destruct (Z_lt_le_dec 0 n) as [Hn | Hn].
    * destruct HL as [HF | [(HGa & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      -- exact (decode_rd_ok_fake_kept B LAWS0 lyc Sc W W2 memc mem2 mdc q n HARc HF Hrd Hn KV KS).
      -- exfalso. exact (HTFG fr eq_refl q ltac:(lia) (HGa q ltac:(lia))).
      -- destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia)
                     ltac:(rewrite Ehi; lia)) as [Ha Hh].
         exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      -- destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
         exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
    * assert (En : n = 0) by lia.
      apply (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV); [intros x Hx; lia|].
      destruct HL as [(c & p & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      -- assert (Hin2 : In (c, p) (frames S2)) by exact (Hfin _ Hin).
         destruct (al_frames _ _ LAWS0 ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (_ & _ & _ & HFsh).
         destruct (TransportGCg.dkg_frame_al64 segs B ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (A1 & A2 & A3).
         destruct (frames_bounds segs B LAWS0 ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (G1 & G2 & _).
         destruct (Z_lt_le_dec q (frame_addr lyc c p + fs_frame_bytes c)) as [Hq | Hq].
         ++ apply (trans_hull_sub _ q 1 q n); [| lia | lia].
            apply (TransportGNotice.frame_hull_vis _ (frame_addr ly2 c p) (fs_frame_bytes c) q 1);
              [lia | exact A1 | exact A2 | rewrite Efa; lia | lia | rewrite Efa; lia |].
            intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
         ++ apply (trans_hull_sub _ (q - 1) 1 q n); [| lia | lia].
            apply (TransportGNotice.frame_hull_vis _ (frame_addr ly2 c p) (fs_frame_bytes c) (q - 1) 1);
              [lia | exact A1 | exact A2 | rewrite Efa; lia | lia | rewrite Efa; lia |].
            intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      -- exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
      -- destruct (Z_lt_le_dec q (ly_stk_hi ly2)) as [Hq | Hq].
         ++ destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
                        ltac:(lia)) as [_ Hh].
            exact (trans_hull_sub _ q 1 q n Hh ltac:(lia) ltac:(lia)).
         ++ destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 (q - 1) 1 HAR2 ltac:(lia)
                        ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia)) as [_ Hh].
            exact (trans_hull_sub _ (q - 1) 1 q n Hh ltac:(lia) ltac:(lia)).
      -- exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
Qed.

(* The awr obligation of a run whose regions write nothing. *)
Ltac wk_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exfalso;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* A register of the machine state of HS, named with its value v, closed by tac. *)
Ltac wk_vreg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "wk_vreg: no match for" T; fail
  end.
(* A register of the machine state of HS, from its value Q at the run's start. *)
Ltac wk_kreg HS rg bb nn r n Q H :=
  lazymatch type of Q with _ = ?v =>
    wk_vreg HS r v H ltac:(exact (eq_trans (wk_dr rg bb nn n r eq_refl) Q)) end.

(* After a run whose regions have no writable byte: every byte of the view is the run's, presence grows. *)
Ltac wk_after HS W KD GR mprev msF :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) =>
      rename mf into msF
  end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) mprev a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a;
    rewrite (aview_wrap64 tfibsegs (w_H W) (ms_mem msF) a), (aview_wrap64 tfibsegs (w_H W) mprev a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?Ex ?rs (mrestrict (w_H W) mprev) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      apply (kept_of_frame Ex rs (w_H W) mprev (ms_mem msF) (fun _ => False) HFx);
      [ let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
        let Hi := fresh "Hi" in let Hx := fresh "Hx" in
        intros bb wlo whi x Hi Hx;
        lazymatch type of Hi with
          In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hi end;
        cbn [In] in Hi;
        repeat (destruct Hi as [Hi | Hi]; [injection Hi as <- <- <-; cbn [base_val] in Hx; lia |]);
        destruct Hi
      | lia
      | intros [] ] end
  | ];
  assert (GR : forall a, apresent (w_H W) mprev a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) mprev) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

Lemma wk_holds : @onann_wk_stmt fx rc B MT.
Proof.
unfold onann_wk_stmt. intros NREL. unfold onann_wk_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F B4 ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof CALLEES as (ASM & LEAFP & PFROM & BCMP & MSET & NTCP & WAKE & MAYBEON & SETSH).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
  Hm & HTF & HTFG & Hrom & Hapart & Hri & Hc4 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof (proj1 HCUR) as CUR0.
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Htw4 & Hkwk & Hgf4 & Hri4 & Hslot).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R23) & R10 & R20 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof HJ1 as (_ & _ & (memS1 & HJi1 & _) & _). rewrite !Z.add_0_r in HJi1.
pose proof HJi1 as (_ & Hlyle1 & _). clear HJi1 memS1.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF0 & _ & _ & _ & ESLO0 & ESHI0 & _).
pose proof Hlyle1 as (_ & _ & _ & _ & _ & ELF1 & _ & _ & _ & ESLO1 & ESHI1 & _).
assert (ELF : ly_F ly2 = ly_F lyc) by (rewrite ELF1, <- ELF0; reflexivity).
assert (ELO : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite ESLO1, <- ESLO0; reflexivity).
assert (EHI : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite ESHI1, <- ESHI0; reflexivity).
assert (HE4 : ESTACK = 4096) by reflexivity.
assert (HWS : 4096 <= WAKE_STK).
{ unfold WAKE_STK, WAKE_FRAME, WAKE_ALIGN.
  pose proof (Z.le_max_l ESTACK (Z.max SENDCTL_STK NOTICE_STK)) as HM1. lia. }
assert (HSS : ONANN_STK = 208 + WAKE_STK) by reflexivity.
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO0, ESHI0; lia).
assert (EV0 : ONANN_EV = WAKE_EV) by reflexivity.
assert (EBWK : BASE + WK_C3 = 0x87fb8) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONANN_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HACE : alloc_ceiling <= sp1) by lia.
assert (Hsp1b : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF; reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof (wk_entry ly2 S2 W2 regs2 mem2 md2 B4 now sp1 HSC HAR2 Htw4 R9 Hsp1b (proj2 Hsp1) Hnow
  Hslot R20 R24) as HS.
set (E0 := wk_E regs2 B4 now) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply wk_env_img).
assert (SHOK : sh_ok segs WK_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 (TW.S_state B4))
  by exact (eq_trans (wk_dr regs2 B4 now 10%nat 10%bv eq_refl) R10).
assert (D32 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_cfg_auto_wake B4))
  by exact (wk_sext (wk_E regs2 B4 now) B4 (wk_ew_32 regs2 B4 now)).
pose proof HJ1 as HJ. clear HJ1.
psrr_branch_tok RUN BR HS SHOK WK_B0.
- (* +0x518 taken: the state is not S_IDLE; the model keeps B4 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (wk_eqb0 _ (wk_state_range B4)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (EBw' : Bw' = B4) by exact (wk_model_keep TF B4 Bw' now Hkwk (or_introl Hc)).
  paj_run_to_tok RUNTO HS HJ SHOK WK_B0 ONANN_NREL.
  { wk_awr. }
  wk_after HS W2 KD GR mem2 msF.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 2) 2%nat R2 Y2.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 3) 3%nat R3 Y3.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 4) 4%nat R4 Y4.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 8) 8%nat R8 Y8.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 9) 9%nat R9 Y9.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 18) 18%nat R18 Y18.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 19) 19%nat R19 Y19.
  wk_kreg HS regs2 B4 now (Z_to_bv 5 23) 23%nat R23 Y23.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
  apply (NREL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 (ms_mem msF) _ 0 (ms_regs msF) HFIX).
  + refine (conj (wk_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2
      (ms_mem msF) _ 0 CUR0 ltac:(first [exact HJ | rewrite Z.add_0_r; exact HJ]) KD GR) (conj _ _)).
    * rewrite EBw'. apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw4 | intros x _; exact (KD x)].
    * rewrite EBw'. exact Hgf4.
  + unfold onann_regs_rel, onann_regs_base.
    exact (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y19)))))) Y23).
- (* +0x518 not taken: the state is S_IDLE *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (wk_eqb0 _ (wk_state_range B4)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into Hidle.
  (* +0x51c .. +0x530: the checked load of g_s.cfg.auto_wake; the run stops at `beqz a0` *)
  paj_run_tok RUN HS HJ SHOK WK_B0.
  { wk_awr. }
  set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
  assert (KA1 : forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
  { intros a. rewrite (aview_wrap64 tfibsegs (w_H W2) (ms_mem ms) a), (aview_wrap64 tfibsegs (w_H W2) mem2 a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| lia | intros []].
    intros bb wlo whi x Hi Hx.
    lazymatch type of Hi with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hi end.
    cbn [In] in Hi.
    repeat (destruct Hi as [Hi | Hi]; [injection Hi as <- <- <-; cbn [base_val] in Hx; lia |]). destruct Hi. }
  assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK WK_B0.
  + (* auto_wake = 0: the model keeps B4 *)
    cbn [branch_taken] in Hc. rewrite D32 in Hc.
    change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (wk_eqb0 _ (wk_awake_range B4)) in Hc. apply Z.eqb_eq in Hc.
    assert (EBw' : Bw' = B4) by exact (wk_model_keep TF B4 Bw' now Hkwk (or_intror Hc)).
    paj_run_to_tok RUNTO HS HJ SHOK WK_B0 ONANN_NREL.
    { wk_awr. }
    wk_after HS W2 KD2 GR2 (ms_mem ms) msF.
    assert (KD : forall a, aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a)
      by (intros a; rewrite (KD2 a); exact (KA1 a)).
    assert (GR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
      by (intros a Ha; exact (GR2 a (GA1 a Ha))).
    wk_kreg HS regs2 B4 now (Z_to_bv 5 2) 2%nat R2 Y2.
    wk_kreg HS regs2 B4 now (Z_to_bv 5 3) 3%nat R3 Y3.
    wk_kreg HS regs2 B4 now (Z_to_bv 5 4) 4%nat R4 Y4.
    wk_kreg HS regs2 B4 now (Z_to_bv 5 8) 8%nat R8 Y8.
    wk_kreg HS regs2 B4 now (Z_to_bv 5 9) 9%nat R9 Y9.
    wk_kreg HS regs2 B4 now (Z_to_bv 5 18) 18%nat R18 Y18.
    wk_kreg HS regs2 B4 now (Z_to_bv 5 19) 19%nat R19 Y19.
    wk_kreg HS regs2 B4 now (Z_to_bv 5 23) 23%nat R23 Y23.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
    apply (NREL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
      pos sp1 F ly2 S2 W2 (ms_mem msF) _ 0 (ms_regs msF) HFIX).
    * refine (conj (wk_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2
        (ms_mem msF) _ 0 CUR0 ltac:(first [exact HJ | rewrite Z.add_0_r; exact HJ]) KD GR) (conj _ _)).
      -- rewrite EBw'. apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw4 | intros x _; exact (KD x)].
      -- rewrite EBw'. exact Hgf4.
    * unfold onann_regs_rel, onann_regs_base.
      exact (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y19)))))) Y23).
  + (* auto_wake <> 0: the call of diginet_session_wake *)
    cbn [branch_taken] in Hc. rewrite D32 in Hc.
    change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (wk_eqb0 _ (wk_awake_range B4)) in Hc. apply Z.eqb_neq in Hc.
    destruct (wk_model_call TF B4 Bw' now Hkwk Hidle Hc) as (rr & Hwm).
    (* +0x538 .. +0x540: a0 = s, a1 = now, `jal diginet_session_wake` *)
    paj_run_tok RUN HS HJ SHOK WK_B0.
    { wk_awr. }
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
    assert (KA2 : forall a, aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) mem2 a).
    { intros a. rewrite <- (KA1 a).
      rewrite (aview_wrap64 tfibsegs (w_H W2) (ms_mem ms0) a), (aview_wrap64 tfibsegs (w_H W2) (ms_mem ms) a).
      pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
      apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| lia | intros []].
      intros bb wlo whi x Hi Hx.
      lazymatch type of Hi with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hi end.
      cbn [In] in Hi.
      repeat (destruct Hi as [Hi | Hi]; [injection Hi as <- <- <-; cbn [base_val] in Hx; lia |]). destruct Hi. }
    assert (GA2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms0) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
    clear HF HFr HG.
    wk_kreg HS regs2 B4 now (2%bv : bv 5) 2%nat R2 T2.
    wk_kreg HS regs2 B4 now (3%bv : bv 5) 3%nat R3 T3.
    wk_kreg HS regs2 B4 now (4%bv : bv 5) 4%nat R4 T4.
    wk_kreg HS regs2 B4 now (8%bv : bv 5) 8%nat R8 T8.
    wk_kreg HS regs2 B4 now (9%bv : bv 5) 9%nat R9 T9.
    wk_kreg HS regs2 B4 now (18%bv : bv 5) 18%nat R18 T18.
    wk_kreg HS regs2 B4 now (19%bv : bv 5) 19%nat R19 T19.
    wk_kreg HS regs2 B4 now (23%bv : bv 5) 23%nat R23 T23.
    wk_vreg HS (10%bv : bv 5) (w64 WAKE_S) T10 ltac:(reflexivity).
    wk_vreg HS (11%bv : bv 5) (w64 now) T11 ltac:(exact (wk_d33 regs2 B4 now Hnow)).
    wk_vreg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + WK_C3)) T1 ltac:(apply codeptr_val; exact HEI).
    assert (USPC : spZ (ms_regs ms0) = sp1)
      by (change (bv_unsigned (YK11.getr (ms_regs ms0) (2%bv : bv 5)) = sp1); rewrite T2; unfold w64;
          apply unsigned_lit_small; lia).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (@cfg_at fx sg (transport_sigma TS_diginet_session_wake) rg mm mdx) Q) end.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARN.
    assert (KCN : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem ms0)
      (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
    { destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
      split; [|split; [|split; [|split; [|split]]]].
      - intros a Ha Hw. rewrite KA2. exact (K1 a Ha Hw).
      - intros bb m i Hb Hi Hn. rewrite KA2. exact (K2 bb m i Hb Hi Hn).
      - intros a Hi HnG Hno Hne. rewrite KA2. exact (K3 a Hi HnG Hno Hne).
      - intros cid pos0 a Hin0 Hr Hn. rewrite KA2. exact (K4 cid pos0 a Hin0 Hr Hn).
      - intros a Ha Hw Hp. apply GA2. exact (K5 a Ha Hw Hp).
      - intros a Ha. apply GA2. exact (K6 a Ha). }
    assert (HTWC : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms0)) B4)
      by (apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw4 | intros x _; exact (KA2 x)]).
    eapply SRr_bind.
    { exact (WAKE fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 (ms_mem ms0) md4 (k + 0)
        (ms_regs ms0) now rr TF B4 Bw'
        HJ
        ltac:(rewrite T1; apply (ret_ok_codeptr_v (PI := PI_transport)); rewrite wk_c3_num;
              [lia | reflexivity])
        ltac:(unfold raZ; rewrite T1, EBWK; rewrite unsigned_lit_small by lia; lia)
        ltac:(rewrite T3; exact Hgp) ltac:(rewrite T4; exact Htp) T10 T11
        ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
              rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
              apply Z.mod_mul; lia)
        ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) Hnow HTWC Hgf4 Hwm
        (wk_tf_call LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms0) md4 regs (ms_regs ms0) TF Bw b pos
           HARc HARN Hfrs Hbl ELF ELO EHI HSTKLT KCN Hapart HTFG ltac:(rewrite USPC; lia)
           ltac:(rewrite USPC; lia) HTF)
        HTFG
        (wk_rom_call HRU HRE lyc Sc W memc W2 (ms_mem ms0) (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)
           Hrom KCN ltac:(intros a Ha Hw; pose proof (inG_G_HARNESS_hull a (wk_wr_G Bw b a Hw)) as Gh;
                          pose proof (trans_ro_rd_bounds a Ha) as Rb; unfold TG.G_HARNESS_LO in Gh; lia))
        ltac:(intros x Hx; apply (Hapart x); right; right; right; right; right; left; exists B4; exact Hx)
        (proj1 Hri4) (proj1 (proj2 Hri4))
        ltac:(rewrite Hfrs, wk_count; exact Hc2)
        ltac:(rewrite EV0 in Hev; lia)). }
    intros W3 c3 _ HPOST.
    unfold transport_wake_post, transport_cg_post in HPOST. cbv beta in HPOST.
    destruct HPOST as (ly3 & S3 & regs3 & mem3 & md5 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
      HA03 & Htw3 & Hgf3).
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
    pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
    pose proof HJi3 as (_ & Hlyle3 & _). clear HJi3 memS3.
    pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
    assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, <- ELF0; reflexivity).
    assert (Hfrs3 : frames S3 = (ONANN_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
    assert (Hperm3c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc))
      by exact (Permutation_trans Hperm3 Hperm).
    destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 (ms_mem ms0) md4 ONANN_CID pos
      F (flag_addr lyc ONANN_CID pos) HARN Hfrs Hbl ELF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
    assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
      (onann_wr Bw b)).
    { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem ms0) W3 mem3
        (spZ regs - ONANN_STK) (spZ regs) (spZ (ms_regs ms0) - WAKE_STK) (spZ (ms_regs ms0))
        (onann_wr Bw b) (wake_wr B4) (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))).
      - lia.
      - lia.
      - exact Efa.
      - intros f Hf. rewrite Hfrs. right. exact Hf.
      - exact Hbl.
      - exact N1.
      - exact N3.
      - exact KCN.
      - exact HK3.
      - rewrite USPC. lia.
      - rewrite USPC. lia.
      - intros a Ha. left. right; right; right; right; right; left. exists B4. exact Ha. }
    (* +0x544: the `j` to the release cut, from a state with no region *)
    rewrite T1.
    pose proof (wk_entry3 W3 regs3 mem3 B4 now) as HS3.
    set (E3 := wk_E regs3 B4 now) in HS3.
    assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply wk_env_img).
    assert (SHOK3 : sh_ok segs WK_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
    paj_run_to_tok RUNTO HS3 HJ3 SHOK3 WK_B0 ONANN_NREL.
    { wk_awr. }
    wk_after HS3 W3 KD3 GR3 mem3 msF.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 2) 2%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 2))) Z2.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 3) 3%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 3))) Z3.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 4) 4%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 4))) Z4.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 8) 8%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 8))) Z8.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 9) 9%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 9))) Z9.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 18) 18%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 18))) Z18.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 19) 19%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 19))) Z19.
    wk_kreg HS3 regs3 B4 now (Z_to_bv 5 23) 23%nat (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 23))) Z23.
    assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms0) (Z_to_bv 5 n))
      by (intros n Hn; exact (HP3 n Hn)).
    pmkst HS3.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
    pose proof HK3 as (L1 & _ & _ & L4 & _).
    rewrite USPC in L1.
    assert (KSTK : forall a, sp1 <= a < spZ regs ->
      aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W2) mem2 a).
    { intros a Ha. refine (eq_trans (KD3 a) (eq_trans (L1 a _ _) (KA2 a))); lia. }
    assert (KFLG : forall i, 0 <= i < 8 ->
      aview segs (w_H W3) (ms_mem msF) (F + ONANN_FBYTES - 8 + i) =
      aview segs (w_H W2) mem2 (F + ONANN_FBYTES - 8 + i)).
    { intros i Hi.
      refine (eq_trans (KD3 (F + ONANN_FBYTES - 8 + i))
        (eq_trans (L4 ONANN_CID pos (F + ONANN_FBYTES - 8 + i) Hin _ _) (KA2 _))).
      - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa, <- EF.
        rewrite onann_fbytes. unfold ONANN_FBYTES in *. lia.
      - intros Hw. apply (N2 (F + ONANN_FBYTES - 8 + i));
          [left; rewrite onann_fbytes; unfold ONANN_FBYTES in *; lia|].
        exact (trans_g_img _ (wk_wake_wr_G B4 _ Hw)). }
    assert (HSo : forall o : Z * Z, In o ONANN_SAVED -> 8 <= fst o <= 104).
    { intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply (NREL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
      pos sp1 F ly3 S3 W3 (ms_mem msF) _ e3 (ms_regs msF) HFIX).
    * split; [|split].
      -- split; [replace (k + e3) with (k + 0 + e3) by lia; exact HJ3|].
         split; [rewrite EV0; exact He3|].
         split; [exact Hfrs3|].
         split; [exact Hperm3c|].
         split; [exact ELF3c|].
         split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
         split.
         ++ destruct KC3 as (M1 & M2 & M3 & M4 & M5 & M6).
            split; [|split; [|split; [|split; [|split]]]].
            ** intros a Ha Hw. rewrite KD3. exact (M1 a Ha Hw).
            ** intros bb m i Hb Hi Hn. rewrite KD3. exact (M2 bb m i Hb Hi Hn).
            ** intros a Hi HnG Hno Hne. rewrite KD3. exact (M3 a Hi HnG Hno Hne).
            ** intros cid pos0 a Hin0 Hr Hn. rewrite KD3. exact (M4 cid pos0 a Hin0 Hr Hn).
            ** intros a Ha Hw Hp. apply GR3. exact (M5 a Ha Hw Hp).
            ** intros a Ha. apply GR3. exact (M6 a Ha).
         ++ split.
            ** rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
               pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
            ** rewrite <- HFLw. apply rdword_ext. intros i Hi. exact (KFLG i Hi).
      -- apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3 | intros x _; exact (KD3 x)].
      -- exact Hgf3.
    * unfold onann_regs_rel, onann_regs_base.
      refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) _).
      -- exact (eq_trans Z2 (eq_trans (CH 2 ltac:(hnf; lia)) T2)).
      -- exact (eq_trans Z3 (eq_trans (CH 3 ltac:(hnf; lia)) T3)).
      -- exact (eq_trans Z4 (eq_trans (CH 4 ltac:(hnf; lia)) T4)).
      -- exact (eq_trans Z8 (eq_trans (CH 8 ltac:(hnf; lia)) T8)).
      -- exact (eq_trans Z9 (eq_trans (CH 9 ltac:(hnf; lia)) T9)).
      -- exact (eq_trans Z18 (eq_trans (CH 18 ltac:(hnf; lia)) T18)).
      -- exact (eq_trans Z19 (eq_trans (CH 19 ltac:(hnf; lia)) T19)).
      -- exact (eq_trans Z23 (eq_trans (CH 23 ltac:(hnf; lia)) T23)).
Qed.

End wk.

(* The wake piece of the walk of on_announce (OnannCut.v onann_wk_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onann_piece_wk : forall fx rc B MT, @onann_wk_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@wk_holds fx rc B MT). Qed.
