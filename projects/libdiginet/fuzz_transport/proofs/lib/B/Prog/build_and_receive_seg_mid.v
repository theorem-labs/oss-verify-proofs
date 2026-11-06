(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 697 of its 763 lines of code are new or changed and 1858 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/on_announce_seg_tail.v, with its module names changed; 1449 of its 1545 lines of code are new or changed and 667 lines of the source are left out. *)
(* build_and_receive_seg_mid: Theorem bar_mid_piece : forall fx rc B MT, @bar_mid_stmt fx rc B MT
   (lib/B/Prog/build_and_receive_segs.v), the mid piece of the image-B walk of build_and_receive
   (fuzz_transport.asan-ubsan 0x85998), from the cut BAR_MID (+0x178) to the cut BAR_CALL (+0x270). Image B's twin of
   lib/A/Prog/build_and_receive_seg_mid.v. The piece holds the caller's G journal with the own class-5 frame, at the
   entry world: it writes no byte of G. Runs of the position-abstract engine (lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x) and three intrinsic calls (TransportGCg.v gx_intrin_at):
     +0x178 .. +0x180  s5 = max (len, 30): `bltu a1, s3` with a1 = 30; both arms reach +0x184 (bm_at184);
     +0x184 .. +0x190  a2 = s5 + 24, a0 = F + 38, a1 = 0, `jal __asan_memset`: frame[6 .. n) = 0;
     +0x194 .. +0x1a0  a2 = 6, a0 = s9 = F + 32, a1 = s6 = dstp, `jal __asan_memcpy`: frame[0 .. 6) = dst;
     +0x1a4 .. +0x1b8  the UBSan test `bgeu s9, -6`, a0 = F + 38, a2 = 6, a1 = srcp (the slot s1 + 56),
                       `jal __asan_memcpy`: frame[6 .. 12) = src;
     +0x1bc .. +0x210  frame[12 .. 16) = 0x88, 0x5f and len + 16 big-endian with their five UBSan tests, a1 = 0,
                       `beqz s3` (to the cut when len = 0);
     +0x214 .. +0x220  a2 = (bodyp <> 0), a3 = a0 = bodyp, a4 = len, then the sum loop at +0x224 (bm_loop): the three
                       UBSan tests of a0 = bodyp + i, the check of the 1-byte load at a0 (a token of
                       lib/Reusable/YCbn.v, decided by the body's placement), the load at a3, a4 - 1, a0 + 1,
                       a1 + the byte, a3 + 1, `bnez a4`; the exit `j +0x270`.
   The nine UBSan branches to the trap word on this stretch are decided by the engine (YP0e.v decide_cond2) from the
   facts of the run's symbolic state, none taken:
     +0x1a8 `bgeu s9, -6`, +0x1c0 `bltu -13, s9`, +0x1d4 `beq s9 + 12, -1`, +0x1e4 `bltu -15, s9`,
     +0x1fc `beq s9 + 14, -1`, +0x208 `bltu -17, s9`: the fact 4096 <= s9 = F + 32 <= 2 ^ 47 on atom 25 (the own
       frame's bounds, YCbq.v frames_bounds: 4096 <= F, F + 2048 <= alloc_ceiling);
     +0x224 `bltu a0, s4`: the condition a0 >=u s4 of the loop state (bodyp + i >= bodyp, no wrap);
     +0x230 `beqz a5` (a5 = (s4 <> 0) xor (a0 = 0)): a2 = 1 and the fact 4096 <= a0 on atom 10 (a0 = 0 is false);
     +0x234 `beqz s4`: the fact 4096 <= s4 on atom 20;
   the loop's facts come from the body's trans_src_ok_place (4096 <= bodyp, bodyp + len <= 2 ^ 47), a bar_ok premise
   when 0 < len. Each intermediate state is stated once (bm_at184, bm_at194, bm_at1a4, bm_at1bc, bm_loop_at) and
   proved from the next. The memory facts carried: bar_run and bar_slots (bm_st), kept by every step that changes
   only frame[0 .. 1514) and the runtime entries' window below sp1 (bm_run_keep); the frame bytes written so far, read
   through aview. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_cg io_send_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import build_and_receive_cg build_and_receive_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TNeed TNeedLink TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. receive's written range lies in G's hull, image bytes            *)
(* ------------------------------------------------------------------ *)

(* The bounds of a byte of one row twb_fld o b A n of a harness global: computed when every argument is closed, else
   (an array entry at an index) the row's address unfolded to the index (diginet_session_poll_seg_kit.v pwh_fld). *)
Ltac bmh_fld H :=
  lazymatch type of H with
  | twb_fld _ _ (TW.A_OW_t_state _) _ _ => unfold twb_fld, TW.A_OW_t_state, TW.OW_t_ESZ, TW.OFF_OW, TB_OW in H
  | twb_fld _ _ (TC.A_OW_dn_body _) _ _ => unfold twb_fld, TC.A_OW_dn_body, TW.OFF_OW, TB_OW in H
  | twb_fld _ _ (TW.A_Cmd_st _) _ _ => unfold twb_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TB_g_cmd in H
  | twb_fld _ _ (TW.A_S_queue_bytes _) _ _ =>
      unfold twb_fld, TW.A_S_queue_bytes, TW.S_queue_ESZ, TW.OFF_g_s, TB_g_s in H
  | twb_fld ?o ?b ?A ?n ?x =>
      let lo := eval vm_compute in (b + (A - o)) in
      let ln := eval vm_compute in n in
      change (lo <= x < lo + ln) in H
  end.

(* Each written-range predicate unfolded down to its rows; a notice's rows by TransportGNoticeB.v notice_wr_G
   (diginet_session_poll_seg_kit.v pwh_go, with receive's recv_wr). *)
Ltac bmh_go H :=
  lazymatch type of H with
  | _ \/ _ => let H1 := fresh "Hw" in let H2 := fresh "Hw" in destruct H as [H1 | H2]; [bmh_go H1 | bmh_go H2]
  | ex _ => let x := fresh "i" in let H1 := fresh "Hw" in destruct H as [x H1]; bmh_go H1
  | (_ <= _ < _) /\ _ => let H1 := fresh "Hb" in let H2 := fresh "Hw" in destruct H as [H1 H2]; bmh_go H2
  | _ /\ _ => let H2 := fresh "Hw" in destruct H as [_ H2]; bmh_go H2
  | notice_wr _ _ _ => exact (inG_G_HARNESS_hull _ (notice_wr_G _ _ _ H))
  | twb_fld _ _ _ _ _ =>
      bmh_fld H; unfold TC.TRANS_MAX, TW.OW_dn_N, TC.CMDS_MAX, TW.S_queue_N, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in *;
      lia
  | recv_wr _ _ => unfold recv_wr in H; bmh_go H
  | poll_wr _ => unfold poll_wr in H; bmh_go H
  | mrx_wr _ => unfold mrx_wr in H; bmh_go H
  | mtick_wr _ _ => unfold mtick_wr in H; bmh_go H
  | mlost_wr _ _ => unfold mlost_wr in H; bmh_go H
  | mset_st_wr _ _ _ => unfold mset_st_wr in H; bmh_go H
  | mset_wr _ _ => unfold mset_wr in H; bmh_go H
  | srx_wr _ _ => unfold srx_wr in H; bmh_go H
  | tick_wr _ _ => unfold tick_wr in H; bmh_go H
  | onann_wr _ _ _ => unfold onann_wr in H; bmh_go H
  | onack_wr _ _ _ => unfold onack_wr in H; bmh_go H
  | ondata_wr _ _ _ => unfold ondata_wr in H; bmh_go H
  | sstate_wr _ _ _ _ => unfold sstate_wr in H; bmh_go H
  | wake_wr _ _ => unfold wake_wr in H; bmh_go H
  | maybeon_wr _ _ => unfold maybeon_wr in H; bmh_go H
  | iosend_wr _ _ => unfold iosend_wr in H; bmh_go H
  | senddata_wr _ => unfold senddata_wr in H; bmh_go H
  end.

(* Every byte receive may store (recv_wr) lies in G's hull [G_HARNESS_B_LO, G_HARNESS_B_HI). *)
Lemma bm_wr_hull : forall bytes a, recv_wr bytes a -> TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI.
Proof. intros bytes a H. bmh_go H. Qed.

(* G's hull lies inside one loaded segment of the image (decided by vm_compute). *)
Lemma bm_hull_img : forall a, TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI -> in_img tfibsegs a.
Proof.
intros a Ha.
apply (decode_seg_covers_img [(TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO)] a).
- vm_compute. reflexivity.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* A one-byte cell read off its value (diginet_session_poll_seg_head.v ph_aview_of_val1). *)
Lemma bm_aview_of_val1 : forall H (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v HV Hv. pose proof (HV 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
lazymatch goal with |- context [?f v 1%nat 0%nat] => unfold f end.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. repeat rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.

(* The 13 saved words lie in [entry sp - 104, entry sp). *)
Lemma bm_saved_off : forall o, In o BAR_SAVED -> 8 <= fst o <= 104.
Proof.
intros o Ho. unfold BAR_SAVED in Ho. cbn [In] in Ho.
repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho.
Qed.

Lemma bm_estack : ESTACK = 4096 /\ ESTACK <= RECV_STK /\ BAR_STK = 208 + RECV_STK.
Proof.
split; [reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity | exact bar_stk_eq].
Qed.

Lemma bm_consts : SHADOW_OFF = 2147450880 /\ kLowShadowBeg = 2147446784 /\ kHighMemBeg = 17594333495296 /\
  kLowMemEnd = 2147450880 /\ kHighShadowEnd = 17594333495296.
Proof. repeat split; reflexivity. Qed.

Section kit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* ------------------------------------------------------------------ *)
(* 2. The frame, and bar_run carried                                    *)
(* ------------------------------------------------------------------ *)

(* The bytes the piece may change: frame[0 .. 1514) and the runtime entries' ESTACK window below sp1. *)
Definition bm_z (c : bar_ctx) (pos a : Z) : Prop :=
  (bar_F c pos + 32 <= a < bar_F c pos + 32 + 1514) \/ (bar_sp1 c - ESTACK <= a < bar_sp1 c).

(* The own frame at a state of bar_run: AR there, the frame live, 64-aligned, below the ceiling, in application
   memory, apart from the image, its bytes and its 256 shadow bytes present. *)
Lemma bm_frame : forall c pos S2 mem md,
  bar_rt B MT (cx_CTX c) -> bar_run B MT c pos S2 mem md ->
  @AR rc segs B (cx_lyc c) S2 (cx_W c) mem md /\ In (BAR_CID, pos) (frames S2) /\
  4096 <= bar_F c pos /\ bar_F c pos mod 64 = 0 /\ bar_F c pos + 2048 <= YM05.alloc_ceiling /\
  (bar_F c pos + 2048 <= kLowShadowBeg \/ kHighMemBeg <= bar_F c pos) /\
  in_app (bar_F c pos) 2048 /\
  (forall a, bar_F c pos <= a < bar_F c pos + 2048 -> ~ in_img segs a) /\
  (forall a, bar_F c pos <= a < bar_F c pos + 2048 -> apresent (w_H (cx_W c)) mem a) /\
  (forall i, 0 <= i < 256 -> apresent (w_H (cx_W c)) mem (shadow_addr (bar_F c pos) + i)).
Proof.
intros c pos S2 mem md HRT HRUN.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _).
destruct HRUN as ((HJ2 & _ & Hfrs & _) & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin : In (BAR_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (_ & HFapp & HFpres & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF64 & _ & _).
pose proof (fun a Ha => frm_img segs B LAWS _ _ _ _ _ BAR_CID pos a HAR2 Hin Ha) as HFimg.
change (fs_frame_bytes BAR_CID / 8) with 256 in HFsh.
change (fs_frame_bytes BAR_CID) with 2048 in HFapp, HFpres, HFc, HFimg.
change (frame_addr (cx_lyc c) BAR_CID pos) with (bar_F c pos) in *.
split; [exact HAR2|]. split; [exact Hin|]. split; [exact HF0|]. split; [exact HF64|]. split; [exact HFc|].
split; [destruct HFapp as (_ & [Hx | [Hx _]]); [left; exact Hx | right; exact Hx]|].
split; [exact HFapp|]. split; [exact HFimg|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
intros i Hi. exact (proj1 (HFsh i Hi)).
Qed.

(* bar_run carried over a step at the same state that changes only bytes of bm_z, with the journal at the new
   memory (diginet_session_poll_seg_kit.v pw_run_win, with the frame's bytes added to the window); the slot s1 + 24
   of bar_cur lies above sp1, outside bm_z. *)
Lemma bm_run_keep : forall c pos S2 mem2 md2 mem3 md3,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem2 md2 ->
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 (cx_W c) mem3 md3 (cx_k c + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ bm_z c pos a ->
     aview segs (w_H (cx_W c)) mem3 a = aview segs (w_H (cx_W c)) mem2 a) ->
  (forall a, apresent (w_H (cx_W c)) mem2 a -> apresent (w_H (cx_W c)) mem3 a) ->
  bar_run B MT c pos S2 mem3 md3.
Proof.
intros c pos S2 mem2 md2 mem3 md3 HRT HOK HRUN HJ3 KD GR.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & FFL & HGX & _).
pose proof (bar_ok_sp B MT c HOK) as (HARc & Hsp & Hce & _ & _ & _ & _ & _ & _ & Hsp1 & Hwin & _).
pose proof (bm_frame c pos S2 mem2 md2 HRT HRUN) as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & _ & HFimg & _).
destruct HRUN as (HCUR & Hab & Hmo & HGK & HSH0 & HSH2 & HPR).
destruct HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL & HS24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
pose proof bm_consts as (K1 & K2 & K3 & K4 & K5).
unfold bm_z in KD.
set (F := bar_F c pos) in *. set (SP := bar_SP c) in *. set (sp1 := bar_sp1 c) in *.
assert (HF8 : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8b : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (HK3 : acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_W c) mem3 (SP - BAR_STK) SP
  (recv_wr (bar_fr c))).
{ apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low G (cx_lyc c) (cx_Sc c) (cx_lyc c) S2 (cx_W c) (cx_memc c)
    (cx_mdc c) (cx_W c) mem2 md2 mem2 mem3 (SP - BAR_STK) SP BAR_CID pos F (flag_addr (cx_lyc c) BAR_CID pos)
    (recv_wr (bar_fr c)) (fun a => (F + 32 <= a < F + 32 + 1514) \/ (sp1 - ESTACK <= a < sp1)) HGX HARc HAR2 Hfrs
    (fun bm Hb => Permutation_in bm (Permutation_sym Hperm) Hb) HlyF eq_refl eq_refl FFL);
  [lia | lia | | exact HK | exact KD | exact GR].
  intros a Ha. cbv beta in Ha. destruct Ha as [Ha | Ha].
  - right; left; left. change (fs_frame_bytes BAR_CID) with 2048. lia.
  - left. lia. }
split; [|split; [exact Hab|split; [exact Hmo|split; [|split; [|split]]]]].
- split; [exact HJ3|]. split; [exact He|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HlyF|].
  split; [exact HMO|]. split; [exact HK3|].
  split; [|split].
  + rewrite Forall_forall in HSV |- *. intros o Ho. rewrite <- (HSV o Ho).
    pose proof (bm_saved_off o Ho) as Hob.
    apply rdword_ext. intros k Hk. apply KD; [lia|]. intros [Hx | Hx]; lia.
  + rewrite <- HFL. apply rdword_ext. intros k Hk. apply KD; [unfold BAR_FBYTES; lia|].
    unfold BAR_FBYTES. intros [Hx | Hx]; lia.
  + refine (eq_trans _ HS24). apply rdword_ext. intros k Hk. apply KD; [lia|]. intros [Hx | Hx]; lia.
- intros a Ha. rewrite <- (HGK a Ha).
  pose proof (inG_low segs B transportb_segs_low G a HGX Ha) as Hl.
  apply KD; [lia|]. intros [Hx | Hx]; [exact (HFimg a ltac:(lia) (proj1 (HGX a Ha))) | lia].
- intros i Hi. rewrite KD; [exact (HSH0 i Hi) | lia |].
  intros [Hx | Hx]; [destruct HappD as [HD | HD]; lia | lia].
- rewrite KD; [exact HSH2 | lia |].
  intros [Hx | Hx]; [destruct HappD as [HD | HD]; lia | lia].
- intros a Ha Hp. exact (GR a (HPR a Ha Hp)).
Qed.

(* bar_slots carried over the same step: the four slots lie in [sp1 + 32, sp1 + 64). *)
Lemma bm_slots_keep : forall c pos mem2 mem3, bar_ok B MT c ->
  bar_F c pos + 2048 <= YM05.alloc_ceiling ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ bm_z c pos a ->
     aview segs (w_H (cx_W c)) mem3 a = aview segs (w_H (cx_W c)) mem2 a) ->
  bar_slots c (cx_W c) mem2 -> bar_slots c (cx_W c) mem3.
Proof.
intros c pos mem2 mem3 HOK HFc KD (S32 & S40 & S48 & S56).
pose proof (bar_ok_sp B MT c HOK) as (_ & Hsp & Hce & _ & _ & _ & _ & _ & _ & Hsp1 & Hwin & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
unfold bm_z in KD.
assert (KS : forall o, 32 <= o <= 56 -> forall k, 0 <= k < 8 ->
  aview segs (w_H (cx_W c)) mem3 (bar_sp1 c + o + k) = aview segs (w_H (cx_W c)) mem2 (bar_sp1 c + o + k)).
{ intros o Ho k Hk. apply KD; [lia|]. intros [Hx | Hx]; lia. }
split; [|split; [|split]].
- rewrite <- S32. apply rdword_ext. intros k Hk. exact (KS 32 ltac:(lia) k Hk).
- rewrite <- S40. apply rdword_ext. intros k Hk. exact (KS 40 ltac:(lia) k Hk).
- rewrite <- S48. apply rdword_ext. intros k Hk. exact (KS 48 ltac:(lia) k Hk).
- rewrite <- S56. apply rdword_ext. intros k Hk. exact (KS 56 ltac:(lia) k Hk).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The ranges the intrinsics read and write                        *)
(* ------------------------------------------------------------------ *)

(* The body's length bound: the model premise rules SPEC_MAX_BODY < len out (bar_body_bound). *)
Lemma bm_len : forall c, bar_ok B MT c -> 0 <= bar_len (cx_body c) <= 1484.
Proof.
intros c HOK.
destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _).
pose proof (bar_body_bound _ _ _ _ _ _ _ _ HM) as Hb. rewrite (proj1 bar_max_body) in Hb.
unfold bar_len in *. lia.
Qed.

(* diginet_session_poll_seg_kit.v pw_src_ok_kept with G's bytes kept by gx_kept (a range a caller passes may be a
   range of G), and the written range E inside G's hull (so no block, frame or shadow byte is written). *)
Lemma bm_src_kept : trans_ro_rd_unowned B -> trans_rom_no_errno B -> AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc -> ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  gx_kept segs G W memc W2 mem2 ->
  (forall a, E a -> TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
intros HRU HRE LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hbl Hfr Hfa Elo Ehi Hstk
  (K1 & K2 & K3 & K4 & _) HGK HEG Hoff Hs Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGH : TG.G_HARNESS_B_HI <= kLowMemEnd) by (unfold TG.G_HARNESS_B_HI; rewrite C5; lia).
assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
   aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
{ intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). intros HE.
  pose proof (HEG s HE) as Hh.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs'. cbn [fst snd] in Hs'.
  unfold shadow_addr, SHADOW_OFF in Hs'. rewrite C5 in HGH. lia. }
assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. intros HE.
    exact (blk_img segs B LAWS lyc Sc W memc mdc bA nA a HAR Hin ltac:(lia) (bm_hull_img a (HEG a HE))).
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|]. intros HE.
      exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia) (bm_hull_img a (HEG a HE))).
    + exact (HGK a (HG a Ha)).
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
    + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
      apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
      intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
      unfold TG.G_HARNESS_B_LO in Gh. lia. }
split; [|exact KV].
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
{ left. exists bA, nA. split; [exact (Hbl _ Hin) | lia]. }
assert (Hrd2 : decode_rd_ok W2 mem2 q n).
{ destruct (Z.eq_dec n 0) as [En | Hn0].
  - subst n. destruct Hrd as (_ & _ & _ & R4 & R5 & R6).
    assert (HH : shadow_hull_vis (aview segs (w_H W2) mem2) q 0).
    { destruct HL as [(cid & pos & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - assert (Hin2 : In (cid, pos) (frames S2)) by exact (Hfr _ Hin).
        destruct (dkg_frame_al64 segs B ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (A1 & A2 & A3).
        destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & _ & HSh).
        destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (G1 & G2 & _).
        rewrite Hfa in A1, HSh, G1, G2.
        set (x := if q <? frame_addr lyc cid pos + fs_frame_bytes cid then q else q - 1).
        assert (Hx : frame_addr lyc cid pos <= x /\ x + 1 <= frame_addr lyc cid pos + fs_frame_bytes cid /\
                     x <= q /\ q <= x + 1).
        { unfold x. destruct (Z.ltb_spec q (frame_addr lyc cid pos + fs_frame_bytes cid)); lia. }
        apply (trans_hull_sub _ x 1 q 0); [|lia|lia].
        apply (TGNA.frame_hull_vis _ (frame_addr lyc cid pos) (fs_frame_bytes cid) x 1); try lia.
        intros i Hi. apply aview_some_of_apresent. exact (proj1 (HSh i Hi)).
      - exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
      - set (x := if ly_stk_lo lyc <? q then q - 1 else q).
        assert (Hx : ly_stk_lo lyc <= x /\ x + 1 <= ly_stk_hi lyc /\ x <= q /\ q <= x + 1).
        { unfold x. destruct (Z.ltb_spec (ly_stk_lo lyc) q); lia. }
        apply (trans_hull_sub _ x 1 q 0); [|lia|lia].
        exact (proj2 (stack_zshadow_ra B ly2 S2 W2 mem2 md2 x 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
          ltac:(rewrite Ehi; lia))).
      - exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)). }
    split; [intros a Ha; lia|]. split; [intros x Hx; lia|]. split; [exact HH|]. exact (conj R4 (conj R5 R6)).
  - assert (Hnp : 0 < n) by lia.
    destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
    + apply (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hnp KV).
      intros cid pos s Hin Hs'. exact (KS cid pos s Hin Hs').
    + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
    + destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hnp ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
        as [Ha Hh].
      exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
    + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh). }
exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hfr Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* A range a caller passes (dst, src, body), at a state of bar_run: readable there with the call's views, apart
   from the own frame and from the runtime entries' window below sp1, and in [4096, 2 ^ 47). *)
Lemma bm_src : forall c pos S2 mem md q n,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem md ->
  trans_src_ok B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) q n -> decode_off_win (cx_regs c) BAR_STK q n ->
  0 < n ->
  decode_rd_ok (cx_W c) mem q n /\
  (forall a, q <= a < q + n -> aview segs (w_H (cx_W c)) mem a = aview segs (w_H (cx_W c)) (cx_memc c) a) /\
  (q + n <= bar_F c pos \/ bar_F c pos + 2048 <= q) /\
  (q + n <= bar_sp1 c - ESTACK \/ bar_sp1 c <= q) /\
  4096 <= q /\ q + n <= 2 ^ 47.
Proof.
intros c pos S2 mem md q n HRT HOK HRUN Hs Hoff Hn.
pose proof HRT as (_ & _ & _ & _ & HRU & HRE & LAWS & _).
pose proof (bar_ok_sp B MT c HOK) as (HARc & Hsp & Hce & _ & _ & _ & Hlo & Hhi & _ & Hsp1 & Hwin & _).
pose proof (bm_frame c pos S2 mem md HRT HRUN) as (HAR2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
assert (HSTKLT : ly_stk_lo (cx_lyc c) < ly_stk_hi (cx_lyc c)).
{ pose proof HOK as (HJc & _).
  pose proof HJc as (_ & _ & (memSc & HJic & _) & _). rewrite !Z.add_0_r in HJic.
  pose proof HJic as (_ & Hlylec & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hlylec as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO & ESHI & _).
  pose proof Hstk as (_ & _ & _ & Hslo & Hshi & _).
  rewrite ESLO, ESHI. lia. }
destruct HRUN as ((HJ2 & _ & Hfrs & Hperm & _ & _ & HK & _) & _ & _ & HGK & _).
destruct (bm_src_kept HRU HRE LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_lyc c) S2 (cx_W c) mem md
  (bar_SP c - BAR_STK) (bar_SP c) (recv_wr (bar_fr c)) q n HARc HAR2
  (fun bm Hb => Permutation_in bm (Permutation_sym Hperm) Hb)
  (fun f Hf => ltac:(rewrite Hfrs; right; exact Hf))
  (fun cid p => eq_refl) eq_refl eq_refl HSTKLT HK HGK (fun a Ha => bm_wr_hull _ a Ha) Hoff Hs ltac:(lia))
  as [Hs2 KV].
pose proof (trans_src_ok_rd B LAWS (cx_lyc c) S2 (cx_W c) mem md q n HAR2 Hs2 Hn) as HRD.
pose proof (trans_src_ok_disj_own B LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_lyc c) S2
  (cx_W c) mem md BAR_CID pos q n HARc HAR2 Hfrs Hperm (fun c0 p => eq_refl) Hs Hn) as HDJ.
change (frame_addr (cx_lyc c) BAR_CID pos) with (bar_F c pos) in HDJ.
change (fs_frame_bytes BAR_CID) with 2048 in HDJ.
pose proof (trans_src_ok_place B LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) q n HARc Hs Hn) as HPL.
unfold decode_off_win in Hoff. fold (bar_SP c) in Hoff.
split; [exact HRD|]. split; [exact KV|]. split; [exact HDJ|].
split; [destruct Hoff as [Ho | Ho]; [left | right]; lia|].
destruct HPL as [HP | HP]; lia.
Qed.

(* frame[o .. o + n) as an intrinsic's destination, at a state of bar_run, called with sp = sp1: in the own frame
   (transport_twr_ok_g), application memory, its shadow addressable (bytes 4 .. 192 of the frame's shadow are 0, byte
   193 is 2) and its hull visible (diginet_session_poll_seg_kit.v pw_buf_at). *)
Lemma bm_dst : forall c pos S2 mem md (regs' : bvmap 5 word) o n,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem md -> spZ regs' = bar_sp1 c ->
  0 <= o -> 0 < n -> o + n <= 1514 ->
  0 <= bar_F c pos + 32 + o /\ bar_F c pos + 32 + o + n <= 2 ^ 63 /\
  transport_twr_ok_g segs B G (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_lyc c) S2
    ((BAR_CID, pos) :: cx_own c) (cx_W c) mem (spZ regs') (bar_F c pos + 32 + o) n /\
  amem_range (bar_F c pos + 32 + o) n /\
  range_addressable (aview segs (w_H (cx_W c)) mem) SHADOW_OFF (bar_F c pos + 32 + o) n /\
  (0 < n -> shadow_hull_vis (aview segs (w_H (cx_W c)) mem) (bar_F c pos + 32 + o) n).
Proof.
intros c pos S2 mem md regs' o n HRT HOK HRUN USP Ho Hn Hon.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _).
pose proof (bar_ok_sp B MT c HOK) as (_ & Hsp & Hce & _ & _ & _ & _ & _ & _ & Hsp1 & Hwin & _).
pose proof (bm_frame c pos S2 mem md HRT HRUN)
  as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & HFapp & HFimg & HFpres & HFsh).
destruct HRUN as ((HJ2 & _) & _ & _ & _ & HSH0 & HSH2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
set (F := bar_F c pos) in *.
assert (DF8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
  assert (M8 : F mod 8 = 0).
  { rewrite D. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  rewrite M8, Z.add_0_r in D8. exact D8. }
assert (HRA : range_addressable (aview segs (w_H (cx_W c)) mem) SHADOW_OFF (F + 32 + o) n).
{ intros x Hx. unfold shadow_of_addr.
  assert (Ex : x / 8 = F / 8 + (x - F) / 8).
  { replace x with (F / 8 * 8 + (x - F)) at 1 by lia. apply Z.div_add_l. lia. }
  rewrite Ex, Z.add_assoc.
  destruct (Z_lt_ge_dec x (F + 1544)) as [Hlt | Hge].
  - exists 0. split; [|left; reflexivity].
    apply HSH0. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  - assert (Eq : (x - F) / 8 = 193) by (symmetry; apply (Z.div_unique _ _ _ (x - F - 1544)); lia).
    rewrite Eq. exists 2. split; [exact HSH2|]. right.
    assert (Em : x mod 8 = x - F - 1544) by (symmetry; apply (Z.mod_unique _ _ (F / 8 + 193)); lia).
    rewrite Em. lia. }
assert (HH : shadow_hull_vis (aview segs (w_H (cx_W c)) mem) (F + 32 + o) n).
{ apply (TGNA.frame_hull_vis _ F 2048 (F + 32 + o) n); [lia | exact HF64 | reflexivity | lia | lia | lia |].
  intros i Hi. change (2048 / 8) with 256 in Hi. apply aview_some_of_apresent. exact (HFsh i Hi). }
split; [lia|]. split; [lia|].
split.
{ eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|].
  intros a Ha. left. split.
  - unfold awr_byte. right; right; right. unfold in_frames. exists BAR_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (frame_addr (cx_lyc c) BAR_CID pos) with F.
    change (fs_frame_bytes BAR_CID) with 2048. lia.
  - rewrite USP. lia. }
split; [apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia]|].
split; [exact HRA|]. intros _. exact HH.
Qed.

(* The source facts __asan_memcpy asks of a caller's 6-byte range at frame[d .. d + 6) (gx_intrin_at's OCpy
   clause), and the range's views, which are the call's. *)
Lemma bm_cpy_src : forall c pos S2 mem md q (regsT : bvmap 5 word) d,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem md ->
  trans_src_ok B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) q 6 -> decode_off_win (cx_regs c) BAR_STK q 6 ->
  spZ regsT = bar_sp1 c -> bar_F c pos <= d -> d + 6 <= bar_F c pos + 2048 ->
  (0 <= q /\ q + 6 <= 2 ^ 63 /\ src_ok segs (cx_W c) regsT mem q 6 /\ (d + 6 <= q \/ q + 6 <= d) /\
   amem_range q 6 /\ range_addressable (aview segs (w_H (cx_W c)) mem) SHADOW_OFF q 6 /\
   (0 < 6 -> shadow_hull_vis (aview segs (w_H (cx_W c)) mem) q 6)) /\
  (forall a, q <= a < q + 6 -> aview segs (w_H (cx_W c)) mem a = aview segs (w_H (cx_W c)) (cx_memc c) a).
Proof.
intros c pos S2 mem md q regsT d HRT HOK HRUN Hs Hoff USP Hd1 Hd2.
destruct (bm_src c pos S2 mem md q 6 HRT HOK HRUN Hs Hoff ltac:(lia))
  as ((Hvis & Hra & Hhull & Hamr & Hq0 & Hq63) & KV & HDJ & HWN & Hq4 & Hq47).
split; [|exact KV].
split; [exact Hq0|]. split; [exact Hq63|].
split; [intros a Ha; split; [exact (Hvis a Ha) | rewrite USP; lia]|].
split; [lia|]. split; [exact Hamr|]. split; [exact Hra | intros _; exact Hhull].
Qed.

End kit.

(* ------------------------------------------------------------------ *)
(* 4. The engine's kit                                                 *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac
   (diginet_session_poll_seg_head.v ph_reg). *)
Ltac bm_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "bm_reg: no match for" T; fail
  end.

(* The goal's getr of HS's machine state, rewritten to the denotation of its computed symbolic value. *)
Ltac bm_rv HS :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS) _)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      refine (eq_trans (st_ok_restrict_reg sg Hh Ex ssx msx _ HS) _)
  end;
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.

(* The low atoms of the current valuation are those of E0 (diginet_session_submit_seg_app.v ssw_low). *)
Ltac bm_low HS E0 HEX :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  end.

(* The write right of a run whose regions have no writable byte. *)
Ltac bm_awr_ro :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The windows a run wrote, each closed by tac. *)
Ltac bm_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Lemma bm_soff0 : forall E a v, ew E a = v -> sv_denot E (SOff a 0) = v.
Proof. intros E a v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma bm_soffk : forall E a k v, ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff a k) = Z_to_bv 64 (v + k).
Proof. intros E a k v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma bm_soffk_w : forall E a k v w, ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> w = v + k ->
  sv_denot E (SOff a k) = w64 w.
Proof. intros E a k v w H Hv ->. exact (bm_soffk E a k v H Hv). Qed.

(* The model a run leaves, named and opaque (diginet_session_submit_seg_app.v ssw_after_ro). *)
Ltac bm_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.

(* A register still its own atom n at the end of a run: its value at the run's start (G : getr regs rn = v). *)
Ltac bm_kreg HS r n rn G HEX EE H :=
  lazymatch type of G with YK11.getr _ _ = ?v =>
    bm_reg HS r v H ltac:(apply bm_soff0; rewrite ?HEX by lia; rewrite (EE n rn eq_refl); exact G) end.

(* The registers every cut keeps, read through bar_rg_run. *)
Definition BM_RGS : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27].

Ltac bm_same_rgs HS EE HEX :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold BM_RGS in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [bm_rv HS; apply bm_soff0; rewrite ?HEX by lia; apply EE; reflexivity |]);
  destruct Hr.

(* The bytes of a list at an address, read through aview. *)
Lemma bm_garr8_aview : forall H (m : word -> option byte) base l,
  garr8 tfibsegs (mrestrict H m) base l ->
  forall j, 0 <= j < Z.of_nat (length l) -> aview tfibsegs H m (base + j) = Some (nth (Z.to_nat j) l 0).
Proof.
intros H m base l HG j Hj. destruct (HG (Z.to_nat j) ltac:(lia)) as [Hv Hr].
rewrite Z2Nat.id in Hv by lia. exact (bm_aview_of_val1 H m _ _ Hv Hr).
Qed.

Lemma bm_garr8_of_aview : forall H (m : word -> option byte) base l,
  (forall j, (j < length l)%nat ->
     aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l Hl j Hj. destruct (Hl j Hj) as [Ha Hr].
split; [exact (YE2y.val_mem1_of_aview H m _ _ Ha) | exact Hr].
Qed.

Definition BM_B0 : Z * Z := (0, 0).

(* The shadow base s7 (x23), the base of every run's shadow entries. *)
Definition BM_Bx : sv := SOff 23 0.

Section mid. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition bm_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transportb) (Ereg regs extra).

Lemma bm_env_img : forall regs extra, img_env VAL A_LIM (bm_E regs extra).
Proof. intros regs extra. unfold bm_E. apply Eimg_env. Qed.

Lemma bm_ew_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (bm_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold bm_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma bm_ew_extra : forall regs extra j, (j < 200)%nat ->
  ew (bm_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
  intros regs extra j Hj. unfold bm_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

(* A state with no region and no fact, at any pc of the listing. *)
Lemma bm_entry_nil : forall pc regs extra mem (W : world segs),
  st_ok_pi segs VAL (bm_E regs extra) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros pc regs extra mem W. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- unfold facts_ok. cbn. tauto.
Qed.

(* bar_rg_run of a register file that agrees with one of bar_rg_run on BM_RGS. *)
Lemma bm_rg_of : forall c pos (regs regs' : bvmap 5 word), bar_rg_run B c pos regs ->
  (forall r, In r BM_RGS -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  bar_rg_run B c pos regs'.
Proof.
intros c pos regs regs' ((G2 & G3 & G4 & G8 & G9 & G18 & G23 & G25 & G26 & G27) & G19 & G20 & G24) HE.
refine (conj (conj (eq_trans (HE 2 _) G2) (conj (eq_trans (HE 3 _) G3) (conj (eq_trans (HE 4 _) G4)
  (conj (eq_trans (HE 8 _) G8) (conj (eq_trans (HE 9 _) G9) (conj (eq_trans (HE 18 _) G18)
  (conj (eq_trans (HE 23 _) G23) (conj (eq_trans (HE 25 _) G25) (conj (eq_trans (HE 26 _) G26)
  (eq_trans (HE 27 _) G27)))))))))) (conj (eq_trans (HE 19 _) G19) (conj (eq_trans (HE 20 _) G20)
  (eq_trans (HE 24 _) G24))));
  unfold BM_RGS; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* bar_rg_run across a call that preserves the callee-saved registers. *)
Lemma bm_rg_pres : forall c pos (regs regs' : bvmap 5 word), bar_rg_run B c pos regs ->
  aregs_preserved regs regs' -> bar_rg_run B c pos regs'.
Proof.
intros c pos regs regs' HRG HP. apply (bm_rg_of c pos regs regs' HRG).
intros r Hr. apply HP. unfold acallee_saved. unfold BM_RGS in Hr. cbn [In] in Hr. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The states the piece passes                                      *)
(* ------------------------------------------------------------------ *)

(* What every state of the piece carries: bar_run and the four slots. *)
Definition bm_st (c : bar_ctx) (pos : Z) (S2 : astate) (mem : word -> option byte) (md : Model) : Prop :=
  bar_run B MT c pos S2 mem md /\ bar_slots c (cx_W c) mem.

(* bm_st carried over a run of the engine whose windows lie in Zs, Zs inside bm_z: the bytes outside Zs kept. *)
Lemma bm_st_step : forall c pos S2 mem md mem' md' (E : env) rs (Zs : Z -> Prop),
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_st c pos S2 mem md ->
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 (cx_W c) mem' md' (cx_k c + 0) ->
  frame_of E rs (mrestrict (w_H (cx_W c)) mem) (mrestrict (w_H (cx_W c)) mem') ->
  mem_grows (mrestrict (w_H (cx_W c)) mem) (mrestrict (w_H (cx_W c)) mem') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  (forall a, Zs a -> bm_z c pos a) ->
  bm_st c pos S2 mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a ->
     aview segs (w_H (cx_W c)) mem' a = aview segs (w_H (cx_W c)) mem a).
Proof.
intros c pos S2 mem md mem' md' E rs Zs HRT HOK (HRUN & HSL) HJ HFr HG HW HZ.
pose proof (@kept_of_frame segs E rs (w_H (cx_W c)) mem mem' Zs HFr HW) as K.
assert (KZ : forall a, 0 <= a < 2 ^ 64 -> ~ bm_z c pos a ->
  aview segs (w_H (cx_W c)) mem' a = aview segs (w_H (cx_W c)) mem a)
  by (intros a Ha Hn; apply K; [exact Ha | intros Hz; exact (Hn (HZ a Hz))]).
pose proof (bm_frame B MT c pos S2 mem md HRT HRUN) as (_ & _ & _ & _ & HFc & _).
split; [split | exact K].
- exact (bm_run_keep B MT c pos S2 mem md mem' md' HRT HOK HRUN HJ KZ (fun a Ha => apresent_grows _ _ _ a HG Ha)).
- exact (bm_slots_keep B MT c pos mem mem' HOK HFc KZ HSL).
Qed.

(* bm_st carried over an intrinsic call from sp1 whose destination [d, d + n) lies in frame[0 .. 1514). *)
Lemma bm_st_call : forall c pos S2 memT mdT mem2 md2 d n,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_st c pos S2 memT mdT ->
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 (cx_W c) mem2 md2 (cx_k c + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) ->
     ~ (cx_sp0 c + (bar_sp1 c - cx_sp0 c) - ESTACK <= a < cx_sp0 c + (bar_sp1 c - cx_sp0 c)) ->
     aview segs (w_H (cx_W c)) mem2 a = aview segs (w_H (cx_W c)) memT a) ->
  (forall a, apresent (w_H (cx_W c)) memT a -> apresent (w_H (cx_W c)) mem2 a) ->
  bar_F c pos + 32 <= d -> d + n <= bar_F c pos + 32 + 1514 ->
  bm_st c pos S2 mem2 md2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (bar_sp1 c - ESTACK <= a < bar_sp1 c) ->
     aview segs (w_H (cx_W c)) mem2 a = aview segs (w_H (cx_W c)) memT a).
Proof.
intros c pos S2 memT mdT mem2 md2 d n HRT HOK (HRUN & HSL) HJ Heff Hgr Hd1 Hd2.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (bar_sp1 c - ESTACK <= a < bar_sp1 c) ->
  aview segs (w_H (cx_W c)) mem2 a = aview segs (w_H (cx_W c)) memT a)
  by (intros a Ha H1 H2; apply Heff; [exact Ha | exact H1 | intros Hx; apply H2; lia]).
assert (KZ : forall a, 0 <= a < 2 ^ 64 -> ~ bm_z c pos a ->
  aview segs (w_H (cx_W c)) mem2 a = aview segs (w_H (cx_W c)) memT a)
  by (intros a Ha Hn; apply K; [exact Ha | intros Hx; apply Hn; unfold bm_z; lia |
      intros Hx; apply Hn; unfold bm_z; lia]).
pose proof (bm_frame B MT c pos S2 memT mdT HRT HRUN) as (_ & _ & _ & _ & HFc & _).
split; [split | exact K].
- exact (bm_run_keep B MT c pos S2 memT mdT mem2 md2 HRT HOK HRUN HJ KZ Hgr).
- exact (bm_slots_keep B MT c pos memT mem2 HOK HFc KZ HSL).
Qed.

(* The regions of the run at +0x1a4 (the slot s1 + 56, srcp, as the extra atom 32) and of the run at +0x1bc
   (frame[12 .. 16) at s9 = F + 32, writable), and their facts: s1 32-aligned, s9 = F + 32 inside [4096, 2 ^ 47]
   and 32-aligned (the own frame's bounds; these decide the six UBSan tests of frame[] + k on the two runs). *)
Definition BM_RG_SRC : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition BM_RG_HDR : YP09.region := YP09.mkRegion (Some 25%nat) 12 16 12 16 [].
Definition BM_FACTS_S : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46 - 208) (2 ^ 47 - 192) 5); (25%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition BM_FACTS_H : facts := mkFacts [(25%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition bm_xs (c : bar_ctx) : list word := [w64 (cx_srcp c)].

Lemma bm_src_slot_ok : forall c (W : world segs) mem (E : env),
  bar_slots c W mem -> bv_unsigned (ew E 9) = bar_sp1 c -> 0 <= bar_sp1 c <= 2 ^ 47 ->
  ew E 32 = w64 (cx_srcp c) -> 0 <= cx_srcp c < 2 ^ 64 ->
  region_ok segs E (mrestrict (w_H W) mem) BM_RG_SRC.
Proof.
intros c W mem E (_ & _ & _ & S56) U9 Hsp E32 Hsr.
unfold BM_RG_SRC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val segs E _ (bar_sp1 c) 56 8 (SOff 32 0) (cx_srcp c));
  [apply bm_soff0; exact E32 | cbn; lia | cbn; lia |].
exact (YE2y.val_mem_of_rdword _ _ _ _ S56).
Qed.

Lemma bm_hdr_ok : forall c pos (W : world segs) mem (E : env),
  bv_unsigned (ew E 25) = bar_F c pos + 32 -> 0 <= bar_F c pos -> bar_F c pos + 2048 <= 2 ^ 47 ->
  (forall a, bar_F c pos <= a < bar_F c pos + 2048 -> apresent (w_H W) mem a) ->
  region_ok segs E (mrestrict (w_H W) mem) BM_RG_HDR.
Proof.
intros c pos W mem E U25 HF0 HFc Hpres.
unfold BM_RG_HDR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U25. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
Qed.

(* The entry of the run that reads the slot s1 + 56 (+0x1a4). *)
Lemma bm_entry_s : forall c pos S2 mem md (regs : bvmap 5 word) pc,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
  st_ok_pi segs VAL (bm_E regs (bm_xs c)) (mkSS pc sr_atoms [BM_RG_SRC] None BM_FACTS_S)
    (restrict (w_H (cx_W c)) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros c pos S2 mem md regs pc HRT HOK (HRUN & HSL) HRG.
pose proof (bar_ok_sp B MT c HOK) as (_ & Hsp & Hce & _ & _ & _ & _ & _ & Hsp1al & Hsp1 & Hwin & _).
pose proof (bm_frame B MT c pos S2 mem md HRT HRUN) as (_ & _ & HF0 & HF64 & HFc & _).
pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & HSS & HOS & _).
destruct (bm_src B MT c pos S2 mem md (cx_srcp c) 6 HRT HOK HRUN HSS HOS ltac:(lia)) as (_ & _ & _ & _ & Hs4 & Hs47).
pose proof HRG as ((_ & _ & _ & _ & G9 & _ & _ & G25 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := bm_E regs (bm_xs c)).
assert (E9 : ew E 9 = YK11.getr regs 9) by (apply bm_ew_reg; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = bar_sp1 c) by (rewrite E9, G9; apply unsigned_lit_small; lia).
assert (E25 : ew E 25 = YK11.getr regs 25) by (apply bm_ew_reg; reflexivity).
assert (U25 : bv_unsigned (ew E 25) = bar_F c pos + 32) by (rewrite E25, G25; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 (cx_srcp c)) by exact (bm_ew_extra regs (bm_xs c) 0 ltac:(lia)).
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  exact (bm_src_slot_ok c (cx_W c) mem E HSL U9 ltac:(lia) E32 ltac:(lia)).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold BM_FACTS_S, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U25. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The entry of the run that writes frame[12 .. 16) (+0x1bc). *)
Lemma bm_entry_h : forall c pos S2 mem md (regs : bvmap 5 word) pc,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
  st_ok_pi segs VAL (bm_E regs []) (mkSS pc sr_atoms [BM_RG_HDR] None BM_FACTS_H)
    (restrict (w_H (cx_W c)) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros c pos S2 mem md regs pc HRT HOK (HRUN & HSL) HRG.
pose proof (bm_frame B MT c pos S2 mem md HRT HRUN)
  as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & HFapp & HFimg & HFpres & HFsh).
pose proof HRG as ((_ & _ & _ & _ & _ & _ & _ & G25 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := bm_E regs []).
assert (E25 : ew E 25 = YK11.getr regs 25) by (apply bm_ew_reg; reflexivity).
assert (U25 : bv_unsigned (ew E 25) = bar_F c pos + 32) by (rewrite E25, G25; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  exact (bm_hdr_ok c pos (cx_W c) mem E U25 ltac:(lia) ltac:(lia) HFpres).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold BM_FACTS_H, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* frame[0 .. 6) = dst, frame[6 .. 12) = src, frame[lo .. n) = 0. *)
Definition bm_fdst (c : bar_ctx) (pos : Z) (mem : word -> option byte) : Prop :=
  forall j, 0 <= j < 6 ->
    aview segs (w_H (cx_W c)) mem (bar_F c pos + 32 + j) = Some (nth (Z.to_nat j) (TW.zs (cx_dst c)) 0).
Definition bm_fsrc (c : bar_ctx) (pos : Z) (mem : word -> option byte) : Prop :=
  forall j, 0 <= j < 6 ->
    aview segs (w_H (cx_W c)) mem (bar_F c pos + 38 + j) = Some (nth (Z.to_nat j) (TW.zs (cx_src c)) 0).
Definition bm_fzero (c : bar_ctx) (pos : Z) (lo : Z) (mem : word -> option byte) : Prop :=
  forall j, lo <= j < bar_N c -> aview segs (w_H (cx_W c)) mem (bar_F c pos + 32 + j) = Some 0.

(* +0x184: s5 = max (len, 30), before the memset. *)
Definition bm_at184 (c : bar_ctx) (pos : Z) (S2 : astate) : Prop :=
  forall mem md (regs : bvmap 5 word),
    bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
    YK11.getr regs 22 = w64 (cx_dstp c) -> YK11.getr regs 21 = w64 (bar_s8 (cx_body c)) ->
    SRr segs (cx_W c) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x184))) mem
      (YK11.seg_rom segs)) md) (bar_post B MT c).

(* +0x194: after the memset. *)
Definition bm_at194 (c : bar_ctx) (pos : Z) (S2 : astate) : Prop :=
  forall mem md (regs : bvmap 5 word),
    bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
    YK11.getr regs 22 = w64 (cx_dstp c) -> YK11.getr regs 21 = w64 (bar_s8 (cx_body c)) ->
    bm_fzero c pos 6 mem ->
    SRr segs (cx_W c) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x194))) mem
      (YK11.seg_rom segs)) md) (bar_post B MT c).

(* +0x1a4: after the dst memcpy. *)
Definition bm_at1a4 (c : bar_ctx) (pos : Z) (S2 : astate) : Prop :=
  forall mem md (regs : bvmap 5 word),
    bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
    YK11.getr regs 21 = w64 (bar_s8 (cx_body c)) ->
    bm_fdst c pos mem -> bm_fzero c pos 6 mem ->
    SRr segs (cx_W c) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x1a4))) mem
      (YK11.seg_rom segs)) md) (bar_post B MT c).

(* +0x1bc: after the src memcpy. *)
Definition bm_at1bc (c : bar_ctx) (pos : Z) (S2 : astate) : Prop :=
  forall mem md (regs : bvmap 5 word),
    bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
    YK11.getr regs 21 = w64 (bar_s8 (cx_body c)) ->
    bm_fdst c pos mem -> bm_fsrc c pos mem -> bm_fzero c pos 12 mem ->
    SRr segs (cx_W c) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x1bc))) mem
      (YK11.seg_rom segs)) md) (bar_post B MT c).

(* +0x224, the sum loop's head at index i: a0 = a3 = bodyp + i, a2 = 1, a4 = len - i, a1 = the sum of the first i
   bytes, the first sixteen frame bytes written and frame[16 .. n) still 0. *)
Definition bm_loop_at (c : bar_ctx) (pos : Z) (S2 : astate) (i : Z) : Prop :=
  forall mem md (regs : bvmap 5 word),
    bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
    YK11.getr regs 21 = w64 (bar_s8 (cx_body c)) ->
    YK11.getr regs 10 = w64 (cx_bodyp c + i) -> YK11.getr regs 13 = w64 (cx_bodyp c + i) ->
    YK11.getr regs 12 = w64 1 ->
    YK11.getr regs 14 = w64 (bar_len (cx_body c) - i) ->
    YK11.getr regs 11 = w64 (DSpec.sum_bytes (firstn (Z.to_nat i) (cx_body c))) ->
    garr8 segs (mrestrict (w_H (cx_W c)) mem) (bar_F c pos + 32)
      (TW.zs (bar_pre16 (cx_dst c) (cx_src c) (cx_body c))) ->
    bm_fzero c pos 16 mem ->
    0 <= i < bar_len (cx_body c) ->
    SRr segs (cx_W c) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x224))) mem
      (YK11.seg_rom segs)) md) (bar_post B MT c).

(* ------------------------------------------------------------------ *)
(* 6. +0x184 .. +0x190: the memset                                     *)
(* ------------------------------------------------------------------ *)

Lemma bm_s184 : forall c pos S2, bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_at194 c pos S2 -> bm_at184 c pos S2.
Proof.
intros c pos S2 HRT HOK NEXT mem md regs HST HRG H22 H21.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _ & _ & _ & _ & HSET & _).
pose proof (bar_ok_sp B MT c HOK)
  as (HARc & Hsp & Hce & _ & _ & Hsp0a & Hlo & Hhi & Hsp1al & Hsp1 & Hwin & Hsp1al16).
pose proof HST as (HRUN & HSL).
pose proof (bm_frame B MT c pos S2 mem md HRT HRUN)
  as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & HFapp & HFimg & HFpres & HFsh).
pose proof (bm_len B MT c HOK) as HLEN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
pose proof HRUN as ((HJ & _) & _).
pose proof HRG as ((G2 & G3 & G4 & G8 & G9 & G18 & G23 & G25 & G26 & G27) & G19 & G20 & G24).
assert (HS8 : 30 <= bar_s8 (cx_body c) <= 1484) by (unfold bar_s8; lia).
set (E0 := bm_E regs []).
assert (HEI : img_env VAL A_LIM E0) by apply bm_env_img.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0; apply bm_ew_reg; exact Hn).
assert (SHOK : sh_ok segs BM_Bx [] E0 (mrestrict (w_H (cx_W c)) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (bm_entry_nil (AF_build_and_receive + 0x184) regs [] mem (cx_W c)) as HS. fold E0 in HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK BM_B0.
{ bm_awr_ro. }
bm_low HS E0 HEX.
destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST HJ HFr HG
  ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST1 K1].
clear HF HFr HG.
bm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x194))) R1
  ltac:(apply codeptr_val; lazymatch goal with H : img_env _ _ ?Ex |- img_env _ _ ?Ex => exact H end).
bm_kreg HS (2%bv : bv 5) 2%nat (2%bv : bv 5) G2 HEX EE R2.
bm_kreg HS (3%bv : bv 5) 3%nat (3%bv : bv 5) G3 HEX EE R3.
bm_kreg HS (4%bv : bv 5) 4%nat (4%bv : bv 5) G4 HEX EE R4.
bm_reg HS (10%bv : bv 5) (w64 (bar_F c pos + 38)) Q10
  ltac:(apply (bm_soffk_w _ 18 38 (bar_F c pos));
        [rewrite ?HEX by lia; rewrite (EE 18%nat 18%bv eq_refl); exact G18 | lia | lia]).
bm_reg HS (11%bv : bv 5) (w64 0) Q11 ltac:(reflexivity).
bm_reg HS (12%bv : bv 5) (w64 (bar_s8 (cx_body c) + 24)) Q12
  ltac:(apply (bm_soffk_w _ 21 24 (bar_s8 (cx_body c)));
        [rewrite ?HEX by lia; rewrite (EE 21%nat 21%bv eq_refl); exact H21 | lia | lia]).
bm_kreg HS (21%bv : bv 5) 21%nat (21%bv : bv 5) H21 HEX EE R21.
bm_kreg HS (22%bv : bv 5) 22%nat (22%bv : bv 5) H22 HEX EE R22.
assert (HRG1 : bar_rg_run B c pos (ms_regs ms)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Q) end.
assert (USP : spZ (ms_regs ms) = bar_sp1 c) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
destruct (bm_dst B MT c pos S2 (ms_mem ms) _ (ms_regs ms) 6 (bar_s8 (cx_body c) + 24) HRT HOK (proj1 HST1) USP
  ltac:(lia) ltac:(lia) ltac:(lia)) as (D0 & D63 & DTW & DAM & DRA & DHH).
replace (bar_F c pos + 32 + 6) with (bar_F c pos + 38) in D0, D63, DTW, DAM, DRA, DHH by lia.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet (transportb_sigma TB___asan_memset)
    (HSET fx) G (cx_W c) _ _ (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 _ (cx_k c + 0) (bar_F c pos + 38) 0 (bar_s8 (cx_body c) + 24)
    (bar_sp1 c - cx_sp0 c) (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x194))) HGX G_HARNESS_B_rw HJ Q10 Q11 Q12).
  - lia.
  - exact D0.
  - exact D63.
  - rewrite USP. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold AF_build_and_receive; lia | reflexivity].
  - exact DTW.
  - exact DAM.
  - exact DRA.
  - exact DHH.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Heff & Hgr2).
destruct (bm_st_call c pos S2 _ _ mem2 md2 (bar_F c pos + 38) (bar_s8 (cx_body c) + 24) HRT HOK HST1 HJ2 Heff Hgr2
  ltac:(lia) ltac:(lia)) as [HST2 K2].
assert (HFZ : bm_fzero c pos 6 mem2).
{ intros j Hj. unfold bar_N, bar_nn in Hj.
  replace (bar_F c pos + 32 + j) with (bar_F c pos + 38 + (j - 6)) by lia.
  rewrite (Hset (j - 6) ltac:(lia)). reflexivity. }
assert (H21b : YK11.getr regs2 21 = w64 (bar_s8 (cx_body c))) by exact (eq_trans (HP2 21 ltac:(hnf; lia)) R21).
assert (H22b : YK11.getr regs2 22 = w64 (cx_dstp c)) by exact (eq_trans (HP2 22 ltac:(hnf; lia)) R22).
exact (NEXT mem2 md2 regs2 HST2 (bm_rg_pres c pos _ regs2 HRG1 HP2) H22b H21b HFZ).
Qed.

(* ------------------------------------------------------------------ *)
(* 7. +0x194 .. +0x1a0: the dst memcpy                                 *)
(* ------------------------------------------------------------------ *)

Lemma bm_s194 : forall c pos S2, bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_at1a4 c pos S2 -> bm_at194 c pos S2.
Proof.
intros c pos S2 HRT HOK NEXT mem md regs HST HRG H22 H21 HFZ.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _ & _ & _ & _ & _ & HCPY & _).
pose proof (bar_ok_sp B MT c HOK)
  as (HARc & Hsp & Hce & _ & _ & Hsp0a & Hlo & Hhi & Hsp1al & Hsp1 & Hwin & Hsp1al16).
pose proof HST as (HRUN & HSL).
pose proof (bm_frame B MT c pos S2 mem md HRT HRUN)
  as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & HFapp & HFimg & HFpres & HFsh).
pose proof (bm_len B MT c HOK) as HLEN.
pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLD &
  HGD & HSD & HOD & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
pose proof HRUN as ((HJ & _) & _).
pose proof HRG as ((G2 & G3 & G4 & G8 & G9 & G18 & G23 & G25 & G26 & G27) & G19 & G20 & G24).
set (E0 := bm_E regs []).
assert (HEI : img_env VAL A_LIM E0) by apply bm_env_img.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0; apply bm_ew_reg; exact Hn).
assert (SHOK : sh_ok segs BM_Bx [] E0 (mrestrict (w_H (cx_W c)) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (bm_entry_nil (AF_build_and_receive + 0x194) regs [] mem (cx_W c)) as HS. fold E0 in HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK BM_B0.
{ bm_awr_ro. }
bm_low HS E0 HEX.
destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST HJ HFr HG
  ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST1 K1].
clear HF HFr HG.
bm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x1a4))) R1
  ltac:(apply codeptr_val; lazymatch goal with H : img_env _ _ ?Ex |- img_env _ _ ?Ex => exact H end).
bm_kreg HS (2%bv : bv 5) 2%nat (2%bv : bv 5) G2 HEX EE R2.
bm_kreg HS (3%bv : bv 5) 3%nat (3%bv : bv 5) G3 HEX EE R3.
bm_kreg HS (4%bv : bv 5) 4%nat (4%bv : bv 5) G4 HEX EE R4.
bm_kreg HS (10%bv : bv 5) 25%nat (25%bv : bv 5) G25 HEX EE Q10.
bm_kreg HS (11%bv : bv 5) 22%nat (22%bv : bv 5) H22 HEX EE Q11.
bm_reg HS (12%bv : bv 5) (w64 6) Q12 ltac:(reflexivity).
bm_kreg HS (21%bv : bv 5) 21%nat (21%bv : bv 5) H21 HEX EE R21.
assert (HRG1 : bar_rg_run B c pos (ms_regs ms)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q) end.
assert (USP : spZ (ms_regs ms) = bar_sp1 c) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
destruct (bm_dst B MT c pos S2 (ms_mem ms) _ (ms_regs ms) 0 6 HRT HOK (proj1 HST1) USP ltac:(lia) ltac:(lia) ltac:(lia))
  as (D0 & D63 & DTW & DAM & DRA & DHH).
rewrite Z.add_0_r in D0, D63, DTW, DAM, DRA, DHH.
destruct (bm_cpy_src B MT c pos S2 (ms_mem ms) _ (cx_dstp c) (ms_regs ms) (bar_F c pos + 32) HRT HOK (proj1 HST1)
  HSD HOD USP ltac:(lia) ltac:(lia)) as (SRC & KVD).
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy (transportb_sigma TB___asan_memcpy)
    (HCPY fx) G (cx_W c) _ _ (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 _ (cx_k c + 0) (bar_F c pos + 32) (cx_dstp c) 6
    (bar_sp1 c - cx_sp0 c) (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x1a4))) HGX G_HARNESS_B_rw HJ Q10 Q11 Q12).
  - lia.
  - exact D0.
  - exact D63.
  - rewrite USP. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold AF_build_and_receive; lia | reflexivity].
  - exact DTW.
  - exact DAM.
  - exact DRA.
  - exact DHH.
  - exact SRC. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcpy & Heff & Hgr2).
destruct (bm_st_call c pos S2 _ _ mem2 md2 (bar_F c pos + 32) 6 HRT HOK HST1 HJ2 Heff Hgr2
  ltac:(lia) ltac:(lia)) as [HST2 K2].
assert (HFD : bm_fdst c pos mem2).
{ intros j Hj. rewrite (Hcpy j Hj), (KVD (cx_dstp c + j) ltac:(lia)).
  apply (bm_garr8_aview _ _ _ _ HGD). unfold TW.zs. rewrite length_map, HLD. lia. }
assert (HFZ2 : bm_fzero c pos 6 mem2).
{ intros j Hj. pose proof (HFZ j Hj) as Hz. unfold bar_N, bar_nn, bar_s8 in Hj.
  rewrite (K2 (bar_F c pos + 32 + j) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (K1 (bar_F c pos + 32 + j) ltac:(lia) (fun x => x)). exact Hz. }
assert (H21b : YK11.getr regs2 21 = w64 (bar_s8 (cx_body c))) by exact (eq_trans (HP2 21 ltac:(hnf; lia)) R21).
exact (NEXT mem2 md2 regs2 HST2 (bm_rg_pres c pos _ regs2 HRG1 HP2) H21b HFD HFZ2).
Qed.

(* ------------------------------------------------------------------ *)
(* 8. +0x1a4 .. +0x1b8: the UBSan test of frame[] + 6, the src memcpy  *)
(* ------------------------------------------------------------------ *)

Lemma bm_s1a4 : forall c pos S2, bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_at1bc c pos S2 -> bm_at1a4 c pos S2.
Proof.
intros c pos S2 HRT HOK NEXT mem md regs HST HRG H21 HFD HFZ.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _ & _ & _ & _ & _ & HCPY & _).
pose proof (bar_ok_sp B MT c HOK)
  as (HARc & Hsp & Hce & _ & _ & Hsp0a & Hlo & Hhi & Hsp1al & Hsp1 & Hwin & Hsp1al16).
pose proof HST as (HRUN & HSL).
pose proof (bm_frame B MT c pos S2 mem md HRT HRUN)
  as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & HFapp & HFimg & HFpres & HFsh).
pose proof (bm_len B MT c HOK) as HLEN.
pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HLS & HGS & HSS & HOS & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
pose proof HRUN as ((HJ & _) & _).
pose proof HRG as ((G2 & G3 & G4 & G8 & G9 & G18 & G23 & G25 & G26 & G27) & G19 & G20 & G24).
set (E0 := bm_E regs (bm_xs c)).
assert (HEI : img_env VAL A_LIM E0) by apply bm_env_img.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0; apply bm_ew_reg; exact Hn).
assert (E32 : ew E0 32 = w64 (cx_srcp c)) by exact (bm_ew_extra regs (bm_xs c) 0 ltac:(lia)).
assert (SHOK : sh_ok segs BM_Bx [] E0 (mrestrict (w_H (cx_W c)) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (bm_entry_s c pos S2 mem md regs (AF_build_and_receive + 0x1a4) HRT HOK HST HRG) as HS. fold E0 in HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 []) as RUN.
(* +0x1a4 .. +0x1b8: `bgeu s9, -6` is decided not taken by the fact on atom 25 (s9 <= 2 ^ 47), then the
   memcpy's arguments and `jal __asan_memcpy` *)
paj_run_tok RUN HS HJ SHOK BM_B0.
{ bm_awr_ro. }
bm_low HS E0 HEX.
destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST HJ HFr HG
  ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST1 K1].
clear HF HFr HG.
bm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x1bc))) R1
  ltac:(apply codeptr_val; lazymatch goal with H : img_env _ _ ?Ex |- img_env _ _ ?Ex => exact H end).
bm_kreg HS (2%bv : bv 5) 2%nat (2%bv : bv 5) G2 HEX EE R2.
bm_kreg HS (3%bv : bv 5) 3%nat (3%bv : bv 5) G3 HEX EE R3.
bm_kreg HS (4%bv : bv 5) 4%nat (4%bv : bv 5) G4 HEX EE R4.
bm_reg HS (10%bv : bv 5) (w64 (bar_F c pos + 38)) Q10
  ltac:(apply (bm_soffk_w _ 25 6 (bar_F c pos + 32));
        [rewrite ?HEX by lia; rewrite (EE 25%nat 25%bv eq_refl); exact G25 | lia | lia]).
bm_reg HS (11%bv : bv 5) (w64 (cx_srcp c)) Q11 ltac:(apply bm_soff0; rewrite ?HEX by lia; exact E32).
bm_reg HS (12%bv : bv 5) (w64 6) Q12 ltac:(reflexivity).
bm_kreg HS (21%bv : bv 5) 21%nat (21%bv : bv 5) H21 HEX EE R21.
assert (HRG1 : bar_rg_run B c pos (ms_regs ms)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q) end.
assert (USP : spZ (ms_regs ms) = bar_sp1 c) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
destruct (bm_dst B MT c pos S2 (ms_mem ms) _ (ms_regs ms) 6 6 HRT HOK (proj1 HST1) USP ltac:(lia) ltac:(lia) ltac:(lia))
  as (D0 & D63 & DTW & DAM & DRA & DHH).
replace (bar_F c pos + 32 + 6) with (bar_F c pos + 38) in D0, D63, DTW, DAM, DRA, DHH by lia.
destruct (bm_cpy_src B MT c pos S2 (ms_mem ms) _ (cx_srcp c) (ms_regs ms) (bar_F c pos + 38) HRT HOK (proj1 HST1)
  HSS HOS USP ltac:(lia) ltac:(lia)) as (SRC & KVS).
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy (transportb_sigma TB___asan_memcpy)
    (HCPY fx) G (cx_W c) _ _ (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 _ (cx_k c + 0) (bar_F c pos + 38) (cx_srcp c) 6
    (bar_sp1 c - cx_sp0 c) (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x1bc))) HGX G_HARNESS_B_rw HJ Q10 Q11 Q12).
  - lia.
  - exact D0.
  - exact D63.
  - rewrite USP. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold AF_build_and_receive; lia | reflexivity].
  - exact DTW.
  - exact DAM.
  - exact DRA.
  - exact DHH.
  - exact SRC. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcpy & Heff & Hgr2).
destruct (bm_st_call c pos S2 _ _ mem2 md2 (bar_F c pos + 38) 6 HRT HOK HST1 HJ2 Heff Hgr2
  ltac:(lia) ltac:(lia)) as [HST2 K2].
assert (HFD2 : bm_fdst c pos mem2).
{ intros j Hj. rewrite (K2 (bar_F c pos + 32 + j) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (K1 (bar_F c pos + 32 + j) ltac:(lia) (fun x => x)). exact (HFD j Hj). }
assert (HFS2 : bm_fsrc c pos mem2).
{ intros j Hj. rewrite (Hcpy j Hj), (KVS (cx_srcp c + j) ltac:(lia)).
  apply (bm_garr8_aview _ _ _ _ HGS). unfold TW.zs. rewrite length_map, HLS. lia. }
assert (HFZ2 : bm_fzero c pos 12 mem2).
{ intros j Hj. pose proof (HFZ j ltac:(lia)) as Hz. unfold bar_N, bar_nn, bar_s8 in Hj.
  rewrite (K2 (bar_F c pos + 32 + j) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (K1 (bar_F c pos + 32 + j) ltac:(lia) (fun x => x)). exact Hz. }
assert (H21b : YK11.getr regs2 21 = w64 (bar_s8 (cx_body c))) by exact (eq_trans (HP2 21 ltac:(hnf; lia)) R21).
exact (NEXT mem2 md2 regs2 HST2 (bm_rg_pres c pos _ regs2 HRG1 HP2) H21b HFD2 HFS2 HFZ2).
Qed.

(* ------------------------------------------------------------------ *)
(* 9. +0x178 .. +0x180: s5 = max (len, 30)                             *)
(* ------------------------------------------------------------------ *)

Lemma bm_s178 : forall c pos S2, bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_at184 c pos S2 ->
  forall mem md (regs : bvmap 5 word),
    bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
    YK11.getr regs 22 = w64 (cx_dstp c) -> YK11.getr regs 11 = w64 30 ->
    SRr segs (cx_W c) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x178))) mem
      (YK11.seg_rom segs)) md) (bar_post B MT c).
Proof.
intros c pos S2 HRT HOK NEXT mem md regs HST HRG H22 H11.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _).
pose proof (bm_len B MT c HOK) as HLEN.
pose proof HST as (((HJ & _) & _) & _).
pose proof HRG as ((G2 & G3 & G4 & G8 & G9 & G18 & G23 & G25 & G26 & G27) & G19 & G20 & G24).
set (E0 := bm_E regs []).
assert (HEI : img_env VAL A_LIM E0) by apply bm_env_img.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0; apply bm_ew_reg; exact Hn).
assert (E11 : ew E0 11 = Z_to_bv 64 30) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E19 : ew E0 19 = Z_to_bv 64 (bar_len (cx_body c))) by (rewrite (EE 19%nat 19%bv eq_refl); exact G19).
assert (SHOK : sh_ok segs BM_Bx [] E0 (mrestrict (w_H (cx_W c)) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (bm_entry_nil (AF_build_and_receive + 0x178) regs [] mem (cx_W c)) as HS. fold E0 in HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK BM_B0.
{ bm_awr_ro. }
bm_md.
destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST HJ HFr HG
  ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST1 _].
clear HF HFr HG HST.
psrr_branch_tok RUN BR HS SHOK BM_B0.
- (* 30 < len: s5 = len *)
  rewrite branch_ltu_U, (U_atom E0 11 30 E11 ltac:(lia)), (U_atom E0 19 _ E19 ltac:(unfold bar_len in *; lia)) in Hc.
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK BM_B0 (AF_build_and_receive + 0x184).
  { bm_awr_ro. }
  bm_md.
  bm_low HS E0 HEX.
  destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST1 HJ HFr HG
    ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST2 _].
  clear HF HFr HG.
  bm_kreg HS (22%bv : bv 5) 22%nat (22%bv : bv 5) H22 HEX EE R22.
  bm_reg HS (21%bv : bv 5) (w64 (bar_s8 (cx_body c))) R21
    ltac:(apply bm_soff0; rewrite ?HEX by lia; rewrite E19; unfold w64, bar_s8; f_equal; lia).
  lazymatch type of HS with context [restrict _ ?msn] =>
    assert (HRG2 : bar_rg_run B c pos (ms_regs msn)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX)
  end.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (NEXT mm mdx rg HST2 HRG2 R22 R21) end.
- (* len <= 30: s5 = 30 *)
  rewrite branch_ltu_U, (U_atom E0 11 30 E11 ltac:(lia)), (U_atom E0 19 _ E19 ltac:(unfold bar_len in *; lia)) in Hc.
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK BM_B0 (AF_build_and_receive + 0x184).
  { bm_awr_ro. }
  bm_md.
  bm_low HS E0 HEX.
  destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST1 HJ HFr HG
    ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST2 _].
  clear HF HFr HG.
  bm_kreg HS (22%bv : bv 5) 22%nat (22%bv : bv 5) H22 HEX EE R22.
  bm_reg HS (21%bv : bv 5) (w64 (bar_s8 (cx_body c))) R21
    ltac:(cbn [sv_denot]; unfold w64, bar_s8; f_equal; lia).
  lazymatch type of HS with context [restrict _ ?msn] =>
    assert (HRG2 : bar_rg_run B c pos (ms_regs msn)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX)
  end.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (NEXT mm mdx rg HST2 HRG2 R22 R21) end.
Qed.

(* ------------------------------------------------------------------ *)
(* 10. The bytes the piece leaves in frame[0 .. 16)                    *)
(* ------------------------------------------------------------------ *)

Lemma bm_nth_zs : forall (l : list byte) j, 0 <= nth j (TW.zs l) 0 < 256.
Proof.
induction l as [|x l IH]; intros [|j]; cbn [TW.zs map nth]; try lia.
- pose proof (bv_unsigned_in_range 8 x) as Hr. unfold bv_modulus in Hr. cbn in Hr. lia.
- exact (IH j).
Qed.

Lemma bm_at8_zs : forall (l : list byte) j, DSpec.at8 l j = nth j (TW.zs l) 0.
Proof.
induction l as [|x l IH]; intros [|j]; try reflexivity.
cbn [TW.zs map nth]. exact (IH j).
Qed.

Lemma bm_b8 : forall z, bv_unsigned (DSpec.b8 z) = z mod 256.
Proof.
intros z. unfold DSpec.b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity.
Qed.

(* The four header bytes the stores at +0x1d0 .. +0x204 leave, read off the run's region of frame[12 .. 16) at
   s9 = F + 32. *)
Lemma bm_hdr_bytes : forall (E : env) (H : word -> bool) (m : word -> option byte) F len cs,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some 25%nat) 12 16 12 16 cs) ->
  In (YP09.mkChunk 15 (CVal 1 (SOff 19 16))) cs ->
  In (YP09.mkChunk 14 (CVal 1 (SAlu ALU_SRL (SOff 19 16) (SLit 8)))) cs ->
  In (YP09.mkChunk 13 (CVal 1 (SLit 95))) cs -> In (YP09.mkChunk 12 (CVal 1 (SLit 136))) cs ->
  bv_unsigned (ew E 25) = F + 32 -> ew E 19 = Z_to_bv 64 len -> 0 <= len <= 1484 ->
  aview segs H m (F + 44) = Some 136 /\ aview segs H m (F + 45) = Some 95 /\
  aview segs H m (F + 46) = Some (((len + 16) / 256) mod 256) /\ aview segs H m (F + 47) = Some ((len + 16) mod 256).
Proof.
intros E H m F len cs RG I15 I14 I13 I12 U25 E19 Hl.
pose proof (field_of_region_any E _ 25 (F + 32) _ _ _ _ _ 12 1 (SLit 136) RG U25 I12 ltac:(lia)) as V44.
pose proof (field_of_region_any E _ 25 (F + 32) _ _ _ _ _ 13 1 (SLit 95) RG U25 I13 ltac:(lia)) as V45.
pose proof (field_of_region_any E _ 25 (F + 32) _ _ _ _ _ 14 1 (SAlu ALU_SRL (SOff 19 16) (SLit 8)) RG U25 I14
  ltac:(lia)) as V46.
pose proof (field_of_region_any E _ 25 (F + 32) _ _ _ _ _ 15 1 (SOff 19 16) RG U25 I15 ltac:(lia)) as V47.
replace (F + 32 + 12) with (F + 44) in V44 by lia. replace (F + 32 + 13) with (F + 45) in V45 by lia.
replace (F + 32 + 14) with (F + 46) in V46 by lia. replace (F + 32 + 15) with (F + 47) in V47 by lia.
assert (U46 : U E (SAlu ALU_SRL (SOff 19 16) (SLit 8)) = (len + 16) / 256).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, E19, unsigned_lit_small by lia.
  change (Z.land (U E (SLit 8)) 63) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (YP0m.zcanon_small (len + 16)) by lia. apply YP0m.zcanon_small.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (U47 : U E (SOff 19 16) = len + 16)
  by (rewrite U_SOff, E19, unsigned_lit_small by lia; apply YP0m.zcanon_small; lia).
unfold U in U46, U47.
change (8 * Z.of_N 1) with 8 in V44, V45, V46, V47. change (2 ^ 8) with 256 in V44, V45, V46, V47.
rewrite U46 in V46. rewrite U47 in V47.
split; [|split; [|split]].
- apply (bm_aview_of_val1 H m _ _ V44). cbn. lia.
- apply (bm_aview_of_val1 H m _ _ V45). cbn. lia.
- apply (bm_aview_of_val1 H m _ _ V46). apply Z.mod_pos_bound. lia.
- apply (bm_aview_of_val1 H m _ _ V47). apply Z.mod_pos_bound. lia.
Qed.

(* garr8 of the first sixteen frame bytes, the form the cut call asks, from their views. *)
Lemma bm_pre16 : forall c pos mem,
  bar_ok B MT c -> bm_fdst c pos mem -> bm_fsrc c pos mem ->
  aview segs (w_H (cx_W c)) mem (bar_F c pos + 44) = Some 136 ->
  aview segs (w_H (cx_W c)) mem (bar_F c pos + 45) = Some 95 ->
  aview segs (w_H (cx_W c)) mem (bar_F c pos + 46) = Some (((bar_len (cx_body c) + 16) / 256) mod 256) ->
  aview segs (w_H (cx_W c)) mem (bar_F c pos + 47) = Some ((bar_len (cx_body c) + 16) mod 256) ->
  garr8 segs (mrestrict (w_H (cx_W c)) mem) (bar_F c pos + 32)
    (TW.zs (bar_pre16 (cx_dst c) (cx_src c) (cx_body c))).
Proof.
intros c pos mem HOK HD HS A44 A45 A46 A47.
destruct (bar_ok_len B MT c HOK) as [HLD HLS].
apply bm_garr8_of_aview. intros j Hj. split; [|apply bm_nth_zs].
assert (Hj16 : (j < 16)%nat).
{ unfold TW.zs in Hj. rewrite length_map, (bar_pre16_len _ _ _ HLD HLS) in Hj. exact Hj. }
unfold bar_pre16, TW.zs. rewrite !map_app.
destruct (Nat.lt_ge_cases j 6) as [J6 | J6].
{ rewrite app_nth1 by (rewrite length_map; lia).
  pose proof (HD (Z.of_nat j) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv. exact Hv. }
rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map, HLD.
destruct (Nat.lt_ge_cases j 12) as [J12 | J12].
{ rewrite app_nth1 by (rewrite length_map; lia).
  pose proof (HS (Z.of_nat j - 6) ltac:(lia)) as Hv.
  replace (Z.to_nat (Z.of_nat j - 6)) with (j - 6)%nat in Hv by lia.
  replace (bar_F c pos + 38 + (Z.of_nat j - 6)) with (bar_F c pos + 32 + Z.of_nat j) in Hv by lia. exact Hv. }
rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map, HLS.
assert (Jc : j = 12%nat \/ j = 13%nat \/ j = 14%nat \/ j = 15%nat) by lia.
destruct Jc as [-> | [-> | [-> | ->]]]; cbn [Nat.sub nth map app DSpec.put16].
- replace (bar_F c pos + 32 + Z.of_nat 12) with (bar_F c pos + 44) by lia. rewrite A44. reflexivity.
- replace (bar_F c pos + 32 + Z.of_nat 13) with (bar_F c pos + 45) by lia. rewrite A45. reflexivity.
- replace (bar_F c pos + 32 + Z.of_nat 14) with (bar_F c pos + 46) by lia. rewrite A46, bm_b8.
  do 2 f_equal. change (2 ^ 8) with 256. f_equal. lia.
- replace (bar_F c pos + 32 + Z.of_nat 15) with (bar_F c pos + 47) by lia. rewrite A47, bm_b8.
  do 2 f_equal. lia.
Qed.

(* A garr8 fact kept by a step that keeps every view. *)
Lemma bm_garr8_keep : forall H (m m' : word -> option byte) base l,
  garr8 segs (mrestrict H m) base l ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs H m' a = aview segs H m a) ->
  0 <= base -> base + Z.of_nat (length l) <= 2 ^ 64 ->
  garr8 segs (mrestrict H m') base l.
Proof.
intros H m m' base l HG K H0 H1. apply (garr8_frame segs _ _ _ _ HG).
intros a Ha. apply (mbyte_of_aview segs). apply K. lia.
Qed.

Lemma bm_pre16_len : forall c, bar_ok B MT c ->
  Z.of_nat (length (TW.zs (bar_pre16 (cx_dst c) (cx_src c) (cx_body c)))) = 16.
Proof.
intros c HOK. destruct (bar_ok_len B MT c HOK) as [HLD HLS].
unfold TW.zs. rewrite length_map, (bar_pre16_len _ _ _ HLD HLS). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 11. The body                                                        *)
(* ------------------------------------------------------------------ *)

(* A non-empty body at a state of bar_run: its bytes, its shadow addressable, in application memory, and its
   placement (trans_src_ok_place): 4096 <= bodyp, bodyp + len <= 2 ^ 47. *)
Lemma bm_body : forall c pos S2 mem md,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem md -> 0 < bar_len (cx_body c) ->
  range_addressable (aview segs (w_H (cx_W c)) mem) SHADOW_OFF (cx_bodyp c) (bar_len (cx_body c)) /\
  amem_range (cx_bodyp c) (bar_len (cx_body c)) /\
  4096 <= cx_bodyp c /\ cx_bodyp c + bar_len (cx_body c) <= 2 ^ 47 /\
  (forall j, 0 <= j < bar_len (cx_body c) ->
     aview segs (w_H (cx_W c)) mem (cx_bodyp c + j) = Some (nth (Z.to_nat j) (TW.zs (cx_body c)) 0)).
Proof.
intros c pos S2 mem md HRT HOK HRUN Hl.
pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & HGB & HPB & _).
destruct (HPB ltac:(unfold bar_len in Hl; lia)) as [HSB HOB].
destruct (bm_src B MT c pos S2 mem md (cx_bodyp c) (bar_len (cx_body c)) HRT HOK HRUN HSB HOB Hl)
  as ((_ & Hra & _ & Hamr & _ & _) & KV & _ & _ & Hb4 & Hb47).
split; [exact Hra|]. split; [exact Hamr|]. split; [exact Hb4|]. split; [exact Hb47|].
intros j Hj. rewrite (KV (cx_bodyp c + j) ltac:(lia)).
apply (bm_garr8_aview _ _ _ _ HGB). unfold TW.zs. rewrite length_map. unfold bar_len in Hj. lia.
Qed.

Lemma bm_regs_ok_pin : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> bv_eqb r 0 = false -> sv_denot E e = YK11.getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e H Hr0 He rr. destruct (decide (rr = r)) as [->|Hne].
  - rewrite sr_get_set_same by exact Hr0. symmetry. exact He.
  - rewrite sr_get_set_other by exact Hne. apply H.
Qed.

(* `addi a4, a4, -1; bnez a4` (+0x24c / +0x25c): another byte to add. *)
Lemma bm_br_a4 : forall E v, ew E 14 = Z_to_bv 64 v -> 1 <= v < 2 ^ 32 ->
  branch_taken BC_NE (sv_denot E (SOff 14 (-1))) (sv_denot E (SLit 0)) = negb (v - 1 =? 0).
Proof.
  intros E v H Hv. rewrite branch_ne_U, U_SLit, U_SOff, H, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The loop's symbolic state at +0x224: a3 = a0 (atom 10), a2 = 1, the body byte at a0 (atom 32), the shadow base
   atom 23. Its facts decide the loop's three UBSan tests: 4096 <= a0 and 4096 <= s4 (atom 20) from the body's
   placement, and the condition a0 >=u s4 (bodyp + i >= bodyp). The token engine decides the check of the 1-byte
   load at a0 from the shadow entry of [a0, a0 + 1). *)
Definition BM_LOOP_SR : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 13) (SOff 10 0)) (Z_to_bv 5 12) (SLit 1).
Definition BM_LOOP_RG : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition BM_LOOP_FACTS : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF 4096 (2 ^ 47 - 1) 0);
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)]
    [mkAC BC_GEU (SOff 10 0) (SOff 20 0)] [].
Definition BM_LOOP_SH : list shent := [mkSHE 10 0 1].
Definition bm_lx (c : bar_ctx) (i : Z) : list word := [w64 (nth (Z.to_nat i) (TW.zs (cx_body c)) 0)].

Lemma bm_entry_loop : forall c pos S2 mem md (regs : bvmap 5 word) i,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bm_st c pos S2 mem md -> bar_rg_run B c pos regs ->
  YK11.getr regs 10 = w64 (cx_bodyp c + i) -> YK11.getr regs 13 = w64 (cx_bodyp c + i) ->
  YK11.getr regs 12 = w64 1 ->
  0 <= i < bar_len (cx_body c) ->
  st_ok_pi segs VAL (bm_E regs (bm_lx c i))
    (mkSS (AF_build_and_receive + 0x224) BM_LOOP_SR [BM_LOOP_RG] None BM_LOOP_FACTS)
    (restrict (w_H (cx_W c)) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_build_and_receive + 0x224))) mem
      (YK11.seg_rom segs))) /\
  sh_ok segs BM_Bx BM_LOOP_SH (bm_E regs (bm_lx c i)) (mrestrict (w_H (cx_W c)) mem).
Proof.
intros c pos S2 mem md regs i HRT HOK (HRUN & HSL) HRG H10 H13 H12 Hi.
destruct (bm_body c pos S2 mem md HRT HOK HRUN ltac:(lia)) as (BRA & BAM & B4 & B47 & BV).
pose proof HRG as ((_ & _ & _ & _ & _ & _ & G23 & _) & _ & G20 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_consts as (K1 & K2 & K3 & K4 & K5).
set (v := nth (Z.to_nat i) (TW.zs (cx_body c)) 0).
pose proof (bm_nth_zs (cx_body c) (Z.to_nat i)) as Hv. fold v in Hv.
set (E := bm_E regs (bm_lx c i)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply bm_ew_reg; exact Hn).
assert (E32 : ew E 32 = w64 v) by exact (bm_ew_extra regs (bm_lx c i) 0 ltac:(lia)).
assert (U10 : bv_unsigned (ew E 10) = cx_bodyp c + i)
  by (rewrite (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = cx_bodyp c)
  by (rewrite (EE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite (EE 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = v) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + unfold BM_LOOP_SR.
    apply bm_regs_ok_pin; [apply bm_regs_ok_pin; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
    * apply bm_soff0. rewrite (EE 10%nat 10%bv eq_refl), H10. symmetry. exact H13.
    * cbn [sv_denot]. symmetry. exact H12.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold BM_LOOP_RG, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (cx_bodyp c + i) 0 1 (SOff 32 0) v); [apply bm_soff0; exact E32 | cbn; lia | cbn; lia |].
    apply YE2y.val_mem1_of_aview. rewrite Z.add_0_r. exact (BV i Hi).
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold BM_LOOP_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, acond_ok. cbn [af_lo af_hi af_al2 ac_c ac_a ac_b].
    rewrite branch_geu_U.
    rewrite (U_atom E 10 (cx_bodyp c + i)), (U_atom E 20 (cx_bodyp c))
      by (first [rewrite (EE 10%nat 10%bv eq_refl); exact H10 | rewrite (EE 20%nat 20%bv eq_refl); exact G20 | lia]).
    rewrite U10, U20, U23, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hge : negb (cx_bodyp c + i <? cx_bodyp c) = true) by (apply negb_true_iff, Z.ltb_ge; lia).
    rewrite Hge.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; lia.
- unfold sh_ok, BM_LOOP_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H (cx_W c)) mem E BM_Bx 10 (cx_bodyp c) (bar_len (cx_body c))
    (cx_bodyp c + i) 0 1 BRA).
  + unfold U, BM_Bx. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U23.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in BAM. lia.
Qed.

(* The write right of the run at +0x1bc: frame[12 .. 16) of the own frame. *)
Ltac bm_awr_hs U25 c pos :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ BAR_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha;
    left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes BAR_CID) with 2048;
    change (frame_addr (cx_lyc c) BAR_CID pos) with (bar_F c pos); lia |];
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* 12. +0x224 .. +0x260: the sum loop                                  *)
(* ------------------------------------------------------------------ *)

Lemma bm_loop : forall c pos S2, bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_call_at B MT c ->
  forall i, bm_loop_at c pos S2 i.
Proof.
intros c pos S2 HRT HOK HCALL.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _).
pose proof (bm_len B MT c HOK) as HLEN.
pose proof (bm_pre16_len c HOK) as HPL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (IND : forall k i, Z.of_nat k = bar_len (cx_body c) - i -> bm_loop_at c pos S2 i).
{ induction k as [|k IH]; intros i Hk mem md regs HST HRG H21 H10 H13 H12 H14 H11 HPRE HZ Hi; [lia|].
  pose proof HST as (((HJ & _) & _) & _).
  pose proof (bm_frame B MT c pos S2 mem md HRT (proj1 HST))
    as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & HFapp & HFimg & HFpres & HFsh).
  destruct (bm_body c pos S2 mem md HRT HOK (proj1 HST) ltac:(lia)) as (_ & _ & B4 & B47 & _).
  set (v := nth (Z.to_nat i) (TW.zs (cx_body c)) 0).
  pose proof (bm_nth_zs (cx_body c) (Z.to_nat i)) as Hv. fold v in Hv.
  set (Sm := DSpec.sum_bytes (firstn (Z.to_nat i) (cx_body c))).
  assert (HSUM : 0 <= Sm <= 255 * Z.of_nat (Z.to_nat i)).
  { pose proof (DSpec.sum_bytes_range (firstn (Z.to_nat i) (cx_body c))) as SR.
    rewrite length_firstn in SR. unfold bar_len in Hi. fold Sm in SR. lia. }
  assert (HSUM1 : DSpec.sum_bytes (firstn (Z.to_nat (i + 1)) (cx_body c)) = Sm + v).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite DSpec.sum_bytes_firstn_S by (unfold bar_len in Hi; lia). rewrite bm_at8_zs. reflexivity. }
  set (E0 := bm_E regs (bm_lx c i)).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
    by (intros n r Hn; unfold E0; apply bm_ew_reg; exact Hn).
  assert (HEI : img_env VAL A_LIM E0) by apply bm_env_img.
  assert (E32 : ew E0 32 = w64 v) by exact (bm_ew_extra regs (bm_lx c i) 0 ltac:(lia)).
  destruct (bm_entry_loop c pos S2 mem md regs i HRT HOK HST HRG H10 H13 H12 Hi) as [HS SHOK].
  fold E0 in HS, SHOK.
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 [])
    as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
  (* +0x224 .. +0x25c: the three UBSan tests (decided by the state's facts), the check of the load at a0 (a
     token), the load at a3, the four updates, up to `bnez a4` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { bm_awr_ro. }
  bm_md.
  bm_low HS E0 HEX.
  destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST HJ HFr HG
    ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST1 K1].
  clear HF HFr HG.
  pose proof (bm_garr8_keep _ _ _ _ _ HPRE (fun a Ha => K1 a Ha (fun x => x)) ltac:(lia) ltac:(rewrite HPL; lia))
    as HPRE1.
  pose proof (fun j (Hj : 16 <= j < bar_N c) =>
    eq_trans (K1 (bar_F c pos + 32 + j) ltac:(unfold bar_N, bar_nn, bar_s8 in Hj; lia) (fun x => x)) (HZ j Hj)) as HZ1.
  clear K1 HPRE HZ.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* another byte: back to +0x224 at i + 1 *)
    lazymatch type of Hc with context [sv_denot ?Ex (SOff 14 (-1))] =>
      rewrite (bm_br_a4 Ex (bar_len (cx_body c) - i)
        ltac:(rewrite ?HEX by lia; rewrite (EE 14%nat 14%bv eq_refl); exact H14) ltac:(lia)) in Hc end.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_build_and_receive + 0x224).
    { bm_awr_ro. }
    bm_md.
    bm_low HS E0 HEX2.
    destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST1 HJ HFr HG
      ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST2 K2].
    clear HF HFr HG.
    pose proof (bm_garr8_keep _ _ _ _ _ HPRE1 (fun a Ha => K2 a Ha (fun x => x)) ltac:(lia) ltac:(rewrite HPL; lia))
      as HPRE2.
    pose proof (fun j (Hj : 16 <= j < bar_N c) =>
      eq_trans (K2 (bar_F c pos + 32 + j) ltac:(unfold bar_N, bar_nn, bar_s8 in Hj; lia) (fun x => x)) (HZ1 j Hj))
      as HZ2.
    bm_kreg HS (21%bv : bv 5) 21%nat (21%bv : bv 5) H21 HEX2 EE R21.
    bm_reg HS (11%bv : bv 5) (w64 (DSpec.sum_bytes (firstn (Z.to_nat (i + 1)) (cx_body c)))) R11
      ltac:(rewrite denot_lit_U, U_SAlu; cbn [zalu_raw];
            rewrite (U_atom _ 11 Sm)
              by (first [rewrite ?HEX2 by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia]);
            rewrite (U_atom _ 32 v) by (first [rewrite ?HEX2 by lia; exact E32 | lia]);
            rewrite HSUM1, YP0m.zcanon_small by lia; unfold w64; f_equal; lia).
    bm_reg HS (10%bv : bv 5) (w64 (cx_bodyp c + (i + 1))) R10
      ltac:(apply (bm_soffk_w _ 10 1 (cx_bodyp c + i));
            [rewrite ?HEX2 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10 | lia | lia]).
    bm_reg HS (13%bv : bv 5) (w64 (cx_bodyp c + (i + 1))) X13
      ltac:(apply (bm_soffk_w _ 10 1 (cx_bodyp c + i));
            [rewrite ?HEX2 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10 | lia | lia]).
    bm_reg HS (12%bv : bv 5) (w64 1) V12 ltac:(reflexivity).
    bm_reg HS (14%bv : bv 5) (w64 (bar_len (cx_body c) - (i + 1))) V14
      ltac:(apply (bm_soffk_w _ 14 (-1) (bar_len (cx_body c) - i));
            [rewrite ?HEX2 by lia; rewrite (EE 14%nat 14%bv eq_refl); exact H14 | lia | lia]).
    lazymatch type of HS with context [restrict _ ?msn] =>
      assert (HRG2 : bar_rg_run B c pos (ms_regs msn)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX2)
    end.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      exact (IH (i + 1) ltac:(lia) mm mdx rg HST2 HRG2 R21 R10 X13 V12 V14 R11 HPRE2 HZ2 ltac:(lia)) end.
  - (* the last byte: `j +0x270`, to the cut call *)
    lazymatch type of Hc with context [sv_denot ?Ex (SOff 14 (-1))] =>
      rewrite (bm_br_a4 Ex (bar_len (cx_body c) - i)
        ltac:(rewrite ?HEX by lia; rewrite (EE 14%nat 14%bv eq_refl); exact H14) ltac:(lia)) in Hc end.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (HSUMF : DSpec.sum_bytes (cx_body c) = Sm + v).
    { rewrite <- HSUM1, firstn_all2 by (unfold bar_len in Hc; lia). reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_build_and_receive + 0x270).
    { bm_awr_ro. }
    bm_md.
    bm_low HS E0 HEX2.
    destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun _ => False) HRT HOK HST1 HJ HFr HG
      ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(lia)) ltac:(intros a [])) as [HST2 K2].
    clear HF HFr HG.
    pose proof (bm_garr8_keep _ _ _ _ _ HPRE1 (fun a Ha => K2 a Ha (fun x => x)) ltac:(lia) ltac:(rewrite HPL; lia))
      as HPRE2.
    pose proof (fun j (Hj : 16 <= j < bar_N c) =>
      eq_trans (K2 (bar_F c pos + 32 + j) ltac:(unfold bar_N, bar_nn, bar_s8 in Hj; lia) (fun x => x)) (HZ1 j Hj))
      as HZ2.
    bm_kreg HS (21%bv : bv 5) 21%nat (21%bv : bv 5) H21 HEX2 EE R21.
    bm_reg HS (11%bv : bv 5) (w64 (DSpec.sum_bytes (cx_body c))) R11
      ltac:(rewrite denot_lit_U, U_SAlu; cbn [zalu_raw];
            rewrite (U_atom _ 11 Sm)
              by (first [rewrite ?HEX2 by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia]);
            rewrite (U_atom _ 32 v) by (first [rewrite ?HEX2 by lia; exact E32 | lia]);
            rewrite HSUMF, YP0m.zcanon_small by lia; unfold w64; f_equal; lia).
    lazymatch type of HS with context [restrict _ ?msn] =>
      assert (HRG2 : bar_rg_run B c pos (ms_regs msn)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX2)
    end.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      exact (HCALL HRT HOK pos S2 mm mdx rg (proj1 HST2) HRG2 (proj2 HST2) R11 R21 HPRE2 HZ2) end. }
intros i mem md regs HST HRG H21 H10 H13 H12 H14 H11 HPRE HZ Hi.
exact (IND (Z.to_nat (bar_len (cx_body c) - i)) i ltac:(lia) mem md regs HST HRG H21 H10 H13 H12 H14 H11 HPRE HZ Hi).
Qed.

(* ------------------------------------------------------------------ *)
(* 13. +0x1bc .. +0x220: the four header stores, a1 = 0, `beqz s3`,    *)
(*     the loop's entry                                                *)
(* ------------------------------------------------------------------ *)

Lemma bm_s1bc : forall c pos S2, bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_call_at B MT c ->
  (forall i, bm_loop_at c pos S2 i) -> bm_at1bc c pos S2.
Proof.
intros c pos S2 HRT HOK HCALL LOOP mem md regs HST HRG H21 HFD HFS HFZ.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _).
pose proof (bar_ok_sp B MT c HOK) as (_ & Hsp & Hce & _ & _ & _ & _ & _ & _ & Hsp1 & Hwin & _).
pose proof HST as (HRUN & HSL).
pose proof (bm_frame B MT c pos S2 mem md HRT HRUN)
  as (HAR2 & Hin & HF0 & HF64 & HFc & HappD & HFapp & HFimg & HFpres & HFsh).
pose proof (bm_len B MT c HOK) as HLEN.
pose proof (bm_pre16_len c HOK) as HPL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof bm_estack as (Hes & HER & EBS).
pose proof HRUN as ((HJ & _) & _).
pose proof HRG as ((G2 & G3 & G4 & G8 & G9 & G18 & G23 & G25 & G26 & G27) & G19 & G20 & G24).
set (E0 := bm_E regs []).
assert (HEI : img_env VAL A_LIM E0) by apply bm_env_img.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0; apply bm_ew_reg; exact Hn).
assert (E19 : ew E0 19 = Z_to_bv 64 (bar_len (cx_body c))) by (rewrite (EE 19%nat 19%bv eq_refl); exact G19).
assert (U25 : bv_unsigned (ew E0 25) = bar_F c pos + 32)
  by (rewrite (EE 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs BM_Bx [] E0 (mrestrict (w_H (cx_W c)) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (bm_entry_h c pos S2 mem md regs (AF_build_and_receive + 0x1bc) HRT HOK HST HRG) as HS. fold E0 in HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* +0x1bc .. +0x210: the four stores; the five UBSan tests of s9 + 12 .. s9 + 17 are decided not taken by the fact
   on atom 25 (4096 <= s9 <= 2 ^ 47); a1 = 0; the run stops at `beqz s3` *)
paj_run_tok RUN HS HJ SHOK BM_B0.
{ bm_awr_hs U25 c pos. }
bm_md.
destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun a => bar_F c pos + 44 <= a < bar_F c pos + 48) HRT HOK HST HJ HFr HG
  ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(first [lia | cbv beta; rewrite U25 in Hx; lia]))
  ltac:(intros a Ha; cbv beta in Ha; unfold bm_z; lia)) as [HST1 K1].
clear HF HFr HG HST.
assert (HFD1 : forall j, 0 <= j < 12 ->
  aview segs (w_H (cx_W c)) (ms_mem ms) (bar_F c pos + 32 + j) = aview segs (w_H (cx_W c)) mem (bar_F c pos + 32 + j))
  by (intros j Hj; apply K1; cbv beta; lia).
assert (HFZ1 : forall j, 16 <= j < bar_N c ->
  aview segs (w_H (cx_W c)) (ms_mem ms) (bar_F c pos + 32 + j) = Some 0)
  by (intros j Hj; rewrite K1 by (cbv beta; unfold bar_N, bar_nn, bar_s8 in Hj; lia); apply HFZ; lia).
clear K1.
psrr_branch_tok RUN BR HS SHOK BM_B0.
- (* len = 0: to the cut call, a1 = 0 = the sum of the empty body *)
  rewrite branch_eq_U, U_SLit, (U_atom E0 19 _ E19 ltac:(lia)) in Hc. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK BM_B0 (AF_build_and_receive + 0x270).
  { bm_awr_hs U25 c pos. }
  bm_md.
  bm_low HS E0 HEX.
  destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun a => bar_F c pos + 44 <= a < bar_F c pos + 48) HRT HOK HST1 HJ HFr HG
    ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(first [lia | cbv beta; rewrite U25 in Hx; lia]))
    ltac:(intros a Ha; cbv beta in Ha; unfold bm_z; lia)) as [HST2 K2].
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msn) =>
    pose proof (st_ok_pi_region_nth Ex _ _ 0 _ HS eq_refl) as RG0; cbn [ms_mem restrict] in RG0;
    destruct (bm_hdr_bytes Ex _ _ (bar_F c pos) (bar_len (cx_body c)) _ RG0
      ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto)
      ltac:(rewrite ?HEX by lia; exact U25) ltac:(rewrite ?HEX by lia; exact E19) ltac:(lia)) as (A44 & A45 & A46 & A47);
    clear RG0;
    assert (HPRE : garr8 segs (mrestrict (w_H (cx_W c)) (ms_mem msn)) (bar_F c pos + 32)
      (TW.zs (bar_pre16 (cx_dst c) (cx_src c) (cx_body c))))
      by (apply (bm_pre16 c pos (ms_mem msn) HOK); [
            intros j Hj; rewrite K2 by (cbv beta; lia); rewrite HFD1 by lia; exact (HFD j Hj) |
            intros j Hj; replace (bar_F c pos + 38 + j) with (bar_F c pos + 32 + (6 + j)) by lia;
            rewrite K2 by (cbv beta; lia); rewrite HFD1 by lia; replace (bar_F c pos + 32 + (6 + j)) with (bar_F c pos + 38 + j)
              by lia; exact (HFS j Hj) |
            exact A44 | exact A45 | exact A46 | exact A47 ]);
    assert (HZ2 : bm_fzero c pos 16 (ms_mem msn))
      by (intros j Hj; rewrite K2 by (cbv beta; unfold bar_N, bar_nn, bar_s8 in Hj; lia); exact (HFZ1 j Hj));
    assert (HRG2 : bar_rg_run B c pos (ms_regs msn)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX)
  end.
  bm_kreg HS (21%bv : bv 5) 21%nat (21%bv : bv 5) H21 HEX EE R21.
  bm_reg HS (11%bv : bv 5) (w64 (DSpec.sum_bytes (cx_body c))) R11
    ltac:(assert (Eb : cx_body c = []) by (apply length_zero_iff_nil; unfold bar_len in Hc; lia);
          rewrite Eb; reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (HCALL HRT HOK pos S2 mm mdx rg (proj1 HST2) HRG2 (proj2 HST2) R11 R21 HPRE HZ2) end.
- (* 0 < len: +0x214 .. +0x220, a2 = (bodyp <> 0), a3 = a0 = bodyp, a4 = len, the loop at 0 *)
  rewrite branch_eq_U, U_SLit, (U_atom E0 19 _ E19 ltac:(lia)) in Hc. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK BM_B0 (AF_build_and_receive + 0x224).
  { bm_awr_hs U25 c pos. }
  bm_md.
  bm_low HS E0 HEX.
  destruct (bm_st_step c pos S2 _ _ _ _ _ _ (fun a => bar_F c pos + 44 <= a < bar_F c pos + 48) HRT HOK HST1 HJ HFr HG
    ltac:(intros b wlo whi a Hin' Hx; bm_win Hin' Hx ltac:(first [lia | cbv beta; rewrite U25 in Hx; lia]))
    ltac:(intros a Ha; cbv beta in Ha; unfold bm_z; lia)) as [HST2 K2].
  clear HF HFr HG.
  destruct (bm_body c pos S2 _ _ HRT HOK (proj1 HST2) ltac:(unfold bar_len in *; lia)) as (_ & _ & B4 & B47 & _).
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msn) =>
    pose proof (st_ok_pi_region_nth Ex _ _ 0 _ HS eq_refl) as RG0; cbn [ms_mem restrict] in RG0;
    destruct (bm_hdr_bytes Ex _ _ (bar_F c pos) (bar_len (cx_body c)) _ RG0
      ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto)
      ltac:(rewrite ?HEX by lia; exact U25) ltac:(rewrite ?HEX by lia; exact E19) ltac:(lia)) as (A44 & A45 & A46 & A47);
    clear RG0;
    assert (HPRE : garr8 segs (mrestrict (w_H (cx_W c)) (ms_mem msn)) (bar_F c pos + 32)
      (TW.zs (bar_pre16 (cx_dst c) (cx_src c) (cx_body c))))
      by (apply (bm_pre16 c pos (ms_mem msn) HOK); [
            intros j Hj; rewrite K2 by (cbv beta; lia); rewrite HFD1 by lia; exact (HFD j Hj) |
            intros j Hj; replace (bar_F c pos + 38 + j) with (bar_F c pos + 32 + (6 + j)) by lia;
            rewrite K2 by (cbv beta; lia); rewrite HFD1 by lia; replace (bar_F c pos + 32 + (6 + j)) with (bar_F c pos + 38 + j)
              by lia; exact (HFS j Hj) |
            exact A44 | exact A45 | exact A46 | exact A47 ]);
    assert (HZ2 : bm_fzero c pos 16 (ms_mem msn))
      by (intros j Hj; rewrite K2 by (cbv beta; unfold bar_N, bar_nn, bar_s8 in Hj; lia); exact (HFZ1 j Hj));
    assert (HRG2 : bar_rg_run B c pos (ms_regs msn)) by (apply (bm_rg_of c pos regs _ HRG); bm_same_rgs HS EE HEX)
  end.
  bm_kreg HS (21%bv : bv 5) 21%nat (21%bv : bv 5) H21 HEX EE R21.
  bm_reg HS (11%bv : bv 5) (w64 (DSpec.sum_bytes (firstn (Z.to_nat 0) (cx_body c)))) R11 ltac:(reflexivity).
  bm_reg HS (10%bv : bv 5) (w64 (cx_bodyp c + 0)) R10
    ltac:(apply bm_soff0; rewrite ?HEX by lia; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r; exact G20).
  bm_reg HS (13%bv : bv 5) (w64 (cx_bodyp c + 0)) X13
    ltac:(apply bm_soff0; rewrite ?HEX by lia; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r; exact G20).
  bm_reg HS (14%bv : bv 5) (w64 (bar_len (cx_body c) - 0)) V14
    ltac:(apply bm_soff0; rewrite ?HEX by lia; rewrite Z.sub_0_r; exact E19).
  bm_reg HS (12%bv : bv 5) (w64 1) V12
    ltac:(rewrite denot_lit_U, U_SAlu; cbn [zalu_raw];
          rewrite U_SLit, (U_atom _ 20 (cx_bodyp c))
            by (first [rewrite ?HEX by lia; rewrite (EE 20%nat 20%bv eq_refl); exact G20 | lia]);
          change (zcanon 0) with 0;
          rewrite (proj2 (Z.ltb_lt 0 (cx_bodyp c))) by lia; reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (LOOP 0 mm mdx rg HST2 HRG2 R21 R10 X13 V12 V14 R11 HPRE HZ2 ltac:(unfold bar_len in *; lia)) end.
Qed.

(* ------------------------------------------------------------------ *)
(* 14. The piece                                                       *)
(* ------------------------------------------------------------------ *)

Lemma bm_mid : forall c, bar_call_at B MT c -> bar_mid_at B MT c.
Proof.
intros c HCALL HRT HOK pos S2 mem2 md2 regs2 HRUN HRG HSL H22 H11.
pose proof (bm_loop c pos S2 HRT HOK HCALL) as LOOP.
pose proof (bm_s1bc c pos S2 HRT HOK HCALL LOOP) as A1bc.
pose proof (bm_s1a4 c pos S2 HRT HOK A1bc) as A1a4.
pose proof (bm_s194 c pos S2 HRT HOK A1a4) as A194.
pose proof (bm_s184 c pos S2 HRT HOK A194) as A184.
exact (bm_s178 c pos S2 HRT HOK A184 mem2 md2 regs2 (conj HRUN HSL) HRG H22 H11).
Qed.

End mid.

Theorem bar_mid_piece : forall fx rc B MT, @bar_mid_stmt fx rc B MT.
Proof. intros fx rc B MT c. exact (@bm_mid fx rc B MT c). Qed.
