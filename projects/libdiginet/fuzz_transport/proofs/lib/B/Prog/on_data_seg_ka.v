(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 2022 of its 2198 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_wake_seg_head.v, with its module paths and module names changed; 561 of its 683 lines of code are new or changed and 2076 lines of the source are left out. *)
(* on_data_seg_ka: Theorem od_ka : od_ka_stmt (lib/B/Prog/on_data_seg_cut.v), the keepalive piece of the walk of
   on_data (fuzz_transport.asan-ubsan 0x88a48, AF_on_data = 0x77a8 of lib/B/Prog/DgnTransportBList.v): from the cut
   od_ka_at at the entry of diginet_frame_is_keepalive (0x8b128; ra = BASE + OD_KAR, a0 = fp) to od_ntc_at (+0x2ec)
   or od_rel_at (+0x40c). Image B's form of lib/A/Prog/on_data_seg_ka.v: the same steps at image B's names and
   offsets, with the two UBSan premises of image B's leaf and image B's register s8.

   The call. diginet_frame_is_keepalive is a leaf: its statement (lib/B/Prog/diginet_frame_is_keepalive_cg.v
   transport_diginet_frame_is_keepalive_cg, read through DgnTransportBCg.v transport_leaf_at) is applied at the cut's
   registers and memory, its dleaf_post turned into the caller's donor journal at the return by
   DgnTransportBLeafb.v decode_leafb_journal, inside the G journal by TransportGCg.v gx_call_leaf. Its premises at the
   cut's memory mem2:
   - f = fp, cmd = fr_cmd b, body = buf + 30, bb = fr_body b (Z.of_nat (length bb) = fr_body_len b: DgnSpec.v
     length_fr_body at fr_code b = 0);
   - image B's two UBSan premises: f mod 8 = 0 (trans_dframe_at's fp mod 8 = 0) and, on the path cmd = 0 and
     length 1, body <> 0 (trans_dframe_at's 0 < buf, so buf + 30 <> 0);
   - the bytes at f + 30 and f + 32 .. f + 47: the cells C1 (b8 (fr_cmd b)), C8 (buf + 30), C8 (fr_body_len b) of
     frame_f_bytes buf b fj (odka_ffb_at), at the entry memory by trans_dframe_at's garr8, kept to mem2 by od_cur's
     acall_kept_g (f lies in a frame of frames Sc: its frame clause; no byte of ondata_wr is a frame byte: every such
     byte lies in G's hull, an image range, odka_wr_hull);
   - the bytes bb at body: b's bytes from 30 on (trans_dframe_at's garr8 of b at buf), kept by acall_kept_g in each case
     of trans_src_ok of [buf, buf + length b) (odka_src_kept: block, frame, machine stack or TRANS_RO_RD; G is ruled out
     by trans_dframe_at, no byte of the range is a byte of G);
   - f's 64 bytes visible and marked usable at mem2 (DgnTransportBCg.v decode_rd_ok_fake_kept_ge0 with the frame
     clause of acall_kept_g), the body's (odka_src_kept), hence the addressable / rng premises (DgnTransportBLeafb.v
     decode_leafb_addressable / decode_leafb_rng / decode_leafb_rng_shadow);
   - the frame [sp1 - 16, sp1) and the leaf's ESTACK window inside the caller's journal window (sp1 = the realigned
     sp, sp - 176 <= sp1 <= sp - 160, ONDATA_STK = 8832); asan_cells (decode_leafb_asan_cells).
   Its post: a0 = 1 when fr_keepalive b, else 0; every byte outside [sp1 - ESTACK, sp1) kept, presence kept, the
   callee-saved registers kept (s6 = fp + 28 and s8 = the shadow address of fp + 28 among them), the caller's G
   journal at the same layout and state.

   The branch. `bnez a0` (+0x2e8) is taken up from a state with no region: a keepalive runs the branch to +0x40c and
   concludes by od_rel_at with Bw' = ondata_w3 (ondata_w2 B1 b r now) b (on_data_cg.v ondata_model,
   on_data_seg_cut.v od_some_inv: odka_rel_model) and g_fail_next Bw' = g_fail_next B1 (the stores of ondata_w2 /
   ondata_w3 are g_s fields: lib/Prog/T/on_data.v od_ok_acks .. od_ok_dc); otherwise the run ends at +0x2ec and
   concludes by od_ntc_at with fr_keepalive b = false.
   What the cut carried moves to the cut's memory (odka_cur_move): the leaf window lies inside on_data's window, above
   alloc_ceiling and below the saved words and the frame word at sp1 + 24, so TransportGFrame.v dk_kept_step_gw
   carries acall_kept_g, and the world relation is kept (G lies below alloc_ceiling). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg on_data_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  DgnTransportBLeafb DgnTransportBCgRun LeafCgKit AsanKA diginet_frame_is_keepalive_c diginet_frame_is_keepalive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem ExecF Frame Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require on_data.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module OdkaLB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBLeafb.
Module OdkaCR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBCgRun.
Module OdkaCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module OdkaKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module OdkaLc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_is_keepalive_c.
Module OdkaL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_is_keepalive_cg.
Module OdkaEF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
Module OdkaC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module OdkaP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
Module OdkaOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module OdkaPW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.on_data.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                         *)
(* ------------------------------------------------------------------ *)

(* Every byte the call may store lies in G's hull. *)
Lemma odka_wr_hull : forall Bw b a, ondata_wr Bw b a -> TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI.
Proof.
intros Bw b a H.
unfold ondata_wr, iosend_wr, notice_wr in H.
change (TI.n_kind (ondata_ntc Bw b)) with TS0.DIGINET_N_DATA in H.
set (g := TW.GOT_n Bw) in H. clearbody g.
unfold twb_fld in H.
unfold TW.A_S_stats_tx_frames, TW.A_S_stats_tx_acks, TW.A_S_stats_rx_data,
  TW.A_S_stats_rx_desk_retries, TW.A_S_backoff_until_us, TW.A_S_stats_rx_duplicates, TW.A_S_desk_counter,
  TW.A_S_desk_counter_valid, TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter, TW.A_M_next_ka,
  TW.A_M_last_display, TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter, TW.A_M_fly_retries,
  TW.A_M_fly_sent, TW.A_M_fly_len, TW.A_M_fly_frame, TW.A_Cmd_st, TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.A_GOT_n,
  TW.A_GOT_acked, TW.A_GOT_desk, TW.A_GOT_ndata, TW.A_GOT_foreign, SENDCTL_F in *.
unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI, TB_g_s, TB_g_fail_next, TB_GOT, TB_g_last_counter, TB_M, TB_g_cmd, TB_g_q,
  TB_g_nq, TW.OFF_g_s, TW.OFF_g_fail_next, TW.OFF_GOT, TW.OFF_g_last_counter, TW.OFF_M, TW.OFF_g_cmd, TW.OFF_g_q,
  TW.OFF_g_nq, TW.SZ_g_q, TW.SZ_g_nq, TC.CMDS_MAX, TC.TRANS_MAX, TC.SPEC_MAX_FRAME,
  TS0.DIGINET_N_DATA, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in *.
repeat match goal with
  | Hx : _ \/ _ |- _ => destruct Hx as [Hx|Hx]
  | Hx : _ /\ _ |- _ => let Hy := fresh "Hy" in destruct Hx as [Hy Hx]
  | Hx : exists _, _ |- _ => let s := fresh "s" in destruct Hx as [s Hx]
  end; lia.
Qed.

(* The keepalive path: the model's world is ondata_w3 (ondata_w2 B1 b r now) b. *)
Lemma odka_rel_model : forall I Fr Bw b now Bw' B1 r f,
  TSS.on_data_m I Fr Bw b now = Some (Bw', tt) ->
  TSS.send_control_m I Fr Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) = Some (B1, (r, f)) ->
  ondata_dup (ondata_w2 B1 b r now) b = false -> DSpec.fr_keepalive b = true ->
  Bw' = ondata_w3 (ondata_w2 B1 b r now) b.
Proof.
intros I Fr Bw b now Bw' B1 r f Hm Hsc Hd Hk.
rewrite ondata_model, Hsc in Hm. cbv beta iota in Hm.
rewrite Hd, Hk in Hm. cbv beta iota in Hm.
symmetry. exact (od_some_inv _ _ Hm).
Qed.

(* The stores of ondata_w2 and ondata_w3 are g_s fields: g_fail_next is send_control's. *)
Lemma odka_gf : forall B1 b r now, length B1 = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (ondata_w3 (ondata_w2 B1 b r now) b) = TW.g_fail_next B1.
Proof.
intros B1 b r now L.
assert (E2 : ondata_w2 B1 b r now = OdkaPW.od_retry (OdkaPW.od_data (OdkaPW.od_acks B1 r)) b now) by reflexivity.
destruct (OdkaPW.od_ok_acks B1 r L) as [G1 L1].
destruct (OdkaPW.od_ok_data _ L1) as [G2 L2].
destruct (OdkaPW.od_ok_retry _ b now L2) as [G3 L3].
destruct (OdkaPW.od_ok_dc _ (DSpec.fr_send b) L3) as [G4 _].
unfold ondata_w3. rewrite E2, G4, G3, G2, G1. reflexivity.
Qed.

(* The 18 bytes 30 .. 47 of struct diginet_frame: cmd, ncmds, body, body_len. *)
Definition odka_mid (buf : Z) (b : list byte) : list byte :=
  [DSpec.b8 (DSpec.fr_cmd b); DSpec.b8 (DSpec.fr_ncmds b)] ++ LMem.le8 (Z_to_bv 64 (buf + 30)) ++
  LMem.le8 (Z_to_bv 64 (DSpec.fr_body_len b)).

Lemma odka_ffb : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  exists pre post : list byte, length pre = 30%nat /\
    frame_f_bytes buf b fj = map (fun x : byte => bv_unsigned x) (pre ++ odka_mid buf b ++ post).
Proof.
intros buf b fj Hc Hfj.
destruct (DSpec.fr_code_ok b Hc) as (Hl & _).
exists (DSpec.fr_dst b ++ DSpec.fr_src b ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_ethertype b)) ++ firstn 2 (skipn 14 fj) ++
  LMem.le2 (Z_to_bv 64 (DSpec.fr_numbytes b)) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_sum b)) ++
  LMem.le4 (Z_to_bv 64 (DSpec.fr_send b)) ++ LMem.le4 (Z_to_bv 64 (DSpec.fr_ack b)) ++
  LMem.le2 (Z_to_bv 64 (DSpec.fr_retry b))).
exists (LMem.le8 (Z_to_bv 64 (DSpec.fr_pad_len b)) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_body_sum b)) ++
  [DSpec.b8 (if DSpec.fr_sum b =? DSpec.fr_body_sum b then 1 else 0)] ++ skipn 59 fj).
split.
- rewrite !length_app, !LMem.length_le2, !LMem.length_le4. unfold DSpec.fr_dst, DSpec.fr_src.
  rewrite !length_firstn, !length_skipn. lia.
- unfold frame_f_bytes, frame_f_cells. rewrite Hc. cbn [Z.eqb]. unfold OdkaP.parse_cells.
  cbn [OdkaC.cells_bytes OdkaC.cbytes]. rewrite ?app_nil_r. unfold odka_mid. rewrite <- !app_assoc. reflexivity.
Qed.

(* The bytes of the body, as b's bytes from 30 on. *)
Lemma odka_nth_body : forall b i d, (i < length (DSpec.fr_body b))%nat ->
  nth i (DSpec.fr_body b) d = nth (30 + i) b d.
Proof.
intros b i d Hi. unfold DSpec.fr_body in *.
assert (Hlen : (30 < length b)%nat) by (rewrite length_firstn, length_skipn in Hi; lia).
set (L := Z.to_nat (DSpec.fr_body_len b)) in *.
set (X := skipn 30 b) in *.
assert (E1 : nth i X d = nth i (firstn L X) d).
{ rewrite <- (firstn_skipn L X) at 1. apply app_nth1. exact Hi. }
rewrite <- E1. unfold X.
assert (H30 : length (firstn 30 b) = 30%nat) by (rewrite length_firstn; lia).
rewrite <- (firstn_skipn 30 b) at 2.
rewrite app_nth2 by lia. rewrite H30. replace (30 + i - 30)%nat with i by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Bytes, shadow and footprint at the cut's memory                   *)
(* ------------------------------------------------------------------ *)

Section ka. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A byte of a garr8 list read off the view (TransportGNoticeB.v aview_of_val_mem1 at the list's j-th cell). *)
Lemma odka_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 segs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview segs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H mem a l j G Hj. destruct (G j Hj) as [V R]. exact (aview_of_val_mem1 H mem _ _ V R).
Qed.

(* Bytes read raw from their view. *)
Lemma odka_bytes_of_aview : forall (W : world segs) mem p (bs : list byte),
  0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat ->
     aview segs (w_H W) mem (p + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  LMem.bytes_at segs mem p bs.
Proof.
intros W mem p bs H0 H1 HA. split; [exact H0|]. split; [exact H1|]. intros i Hi.
destruct (OdkaLB.decode_leafb_mrd_aview W mem _ _ (HA i Hi)) as (b0 & Hb & Hv).
transitivity (Some b0); [exact Hb|].
rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. exact Hv.
Qed.

(* The bytes 30 .. 47 of the frame at fp, read from frame_f_bytes. *)
Lemma odka_ffb_at : forall (H : word -> bool) mem fp buf b fj i,
  garr8 segs (mrestrict H mem) fp (frame_f_bytes buf b fj) -> DSpec.fr_code b = 0 -> length fj = 64%nat ->
  (i < 18)%nat ->
  aview segs H mem (fp + 30 + Z.of_nat i) = Some (bv_unsigned (nth i (odka_mid buf b) (Z_to_bv 8 0))).
Proof.
intros H mem fp buf b fj i HG Hc Hfj Hi.
destruct (odka_ffb buf b fj Hc Hfj) as (pre & post & Hl & E).
assert (Hm : length (odka_mid buf b) = 18%nat)
  by (unfold odka_mid; rewrite !length_app, !LMem.length_le8; reflexivity).
rewrite E in HG.
replace (fp + 30 + Z.of_nat i) with (fp + Z.of_nat (30 + i)) by lia.
rewrite (odka_garr8_aview H mem fp _ (30 + i) HG) by (rewrite length_map, !length_app; lia).
f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, !length_app; lia).
rewrite map_nth. cbv beta. f_equal.
rewrite app_nth2 by lia. rewrite Hl. replace (30 + i - 30)%nat with i by lia.
rewrite app_nth1 by lia. reflexivity.
Qed.

(* Application memory from amem_range. *)
Lemma odka_app : forall p n a, amem_range p n -> p <= a < p + n -> 0 <= p -> ACells.app_mem a.
Proof.
intros p n a Ham Ha H0. pose proof (@asan_consts rc) as (_ & _ & C3 & C4 & C5).
unfold ACells.app_mem, ACells.LOWMEM_END, ACells.HIGHMEM_BEG, ACells.APPMEM_END.
unfold amem_range in Ham. destruct Ham as [Hm1 | Hm1]; [left | right]; lia.
Qed.

(* addressable of a sub-range of a decode_rd_ok range. *)
Lemma odka_addr : forall (W : world segs) mem q n q' n', decode_rd_ok W mem q n -> q <= q' -> q' + n' <= q + n ->
  0 <= n' -> ACells.addressable mem q' n'.
Proof.
intros W mem q n q' n' (Hv & HRA & Hh & Ham & H0 & H63) H1 H2 H3.
pose proof (@asan_consts rc) as (_ & _ & C3 & C4 & C5).
apply (OdkaLB.decode_leafb_addressable W mem q' n' (fun x Hx => HRA x ltac:(lia))).
- lia.
- lia.
- unfold ACells.APPMEM_END. unfold amem_range in Ham. lia.
- intros i Hi. apply (odka_app q n); [exact Ham | lia | lia].
Qed.

(* The bytes of a decode_rd_ok range are visible. *)
Lemma odka_vis : forall (W : world segs) mem q n, decode_rd_ok W mem q n ->
  forall a, q <= a < q + n -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W mem q n (Hv & _) a Ha. specialize (Hv a Ha).
destruct (aview segs (w_H W) mem a) as [z|] eqn:Ez; [|contradiction].
exact (OdkaLB.decode_leafb_aview_vis W mem a z Ez).
Qed.

Lemma odka_rng : forall (W : world segs) mem q n q' n', decode_rd_ok W mem q n -> q <= q' -> q' + n' <= q + n ->
  0 <= n' -> OdkaEF.rng (OdkaCK.RNG_W (world segs) (@w_H segs) W) q' n'.
Proof.
intros W mem q n q' n' Hrd H1 H2 H3. pose proof Hrd as (_ & _ & _ & _ & H0 & H63).
apply (OdkaLB.decode_leafb_rng W); [lia | lia |]. intros a Ha. apply (odka_vis W mem q n Hrd). lia.
Qed.

(* The shadow of m bytes at x inside one granule is one byte. *)
Lemma odka_sh1 : forall x m, 0 <= x -> 0 < m -> x mod 8 + m <= 8 ->
  ACells.shadow_addr (x + m - 1) - ACells.shadow_addr x + 1 = 1.
Proof.
intros x m Hx Hm Hxm. unfold ACells.shadow_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
assert (E1 : (x + m - 1) / 8 = x / 8).
{ replace (x + m - 1) with (x / 8 * 8 + (x mod 8 + m - 1)) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (x mod 8 + m - 1) 8) by lia. lia. }
lia.
Qed.

Lemma odka_rng_sh : forall (W : world segs) mem q n x m, decode_rd_ok W mem q n -> q <= x -> x + m <= q + n ->
  0 < m -> x mod 8 + m <= 8 ->
  OdkaEF.rng (OdkaCK.RNG_W (world segs) (@w_H segs) W) (ACells.shadow_addr x) 1.
Proof.
intros W mem q n x m (Hv & HRA & _ & _ & H0 & H63) H1 H2 Hm Hxm.
pose proof (OdkaLB.decode_leafb_rng_shadow W mem x m (fun y Hy => HRA y ltac:(lia)) ltac:(lia) Hm ltac:(lia)) as RS.
rewrite (odka_sh1 x m ltac:(lia) Hm Hxm) in RS. exact RS.
Qed.

(* G's hull lies inside one loaded segment of image B (decided by vm_compute). *)
Lemma odka_hull_img : forall a, TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI -> in_img segs a.
Proof.
intros a Ha.
exact (OdkaCR.decode_covers_img TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) a
  ltac:(vm_compute; reflexivity) ltac:(lia)).
Qed.

(* The frame [q, q + n) of frames Sc: its bytes at the cut are those at entry (no byte of ondata_wr is a frame
   byte: ondata_wr lies in G's hull, an image range). *)
Lemma odka_fake_kept : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 slo shi Bw b q n,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi (ondata_wr Bw b) ->
  decode_in_fake lyc Sc q n ->
  forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a.
Proof.
intros lyc Sc W memc mdc W2 mem2 slo shi Bw b q n LAWS HAR (K1 & K2 & K3 & K4 & K5 & K6) (cid & pos & Hin & F1 & F2)
  a Ha.
apply (K4 cid pos a Hin).
- left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- intros Hw. pose proof (odka_wr_hull Bw b a Hw) as Hh.
  apply (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia)).
  exact (odka_hull_img a Hh).
Qed.

(* The shadow bytes of the frames of Sc at the cut are those at entry (they lie above G's hull). *)
Lemma odka_fake_sh_kept : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 slo shi Bw b,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi (ondata_wr Bw b) ->
  forall cid pos s, In (cid, pos) (frames Sc) ->
    in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
    aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s.
Proof.
intros lyc Sc W memc mdc W2 mem2 slo shi Bw b LAWS HAR (K1 & K2 & K3 & K4 & K5 & K6) cid pos s Hin Hs.
apply (K4 cid pos s Hin); [right; exact Hs|].
intros Hw. pose proof (odka_wr_hull Bw b s Hw) as Hh.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
unfold in_zr in Hs. cbn [fst snd] in Hs. unfold shadow_addr, SHADOW_OFF, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in *. lia.
Qed.

Lemma odka_rd_fake : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 slo shi Bw b q n,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi (ondata_wr Bw b) ->
  decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> 0 <= n -> decode_rd_ok W2 mem2 q n.
Proof.
intros lyc Sc W memc mdc W2 mem2 slo shi Bw b q n LAWS HAR HK HF Hrd Hn.
exact (decode_rd_ok_fake_kept_ge0 B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn
  (odka_fake_kept lyc Sc W memc mdc W2 mem2 slo shi Bw b q n LAWS HAR HK HF)
  (odka_fake_sh_kept lyc Sc W memc mdc W2 mem2 slo shi Bw b LAWS HAR HK)).
Qed.

(* A source range of the call (trans_src_ok at entry, outside the call's window, apart from G): its bytes at the cut
   are those at entry, and it is visible and marked usable there. *)
Lemma odka_src_kept : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2
    (regs : bvmap 5 word) Bw b q n,
  AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - ONDATA_STK) (spZ regs) (ondata_wr Bw b) ->
  trans_src_ok B lyc Sc W memc q n -> decode_off_win regs ONDATA_STK q n ->
  (forall x, q <= x < q + n -> ~ inG TG.G_HARNESS_B x) -> 0 < n ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  decode_rd_ok W2 mem2 q n.
Proof.
intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 regs Bw b q n LAWS HRO HRE HAR HAR2 Hbl Elo Ehi HK Hs Hoff HnG Hn.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (@asan_consts rc) as (C1 & C2 & C3 & C4 & C5).
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
- split.
  + intros a Ha. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _).
    assert (Hr : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
    replace a with (bA + (a - bA)) by lia. apply (K2 bA nA (a - bA) Hin); [lia|].
    intros Hw. pose proof (odka_wr_hull Bw b _ Hw) as Hh.
    apply (blk_img segs B LAWS lyc Sc W memc mdc bA nA (bA + (a - bA)) HAR Hin ltac:(lia)).
    exact (odka_hull_img (bA + (a - bA)) Hh).
  + apply (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 q n HAR2); [|exact Hn].
    left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
- destruct HL as [HF | [(HG & _) | [(S1 & S3) | (HR & Hsh)]]].
  + split; [exact (odka_fake_kept lyc Sc W memc mdc W2 mem2 _ _ Bw b q n LAWS HAR HK HF)|].
    exact (odka_rd_fake lyc Sc W memc mdc W2 mem2 _ _ Bw b q n LAWS HAR HK HF Hrd ltac:(lia)).
  + exfalso. exact (HnG q ltac:(lia) (HG q ltac:(lia))).
  + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2].
    assert (KS : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
    { intros a Ha. apply K1; [lia|]. unfold decode_off_win in Hoff. intros Hw. destruct Hoff as [Ho | Ho]; lia. }
    split; [exact KS|].
    destruct (stack_zshadow_ra_ge0 B ly2 S2 W2 mem2 md2 q n HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
      ltac:(rewrite Ehi; lia)) as [Ha Hh].
    exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KS Ha Hh).
  + assert (KR : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
    { intros a Ha. pose proof (HR a Ha) as Ha'.
      destruct (trans_ro_rd_scoped B HRO HRE a Ha') as [N1 N2].
      apply K3; [exact (trans_ro_img a Ha') | exact (HnG a Ha) | exact N1 | exact N2]. }
    split; [exact KR|].
    destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
    exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KR Ha Hh).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. What the cut carries, at a later memory                           *)
(* ------------------------------------------------------------------ *)

(* od_cur at a later memory that keeps every byte outside a window [lo, hi) inside the call's window, above
   alloc_ceiling and below the 13 saved words, and keeps presence. *)
Lemma odka_cur_move : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
    b Bw pos F ly2 S2 (W2 : world segs) mem2 md2 mem3 md3 e lo hi,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  od_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONDATA_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  alloc_ceiling <= lo -> spZ regs - ONDATA_STK <= lo -> lo <= hi -> hi <= spZ regs - 104 -> spZ regs <= 2 ^ 47 ->
  0 <= F -> F + OD_FBYTES <= alloc_ceiling ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  od_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e lo hi
  LAWS HAR (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 Hlo1 Hlo2 Hlh Hhi1 H47 HF0 HFc KM GM.
pose proof (@asan_consts rc) as (C1 & C2 & C3 & C4 & C5).
assert (OS : ONDATA_STK = 8832) by reflexivity.
unfold OD_FBYTES in HFc.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 mem3
    (spZ regs - ONDATA_STK) (spZ regs) (ondata_wr Bw b) (fun a => lo <= a < hi) HAR HK KM GM).
  + intros a Ha _. cbv beta in Ha. lia.
  + intros bb m i Hb Hi Ha. exfalso. cbv beta in Ha.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HAR Hb) as (_ & H4096 & Hce & _). lia.
  + intros a Ha Hi _ _ _. cbv beta in Ha. pose proof (transportb_segs_low a Hi). lia.
  + intros cid pos0 a Hin Hr Ha. exfalso. cbv beta in Ha.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
- apply Forall_forall. intros o Hin. pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Ho. cbv beta in Ho.
  assert (Hb : 8 <= fst o <= 104).
  { unfold OD_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [fst]; lia|]). destruct Hin. }
  rewrite <- Ho. apply rdword_ext. intros k0 Hk0. apply KM; lia.
- rewrite <- HFL. apply rdword_ext. intros k0 Hk0. unfold OD_FBYTES in *. apply KM; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The branch at +0x2e8, from a state with no region                 *)
(* ------------------------------------------------------------------ *)

Definition odka_B0 : Z * Z := (0, 0).
Definition odka_ss : sstate := mkSS OD_KAR sr_atoms [] None (mkFacts [] [] []).
Definition odka_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma odka_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (odka_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold odka_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma odka_env_img : forall regs, img_env VAL A_LIM (odka_E regs).
Proof. intros regs. unfold odka_E. apply Eimg_env. Qed.

Lemma odka_entry : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (odka_E regs) odka_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OD_KAR)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold odka_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac odka_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register at the machine state of HS, from the equation Q of its value at the branch. *)
Ltac odka_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    odka_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (odka_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The awr obligation's regions, computed. *)
Ltac odka_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* After the one instruction to a cut (a run from a state with no region): every byte of the view as at the branch
   (KD), presence grown (GR). *)
Ltac odka_after_cut HS W KD GR m5 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (@can_aview_kept_frame tfibsegs E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

(* ------------------------------------------------------------------ *)
(* 5. The piece                                                          *)
(* ------------------------------------------------------------------ *)

Lemma odka_holds : @od_ka_stmt fx rc B MT.
Proof.
unfold od_ka_stmt. intros NTC REL.
unfold od_ka_at.
intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B1 r f ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof HLAWS as (HPCS & HCELLS & HONC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HCALL as (_ & _ & LEAF & _ & _).
pose proof HFIX as (HPRE & HTFG & Esp1 & EF & HF4096 & HF64 & HFc & HFapp).
pose proof HPRE as (HJe & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw & Hgf & Hm &
  HTF & HROM & HAP & HI1 & HI4 & HI3 & Hcnt & Hev).
pose proof HDF as (Hcode & Hbuf0 & Hgb & Hsrc & Hoffb & HnGb & Hfp0 & Hfp8 & Hfj & HgF & Hfake & Hrdf & Hofff).
pose proof HCUR as (HC0 & HW24 & Hsc & Htw2 & Hgf1 & Hdup).
pose proof HC0 as (HJ2 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R25 & R26) & R18 & R19 & R20 & R21 & R27) & R1 & R22 & R24 & R10).
change FRAME_F_SIZE with 64 in Hfake, Hrdf, Hofff.
unfold OD_FBYTES in HFc.
(* the journals, the layout's stack *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof HJe as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (H16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (_ & Hly2 & _).
destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo0 & Ehi0 & _).
destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
clear HJi0 HJi2 memS0 memS2.
assert (Elo : ly_stk_lo ly2 = ly_stk_lo lyc) by congruence.
assert (Ehi : ly_stk_hi ly2 = ly_stk_hi lyc) by congruence.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
pose proof (@asan_consts rc) as (C1 & C2 & C3 & C4 & C5).
assert (OS : ONDATA_STK = 8832) by reflexivity.
assert (ES : ESTACK = 4096) by reflexivity.
assert (FS : OdkaLc.DIGINET_FRAME_IS_KEEPALIVE_FRAME = 16) by reflexivity.
(* the realigned stack pointer *)
assert (SP1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONDATA_FRAME.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D32.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M32.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct SP1 as [SP1 SP32].
assert (SP2 : spZ regs2 = sp1).
{ change (spZ regs2) with (bv_unsigned (YK11.getr regs2 2)). rewrite R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (SPU : bv_unsigned (YK11.getr regs2 (Z_to_bv 5 2)) = sp1) by exact SP2.
assert (M16 : (sp1 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0.
  rewrite SP32 in D1. rewrite H16 in D0.
  replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
(* the frame f and the bytes at buf *)
pose proof (DSpec.fr_code_ok b Hcode) as (Hlb & _ & Hnb1 & Hnb2).
pose proof (DSpec.fr_body_len_ok b Hcode) as (Hbl0 & Hpad0 & Hbl1).
assert (LB : Z.of_nat (length (DSpec.fr_body b)) = DSpec.fr_body_len b)
  by (rewrite (DSpec.length_fr_body b Hcode), Z2Nat.id by lia; reflexivity).
pose proof (DSpec.at8_range b 28) as Hcmd. change (DSpec.at8 b 28) with (DSpec.fr_cmd b) in Hcmd.
assert (Hlen0 : 0 < Z.of_nat (length b)) by lia.
pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc buf _ HARc Hsrc Hlen0) as Hrdb.
pose proof Hrdb as (_ & _ & _ & _ & Hb0 & Hb63).
pose proof Hrdf as (_ & _ & _ & _ & Hf0' & Hf63).
destruct Hfake as (fcid & fpos & Hfin & Hfk1 & Hfk2).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc fcid fpos HARc Hfin) as (Hfb1 & Hfb2 & _).
assert (Hfake : decode_in_fake lyc Sc fp 64) by (exists fcid, fpos; split; [exact Hfin | lia]).
assert (KF : forall a, fp <= a < fp + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a)
  by exact (odka_fake_kept lyc Sc W memc mdc W2 mem2 _ _ Bw b fp 64 LAWS HARc HK Hfake).
pose proof (odka_rd_fake lyc Sc W memc mdc W2 mem2 _ _ Bw b fp 64 LAWS HARc HK Hfake Hrdf ltac:(lia)) as Hrdf2.
destruct (odka_src_kept lyc Sc W memc mdc ly2 S2 W2 mem2 md2 regs Bw b buf (Z.of_nat (length b)) LAWS HROU HRNE
  HARc HAR2 Hbl Elo Ehi HK Hsrc Hoffb HnGb Hlen0) as [KB Hrdb2].
assert (HFB : forall i, (i < 18)%nat ->
  aview segs (w_H W2) mem2 (fp + 30 + Z.of_nat i) = Some (bv_unsigned (nth i (odka_mid buf b) (Z_to_bv 8 0)))).
{ intros i Hi. rewrite KF by lia. exact (odka_ffb_at (w_H W) memc fp buf b fj i HgF Hcode Hfj Hi). }
assert (M30 : (fp + 30) mod 8 = 6) by (rewrite Z.add_mod, Hfp8 by lia; reflexivity).
assert (M32 : (fp + 32) mod 8 = 0) by (rewrite Z.add_mod, Hfp8 by lia; reflexivity).
assert (M40 : (fp + 40) mod 8 = 0) by (rewrite Z.add_mod, Hfp8 by lia; reflexivity).
(* ---- the call of diginet_frame_is_keepalive (a leaf), in the G journal ---- *)
assert (RA : YK0s.ret_ok (YK11.getr regs2 1)).
{ rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold OD_KAR, AF_on_data; lia | reflexivity]. }
rewrite <- OdkaL.diginet_frame_is_keepalive_at_sigma.
eapply SRr_bind.
{ eapply (gx_call_leaf (fx := fx) (rc := rc) (SK := tfib_sink_head) segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0
    ((ONDATA_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) _ (YK11.getr regs2 1) _ HJ2).
  intros memS HJS.
  eapply (OdkaLB.decode_leafb_journal (fx := fx) (SK := tfib_sink_head) B LAWS W2 regs2 mem2 STK sp0 FP ly S W0
    memS md0 ((ONDATA_CID, pos) :: own) ly2 S2 md2 (k + e) (sp1 - sp0) OdkaLc.DIGINET_FRAME_IS_KEEPALIVE
    (Some (if DSpec.keepalive_of (DSpec.fr_cmd b) (Z.of_nat (length (DSpec.fr_body b))) (DSpec.fr_body b)
           then 1 else 0)) [] (fun _ => True) HJS).
  - rewrite SP2. lia.
  - exact M16.
  - lia.
  - lia.
  - exact RA.
  - exact (eq_trans R3 Hgp).
  - exact (eq_trans R4 Htp).
  - intros a Ha. unfold OdkaLB.LCK.in_wr in Ha. inversion Ha.
  - intros HPRE2.
    pose proof (LEAF fx) as LF.
    unfold transport_leaf_at, OdkaL.transport_diginet_frame_is_keepalive_cg in LF.
    specialize (LF ly2 S2 W2 regs2 mem2 md2 fp (DSpec.fr_cmd b) (buf + 30) (sp1 - 16) (DSpec.fr_body b) HPRE2).
    cbv zeta in LF.
    apply LF; clear LF.
    + exact R10.
    + lia.
    + exact Hfp8.
    + exact Hcmd.
    + lia.
    + apply (odka_bytes_of_aview W2 mem2 (fp + 30) [DSpec.b8 (DSpec.fr_cmd b)]); [lia | cbn [length]; lia |].
      intros i Hi. cbn [length] in Hi. replace i with 0%nat by lia. exact (HFB 0%nat ltac:(lia)).
    + rewrite LB.
      apply (odka_bytes_of_aview W2 mem2 (fp + 32)).
      * lia.
      * rewrite length_app, !LMem.length_le8. lia.
      * intros i Hi. rewrite length_app, !LMem.length_le8 in Hi.
        replace (fp + 32 + Z.of_nat i) with (fp + 30 + Z.of_nat (2 + i)) by lia.
        rewrite (HFB (2 + i)%nat ltac:(lia)). reflexivity.
    + apply (odka_bytes_of_aview W2 mem2 (buf + 30) (DSpec.fr_body b)); [lia | rewrite LB; lia |].
      intros i Hi. pose proof Hi as Hi'. apply Nat2Z.inj_lt in Hi'. rewrite LB in Hi'.
      rewrite KB by lia.
      replace (buf + 30 + Z.of_nat i) with (buf + Z.of_nat (30 + i)) by lia.
      rewrite (odka_garr8_aview (w_H W) memc buf (TW.zs b) (30 + i) Hgb)
        by (unfold TW.zs; rewrite length_map; lia).
      f_equal. rewrite (odka_nth_body b i (Z_to_bv 8 0) Hi). unfold TW.zs.
      rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
      rewrite map_nth. reflexivity.
    + rewrite SPU. apply (OdkaLB.decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS); lia.
    + rewrite SPU, FS. lia.
    + exact (OdkaLB.decode_leafb_asan_cells B HCELLS ly2 S2 W2 mem2 md2 (proj1 HJS)).
    + rewrite SPU, FS. apply (@OdkaLB.decode_leafb_app_stack rc). lia.
    + rewrite SPU. apply (@OdkaLB.decode_leafb_app_stack rc). lia.
    + unfold OdkaKA.off_stk. rewrite SPU, FS. left. unfold ACells.GOT_CELL_K. lia.
    + unfold OdkaKA.off_stk. rewrite SPU, FS. left. unfold ACells.CELL_K. lia.
    + unfold OdkaKA.off_stk. rewrite SPU, FS. left. lia.
    + exact (odka_addr W2 mem2 fp 64 (fp + 30) 1 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _. split.
      * unfold OdkaKA.off_stk. rewrite SPU, FS. left. lia.
      * exact (odka_addr W2 mem2 fp 64 (fp + 40) 8 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _ HL1. rewrite LB in HL1.
      split; [|split; [|split; [|split]]].
      * unfold OdkaKA.off_stk. rewrite SPU, FS. left. lia.
      * exact (odka_addr W2 mem2 fp 64 (fp + 32) 8 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia)).
      * unfold OdkaKA.off_stk. rewrite SPU, FS. unfold decode_off_win in Hoffb.
        destruct Hoffb as [Ho | Ho]; [left | right]; lia.
      * exact (odka_addr W2 mem2 buf (Z.of_nat (length b)) (buf + 30) 1 Hrdb2 ltac:(lia) ltac:(lia) ltac:(lia)).
      * lia.
    + rewrite SPU, FS. apply (OdkaLB.decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS); lia.
    + exact (proj1 (OdkaLB.decode_leafb_rng_cells W2)).
    + exact (proj2 (OdkaLB.decode_leafb_rng_cells W2)).
    + exact (odka_rng W2 mem2 fp 64 (fp + 30) 1 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (odka_rng_sh W2 mem2 fp 64 (fp + 30) 1 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _. exact (odka_rng W2 mem2 fp 64 (fp + 40) 8 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _. exact (odka_rng_sh W2 mem2 fp 64 (fp + 40) 8 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _ _. exact (odka_rng W2 mem2 fp 64 (fp + 32) 8 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _ _. exact (odka_rng_sh W2 mem2 fp 64 (fp + 32) 8 Hrdf2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _ HL1. rewrite LB in HL1.
      exact (odka_rng W2 mem2 buf (Z.of_nat (length b)) (buf + 30) 1 Hrdb2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _ HL1. rewrite LB in HL1.
      pose proof (Z.mod_pos_bound (buf + 30) 8 ltac:(lia)).
      exact (odka_rng_sh W2 mem2 buf (Z.of_nat (length b)) (buf + 30) 1 Hrdb2 ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia)). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HRES & HEFF & HGR & _).
specialize (HRES _ eq_refl). rewrite LB in HRES.
change (DSpec.keepalive_of (DSpec.fr_cmd b) (DSpec.fr_body_len b) (DSpec.fr_body b)) with (DSpec.fr_keepalive b)
  in HRES.
rewrite R1.
(* the registers after the call *)
assert (X2 : YK11.getr regs3 2 = w64 sp1) by exact (eq_trans (HP3 2 ltac:(unfold acallee_saved; lia)) R2).
assert (X3 : YK11.getr regs3 3 = YK11.getr regs 3) by exact (eq_trans (HP3 3 ltac:(unfold acallee_saved; lia)) R3).
assert (X4 : YK11.getr regs3 4 = YK11.getr regs 4) by exact (eq_trans (HP3 4 ltac:(unfold acallee_saved; lia)) R4).
assert (X8 : YK11.getr regs3 8 = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(unfold acallee_saved; lia)) R8).
assert (X9 : YK11.getr regs3 9 = w64 sp1) by exact (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) R9).
assert (X18 : YK11.getr regs3 18 = w64 (SHADOW_OFF + (fp + 20) / 8))
  by exact (eq_trans (HP3 18 ltac:(unfold acallee_saved; lia)) R18).
assert (X19 : YK11.getr regs3 19 = w64 ONDATA_S) by exact (eq_trans (HP3 19 ltac:(unfold acallee_saved; lia)) R19).
assert (X20 : YK11.getr regs3 20 = w64 fp) by exact (eq_trans (HP3 20 ltac:(unfold acallee_saved; lia)) R20).
assert (X21 : YK11.getr regs3 21 = w64 (fp + 20)) by exact (eq_trans (HP3 21 ltac:(unfold acallee_saved; lia)) R21).
assert (X22 : YK11.getr regs3 22 = w64 (fp + 28)) by exact (eq_trans (HP3 22 ltac:(unfold acallee_saved; lia)) R22).
assert (X24 : YK11.getr regs3 24 = w64 (SHADOW_OFF + (fp + 28) / 8))
  by exact (eq_trans (HP3 24 ltac:(unfold acallee_saved; lia)) R24).
assert (X25 : YK11.getr regs3 25 = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (HP3 25 ltac:(unfold acallee_saved; lia)) R25).
assert (X26 : YK11.getr regs3 26 = w64 F) by exact (eq_trans (HP3 26 ltac:(unfold acallee_saved; lia)) R26).
assert (X27 : YK11.getr regs3 27 = w64 SHADOW_OFF) by exact (eq_trans (HP3 27 ltac:(unfold acallee_saved; lia)) R27).
(* what the call kept: every byte outside its window [sp1 - ESTACK, sp1) *)
assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply HEFF; [exact Ha | rewrite SP2; exact Hn |]. intros Hw. inversion Hw. }
(* ---- +0x2e8: `bnez a0`, from a state with no region ---- *)
pose proof (odka_entry W2 regs3 mem3) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (odka_E regs3) (mrestrict (w_H W2) mem3)) by constructor.
assert (HEIk : img_env VAL A_LIM (odka_E regs3)) by apply odka_env_img.
assert (D10 : sv_denot (odka_E regs3) (SOff 10 0) =
    Z_to_bv 64 (if DSpec.fr_keepalive b then 1 else 0))
  by (cbn [sv_denot]; rewrite (odka_ew_reg regs3 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HRES).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
rename HJ3 into HJ.
assert (HB1 : length B1 = Z.to_nat TW.W_LEN)
  by exact (proj1 (OdkaOK.send_control_m_keep timg_B TF Bw _ _ B1 (r, f) (tw_len _ _ _ Htw) Hsc)).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_KAR)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOK odka_B0.
- (* a keepalive: to the release cut +0x40c *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (odka_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  destruct (DSpec.fr_keepalive b) eqn:EK; rewrite ?EK in Hc; [|vm_compute in Hc; discriminate Hc].
  pose proof (odka_rel_model timg_B TF Bw b now Bw' B1 r f Hm Hsc Hdup EK) as EBw'.
  paj_run_to_tok RUNTO HS HJ SHOK odka_B0 OD_REL.
  { odka_awr_rs. apply awr_ok_x_nil. }
  odka_after_cut HS W2 KD GR mem3 msF.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) ->
    aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a)
    by (intros a Ha Hn; rewrite KD; exact (KL a Ha Hn)).
  assert (GM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (GR a (HGR a Ha))).
  odka_kreg HS regs3 (2%bv : bv 5) 2%nat X2 Y2. odka_kreg HS regs3 (3%bv : bv 5) 3%nat X3 Y3.
  odka_kreg HS regs3 (4%bv : bv 5) 4%nat X4 Y4. odka_kreg HS regs3 (8%bv : bv 5) 8%nat X8 Y8.
  odka_kreg HS regs3 (9%bv : bv 5) 9%nat X9 Y9. odka_kreg HS regs3 (25%bv : bv 5) 25%nat X25 Y25.
  odka_kreg HS regs3 (26%bv : bv 5) 26%nat X26 Y26.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_REL)) mm rom) mdx) Q) end.
  apply (REL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msF) _ e (ms_regs msF) HFIX).
  + refine (conj (odka_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b Bw pos F ly2 S2 W2 mem2
      md2 (ms_mem msF) _ e (sp1 - ESTACK) sp1 LAWS HARc HC0 HJ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia)
      ltac:(unfold OD_FBYTES; lia) KM GM) (conj _ (conj _ _))).
    * rewrite <- HW24. apply rdword_ext. intros i Hi. apply KM; lia.
    * rewrite EBw'. apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw2|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KM; lia.
    * rewrite EBw', (odka_gf B1 b r now HB1). exact Hgf1.
  + unfold od_regs_rel. refine (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y25 Y26)))))).
    * exact Y3.
    * exact Y4.
- (* not a keepalive: to the notice path +0x2ec *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (odka_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  destruct (DSpec.fr_keepalive b) eqn:EK; rewrite ?EK in Hc; [vm_compute in Hc; discriminate Hc|].
  paj_run_to_tok RUNTO HS HJ SHOK odka_B0 OD_NTC.
  { odka_awr_rs. apply awr_ok_x_nil. }
  odka_after_cut HS W2 KD GR mem3 msF.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) ->
    aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a)
    by (intros a Ha Hn; rewrite KD; exact (KL a Ha Hn)).
  assert (GM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (GR a (HGR a Ha))).
  odka_kreg HS regs3 (2%bv : bv 5) 2%nat X2 Y2. odka_kreg HS regs3 (3%bv : bv 5) 3%nat X3 Y3.
  odka_kreg HS regs3 (4%bv : bv 5) 4%nat X4 Y4. odka_kreg HS regs3 (8%bv : bv 5) 8%nat X8 Y8.
  odka_kreg HS regs3 (9%bv : bv 5) 9%nat X9 Y9. odka_kreg HS regs3 (18%bv : bv 5) 18%nat X18 Y18.
  odka_kreg HS regs3 (19%bv : bv 5) 19%nat X19 Y19. odka_kreg HS regs3 (20%bv : bv 5) 20%nat X20 Y20.
  odka_kreg HS regs3 (21%bv : bv 5) 21%nat X21 Y21. odka_kreg HS regs3 (22%bv : bv 5) 22%nat X22 Y22.
  odka_kreg HS regs3 (25%bv : bv 5) 25%nat X25 Y25. odka_kreg HS regs3 (26%bv : bv 5) 26%nat X26 Y26.
  odka_kreg HS regs3 (27%bv : bv 5) 27%nat X27 Y27. odka_kreg HS regs3 (24%bv : bv 5) 24%nat X24 Y24.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_NTC)) mm rom) mdx) Q) end.
  apply (NTC HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    B1 r f ly2 S2 W2 (ms_mem msF) _ e (ms_regs msF) HFIX).
  + refine (conj (conj (odka_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b Bw pos F ly2 S2 W2
      mem2 md2 (ms_mem msF) _ e (sp1 - ESTACK) sp1 LAWS HARc HC0 HJ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia)
      ltac:(unfold OD_FBYTES; lia) KM GM) (conj _ (conj Hsc (conj _ (conj Hgf1 Hdup))))) EK).
    * rewrite <- HW24. apply rdword_ext. intros i Hi. apply KM; lia.
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw2|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KM; lia.
  + unfold od_regs_ntc, od_regs_s, od_regs_rel.
    refine (conj (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y25 Y26))))))
      (conj Y18 (conj Y19 (conj Y20 (conj Y21 Y27))))) (conj Y22 Y24)).
    * exact Y3.
    * exact Y4.
Qed.
End ka.

(* The keepalive piece of the walk of on_data (on_data_seg_cut.v od_ka_stmt), at every machine, run ceiling, record
   and meter. *)
Theorem od_ka : forall fx rc B MT, @od_ka_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odka_holds fx rc B MT). Qed.

Print Assumptions od_ka.
