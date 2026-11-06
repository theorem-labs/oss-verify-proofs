(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 521 of its 575 lines of code are new or changed and 505 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_recv.v, with its module paths, module names, addresses and numbers changed; 207 of its 374 lines of code are new or changed and 408 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_bar1: Lemma lc_bar1_ok, the segment BAR1 of the image-B walk of LLVMFuzzerTestOneInput
   (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v lc_bar1_stmt), from the cut lc_st_bar1 (+0x1474) to the loop tail
   lc_st_tail (+0x1670). The code (pc = 0x812a0 + offset, lib/B/Prog/DgnTransportBList.v):
     +0x1474  jal build_and_receive (0x85998), return address +0x1478: a0 / a1 = the dst / src table entries, a2 = send,
              a3 = ack, a4 = retry, a5 = cmd, a6 = the body in the input, a7 = its length (lc_frame_vals);
              build_and_receive is a G-form callee in the walk's own G journal (build_and_receive_cg.v
              transport_build_and_receive_cg at CTX_build_and_receive, the premise lp_bar);
     +0x1478  mv s8, s5 (the cursor after the take);
     +0x147c  j +0x1670, the tail.
   The callee's pre at +0x1474: dst and src are read-only MACs (the read-only disjunct of trans_src_ok from the kit
   statement K2, their bytes from K1 and LLVMFuzzerTestOneInput_st.v lc_rom_bytes), the body lies in the input block
   (decode_in_block), the model's Some from TSim/LoopOk.v op_ok at the start facts through
   LLVMFuzzerTestOneInput_st.v lc_frame_eq, the run invariants and g_fail_next <= 1 (K6), recv_dn_each of the frame
   (K5) and the frame-pointer chain (K7); the five frame counts (class 5: 0 + 2, class 1: 0 + 1, class 2: 1 + 2,
   classes 3 and 0: 0) from frames = [(2, fpos)]. The kit statements are the lemma's arguments. The call's helpers
   come from segment RECV's file (LLVMFuzzerTestOneInput_seg_recv.v): the symbolic state with no region lr_entry0,
   the loop's facts across the run to the call (lc_lcore_run) and across the G-form call (lc_lcore_call, with
   lc_recv_wr_hull: receive's written range lies in G's hull), the body's bytes (lc_garr8_sub), and the join
   `mv s8, s5; j` from +0x1478 to the tail (lc_join_tail).
   The four lemmas b1_mac_ok, b1_rom_garr8, b1_stk and b1_ctx_at are top level: segment BAR2 uses them. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_data_cg on_announce_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st LLVMFuzzerTestOneInput_seg_recv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TOps TNeed
  TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof RxOpLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module RXL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.RxOpLib.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The values op_frame hands build_and_receive                      *)
(* ------------------------------------------------------------------ *)

(* sel, send, ack, retry and the take of op_frame (lc_frame_vals): their ranges, and the body inside D. *)
Lemma b1_fv_ok : forall (D Bw : list byte) c1, QF.fuzz_in_ok D c1 ->
  0 <= fv_sel (lc_frame_vals D Bw c1) < 256 /\
  0 <= fv_send (lc_frame_vals D Bw c1) < 2 ^ 16 /\
  0 <= fv_ack (lc_frame_vals D Bw c1) < 2 ^ 32 /\
  0 <= fv_retry (lc_frame_vals D Bw c1) < 2 ^ 8 /\
  0 <= fv_off (lc_frame_vals D Bw c1) /\
  0 <= fv_len (lc_frame_vals D Bw c1) <= TC.SPEC_MAX_BODY /\
  fv_off (lc_frame_vals D Bw c1) + fv_len (lc_frame_vals D Bw c1) <= Z.of_nat (length D).
Proof.
intros D Bw c1 Hc. unfold lc_frame_vals.
destruct (QF.fuzz_u8_ok D c1 Hc) as (c1' & sel & E1 & Hc1 & Hsel). rewrite E1. cbv beta iota zeta.
destruct (QF.fuzz_u16_ok D c1' Hc1) as (c2 & send & E2 & Hc2 & Hsend). rewrite E2. cbv beta iota zeta.
destruct (QF.fuzz_u16_ok D c2 Hc2) as (c3 & ack0 & E3 & Hc3 & Hack). rewrite E3. cbv beta iota zeta.
destruct (QF.fuzz_u8_ok D c3 Hc3) as (c4 & r & E4 & Hc4 & Hr). rewrite E4. cbv beta iota zeta.
destruct (QF.fuzz_u16_ok D c4 Hc4) as (c5 & w & E5 & Hc5 & Hw). rewrite E5. cbv beta iota zeta.
assert (SMB : TC.SPEC_MAX_BODY = 1484) by reflexivity.
pose proof (Z.mod_pos_bound w (TC.SPEC_MAX_BODY + 1) ltac:(rewrite SMB; lia)) as Hwm.
destruct (QF.fuzz_take_ok D c5 (w mod (TC.SPEC_MAX_BODY + 1)) Hc5 (proj1 Hwm))
  as (c6 & off & len & E6 & _ & Hn & Hoff & Hend & _).
rewrite E6. cbv beta iota zeta. cbn [fv_sel fv_send fv_ack fv_retry fv_off fv_len].
assert (Hrt : 0 <= Z.land r 3 < 4).
{ change 3 with (Z.ones 2). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
split; [lia|]. split; [change (2 ^ 16) with 65536; lia|].
split.
{ destruct (Z.land sel 0x80 =? 0); [change (2 ^ 32) with 4294967296; lia|].
  unfold TW.g_last_counter. pose proof (TWL.u_at_range Bw TW.OFF_g_last_counter 4) as Hg.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hg. exact Hg. }
split; [change (2 ^ 8) with 256; lia|].
split; [lia|]. split; [lia | lia].
Qed.

(* The command byte op_frame.CMD[(sel & 7) mod 7]. *)
Lemma b1_cmd_ok : forall sel, 0 <= lc_fcmd sel < 2 ^ 8.
Proof.
intros sel. unfold lc_fcmd.
assert (H : (Z.to_nat (Z.land sel 7 mod 7) < 7)%nat)
  by (pose proof (Z.mod_pos_bound (Z.land sel 7) 7 ltac:(lia)); lia).
destruct (Z.to_nat (Z.land sel 7 mod 7)) as [|[|[|[|[|[|[|n]]]]]]];
  unfold TOP.op_frame_CMD; cbn [nth]; change (2 ^ 8) with 256; lia.
Qed.

(* The six MACs op_frame reads (op_frame.DST and op_frame.SRC), with their addresses. *)
Definition b1_macs : list (Z * list byte) :=
  [(TRANS_HOST, TC.HOST); (TRANS_DESK, TC.DESK); (TRANS_SPEC_BCAST, TC.SPEC_BCAST); (TRANS_OTHER, TC.OTHER);
   (TRANS_DESK2, TC.DESK2); (TRANS_NOTDD, TC.NOTDD)].

Ltac b1_in := repeat (first [left; reflexivity | right]).

Lemma b1_idx : forall x, (Z.to_nat (Z.land x 3) < 4)%nat.
Proof.
intros x. assert (H : 0 <= Z.land x 3 < 4).
{ change 3 with (Z.ones 2). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
lia.
Qed.

Lemma b1_dst_in : forall sel, In (lc_fdst_a sel, lc_fdst sel) b1_macs.
Proof.
intros sel. unfold lc_fdst_a, lc_fdst. pose proof (b1_idx (Z.shiftr sel 5)) as H.
destruct (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) as [|[|[|[|n]]]];
  [unfold TOP.op_frame_DST, b1_macs; cbn [nth]; b1_in .. | lia].
Qed.

Lemma b1_src_in : forall sel, In (lc_fsrc_a sel, lc_fsrc sel) b1_macs.
Proof.
intros sel. unfold lc_fsrc_a, lc_fsrc. pose proof (b1_idx (Z.shiftr sel 3)) as H.
destruct (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) as [|[|[|[|n]]]];
  [unfold TOP.op_frame_SRC, b1_macs; cbn [nth]; b1_in .. | lia].
Qed.

(* A byte of a read-only global of 6 bytes is a TRANS_RO_RD byte. *)
Lemma b1_ro_glob : forall q, In (q, 6) TRANS_RO_GLOBALS -> forall i, 0 <= i < 6 -> trans_in_ro_rd (q + i).
Proof.
intros q Hq i Hi. unfold trans_in_ro_rd, TRANS_RO_RD. apply Exists_exists. exists (q, 6).
split; [apply in_or_app; right; exact Hq | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* Each MAC: its bytes in the image (lc_rom_tab), its length, a range K2 places, and each byte read-only. *)
Lemma b1_mac_ok : forall q l, In (q, l) b1_macs ->
  In (q, l) lc_rom_tab /\ length l = 6%nat /\
  In (q, 6) [(TRANS_HOST, 6); (TRANS_DESK, 6); (TRANS_SPEC_BCAST, 6); (TRANS_OTHER, 6); (TRANS_DESK2, 6);
             (TRANS_NOTDD, 6); (TRANS_STR_C24, 8); (TRANS_STR_C24, 9); (TRANS_STR_PC, 8); (TRANS_STR_PC, 9);
             (TRANS_STR4, 5); (TRANS_STR4, 6); (TRANS_IO, 32)] /\
  (forall i, 0 <= i < 6 -> trans_in_ro_rd (q + i)).
Proof.
intros q l H. unfold b1_macs in H. cbn [In] in H.
destruct H as [H | [H | [H | [H | [H | [H | []]]]]]]; apply pair_equal_spec in H as [<- <-];
  (split; [unfold lc_rom_tab; b1_in|]); (split; [reflexivity|]); (split; [b1_in|]);
  apply b1_ro_glob; unfold TRANS_RO_GLOBALS; b1_in.
Qed.

(* A range of the image read as lc_rom_tab holds it, at a memory whose read-only view is the image's (K1). *)
Lemma b1_rom_garr8 : forall (W : world tfibsegs) mem q l,
  trans_rom_view_rd W mem -> In (q, l) lc_rom_tab ->
  (forall i, 0 <= i < Z.of_nat (length l) -> trans_in_ro_rd (q + i)) ->
  garr8 tfibsegs (mrestrict (w_H W) mem) q (TW.zs l).
Proof.
intros W mem q l HR Hin Hro. apply garr8_of_aview. intros j Hj. unfold TW.zs in Hj |- *. rewrite length_map in Hj.
rewrite (HR (q + Z.of_nat j) (Hro (Z.of_nat j) ltac:(lia))).
rewrite (lc_rom_bytes q l Hin j Hj).
rewrite (nth_indep (map (@bv_unsigned 8) l) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. reflexivity.
Qed.

(* The operation's model equation from build_and_receive's answer, and build_and_receive's Some from the
   operation's. *)
Lemma b1_frame_op : forall (D : list byte) c (B0 : list byte) a (Bw' : list byte) k,
  lc_opc D c = 1 ->
  TOP.build_and_receive_m timg_B B0 a (lc_fdst (fv_sel (lc_frame_vals D B0 (lc_oc D c))))
    (lc_fsrc (fv_sel (lc_frame_vals D B0 (lc_oc D c)))) (fv_send (lc_frame_vals D B0 (lc_oc D c)))
    (fv_ack (lc_frame_vals D B0 (lc_oc D c))) (fv_retry (lc_frame_vals D B0 (lc_oc D c)))
    (lc_fcmd (fv_sel (lc_frame_vals D B0 (lc_oc D c))))
    (TW.sub D (fv_off (lc_frame_vals D B0 (lc_oc D c))) (Z.to_nat (fv_len (lc_frame_vals D B0 (lc_oc D c))))) =
    Some (Bw', tt) ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 (fun _ => a) D c k =
    Some (Bw', (fv_c (lc_frame_vals D B0 (lc_oc D c)), S k)).
Proof.
intros D c B0 a Bw' k Ho Hr. rewrite (lc_frame_eq timg_B B0 (fun _ => a) D c k Ho). cbv beta zeta.
rewrite Hr. reflexivity.
Qed.

Lemma b1_frame_some : forall (D : list byte) c (B0 : list byte) a k,
  lc_opc D c = 1 ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 (fun _ => a) D c k <> None ->
  TOP.build_and_receive_m timg_B B0 a (lc_fdst (fv_sel (lc_frame_vals D B0 (lc_oc D c))))
    (lc_fsrc (fv_sel (lc_frame_vals D B0 (lc_oc D c)))) (fv_send (lc_frame_vals D B0 (lc_oc D c)))
    (fv_ack (lc_frame_vals D B0 (lc_oc D c))) (fv_retry (lc_frame_vals D B0 (lc_oc D c)))
    (lc_fcmd (fv_sel (lc_frame_vals D B0 (lc_oc D c))))
    (TW.sub D (fv_off (lc_frame_vals D B0 (lc_oc D c))) (Z.to_nat (fv_len (lc_frame_vals D B0 (lc_oc D c))))) <> None.
Proof.
intros D c B0 a k Ho Hs Hn. apply Hs. rewrite (lc_frame_eq timg_B B0 (fun _ => a) D c k Ho). cbv beta zeta.
rewrite Hn. reflexivity.
Qed.

Lemma b1_ctx_at : CTX_build_and_receive = [[0x82110]; [0x82110; RA_LLVMF]; [0x82718]; [0x82718; RA_LLVMF]].
Proof. reflexivity. Qed.

Lemma b1_stk : BAR_STK = 16720.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The segment                                                       *)
(* ------------------------------------------------------------------ *)

Section bar1. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma lc_bar1_ok (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K2 : @lc_src_ro_stmt rc B MT XL RLO RHI)
    (K5 : lc_dn_each_stmt) (K6 : lc_runinv_stmt) (K7 : @lc_chain_stmt rc B MT XL RLO RHI) :
  @lc_bar1_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_bar1_stmt. intros HP cx op W c HB HST.
destruct HST as (ly' & S' & regs' & mem' & md' & e & HST). cbv zeta in HST.
destruct HST as (-> & Hopc & HL & Htw & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & (R21 & R27) & R20 & R22).
set (D := l_pl cx) in *.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOPOK & He & HMET & R19).
pose proof HOPOK as (HAG & Hops & Hcin & Hcn & Hk).
destruct (QF.fuzz_u8_ok D (lo_c op) Hcin) as (c1 & ob & Eoc & Hc1 & _).
assert (Hoc : QF.fuzz_in_ok D (lc_oc D (lo_c op))) by (unfold lc_oc; rewrite Eoc; exact Hc1).
destruct (b1_fv_ok D (lo_B op) (lc_oc D (lo_c op)) Hoc) as (Hsel & Hsend & Hack & Hret & Hoff & Hlen0 & Hend).
pose proof (b1_dst_in (fv_sel (lc_frame_vals D (lo_B op) (lc_oc D (lo_c op))))) as Hdst.
pose proof (b1_src_in (fv_sel (lc_frame_vals D (lo_B op) (lc_oc D (lo_c op))))) as Hsrc.
pose proof (b1_cmd_ok (fv_sel (lc_frame_vals D (lo_B op) (lc_oc D (lo_c op))))) as Hcmd.
set (fv := lc_frame_vals D (lo_B op) (lc_oc D (lo_c op))) in *.
destruct (b1_mac_ok _ _ Hdst) as (Hdrom & Hdlen & Hdk2 & Hdro).
destruct (b1_mac_ok _ _ Hsrc) as (Hsrom & Hslen & Hsk2 & Hsro).
set (body := TW.sub D (fv_off fv) (Z.to_nat (fv_len fv))).
assert (Hlen : Z.of_nat (length body) = fv_len fv)
  by (unfold body; rewrite (QF.length_sub_D D (fv_off fv) (fv_len fv)) by lia; lia).
set (frame := bar_frame (lc_fdst (fv_sel fv)) (lc_fsrc (fv_sel fv)) (fv_send fv) (fv_ack fv) (fv_retry fv)
  (lc_fcmd (fv_sel fv)) body).
assert (Hfl : Z.of_nat (length frame) <= 1514).
{ unfold frame, bar_frame. apply RXL.spec_build_frame_len.
  assert (SMB : TC.SPEC_MAX_BODY = 1484) by reflexivity. lia. }
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & Hfrs & _ & _ & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & _).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME in Hsp1.
(* the model: build_and_receive answers at every address the malloc can return *)
assert (HMOD : forall a, recv_addr_ok a ->
  TOP.build_and_receive_m timg_B (lo_B op) a (lc_fdst (fv_sel fv)) (lc_fsrc (fv_sel fv)) (fv_send fv) (fv_ack fv)
    (fv_retry fv) (lc_fcmd (fv_sel fv)) body <> None).
{ intros a (Ha1 & Ha2).
  destruct (LOK.op_ok LP.links_holds timg_B (lo_ops op) (lo_B op) (fun _ => a) D (lo_c op) (lo_k op) HAG Hops Hcin Hcn
    Ha1 Ha2) as (B' & c' & k'' & E' & _).
  exact (b1_frame_some D (lo_c op) (lo_B op) a (lo_k op) Hopc ltac:(rewrite E'; discriminate)). }
(* the run invariants and receive's invariant (3) at the operation's start world *)
destruct (K6 (lo_ops op) (lo_B op) HAG) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & Hgf).
assert (Hdn : recv_dn_each timg_B (lo_B op) frame 0 0)
  by (apply (K5 (lo_ops op) (lo_B op) frame 0 0 HAG Hops); lia).
(* the events, the live bytes and the meter *)
pose proof HB as HB2. unfold lc_base, tfib_lib_pre_x in HB2.
destruct HB2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
pose proof transport_llvmf_events_ok as HEV. unfold transport_llvmf_events in HEV.
assert (PEV : st_nev (l_S cx) + e + BAR_EV <= EV_MAX) by (change BAR_EV with 2; change RECV_EV with 2 in *; lia).
assert (PLIVE : blocks_bytes S' + RECV_LIVE <= LIVE_MAX) by (unfold RECV_LIVE, LIVE_LIB in *; lia).
pose proof HMET as (Hmle & Hmok).
assert (R0 : 0 <= lf_rcost MT).
{ unfold lf_rcost. pose proof (mo_malloc_nonneg MT MTL 65535 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
assert (Hcost : recv_cost MT (Z.of_nat (length frame)) <= lf_rcost MT).
{ unfold recv_cost, lf_rcost.
  pose proof (mo_malloc_mono MT MTL (Z.max 1 (Z.of_nat (length frame))) 65535 ltac:(lia)). lia. }
assert (PCOST : recv_cost MT (Z.of_nat (length frame)) <= (TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT).
{ assert (H1 : 1 <= TC.OPS_MAX - Z.of_nat (lo_k op)) by lia.
  pose proof (Z.mul_le_mono_nonneg_r 1 (TC.OPS_MAX - Z.of_nat (lo_k op)) (lf_rcost MT) R0 H1). lia. }
(* ---- +0x1474: jal build_and_receive ---- *)
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (lr_entry0 (l_fx cx) W regs' mem' LO_BAR1) as HS.
set (E := lr_E0 regs') in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply lr_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
  by (intros n r Hn0; unfold E; apply lr_ew; exact Hn0).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E (mrestrict (w_H W) mem')) by constructor.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_BAR1)) mem' (YK11.seg_rom segs)) md')
    Q) end.
paj_run_tok RUN HS HJ SHOK LR_B0.
{ lr_awr. }
lr_kept HFr KC W mem' ms.
assert (GC : forall x, apresent (w_H W) mem' x -> apresent (w_H W) (ms_mem ms) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
lr_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 5240)) C1 ltac:(apply codeptr_val; exact HEI).
lr_keq HS EW regs' (2%bv : bv 5) 2%nat C2. lr_keq HS EW regs' (3%bv : bv 5) 3%nat C3.
lr_keq HS EW regs' (4%bv : bv 5) 4%nat C4. lr_keq HS EW regs' (8%bv : bv 5) 8%nat C8.
lr_keq HS EW regs' (9%bv : bv 5) 9%nat C9. lr_keq HS EW regs' (10%bv : bv 5) 10%nat C10.
lr_keq HS EW regs' (11%bv : bv 5) 11%nat C11. lr_keq HS EW regs' (12%bv : bv 5) 12%nat C12.
lr_keq HS EW regs' (13%bv : bv 5) 13%nat C13. lr_keq HS EW regs' (14%bv : bv 5) 14%nat C14.
lr_keq HS EW regs' (15%bv : bv 5) 15%nat C15. lr_keq HS EW regs' (16%bv : bv 5) 16%nat C16.
lr_keq HS EW regs' (17%bv : bv 5) 17%nat C17. lr_keq HS EW regs' (18%bv : bv 5) 18%nat C18.
lr_keq HS EW regs' (19%bv : bv 5) 19%nat C19. lr_keq HS EW regs' (20%bv : bv 5) 20%nat C20.
lr_keq HS EW regs' (21%bv : bv 5) 21%nat C21. lr_keq HS EW regs' (22%bv : bv 5) 22%nat C22.
lr_keq HS EW regs' (26%bv : bv 5) 26%nat C26. lr_keq HS EW regs' (27%bv : bv 5) 27%nat C27.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  set (regsC := rg) in *; set (memC := mm) in *; set (mdC := mdx) in * end.
(* the loop's facts at the call *)
assert (HLC : @lc_lcore rc B MT cx op false false (lo_k op) ly' S' W regsC memC mdC e)
  by exact (lc_lcore_run B MT cx op false false (lo_k op) ly' S' W regs' mem' md' e regsC memC mdC HL HJ KC GC
              C2 C3 C4 C8 C9 C18 C19 C26).
pose proof HLC as (HCC & _).
pose proof HCC as (HJC & _).
assert (USPC : spZ regsC = lc_sp1 cx)
  by (unfold spZ; rewrite C2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (S0C : s0Z regsC = lc_sp0 cx)
  by (unfold s0Z; rewrite C8, R8; unfold w64; apply unsigned_lit_small; unfold lc_sp0 in *; lia).
assert (RAC : raZ regsC = 0x82718) by (unfold raZ; rewrite C1; vm_compute; reflexivity).
pose proof (K1 HP cx ly' S' W regsC memC mdC e HB HCC) as PROM.
destruct (K7 HP cx ly' S' W regsC memC mdC e HB HCC) as (ch & Hch & Hspine).
(* dst and src: read-only MACs of the image *)
assert (Pdg : garr8 segs (mrestrict (w_H W) memC) (lc_fdst_a (fv_sel fv)) (TW.zs (lc_fdst (fv_sel fv))))
  by (apply (b1_rom_garr8 W memC _ _ PROM Hdrom); rewrite Hdlen; exact Hdro).
assert (Psg : garr8 segs (mrestrict (w_H W) memC) (lc_fsrc_a (fv_sel fv)) (TW.zs (lc_fsrc (fv_sel fv))))
  by (apply (b1_rom_garr8 W memC _ _ PROM Hsrom); rewrite Hslen; exact Hsro).
pose proof (K2 HP cx ly' S' W regsC memC mdC e (lc_fdst_a (fv_sel fv)) 6 HB HCC Hdk2) as Pds.
pose proof (K2 HP cx ly' S' W regsC memC mdC e (lc_fsrc_a (fv_sel fv)) 6 HB HCC Hsk2) as Pss.
assert (Pdw : decode_off_win regsC BAR_STK (lc_fdst_a (fv_sel fv)) BAR_MAC).
{ pose proof (trans_ro_rd_bounds _ (Hdro 5 ltac:(lia))) as Hb.
  left. rewrite USPC, b1_stk. unfold BAR_MAC. lia. }
assert (Psw : decode_off_win regsC BAR_STK (lc_fsrc_a (fv_sel fv)) BAR_MAC).
{ pose proof (trans_ro_rd_bounds _ (Hsro 5 ltac:(lia))) as Hb.
  left. rewrite USPC, b1_stk. unfold BAR_MAC. lia. }
(* the body: a sub-range of the input block *)
assert (Pbg : garr8 segs (mrestrict (w_H W) memC) (l_p cx + fv_off fv) (TW.zs body)).
{ pose proof HCC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HPAYg & _)).
  exact (lc_garr8_sub (mrestrict (w_H W) memC) (l_p cx) D (fv_off fv) (fv_len fv) Hoff (proj1 Hlen0) Hend HPAYg). }
assert (Pbs : (0 < length body)%nat ->
  trans_src_ok B ly' S' W memC (l_p cx + fv_off fv) (Z.of_nat (length body)) /\
  decode_off_win regsC BAR_STK (l_p cx + fv_off fv) (Z.of_nat (length body))).
{ intros Hpos. destruct Hn as (Hn1 & Hnl). fold D in Hnl.
  assert (Hn0 : 0 < l_n cx) by lia.
  pose proof (HINg Hn0) as Hin.
  destruct (al_blocks _ _ LAWS ly' S' W mem' md' (l_p cx) (l_n cx) HARg Hin) as (_ & H4096 & Hce & _ & _ & _ & Hnb).
  pose proof (req_size_pos (l_n cx) (proj1 Hnb)) as [_ Hreq].
  rewrite Hlen. split.
  - left. exists (l_p cx), (l_n cx). split; [exact Hin | lia].
  - left. rewrite USPC, b1_stk. lia. }
assert (Ptw : tw_at TMAP_B (aview segs (w_H W) memC) (lo_B op)).
{ unfold lc_tw in Htw. apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh. apply KC. lia. }
assert (PC5 : count_cid BAR_CID (frames S') + 2 < fs_frames BAR_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC1 : count_cid SRX_CID (frames S') + 1 < fs_frames SRX_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC4 : count_cid ONANN_CID (frames S') < fs_frames ONANN_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC0 : count_cid SENDDATA_CID (frames S') < fs_frames SENDDATA_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC2 : count_cid ONDATA_CID (frames S') + 2 < fs_frames ONDATA_CID) by (rewrite Hfrs; vm_compute; reflexivity).
(* +0x1474: build_and_receive *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB_build_and_receive)) mm rom) mdx)
    Q)
end.
eapply SRr_bind.
{ exact (lp_bar _ _ _ _ _ HP (l_fx cx) LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly' S' W memC mdC e regsC (lc_fdst_a (fv_sel fv)) (lc_fsrc_a (fv_sel fv))
    (l_p cx + fv_off fv) (fv_send fv) (fv_ack fv) (fv_retry fv) (lc_fcmd (fv_sel fv))
    ((TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT) (lc_fdst (fv_sel fv)) (lc_fsrc (fv_sel fv)) body (lo_B op) ch
    HJC
    ltac:(rewrite C1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(rewrite RAC; lia)
    (eq_trans C3 R3) (eq_trans C4 R4) (eq_trans C10 R10) (eq_trans C11 R11)
    ltac:(rewrite C12; exact R12) ltac:(rewrite C13; exact R13)
    (eq_trans C14 R14) (eq_trans C15 R15) (eq_trans C16 R16)
    ltac:(rewrite C17, R17, Hlen; reflexivity)
    ltac:(rewrite USPC, S0C; exact Hch)
    ltac:(rewrite RAC, b1_ctx_at; destruct Hspine as [Hsp | Hsp]; rewrite Hsp;
          [right; right; left; reflexivity | right; right; right; left; reflexivity])
    ltac:(rewrite USPC; pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as Dm;
          rewrite Hsp1al, Z.add_0_r in Dm; rewrite Dm;
          replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring; apply Z.mod_mul; lia)
    ltac:(rewrite USPC, b1_stk; unfold LLVMF_STK; lia)
    ltac:(rewrite USPC; lia)
    Hsend Hack Hret Hcmd
    Hdlen Pdg Pds Pdw Hslen Psg Pss Psw Pbg Pbs Ptw Hgf HMOD PROM I1 I2 I3 I4 I5 I6 I7 Hdn
    PC5 PC1 PC4 PC0 PC2 PEV PLIVE Hmok PCOST). }
cbv beta. intros W3 c3 _ HPOST.
unfold transport_bar_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (a & Bw' & Haok & Hbm & Htw3 & Hgf3)).
rewrite USPC in HK3.
assert (HL3 : @lc_lcore rc B MT cx op false false (S (lo_k op)) ly3 S3 W3 regs3 mem3 md3 (e + e3))
  by exact (lc_lcore_call B MT XL RLO RHI cx op ly' S' W regsC memC mdC e BAR_STK (recv_wr frame)
              (recv_cost MT (Z.of_nat (length frame))) ly3 S3 W3 regs3 mem3 md3 e3 HP HB HLC HJ3 He3 HP3 Hfr3 Hperm3
              HK3 ltac:(rewrite b1_stk; unfold LLVMF_STK; lia) (lc_recv_wr_hull frame) Hmo3 Hcost).
(* +0x1478 .. +0x147c: the join *)
rewrite C1.
apply (lc_join_tail B MT XL RLO RHI cx op 0x1478 W3 _ HP (or_intror eq_refl)).
exists ly3, S3, regs3, mem3, md3, (e + e3), a, Bw', (fv_c fv), (S (lo_k op)).
split; [reflexivity|].
split; [exact HL3|].
split; [exact Haok|].
split; [exact (b1_frame_op D (lo_c op) (lo_B op) a Bw' (lo_k op) Hopc Hbm)|].
split; [exact Htw3|].
split; [split; [exact (lc_reg_kept regsC regs3 21 _ HP3 ltac:(hnf; lia) (eq_trans C21 R21))
              | exact (lc_reg_kept regsC regs3 27 _ HP3 ltac:(hnf; lia) (eq_trans C27 R27))]|].
split; [exact (lc_reg_kept regsC regs3 20 _ HP3 ltac:(hnf; lia) (eq_trans C20 R20))
      | exact (lc_reg_kept regsC regs3 22 _ HP3 ltac:(hnf; lia) (eq_trans C22 R22))].
Qed.

End bar1.
