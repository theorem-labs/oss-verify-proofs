(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput - the
   jump table's arm 2 (op_drain, fuzz_reply.c:596-609), from the arm's entry 0x84520 to the latch 0x84490, in the
   form of lib/A/W_LLVMFuzzerTestOneInput_cut.v's worked dispatch lf_seg_jt and of the loop walk
   lib/A/W_check_bounded.v (cb_loopX: a loop from a fresh symbolic state at its head, by induction on the trips
   left, spliced back with jafter_stretch_pi).
   The arm: relay_source(s->fd) scans g_src[0 .. g_nsrc) for the entry whose fd is the picked source's
   (0x84520-0x84584); with no entry, or with r->eof set, the operation is a no-op (0x846c8 / 0x84a40, both joining
   at 0x84a80); otherwise pthread_mutex_lock(&g_lock), drain(r), pthread_mutex_unlock(&g_lock),
   check_no_loss_read(s), check_no_loss(s, &at), check_shape_done(at) (0x84a44-0x84a7c), then the same join.
   The out-parameter `at` is the frame cell F+192: check_no_loss runs under its journal at XO = 208 with
   OUT = [(F+192, F+200)] (W_journal.v; the cell is inside the caller's own window, and ajournal_gx_sub carries it).
   The eof = 0 path is cut at the six return points into stages dc_stA .. dc_stF over dc_at (composed in dc_calls).
   What this file takes, and from whom (all Section hypotheses, none proved here):
     LAWS / HG / RINV / LS / the contract parameters - _cut's Section w, verbatim; GWR / ERR - _cut's glob_wr_law
       / errno_law, verbatim;
     TL : PALib B - the allocator instance (W_kit.v);
     DRAIN - W7's dr_spec B MT MMAX fr_RG, verbatim (lib/A/W_contract.v);
     ALOCK / AUNLOCK - W6's alock_realizes / aunlock_realizes (lib/A/W_sites.v), proved by R5
       (rt_pthread_mutex_lock / rt_pthread_mutex_unlock, a working branch);
     CSD - check_shape_done, proved (W_check_shape_done.v pb_check_shape_done);
     CNLR - W_contract.v's cnlr_spec, proved (W_check_no_loss_read.v pb_check_no_loss_read);
     CNL - check_no_loss, W3's cnl_spec as lib/A/W_contract.v Section w3n publishes it (the readable-stack premise
       LAST, passed from the cut's STKR by dr_stkr), at every G with gx_ok / gx_rt, taken at the slot's two list headers;
     the G-coverage and image facts (HGs, HG_DR, HGlock, HG_GK, HERR_HI, DR_ROM_OUT, HZS, HAP), and
     the model obligations RI_* / LS_* (pure, over lmod and the plain records). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_drain.v, with its module paths and module names changed; 1631 of its 1751 lines of code are new or changed and 5267 lines of the source are left out. *)
(* The ARx-generic entry composition of fuzz_reply.asan's LLVMFuzzerTestOneInput, AT THE cf INSTANCE (a Theorem Labs lane's
   route (b), step 8; the link ATopKeeper's driver bridge consumes): fr_contract_top_x is cut_x's
   fr_lib_contract_cf_x at
     B   := TfibB (lib/A/AD2l.v, the start-up instance, TfibB_syms : TfibSyms TfibB);
     ARx := ARX, the cf live state CONJOINED with an empty ghost poisoned-head set,
            fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []
            (XcfFinish, 2026-10-29: ARcf does not force Hp = []; fuzz_reply calls no poison routine and every cf leaf
            keeps Hp = [] - malloc threads Hp, free is at the same Hp, realloc's remove p [] = [] - so the instance is
            the conjunction and HP0 is its second projection); laws by W_journal_x.AR_laws_x_and_hp over
            YGcallcf.AR_laws_x_cf (YG0lawscf.AR_laws_ok_cf), hl := cf_head;
     PST := [] (every walk writes its globals through the G overlay; the driver's PST := G_fr_c is reached once, in
            ATopKeeper's bridge, after this post);
     G_fr := G_fr_c TfibB (_G.v), HG by c_gx_ok from k1's zz_HEV / zz_HOWN at TfibB_syms.
   The segments are Section hypotheses in cut_x's text at that instance (SEG_JT is walked inside cut_x); each is
   replaced by its ARx proof as the arms convert (a Theorem Labs lane's step 7).  PLUGGED: SEG_LATCH (LatchX 06d592d632a, with
   W1Verify's pb_check_bounded_x), ARM_close / eintr / sendmax / default (SmallX 28fb6f8ad6a), ARM_add (AddX
   3937a0897a6, op_add by W2's pb_op_add_g_x), ARM_write (WriteX d4edf5e9938, list_push by W2's pb_list_push_g_x), ARM_event (SmallX def8de66efe), SEG_HEAD (HeadX 1ae64ddcacd), SEG_PRO (SmallX bc067575400, from
   a Theorem Labs lane's lf_seg_pro 5c8023c8afd), ARM_drain (AddX 89264be9121, from a Theorem Labs lane's lf_arm_drain 129f255c729),
   SEG_EXIT (LatchX, W_LLVMFuzzerTestOneInput_exit_x.v from a Theorem Labs lane's lf_seg_exit b86949b953d, with the kit's
   YE01_x.v), ARM_remove (WriteX, W_LLVMFuzzerTestOneInput_remove_x.v from a Theorem Labs lane's lf_arm_remove 30d91cacb63
   adapted at ddbe0ec6590, its .str.2 shadow facts by W_shadow_pin_x.v's ashp_str2_1_fr_cf), ARM_gone (SmallX,
   W_LLVMFuzzerTestOneInput_gone_x.v 95a5de32ab2 from a Theorem Labs lane's lf_arm_gone 312c6aa4c95 adapted at 95cae0d4740).
   CSD_x / CNLR_x (TOPX-W3): built in the proof from W3's pb_check_shape_done_x / pb_check_no_loss_read_x (merged from
   a working branch b591c7b0a70).  CSE_x / CSHE_x (TOPX-W3): built in the proof from W3's pb_check_shape_event_x /
   pb_check_shape_ends_x, their callees by W1's pb_next_line_x / pb_list_find_x / alist_at_drop, bcmp / memchr /
   memmove by a Theorem Labs lane's TopX_RT3.v (2987442b75b) and their placement premises by W_w3_place_fr.v.  CNL_x (TOPX-W3):
   built in the proof from W3's pb_check_no_loss_x, gesture_model by W8Entry-2's pb_gesture_model_g_cf (room form,
   W_gesture_model_g.v:185) with the caller-context list_drop pb_list_drop_ro_cx_x (room form, a Theorem Labs lane's
   783a1c55991, W_list_drop_top.v:549).  Ported to the room texts from a Theorem Labs lane's TOPX-W3 (764bfe704f9): RPi after
   MT in each room-form callee and in CSHE_x / CNL_x.
   RR_x / RIG_x: built in the proof from pb_relay_remove_x / pb_relay_instance_gone_x (lib/A/W_relay_remove.v:149 /
   lib/A/W_relay_instance_gone.v:140), their instance facts by lib/A/TopxRelayFacts.v, snprintf's literals' location by
   SnpNarrowSites.v HLITGOT_PB_fr; relay_remove's to == from __asan_memcpy contract AMEMCPYS_x is a Theorem Labs lane's
   TopX_MEMCPYS.topx_AMEMCPYS_W (QMm W1 lift of a Theorem Labs lane's closed topx_AMEMCPYS), in the proof.
   THE ROOM ROUND'S TOP STEP (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d); TOPX-PLUGS.md (sha256 e0a351b05fe4; internal record)): NP is the cf instance's room
   invariant room_live_cf (cp := CfParams_reply), and every allocator rule and callee spec is taken at a Theorem Labs lane's room
   record RPi := CfRBridgeRules.RP_cf (rp_RM := fun S _ => room_live_cf S), so the re-fit arms' RP_NP / NPF hold by
   iff_refl / room_live_set_fs and RMM / RPF by RP_cf's fields.  The four allocator rules stay hypotheses at MT (the
   instance file, at MT := MT_sec nsec_cf cf_kmax, discharges their route-R forms in Section topxR by the TOPK_rh
   theorems, with MLAW / MO_FR by ReplyKfMeter).  Built in the proof from their lemmas: ERRL_x (W_ERRL_x), GSHV_x /
   TLF / XE_LIT_S_x / HGOTG_x / GN_LITS_x (TopxImage, carried to ARX by ARX_rt_of), ALOCK / AUNLOCK / ASTRLEN_x /
   ASTRNLEN_x / AMEMCPY_x / AMEMSET_x (the QMm W1 lifts topx_*_W: this file's lock / unlock / strlen lifts over TopX_RT,
   TopX_RT2, TopX_INTRIN),
   HFP_pro (TopxEntry.hfp_pro_x, at the new hypothesis FPCOV).  The arms' count rows (the LS_cnt rows,
   CNT_gone_rig / CNT_gone_step, DR_CNT_grow / DR_CNT_cnl, RM_CNT_cnl / RM_CNT_cshe / RM_CNT_sr) are hypotheses,
   discharged in the instance file by s5-r1d's ReplyLScnt.v / ReplyGnCnt.v rows.
   fr_live_pre / fr_live_post / fr_surv / LIBROOM / fr_FP / LS / RINV stay Variables: the driver instantiates them
   (ACfn_cf.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_addI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
(* QMm W1: image A's kept-bytes facts (arodata_kept_A, arodata_none_A), Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyKeptAroA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x W_contract_x W_check_bounded W_palib_fr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_top.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* the start-up table's facts (ts_owned, ts_errno, Tfib_owned_static), as addI uses them *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m.
(* the AR arm files for the model functions the RI_* / LS_* rules name (sm_*, ad_*, wr_*, WR_MMAX); Require Import
   is not transitive through _top.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_write.
(* SEG_PRO: the AR file for pro_m and its model texts, and SmallX's conversion, with the frame kit its facts name
   (W_frame's PALibF, W_frame_x's astack_malloc_pres_x / frame_flag_lawP_x, YGcallx's laws, YG01cf / YG05cf's Wf_cf and
   stack_malloc progress); imported BEFORE W_op_add so that W_op_add's oa_first / oa_cost / oa_spec_g_x (the names
   below) are not shadowed by _pro.v's / _pro_x.v's copies *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_latch_x W_LLVMFuzzerTestOneInput_small_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_op_add W_list_push ACk0 W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write_x.
(* ARM_event: the AR file for et_GL / et_GRE / ev_* (Require Import is not transitive), and SmallX's conversion *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_event W_LLVMFuzzerTestOneInput_event_x.
(* SEG_HEAD: the AR file for hd_kb / hd_k', and HeadX's conversion *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x.
(* ARM_drain: Prog's CheckRep (texts / count_begin / set_exp_held, which its rules name), the AR file for the drain
   model (dr_at_op / dr_pick / dr_step / dr_cost ..., DR_GK), and AddX's conversion; last, and they define none of
   the names above (checked: their only clashes are Local notations) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_drain W_LLVMFuzzerTestOneInput_drain_x.
(* SEG_EXIT: the AR file (its model functions lx_* / xr_GM, cited qualified below), LatchX's conversion, the kit's
   YE01_x.v that conversion cites, _Gx.v's XR_HGM witness, AD1u.v's tfib_AIL and YG0tcf.v's stack_free law; Require
   without Import, so none of their names shadows a name the text above uses *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_exit W_LLVMFuzzerTestOneInput_exit_x YE01_x W_LLVMFuzzerTestOneInput_Gx AD1u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
(* ARM_remove: the AR file (its model functions rm_*, cited qualified below), WriteX's conversion, the .str.2 shadow
   lemma over ARx and W6's rg_place assembly; Require without Import, as SEG_EXIT's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_shadow_pin_x W_rg_place.
(* ARM_gone: the AR files (gone_base's model texts GN_*, cited qualified below) and SmallX's conversion; Require
   without Import, as SEG_EXIT's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_sites W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone W_LLVMFuzzerTestOneInput_gone_x.
(* C1 (a Theorem Labs lane's 922a710cda0; relay_event re-proved by AddX's C3 88557c15170): relay_add's, relay_event's and
   relay_finish's _x proofs, which build RA_x / RE_x / RF_x below; Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_relay_add W_relay_event W_relay_finish_h.
(* W3's check_shape_done and check_no_loss_read _x walks, which build CSD_x / CNLR_x below; Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_check_shape_done W_check_no_loss_read.
(* the top step's plugs (the room round; TOPX-PLUGS.md (sha256 e0a351b05fe4; internal record)), Require without Import, cited qualified:
   the room record of the cf instance RP_cf and the room invariant room_live_cf (a Theorem Labs lane's CfRBridgeRules.v Section TOP,
   Reusable/YGcfRoomLive.v), errno's law over any ARx (a Theorem Labs lane's W_ERRL_x.v), SEG_PRO's entry facts (a2's TopxEntry.v),
   the image facts (a6's TopxImage.v), the pthread / strlen / strnlen / memcpy / memset / errno_location contracts at
   ARX (a Theorem Labs lane's TopX_RT.v / TopX_RT2.v / TopX_INTRIN.v / TopX_RT4.v), send_line's _x walk and its instance facts
   (a Theorem Labs lane / a Theorem Labs lane's W_send_line_x.v / W_send_line_x_top.v) and the count rows' peaks (s5-r1d's ReplyLScnt.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
CfRBridgeRules W_ERRL_x TopxEntry TopxImage TopX_RT TopX_RT2 TopX_RT4 TopX_INTRIN TopX_MEMCPYS ReplyCnt ReplyLScnt ReplyTrPeakCnl
W_source_reset W_gesture_end W_gestures_end_top AsmTopX W_send_line_x W_send_line_x_top W_drain_pb TopxDrainLit ACej.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomLive.
(* W3's check_shape_event, check_shape_ends and check_no_loss _x walks, which build CSE_x / CSHE_x / CNL_x below, with
   their callees: W1's next_line / list_find / list_drop (alist_at_drop, the caller-context walk W_list_drop_top),
   W8Entry-2's gesture_model at ARX (W_gesture_model_g.v), the placement facts (W_w1_place.v, W_rom_place_fr.v,
   W_w3_place_fr.v) and a Theorem Labs lane's bcmp / memchr / memmove contracts at ARX (TopX_RT3.v); Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_check_shape_event W_cshe_top W_check_no_loss W_next_line W_list_find W_list_drop W_list_drop_top W_gesture_model_g
W_w1_place W_rom_place_fr W_w3_place_fr TopX_RT3.
(* relay_remove's and relay_instance_gone's _x walks, which build RR_x / RIG_x below, with their instance facts
   (TopxRelayFacts.v), the snprintf literals' location (SnpNarrowSites.v HLITGOT_PB_fr) and the laws' granule-tail
   lemma (W_drain_cx_x.v alloc_tail_x); Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_relay_remove_cx W_relay_remove W_relay_instance_gone_cx W_relay_instance_gone W_drain_cx_x SnpNarrowSites
TopxRelayFacts.
(* route R (Section topxR): the R contract texts (W_contract_srlf_xR / W_contract_xR / _g3 / _g6 / _relay), the R walks
   that build the R callee specs (list_free's W_list_free.v; check_shape_ends' loops 2 and 3 at R, a Theorem Labs lane's
   W_cshe_l2w.v / W_cshe_l3.v) and the strict -> R lift of strndup's rule (CfRBridgeRulesRh.v); Require without
   Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_contract_srlf_xR W_contract_xR W_contract_xR_g3 W_contract_xR_g6 W_contract_xR_relay W_list_free W_cshe_l2w W_cshe_l3
CfRBridgeRulesRh.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* the ASan image's sink instance, the one cut_x's journals and the arm files name (write_x.v:60) *)
#[local] Existing Instance AE2k.tfib_sink_head.

Section topx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ---- the instance ---- *)
(* QMm W1 (a Theorem Labs lane, a Theorem Labs lane 23:17Z): ARX carries arodata_ok_cf, the value fact the allocator rules read at the
   call memory (QMm_cf; part 3c widens arodata_ok_cf to cover the refill report's five read-only reads too). It is
   a conjunct of the RELATION, so every walk hands it to the next call. ARX_laws still holds because QMm W0' gave
   YCbqG.ARx_frame_law its kept-bytes premise and reply A's RELRO is inside AF0m.Tfib_kept
   (ReplyKeptAroA.arodata_kept_A). At the driver's entry it comes from ReplyKeptAroA.arodata_none_A. *)
Definition ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem.
Lemma ARX_laws : AR_laws_x segs TfibB ARX (@cf_head CfParams_reply).
Proof.
  apply (AR_laws_x_iff segs TfibB (fun ly S Hp W mem md =>
           (ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []) /\
           @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem)).
  { intros ly S Hp W mem md. unfold ARX. split.
    - intros ((H1 & H2) & H3). exact (conj H1 (conj H2 H3)).
    - intros (H1 & H2 & H3). exact (conj (conj H1 H2) H3). }
  apply (AR_laws_x_and_mem segs TfibB _ (@YG0dcf.arodata_ok_cf CfImg_A segs TfibB) ReplyKeptAroA.arodata_kept_A).
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB
           (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.
(* cut_x's HP0 at the instance *)
Lemma ARX_hp0 : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> Hp = [].
Proof. intros ly S Hp W mem md H. exact (proj1 (proj2 H)). Qed.
Lemma GX_ok : gx_ok segs TfibB (G_fr_c TfibB).
Proof.
  exact (c_gx_ok TfibB (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms)
           (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms)
           (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms)).
Qed.
(* ---- QMm W1 at this file's ARX (TopX_RT.ARX_rtW is ARX, by delta).  The pre-W1 relation TopX_RT.ARX_rt
   (ARcf /\ Hp = []) is ARX's first two conjuncts: TopxImage.v, TopxDrainLit.v and TopxRelayFacts.v, W_shadow_pin_x.v's
   ashp_str2_1_fr_cf and W_w3_place_fr.v's check_shape_ends_HEND5S_fr state their facts there, each with the relation
   as a premise only, so ARX_rt_of carries them to ARX.  The lock / unlock / strlen rows at ARX_rtW: the W1 base
   (a Theorem Labs lane, a164e396ab3d) adds the shared W1 names to TopX_RT.v but no lift of these three, so they are lifted here,
   token for token as image B's TopX_RT_lock.v topx_ALOCK_W / topx_AUNLOCK_W and TopX_RT_B2.v topx_ASTRLEN_B_W
   (a working branch) lift theirs ---- *)
Lemma ARX_rt_of : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> TopX_RT.ARX_rt ly S Hp W mem md.
Proof. intros ly S Hp W mem md (H1 & H2 & _). exact (conj H1 H2). Qed.
Lemma ashp_x_of_rt : forall a n, ashp_x TopX_RT.ARX_rt a n -> ashp_x ARX a n.
Proof. intros a n H ly S Hp W mem md HA. exact (H ly S Hp W mem md (ARX_rt_of ly S Hp W mem md HA)). Qed.
Lemma dlit_at_x_of_rt : forall i l, W_drain_cx_x.dlit_at_x (PI := PB_fr) TopX_RT.ARX_rt i l ->
  W_drain_cx_x.dlit_at_x (PI := PB_fr) ARX i l.
Proof. intros i l (H1 & H2 & H3). exact (conj H1 (conj H2 (ashp_x_of_rt _ _ H3))). Qed.
Lemma glit_at_x_of_rt : forall i l, W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) TopX_RT.ARX_rt i l ->
  W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) ARX i l.
Proof. intros i l (H1 & H2 & H3 & H4). exact (conj H1 (conj H2 (conj (ashp_x_of_rt _ _ H3) H4))). Qed.
(* the writing rules' write set [A + 4, A + 8) holds no kept byte by the rule's own premise (W_sites_x.v) *)
Lemma topx_ALOCK_W : alock_realizes_x TfibB TopX_RT.ARX_rtW (SIGMA WS_pthread_mutex_lock).
Proof.
intros ly S Hp W regs mem md A tb HPRE H10 HA0 HA4 HA12 Htb Htb16 HV0 HIN HDST HKW.
destruct (TopX_RT.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
eapply YA0n.SRr_mono;
  [exact (TopX_RT.topx_ALOCK ly S Hp W regs mem md A tb HPRE0 H10 HA0 HA4 HA12 Htb Htb16 HV0 HIN HDST HKW)|].
intros W' c' _ HP.
apply (TopX_RT.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | exact HKW | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
Qed.
Lemma topx_AUNLOCK_W : aunlock_realizes_x TfibB TopX_RT.ARX_rtW (SIGMA WS_pthread_mutex_unlock).
Proof.
intros ly S Hp W regs mem md A HPRE H10 HA0 HA4 HA12 V0 V4 V8 HIN HDEST HKW.
destruct (TopX_RT.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
eapply YA0n.SRr_mono;
  [exact (TopX_RT.topx_AUNLOCK ly S Hp W regs mem md A HPRE0 H10 HA0 HA4 HA12 V0 V4 V8 HIN HDEST HKW)|].
intros W' c' _ HP.
apply (TopX_RT.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | exact HKW | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
Qed.
(* strlen writes nothing: its post keeps every view off the call's 2 * ESTACK stack window, which lies above the image
   (TopX_RT.stk_above_img), so arodata_ok_cf carries over by TopX_RT.aro_keep_view with X := False *)
Lemma topx_ASTRLEN_x_W : astrlen_realizes_x TfibB TopX_RT.ARX_rtW (SIGMA WS_strlen).
Proof.
intros ly S Hp W regs mem md x k HPRE.
destruct (TopX_RT.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
pose proof HPRE0 as (HA & _ & _ & Hlo & _).
pose proof (TopX_RT.stk_above_img _ _ _ _ _ _ HA) as HI.
intros. eapply YA0n.SRr_mono; [eapply (TopX_RT.topx_ASTRLEN_x ly S Hp W regs mem md x k HPRE0); eassumption|].
intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HR & HV & Hpr).
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|].
split; [|exact (conj Hrp (conj Hsm (conj HR (conj HV Hpr))))].
split; [exact HA'|]. split; [exact HH'|].
apply (TopX_RT.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - 2 * ESTACK <= a < spZ regs) HA).
- intros a [].
- intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
- intros a Ha _ HnY. exact (HV a Ha HnY).
- exact HQ.
Qed.

(* ---- the driver's parameters ---- *)
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM : astate -> Prop.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d) 5): the cut's room invariant NP is the cf instance's room_live_cf, and the
   allocator rules' room record is a Theorem Labs lane's RP_cf (CfRBridgeRules.v:852; its rp_RM is fun S _ => room_live_cf S, its
   counts ReplyCnt's Psec / P24 / Lsec / L24 / Pcls / LPRIM).  So the arms' RP_NP holds by iff_refl, their NPF is
   room_live_set_fs (YGcfRoomLive.v:1236), and RMM / RPF are RP_cf's fields rp_RMM / rp_RPF *)
Local Notation NP := (YGcfRoomLive.room_live_cf (cp := CfParams_reply)).
Local Notation RPi := CfRBridgeRules.RP_cf.
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

Local Notation G := (G_fr_c TfibB).
Local Notation BASEx cx Hp := (lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp).
Local Notation IH := (INV_H_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation ID := (INV_D_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation IA := (INV_A_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation IK := (INV_K_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation IX := (INV_X_x TfibB NP G fr_FP [] ARX LSx RINV).
(* qualified: W_contract_x.v:321 also defines an lf_post_x (list_find's post), imported after cut_x *)
Local Notation POST := (W_LLVMFuzzerTestOneInput_cut_x.lf_post_x TfibB MT XN_LIB fr_live_post fr_surv NP G fr_FP [] ARX).

(* the pthread contracts of the default arm at ARX are topx_ALOCK_W / topx_AUNLOCK_W above (QMm W1 lifts of a Theorem Labs lane's
   TopX_RT.topx_ALOCK / topx_AUNLOCK), in the proof *)
(* ---- the small arms' model rules (W_LLVMFuzzerTestOneInput_small_x.v, at the walk's choice), verbatim ---- *)
Hypothesis RI_close : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_close cx m i).
Hypothesis RI_eintr : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_eintr cx m i).
Hypothesis RI_sendmax : forall cx t m, RINV cx t m ->
  RINV cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
Hypothesis RI_default : forall cx t m, RINV cx t m -> RINV cx (t + 1) (sm_default cx m (sm_dg cx m)).
Hypothesis LS_close : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (sm_close cx m i) ly S.
Hypothesis LS_eintr : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (sm_eintr cx m i) ly S.
Hypothesis LS_sendmax : forall cx t m ly S, LSx cx t m ly S ->
  LSx cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Hypothesis LS_default : forall cx t m ly S, LSx cx t m ly S -> LSx cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.

(* ---- the cf instance's allocator contracts at ARX, each at its OWN K0 table, in the room texts at RPi (a Theorem Labs lane's
   ruling: rule texts stay published at MT; W8Entry-2's (a), 2026-10-30): the meter is the driver's Variable MT.  The
   instance file (MT := MT_sec nsec_cf cf_kmax) composes at route R, where Section topxR's AMA_R / ARE_R / AFREE_R /
   AFREE0_R take these rules' places (CfRBridgeRulesRhTop / CfRBridgeRulesFreeRh TOPK_rh), and discharges MLAW / MO_FR
   by ReplyKfMeter.MT_sec_laws / MT_sec_set_fs.  The callee specs op_add and list_push take are built below (W2's
   pb_op_add_g_x / pb_list_push_g_x), source_reset by F1's pb_source_reset_gc_x ---- *)
Hypothesis MLAW : ameter_laws MT.
Hypothesis AMA_x : amalloc_cf_rule_c_x segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi CTX_AMALLOC.
Hypothesis ARE_x : arealloc_cf_rule_c_x segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi CTX_AREALLOC
  (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).
(* ---- relay_add's and relay_finish's premise at ARX that no lemma gives (RA_x / RF_x are built in the proof): the
   meter law that freeing a fake frame (set_fs, YG01) costs nothing (KF-COUNT #4, the text of W_relay_add.v /
   W_relay_finish_h.v / the F6 walks since b1b31dd6b09 / 329fe7bd84a; the earlier `same blocks -> mo_le s s' 0` is
   false at a meter of secondary requests; MT is the driver's; discharged in the instance file, as MLAW).
   __asan_stack_malloc_0's and _1's contracts over ARX are a Theorem Labs lane's AsmTopX.asm0_pres_ARX / asm1_pres_ARX,
   __asan_memset's and __asan_memcpy's intrinsic contracts a Theorem Labs lane's TopX_INTRIN.topx_AMEMSET_x_W / topx_AMEMCPY_x_W,
   errno's law a Theorem Labs lane's W_ERRL_x.errno_law_x_holds and ad_G's shadow hulls a6's TopxImage.topx_GSHV_x, in the
   proof ---- *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* ---- ARM_add's and ARM_write's model rules (_add_x.v / _write_x.v), verbatim ---- *)
Hypothesis RI_add_pre : forall cx t m,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Hypothesis RI_add_open : forall cx t m i q pj ev,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (ad_open m i q pj ev).
Hypothesis RI_add_none : forall cx t m,
  RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None -> RINV cx (t + 1) (ad_none m).
Hypothesis LS_add_room : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S (oa_cost MT).
Hypothesis LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSx cx (t + 1) (ad_open m i q pj ev) ly' S'.
Hypothesis LS_add_none : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSx cx (t + 1) (ad_none m) ly S.
(* ARM_add's count row (_add_x.v LS_cnt at RP := RPi; s5-r1d's ReplyLScnt.v fr_LS3cp_cnt_add) *)
Hypothesis LS_cnt_add : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB ly S).
Hypothesis RI_write_skip : forall cx t m,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
  RINV cx (t + 1) (wr_skip m (wr_k2 cx m)).
Hypothesis LS_write_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Hypothesis RI_write_push : forall cx t m si h l' d ev,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev).
Hypothesis LS_write_room : forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok MT S (lp_cost MT (hs_pending h) (wr_n cx m)).
(* W8Add's proposed text (commit f57b3e2d0ca, ReplyLS.v atop_LS_write_push_prop, proved at the
   instance), adopted as the arm states it (a Theorem Labs lane 23184ff5c2a): lp_post's facts about the pushed list l' *)
Hypothesis LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
(* ARM_write's count row (_write_x.v LS_cnt at RP := RPi; s5-r1d's ReplyLScnt.v fr_LS3cp_cnt_write) *)
Hypothesis LS_cnt_write : forall cx t m si h ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (lp_peak (hs_pending h) (wr_n cx m)) (ablocks TfibB ly S).

(* ---- ARM_event's callee contracts at ARX (W_LLVMFuzzerTestOneInput_event_x.v, SmallX def8de66efe): the cf
   instance's free rule at K0's CTX_AFREE, relay_event's _x spec (W5 kit twin; RE_x is built in the proof), and
   strnlen's realizes over ARX (event_x's et_strnlen_spec_x), which is a Theorem Labs lane's TopX_RT2.topx_ASTRNLEN_x_W (RTx.v's
   astrnlen_whole_realizesM_x, convertible by unfolding: TopX_RT2.v's header), in the proof.  Its CSE is built in the
   proof (W3's pb_check_shape_event_x) ---- *)
Hypothesis AFREE_x : afree_cf_rule_c_x segs TfibB [] ARX MT RPi CTX_AFREE.
(* ---- ARM_event's model rules (_event_x.v), verbatim, MMAX := fr_MMAX ---- *)
Hypothesis RI_event_live : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).
Hypothesis RI_event_step : forall cx t m e v out',
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  RINV cx (t + 1) (ev_step cx m e v out').
Hypothesis LS_event_malloc : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e)).
Hypothesis LS_event_relay : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < CfParamsReply.fr_MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Hypothesis LS_event_free : forall cx t m ly S (S1 S2 : astate) e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).
(* s5-r1d's text (fr_LS3c_event_step_p, commit 6d19e580568, lib/A/ReplyLS3cArms.v:91), LS -> LSx: the three states
   are tied to the calls' posts - S1 by the malloc rule's ablocks equation, S1 / S2 by relay_event's (send_line's)
   aout Permutations, S3 by the free's split with the event's block removed *)
Hypothesis LS_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (ev_step cx m e v out') ly3 S3.
(* the live counts at the arm's entry leave room for its peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2; the row
   fr_LS3cp_cnt_event, commit ba8e99b5bd2, lib/A/ReplyLScnt.v:265, with its peak pk_event e P = [P (re_len e)] + 2 and
   its guards, msz_ok inline): malloc (re_len e) at the entry's counts, relay_event's count premise (re_pk = 2) at the
   entry's blocks plus the event's, free at relay_event's post (g_out replaced: at most one block more).  Stated over
   the room record's count fields; at the cf instance they are ReplyCnt's Psec / P24 / Lsec / L24 / Pcls / LPRIM *)
Hypothesis LS_cnt_event : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  Forall (fun e0 => 0 <= re_cap e0 <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e0)) (lm_es m) /\
  Forall (fun o => match o with
                   | Some h => Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_expected h)) /\
                               Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_held h))
                   | None => True end) (lm_hs m) ->
  0 <= t < OPS_MAX ->
  (ReplyCnt.acnt (rp_Psec RPi) (ablocks TfibB ly S) + ((if rp_Psec RPi (re_len e) then 1 else 0) + 2) <= rp_Lsec RPi)%nat /\
  (ReplyCnt.acnt (rp_P24 RPi) (ablocks TfibB ly S) + ((if rp_P24 RPi (re_len e) then 1 else 0) + 2) <= rp_L24 RPi)%nat /\
  (forall c, 1 <= c <= 30 ->
     (ReplyCnt.acnt (rp_Pcls RPi c) (ablocks TfibB ly S) + ((if rp_Pcls RPi c (re_len e) then 1 else 0) + 2)
        <= rp_LPRIM RPi c)%nat).

(* ---- SEG_HEAD's model rules (_head_x.v, HeadX 1ae64ddcacd), verbatim ---- *)
Hypothesis RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
Hypothesis LS_head_nout : forall cx t m ly S, LSx cx t m ly S -> LSx cx t (lm_clear_O m) ly S.
Hypothesis RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Hypothesis LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LSx cx t m ly S -> LSx cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.

(* ---- SEG_PRO's instance fact at ARX that no lemma gives yet (W_LLVMFuzzerTestOneInput_pro_x.v's text at the
   instance): the flag law over ARX (W_frame_x.v:71; YG0scf.v's AR_flag_law_ok_cf gives in_app, not ~ in_img /
   zone2; no theorem concludes frame_flag_lawP_x at the cf instance).  The fake-stack fields of the symbol table are
   a6's TopxImage.topx_TLF and __asan_stack_malloc_1's contract a Theorem Labs lane's AsmTopX.asm1_pres_ARX, in the proof ---- *)
Hypothesis FFL : frame_flag_lawP_x segs TfibB ARX.
(* ---- SEG_PRO's model rules (_pro_x.v), verbatim at the instance.  Its HFP_pro is a2's TopxEntry.hfp_pro_x (in the
   proof), at a footprint that covers the harness blocks: FPCOV, which the instance file discharges at the driver's
   fr_FP (TopxEntry.fr_FP_text_cov, as FP_SINK) ---- *)
Hypothesis FPCOV : forall regs ly S (W : world segs) mem b, In b (fr_hblks W mem) ->
  In (fst b, fst b + snd b) (fr_FP regs ly S W mem).
Hypothesis LS_pro_oa : forall cx Hp (S2 : astate) pos,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le MT (c_S cx) S2 0 ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 (oa_cost MT).
Hypothesis RI_pro : forall cx Hp q T' pj c O cap out,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (pro_m q T' pj c O cap out).
(* LS_pro at the PROPOSED text (a Theorem Labs lane 20:4xZ; W8Add's fr_LS_pro, commit f57b3e2d0ca,
   lib/A/ReplyLS.v:571): the blocks after op_add are given with the entry's split at its table T0 (HFP_pro's first
   conjunct) and relay_add's two cases (T0 = 0: a new table T'; T0 <> 0: T' = T0), so LS's own rest can be built.
   The published premise (a bare disjunction of the two Permutations) gives no such split.  The room round's form (a):
   the entry's xcnt_ok and HFH0 inside the existential, s5-r1d's TX_LS_pro_xok (66e5beebeaa,
   lib/A/ReplyLS3cTopxPro.v:148) at B := TfibB *)
Hypothesis LS_pro : forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S (oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (pro_m q T' pj c O cap out) ly S.
(* SEG_PRO's count row (_pro_x.v LS_cnt at RP := RPi; s5-r1d's ReplyLScnt.v fr_cnt_pro): op_add's count premise at the
   seat's state, from the entry's xcnt_ok *)
Hypothesis LS_cnt_pro : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB (c_ly cx) S2).

(* ---- ARM_drain's callee contract at ARX is built in the proof (DR_x, by a Theorem Labs lane's pb_drain_x, W_drain_pb.v).  Its
   one premise that no lemma gives here is strndup's cf rule at ARX (CfRStrndup.ASTRNDUP_x_kf at the counting meter, over
   the layer leaf astrndup_realizes_cf), stated at W_journal_x.v's astrndup_cf_rule_c_x with the drain's strndup
   context ACej.CTX_strndup ---- *)
Hypothesis ASTRNDUP_x : astrndup_cf_rule_c_x segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi ACej.CTX_strndup
  (@pa_sigma _ fr_prog_listing PB_fr WS_strndup).
(* ---- ARM_drain's model rules (_drain_x.v, HeadX's 13a792ebbad), verbatim at the instance (B := TfibB, RP := RPi,
   MMAX := fr_MMAX, dr_cnl_pk := s5-r1d's ReplyTrPeakCnl.cnl_pk of the held list and the drained lines).  Its RI_gone
   is RI_event_live's text, word for word, so it is discharged by RI_event_live.  The rows at s5-r1d's TX texts:
   LS_drain_pre (TX_LS_drain_pre, peak form), LS_cnl_pre (TX_LS_cnl_pre), LS_drain_step (TX_LS_drain_step_t) ---- *)
Hypothesis RI_drain_skip : forall cx t m si h,
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
Hypothesis RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  RINV cx t m -> 0 <= t < OPS_MAX ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
(* ---- the drain's count growth (the room round's count rule).  check_no_loss's count premise is at the state the
   drain leaves; LS_cnt bounds the counts at the cut.  dr_post's two Permutations (W_contract_x.v dr_post_x) make the
   change of every count the change over the drained entry's, source's and g_out's blocks, with the same rest; this
   rule says that change is at most the drain trace's count peak, for every count predicate P.  A PURE MODEL rule
   (no astate; W8Entry-2's 04:20Z pattern, as the gone arm's GN_CNT_step), with the premises the walk holds at the
   drain's return (dc_stB): the cut's model facts at the call (dc_static, LS_cnt's guards, the dr3 / ls3 bundles of the
   entry and the source) and dr_post's model clauses (dr_dfun, dr3_epost, dr3_hpost, ls3_dpost) ---- *)
Hypothesis DR_CNT_grow : forall cx t m si h j e' h' LB out' (P : Z -> bool),
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = 0 \/ re_skip (nth j (lm_es m) dr_e0) = 1 ->
  msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
  dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  dr_dfun m si h j e' h' LB ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h ->
  (re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e') ->
  dr3_hpost h h' ->
  ls3_dpost m j h e' h' ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
   ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
   Z.to_nat (ReplyCnt.tr_peakP P
     (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat.
(* ---- the model facts the callees' premises need, read off RINV (projections, not steps) ---- *)
(* the picked source at the top of an operation: check_no_loss emptied its expected list, its held texts are
   distinct (the plain proof's pair_ok, Prog/SlotInv.v:253-263) *)
Hypothesis RI_src : forall cx t m si h,
  RINV cx t m -> dr_pick cx m si h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
(* the open sources have distinct fds (so drain's aothers_at holds of the other three slots) *)
Hypothesis RI_fds : forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* the relay's entry for an open source it still reads, and the source, agree (pair_ok's re_eof = 0 clauses) *)
Hypothesis RI_pair : forall cx t m si h j,
  RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
  length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat.

(* ---- the allocator-state facts the two calls take, read off LSx; the instance discharges them ---- *)
(* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3): conjunct 5
   is s5-r1d's fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:927), and the three premises after re_eof are the ones its
   rows take (fr_LS3_drain_pre_c4 ReplyLS3Arms.v:791, fr_LS_drain_pre_c5p): dc_regs' Ht, aentry_ok's |re_U| bound and
   the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was FALSE at reachable states. *)
Hypothesis LS_drain_pre : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
(* after the drain: what check_no_loss takes of the state it is called in.  A Theorem Labs lane's TX_LS_cnl_pre
   (commit d0d75bf92db, lib/A/ReplyLS3cTopxPost.v:146; proved as ReplyLS3Arms.v:841 fr_LS3_cnl_pre_p), with
   CfParamsReply.fr_MMAX -> MMAX: the binders e' cap' out' and nine premises after the old ten, each held at
   dc_calls (dc_regs' Ht, dr_at_op's lm_O m = [], and dc_stB's dcB_out: the cut's entry and source at the call,
   dr_post's frame and its entry / source clauses) *)
Hypothesis LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
(* the two steps of the allocator-state invariant *)
Hypothesis LS_drain_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
(* the drain charges the meter dr_cost of the entry and source it was called with (S to S1), check_no_loss
   cnl_cost of the lists it was called with (S1 to S'); lock, unlock, check_no_loss_read and check_shape_done
   keep the allocator state.  A Theorem Labs lane's TX_LS_drain_step (commit d0d75bf92db, lib/A/ReplyLS3cTopxPost.v:118;
   proved as ReplyLS3cArms.v:119 fr_LS3c_drain_step_p): the binders ly1 h1 E' H' and twenty premises after the old
   five, each held at dc_calls (the drain's and check_no_loss's frames, dcB_out and dc_stE's exports); and, last,
   dc_regs' `0 <= t < OPS_MAX`, as s5-r1d's TX_LS_drain_step_t (1318828167d lib/A/ReplyLSI.v:134, its LS instance's
   lsi_LS_drain_step :509) *)
Hypothesis LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
  dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 ->
  ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
(* the live counts at the cut leave room for the arm's peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2):
   a Theorem Labs lane's row fr_LS3cp_cnt_drain (commit ba8e99b5bd2, lib/A/ReplyLScnt.v:371) with its guards, over the
   room record's count fields (at the cf instance they are ReplyCnt's Psec / P24 / Lsec / L24 / Pcls / LPRIM; the
   top plugs it with ReplyLScntRP.v's lsc_rp_of_acnt).  Its peak is the row's pk_drain m h j (ReplyLScnt.v:151) with
   check_no_loss's part the parameter dr_cnl_pk (below): drain's trace peak + check_no_loss's peak over the drained
   lines + 2, which covers dr_spec's count premise (dr_pk) at the cut and cnl_spec's (cnl_pk) at the state the drain
   leaves (DR_CNT_grow, DR_CNT_cnl) *)
(* the kit's check_no_loss trace after a drain has at most that peak: the expected list was empty at the operation's
   start (RI_src) and the drain appended the lines (dr_dfun), the held list is kept (a PURE MODEL rule; at the top
   ReplyLScnt.lsc_cnl_call proves it with = at j := 0, nm := fun _ => RelayRunF.adr0) *)
Hypothesis DR_CNT_cnl : forall (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  (Z.to_nat (ReplyCnt.tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) <= ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P)%nat.
Hypothesis LS_cnt_drain : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RPi
    (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
       (ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P + 2))%nat)
    (ablocks TfibB ly S).

(* ---- SEG_EXIT's callee contracts at ARX: its CSHE is built in the proof from W3's pb_check_shape_ends_x, its RFg is
   C1's pb_relay_finish_h_x and its SR F1's pb_source_reset_gc_x, built in the proof.  relay_finish's callees at ARX:
   free(NULL)'s rule at K0's CTX_AFREE (a room rule, discharged in the instance file like AFREE_x); gestures_end's _x
   spec is F7's pb_gestures_end_closed_x over pb_gesture_end_x, built in the proof ---- *)
Hypothesis AFREE0_x : afree_null_cf_rule_c_x segs TfibB [] ARX MT RPi CTX_AFREE.
(* the "" literal's shadow facts over ARX (exit_x's XE_LIT_S) are a6's TopxImage.topx_XE_LIT_S_x, in the proof *)
(* ---- SEG_EXIT's model rules (_exit_x.v), verbatim at the instance, MMAX := fr_MMAX; the AR file's model functions
   qualified ---- *)
(* LS_rf_room at s5-r1d's TX_LS_rf_room (ReplyLSI.v; plug lsi_LS_rf_room :611): on the room line the kit's ge_room
   is the peak form and lib/A/W_LLVMFuzzerTestOneInput_exit.v's lx_rf_room threads `bb + gse_cap r - cap` (AddX's 9889b5a89d8), so lx_rf_room is
   s5's lx_rf_room_p; the row takes TX's `0 <= t <= OPS_MAX` *)
Hypothesis LS_rf_room : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  W_LLVMFuzzerTestOneInput_exit.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m)
    (lm_es m).
(* LS_exit_budget takes lregs_X's t bound and the relay entries' non-empty key texts (exit_x's exit_keys_nonempty,
   from amodel_at's aentry_ok) *)
Hypothesis LS_exit_budget : forall cx t m ly S, LSx cx t m ly S ->
  0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m).
Hypothesis RI_exit_slots : forall cx t m, RINV cx t m ->
  forall j, (j < 4)%nat -> W_LLVMFuzzerTestOneInput_exit.lx_ends_slot_ok (nth j (lm_hs m) None).
Hypothesis RI_exit_ends : forall cx t m, RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  W_LLVMFuzzerTestOneInput_exit.lx_ends_run (lm_gn m) (W_LLVMFuzzerTestOneInput_exit.lx_rf_O m)
    (W_LLVMFuzzerTestOneInput_exit.lx_norder m) (W_LLVMFuzzerTestOneInput_exit.lx_ord m) (lm_hs m) 0 =
  Some (Z.of_nat (length (W_LLVMFuzzerTestOneInput_exit.lx_rf_O m))).
(* LS_exit_end at s5-r1d's TX_LS_exit_end_e (ReplyLSI.v; plug lsi_LS_exit_end :647): ReplyLS3e.v LS_exit_end3e's four
   added premises, then the start model's non-empty key texts (exit_x's exit_keys_nonempty), last *)
Hypothesis LS_exit_end : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the room round's two exit rules for the post's XCNT and CAPOUT conjuncts and the count row at X (_exit_x.v,
   RiRestate's 5a9b16eac9e, at the instance; LS_cnt_exit is s5-r1d's fr_LS3cp_cnt_exit_c, ReplyLScntX.v:152, over
   the closed range of lregs_X's t) *)
Hypothesis LS_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks TfibB ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok TfibB S' ly' (input_blks cx) (lm_G m) cap out.
Hypothesis LS_exit_cap : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
Hypothesis LS_cnt_exit : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> amodel_at TfibB ly S W mem m -> 0 <= t <= OPS_MAX ->
  cnt_ok_pk RPi rf_pk (ablocks TfibB ly S).
Hypothesis FP_SINK : forall cx Hp, BASEx cx Hp -> ~ YI16.sink_open_fp (lf_FP fr_FP cx).
(* ---- ARM_remove's model rules (_remove_x.v, RiRestate's 6666490987b), verbatim at the instance (B := TfibB,
   RP := RPi, MMAX := fr_MMAX); the AR file's model functions and remove_x's rm_pk qualified.  Its RI_rm_rr_fds is
   ARM_drain's RI_fds, word for word, so it is discharged by RI_fds; its HT is TfibB_syms.  The rows at s5-r1d's TX
   texts: LS_rm_rr_pre (TX_LS_rm_rr_pre), LS_rm_cnl_pre (TX_LS_rm_cnl_pre), LS_rm_step (TX_LS_rm_step_t) ---- *)
Hypothesis RI_rm_found : forall cx t m si h,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 4 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_remove.rm_kb cx m) = Some si -> nth si (lm_hs m) None = Some h ->
  exists j, (j < length (lm_es m))%nat /\ re_fd (W_LLVMFuzzerTestOneInput_remove.rm_ent m j) = hs_fd h.
Hypothesis RI_rm_rr_pair : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
  re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = hs_overlong h /\ (re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 -> bzs (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) = bzs (hs_W h)).
(* the removed slot's expected list is empty at the arm's start (drain_x's RI_src's first conjunct, at rm_at; the
   plain proof's pair_ok, Prog/SlotInv.v:253-263) *)
Hypothesis RI_rm_src : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> hl_recs (hs_expected h) = [].
(* relay_remove's sizes and budget: a Theorem Labs lane's TX_LS_rm_rr_pre (lib/A/ReplyLS3Peak.v:152, commit 1318828167d)
   in this Section's names (MMAX for CfParamsReply.fr_MMAX; its ent_capout_ok0 (c_W cx) (c_mem cx), ReplyLS3eCap.v:134,
   stated by its body: that file Requires the AR arms); conjuncts 3 and 6 in rr_spec_x's peak form *)
Hypothesis LS_rm_rr_pre : forall cx t m ly S si h j0,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) /\ lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Hypothesis RI_rm_cnl_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
(* check_no_loss's allocator facts after relay_remove's charge: a Theorem Labs lane's TX_LS_rm_cnl_pre (lib/A/
   ReplyLS3cTopxPost.v:178, commit d0d75bf92db) in this Section's names: the start model's block sizes (rm_mfacts) and
   the composed frame to the call's state (rm_fr).  LS_rm_cnl_pre, LS_rm_cshe_pre and LS_rm_sr_pre take, after rm_rr_ok,
   the arm's t bound (lregs_rmc) and the removed entry's partial-line bound (remove_x's rm3_pre); LS_rm_step takes the
   partial-line bound after LSx *)
Hypothesis LS_rm_cnl_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).
Hypothesis RI_rm_cnlr_eof : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> 0 <= re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) <= 1.
Hypothesis RI_rm_cshe_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Hypothesis LS_rm_cshe_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)) ->
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H').
Hypothesis RI_rm_csd : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  0 <= lm_gn m <= 1 ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 + cc = Z.of_nat (length O2).
Hypothesis LS_rm_sr_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' -> W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H') ->
  mo_ok MT S (sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))).
Hypothesis RI_rm_step : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2).
Hypothesis LS_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
(* the room round's count row (a Theorem Labs lane's ROOM-TEXTS (c); a Theorem Labs lane's lib/A/ReplyLScnt.v fr_LS3cp_cnt_rm at
   commit ba8e99b5bd2): at the arm's start, the live counts plus the arm's peak rm_pk stay under RP's bounds.  The
   guards are the walk's facts there (the model's sizes come from amodel_at) *)
Hypothesis LS_cnt_remove : forall cx t m ly S (W : world segs) mem si h j0,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0) (ablocks TfibB ly S).
(* the count rules (W8Entry-2's pattern decision): a later callee's count premise is LS_cnt's at the arm's start
   moved by the composed frame (rm_fr: the call's live blocks are the input, the model's blocks at the call and the
   start's rest), so what it needs beyond LS_cnt is a fact of the MODEL alone: the model's count at the call plus the
   callee's premise peak stays under the start model's count plus rm_pk, for every count predicate P.  Pure model
   rules (no astate); the premises are what the walk holds at the call *)
Hypothesis RM_CNT_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 (P : Z -> bool),
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_mfacts m ->
  W_LLVMFuzzerTestOneInput_remove_x.rm3_pre (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) +
     W_contract_x.cnl_pk (hs_expected h1) (hs_held h1) P <= ReplyCnt.acnt P (model_blks m) + W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0 P)%nat.
Hypothesis RM_CNT_cshe : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' (P : Z -> bool),
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_mfacts m -> W_LLVMFuzzerTestOneInput_remove_x.rm3_pre (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2)) +
     W_contract_x.cshe_pk P <= ReplyCnt.acnt P (model_blks m) + W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0 P)%nat.
Hypothesis RM_CNT_sr : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc (P : Z -> bool),
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc -> W_LLVMFuzzerTestOneInput_remove.rm_mfacts m ->
  W_LLVMFuzzerTestOneInput_remove_x.rm3_pre (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2)) +
     W_contract_x.sr_pk P <= ReplyCnt.acnt P (model_blks m) + W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0 P)%nat.
(* the callee specs, in their kit _x forms (W_contract_x.v; each owner proves its _x twin) *)

(* ---- ARM_gone's callee contract at ARX that no _x proof gives yet (W_LLVMFuzzerTestOneInput_gone_x.v's SNP at the
   instance; W_sites.v's snprintf chain proves the AR form only).  Its relay_instance_gone (RIG_x) is built in the
   proof (pb_relay_instance_gone_x) ---- *)
Hypothesis SNP_x : asnprintf_realizes_x TfibB ARX (SIGMA WS_snprintf) W_sites.FR_GOT_GUARD W_sites.FR_GUARD.
(* gone_x's HGOTG / GN_LITS over ARX are a6's TopxImage.topx_HGOTG_x / topx_GN_LITS_x, in the proof *)
(* ---- ARM_gone's model rules (_gone_x.v's RIR / HPAIRS / HLSRIG / RIstep / RIend), verbatim at the instance, MMAX :=
   fr_MMAX: _gone_base.v's texts, cited qualified.  Its HFDS (GN_RI_fds) is ARM_drain's RI_fds, word for word, so it
   is discharged by RI_fds ---- *)
Hypothesis RI_gone_read : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_read RINV.
Hypothesis RI_gone_pairs : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_pairs RINV.
(* LS_gone_rig at s5-r1d's adopted peak text TX_GN_LS_rig (1318828167d, ReplyLS3Peak.v; plug lsi_GN_LS_rig,
   ReplyLSI.v:672), in W8's names (gone_base's gn_pairs / gn_op / gn_id; ReplyLS3eCap.v's ent_capout_ok0 inline) *)
Hypothesis LS_gone_rig : forall cx t m ly S hs,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\ mo_ok MT S (tr_cost MT tr) /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Hypothesis RI_gone_step : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step TfibB MT LSx RINV CfParamsReply.fr_MMAX.
Hypothesis RI_gone_end : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end TfibB MT LSx RINV.
(* ARM_gone's count rows (_gone_x.v CNTRIG / LSCNT / CNTSTEP at RP := RPi and the arm's peak gn_pk := s5-r1d's
   ReplyLScnt.pk_gone; GoneRestate's 6e8e0f9f814): relay_instance_gone's premise peak and check_no_loss's inside the
   arm's, and the cut's counts under it (s5's fr_LS3cp_cnt_gone, ReplyLScnt.v:586, at the instance) *)
Hypothesis CNT_gone_rig : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_rig ReplyLScnt.pk_gone (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m)
    (lm_es m) hs)).
Hypothesis LS_cnt_gone : W_LLVMFuzzerTestOneInput_gone_base_x.GN_LS_cnt_x TfibB LSx RINV RPi ReplyLScnt.pk_gone.
Hypothesis CNT_gone_step : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_step RINV ReplyLScnt.pk_gone
  (fun h => cnl_pk (hs_expected h) (hs_held h)).

(* C1's placement premises at fr_globals / PB_fr / TfibB, decided: a list of ranges inside a band, a list pairwise
   apart (zseps), and one range of plain image bytes (in a segment, apart from the owned statics and from errno) *)
Local Ltac c1_forall :=
  apply Forall_forall; let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [fst snd]; lia |]); destruct Hr.
Local Ltac c1_seps :=
  vm_compute; repeat split; first [left; discriminate | right; discriminate |
    left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H].
Local Ltac c1_plain Hz :=
  lazymatch type of Hz with in_zr ?a ?r =>
    split; [apply segin_ok; apply (rng_all_in (segin segs) [r]); [vm_compute; reflexivity | apply inG_cons; left; exact Hz]|];
    split;
    [ rewrite (@ts_owned TfibB TfibB_syms); let Hex := fresh "Hex" in intros Hex;
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (fst r) (snd r) Tfib_owned_static ltac:(vm_compute; reflexivity) a
        Hex Hz)
    | rewrite (@ts_errno TfibB TfibB_syms); let He := fresh "He" in intros He;
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (fst r) (snd r) [(TFIB_ERRNO, 4)] ltac:(vm_compute; reflexivity) a
        (proj2 (inG_cons (TFIB_ERRNO, 4) [] a) (or_introl He)) Hz) ]
  end.

Theorem fr_contract_top_x :
  @fr_lib_contract_cf_x fx rc checksum_shape TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP
    G fr_FP [] ARX.
Proof.
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms) as HEV.
  pose proof (palib_tfib TfibB TfibB_syms) as TL.
  (* ---- the top step's plugs (TOPX-PLUGS.md sha256 e0a351b05fe4; internal record), each the Section hypothesis it replaces, by its lemma ---- *)
  (* the room round: the arms' RP_NP at RPi (rp_RM RP_cf S k is room_live_cf S) and NPF (room_live_set_fs) *)
  assert (RP_NP : forall S k, rp_RM RPi S k <-> NP S) by (intros S k; exact (iff_refl _)).
  assert (NPF : forall S f, NP S -> NP (set_fs f S)) by exact YGcfRoomLive.room_live_set_fs.
  (* errno's law over ARX (a Theorem Labs lane's W_ERRL_x.v:93) *)
  assert (ERRL_x : errno_law_x TfibB ARX) by exact (W_ERRL_x.errno_law_x_holds TfibB TfibB_syms ARX).
  (* a6's image group (TopxImage.v): ad_G's shadow hulls, the symbol table's fake-stack fields, the "" literal's
     shadow, the GOT word of __stack_chk_guard and snprintf's two literals, each at the pre-W1 relation, carried to ARX
     by ARX_rt_of *)
  assert (GSHV_x : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
    (forall x, a <= x < a + n -> inG ad_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n)
    by (intros ly S Hp W mem md a n H; exact (TopxImage.topx_GSHV_x ly S Hp W mem md a n (ARX_rt_of _ _ _ _ _ _ H))).
  assert (TLF : PALibF TfibB) by exact TopxImage.topx_TLF.
  assert (XE_LIT_S_x : ashp_x ARX (VAL W_LLVMFuzzerTestOneInput_exit.AX_lit_empty) 1)
    by exact (ashp_x_of_rt _ _ TopxImage.topx_XE_LIT_S_x).
  assert (HGOTG_x : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
    rdword (aview segs (w_H W) mem) W_sites.FR_GOT_GUARD = Some W_sites.FR_GUARD)
    by (intros ly S Hp W mem md H; exact (TopxImage.topx_HGOTG_x ly S Hp W mem md (ARX_rt_of _ _ _ _ _ _ H))).
  assert (GN_LITS_x : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 7 /\
    shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 20)) 7 /\
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 21)) 14 /\
    shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 21)) 14)
    by (intros ly S Hp W mem md H; exact (TopxImage.topx_GN_LITS_x ly S Hp W mem md (ARX_rt_of _ _ _ _ _ _ H))).
  (* the runtime rows at ARX: the QMm W1 lifts at TopX_RT.ARX_rtW (this file's ARX, by delta), lock / unlock / strlen
     above, memcpy / memset TopX_INTRIN.v's *)
  assert (ALOCK : alock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_lock)) by exact topx_ALOCK_W.
  assert (AUNLOCK : aunlock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_unlock)) by exact topx_AUNLOCK_W.
  assert (ASTRLEN_x : astrlen_realizes_x TfibB ARX (SIGMA WS_strlen)) by exact topx_ASTRLEN_x_W.
  assert (AMEMCPY_x : aintrin_realizes_x segs TfibB ARX OCpy (SIGMA WS_asan_memcpy))
    by exact TopX_INTRIN.topx_AMEMCPY_x_W.
  assert (AMEMSET_x : aintrin_realizes_x segs TfibB ARX OSet (SIGMA WS_asan_memset))
    by exact TopX_INTRIN.topx_AMEMSET_x_W.
  (* relay_remove's to == from __asan_memcpy contract (W_sites_x.v amemcpy_same_realizes_x), a Theorem Labs lane's
     TopX_MEMCPYS.topx_AMEMCPYS_W at ARX_rtW (this file's ARX, by delta) *)
  assert (AMEMCPYS_x : amemcpy_same_realizes_x TfibB ARX (SIGMA WS_asan_memcpy)) by exact TopX_MEMCPYS.topx_AMEMCPYS_W.
  assert (ASTRNLEN_x : et_strnlen_spec_x TfibB ARX 0x10350 0x10370 (SIGMA WS_strnlen))
    by (unfold et_strnlen_spec_x; exact TopX_RT2.topx_ASTRNLEN_x_W).
  (* a Theorem Labs lane's route (b) ASM rows at top_x's relation (AsmTopX.v:162 / :169, ARX_asm is ARX over tfibsegs) *)
  assert (ASM0 : astack_malloc_pres_x segs TfibB ARX 0) by exact AsmTopX.asm0_pres_ARX.
  assert (ASM1 : astack_malloc_pres_x segs TfibB ARX 1) by exact AsmTopX.asm1_pres_ARX.
  (* check_shape_done and check_no_loss_read at ARX (ARM_drain, ARM_remove, ARM_gone, SEG_EXIT): W3's
     pb_check_shape_done_x / pb_check_no_loss_read_x, whose premises are the laws and TL *)
  assert (CSD_x : csd_spec_x TfibB [] ARX (BASE + AF_fr_check_shape_done))
    by exact (W_check_shape_done.pb_check_shape_done_x (PI := PB_fr) TfibB [] ARX ARX_laws TL).
  assert (CNLR_x : cnlr_spec_x TfibB [] ARX (BASE + AF_fr_check_no_loss_read))
    by exact (W_check_no_loss_read.pb_check_no_loss_read_x (PI := PB_fr) TfibB [] ARX ARX_laws TL).
  (* IMGC at image A from the laws' image field (W_img_x.v:29, the kit's form; HeadX uses the same) *)
  pose proof (W_img_x.fr_img_cover_x TfibB ARX ARX_laws) as IMGC.
  (* a live cf block's size is nonnegative: AR_blocks_law_cf's last conjunct (0 <= n < cf_malloc_max), the way BLKR
     below reads it *)
  assert (BLKN : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn). lia. }
  (* SEG_PRO's HFP_pro: a2's TopxEntry.hfp_pro_x (TopxEntry.v:149) at the cf block bound arcf_blk (stated at the pre-W1
     relation, carried to ARX by ARX_rt_of) and FPCOV *)
  pose proof (TopxEntry.hfp_pro_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX fr_FP
    (fun ly S Hp W mem md p n H => TopxEntry.arcf_blk ly S Hp W mem md p n (ARX_rt_of ly S Hp W mem md H)) FPCOV)
    as HFP_pro.
  pose proof (@pb_check_bounded_x fx rc AE2k.tfib_sink_head PB_fr TfibB [] ARX _ ARX_laws ARX_hp0 TL fr_CBAP IMGC BLKN)
    as CBX.
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HZS TfibB TfibB_syms) as HZS.
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_ROMPIN TfibB TfibB_syms) as ROMPIN.
  assert (HPST : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  assert (HMMAX : APARTIAL < CfParamsReply.fr_MMAX) by (unfold APARTIAL; apply Z.ltb_lt; vm_compute; reflexivity).
  (* SEG_PRO's stack_malloc facts at ARX, from the cf laws: YGcallcf.v's owned-low and Wf laws (WFx := Wf_cf, ARX's
     first projection), and YG05cf.v's stack_malloc progress and post (W_frame_x.v:1015 SMALLOC_AR's proof, cf form) *)
  assert (OWNLOW : ARx_owned_low_law segs TfibB ARX).
  { intros ly S Hp W mem md a H Ho.
    exact (ARx_owned_low_law_cf_x (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
      ly S Hp W mem md a (proj1 H) Ho). }
  assert (WFL : ARx_wf_law segs ARX (Wf_cf (cp := CfParams_reply) (as_universe TfibB))).
  { intros ly S Hp W mem md H. exact (ARx_wf_law_cf_x (cp := CfParams_reply) segs TfibB ly S Hp W mem md (proj1 H)). }
  assert (SMALLOC : forall s cid, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> 0 <= cid <= 10 ->
    count_cid cid (frames s) < fs_frames cid ->
    exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
    frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s)).
  { intros s cid HWF Hcid Hcnt.
    destruct (stack_malloc_progress_cf (cp := CfParams_reply) _ s cid HWF Hcid Hcnt) as (pos & s' & Hpath).
    pose proof (stack_malloc_ok_cf (cp := CfParams_reply) _ s cid HWF Hcid) as HTOK.
    destruct (atok_apath _ _ _ [] (PFake cid pos, s') HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post_cf in HQ.
    destruct HQ as (_ & Hf & _ & _ & Hfrs & Hfresh).
    exists pos, s'. split; [exact Hpath|]. split; [exact Hf|]. split; [exact Hfrs | exact Hfresh]. }
  (* ARM_drain's two image facts that no _G.v lemma states in its form: every DR_GK range is one of G_fr_c's 20
     objects (c_HGW's proof), and a live cf block's request is below 2 ^ 30 (AR_blocks_law_cf's last conjunct,
     n < cf_malloc_max, and YG08cf.cf_malloc_max_bound) *)
  assert (HG_GK : forall a, inG DR_GK a -> inG G a).
  { apply inG_sub. unfold DR_GK.
    repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  assert (BLKR : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n < 2 ^ 30).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)) as Hb. lia. }
  (* SEG_EXIT's instance facts: the stack_free law over ARX (YG0tcf.v's astack_free_law_ok_cf on ARX's first
     projection; Hp is unchanged; QMm W1: arodata_ok_cf at mem' by ReplyKeptAroA.arodata_kept_A from the law's last
     premise, the kept-bytes frame), the frame split after stack_free (YG05cf.v's stack_free_ok_cf, WFx := Wf_cf), a
     live block's request below 2 ^ 30 (BLKR), the g_s slots' shadow hull (GSHV_x: g_s is ad_G's first range), and the
     stdio cells apart from G_fr_c (tfib_K's six ranges against G_fr_c's objects and errno, decided) *)
  assert (ASF : astack_free_law_x segs TfibB ARX).
  { intros ly S Hp W mem md mem' md' cid pos H Hin HF HO HV Hvm Hlz He HK HKEPT. unfold ARX in H |- *.
    destruct H as (HAR & HH & HQ).
    split; [|split; [exact HH | exact (ReplyKeptAroA.arodata_kept_A mem mem' HQ HKEPT)]].
    exact (YG0tcf.astack_free_law_ok_cf (cp := CfParams_reply) segs TfibB ly S Hp W mem md mem' md' cid pos HAR
      Hin HF HO HV Hvm Hlz He HK). }
  assert (SFREE : forall s cid pos, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> In (cid, pos) (frames s) ->
    exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2).
  { intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf (cp := CfParams_reply) _ s cid pos HWF Hin)). }
  assert (BLKM : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    n < 2 ^ 30).
  { intros ly S Hp W mem md p n H Hin. exact (proj2 (BLKR ly S Hp W mem md p n H Hin)). }
  assert (XR_GSHV : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
    (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
    shadow_hull_vis (aview segs (w_H W) mem) a n).
  { intros ly S Hp W mem md a n H Hn Hx. apply (GSHV_x ly S Hp W mem md a n H Hn).
    intros x Hx'. unfold ad_G. cbn [app]. apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact (Hx x Hx'). }
  (* ---- C1 at the instance (a Theorem Labs lane's 922a710cda0; relay_event re-proved by AddX's C3 88557c15170): relay_add's,
     relay_event's and relay_finish's _x proofs build RA_x / RE_x / RF_x.  Their premises come from the facts above,
     _G.v's deciders at fr_globals / PB_fr / TfibB (the placements, decided), and the Section hypotheses ASM0, MO_FR,
     AMEMSET_x, ASTRLEN_x, AFREE0_x (the callees and laws no _x proof gives yet) ---- *)
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms) as HOWN.
  (* source_reset at ARX (F1's walk, W_source_reset.v:2537 pb_source_reset_gc_x): the free rules at K0's CTX_AFREE,
     memset / memmove by a Theorem Labs lane's rows, its three free contexts rows of CTX_AFREE (decided) *)
  assert (SR_x : sr_spec_g_x TfibB [] ARX MT RPi (BASE + AF_fr_source_reset)).
  { refine (W_source_reset.pb_source_reset_gc_x (PI := PB_fr) TfibB [] ARX ARX_laws ARX_hp0 IMGC BLKN HPST TL MT RPi
      MLAW CTX_AFREE AFREE_x AFREE0_x AMEMSET_x TopX_RT3.topx_AMEMMOVE_W _ _ _).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). }
  (* gesture_end and gestures_end at ARX (F7's walks, W_gesture_end.v:755 pb_gesture_end_x and W_gestures_end_top.v:92
     pb_gestures_end_closed_x): send_line by SL_x, strlen by TopX_RT's row, the " end\0" literal's shadow by
     W_shadow_pin_x.ashp_end5_5_fr_x, and their placement premises at fr_RG / PB_fr / TfibB, decided *)
  assert (HGSL : gx_ok segs TfibB (G_SL TfibB fr_RG)).
  { intros a Ha. pose proof (c_HG_SL TfibB a Ha) as Hg. exact (conj (c_img TfibB HEV a Hg)
      (conj (HOWN a Hg) (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms a Hg))). }
  assert (HROMO_SL : rom_out segs TfibB (G_SL TfibB fr_RG)).
  { apply (W_LLVMFuzzerTestOneInput_pro.pro_rom_out TfibB HEV ROMPIN).
    intros a Hr Hg. exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg)). }
  (* send_line at ARX (a Theorem Labs lane / a Theorem Labs lane's W_send_line_x.v pb_send_line_x): its premises by the asserts above, the
     AR-free instance facts of W_send_line_x_top.v, errno_location by TopX_RT4.v, and errno's zero shadow by
     W_ERRL_x.errno_azs (AF0m's zero-shadow range) *)
  pose proof (W_ERRL_x.errno_azs TfibB TfibB_syms) as HERRZ.
  assert (SL_x : sl_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_send_line)).
  { exact (W_send_line_x.pb_send_line_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG ARX_laws ARX_hp0
      BLKM HGSL W_send_line_x_top.slx_HGR HROMO_SL W_send_line_x_top.slx_HGO MLAW TL TopX_RT4.topx_AERRNO_W AMEMCPY_x
      CTX_AREALLOC ARE_x W_send_line_x_top.slx_HCTX_slr W_send_line_x_top.slx_HERRNO HERRZ
      W_send_line_x_top.slx_HV9 W_send_line_x_top.slx_HV10 W_send_line_x_top.slx_HV11 W_send_line_x_top.slx_HV12
      W_send_line_x_top.slx_HV13 W_send_line_x_top.slx_HV14 W_send_line_x_top.slx_HV15 W_send_line_x_top.slx_HH17
      W_send_line_x_top.slx_HH19 W_send_line_x_top.slx_HH21 W_send_line_x_top.slx_HSM W_send_line_x_top.slx_HH22
      W_send_line_x_top.slx_HH23 W_send_line_x_top.slx_HH24 W_send_line_x_top.slx_HRGD). }
  assert (HE5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom segs a).
  { intros a Ha. eapply W_LLVMFuzzerTestOneInput_exit.xe_romseg_ok; [| exact Ha]. vm_compute. reflexivity. }
  assert (HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img segs a).
  { intros a Ha. apply segin_ok. apply (rng_all_in (segin segs) [(VAL A_lit_end5, 5)]); [vm_compute; reflexivity|].
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Ha. }
  assert (HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
    ~ inG (G_SL TfibB fr_RG) a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { intros a Ha. pose proof (HE5R a Ha) as Hr. split; [intros Hg; exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg))|].
    split; [|exact (c_ROM_ERR TfibB HEV a Hr)].
    rewrite (@ts_owned TfibB TfibB_syms). intros Hex.
    exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (VAL A_lit_end5) 5 Tfib_owned_static ltac:(vm_compute; reflexivity) a Hex
      ltac:(unfold in_zr; cbn [fst snd]; exact Ha)). }
  assert (GE_x : ge_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_gesture_end)).
  { refine (W_gesture_end.pb_gesture_end_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG ARX_laws
      ARX_hp0 BLKN HGSL ASTRLEN_x SL_x HEND5I (W_shadow_pin_x.ashp_end5_5_fr_x TfibB TfibB_syms ARX ARX_laws)
      (fun a _ H => ltac:(inversion H)) (fun a _ H => ltac:(inversion H)) MLAW _ HEND5G HROMO_SL).
    intros r Hr. unfold aout_fp in Hr. rewrite HEV in Hr. vm_compute in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbn [fst snd]; lia |]). destruct Hr. }
  assert (GSE_x : gse_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_gestures_end)).
  { refine (W_gestures_end_top.pb_gestures_end_closed_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG
      ARX_laws ARX_hp0 TL HGSL MLAW GE_x CTX_AFREE AFREE_x AFREE0_x _ _ HROMO_SL _ HEND5I HEND5G
      (fun a _ H => ltac:(inversion H)) (fun a _ H => ltac:(inversion H)) IMGC BLKN).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
    - (* HOUTG: the stream's cells other than errno are G_fr_c's (_G.v), so image, not read-only, not owned *)
      intros r a Hr Ha Hne. cbn [In aout_fp Z.eqb] in Hr.
      assert (HGa : inG G a).
      { destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]; cbn [fst snd] in Ha.
        + exact (c_HG_smax TfibB a Ha).
        + apply (c_HG_SL TfibB). unfold G_SL, inG.
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
        + apply (c_HG_SL TfibB). unfold G_SL, inG.
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
        + apply (c_HG_SL TfibB). unfold G_SL, inG.
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
        + exact (c_HG_client TfibB a Ha).
        + exact (c_HG_cbroken TfibB a Ha).
        + exact (c_HG_sdead TfibB a Ha).
        + exact (c_HG_seintr TfibB a Ha).
        + exfalso. exact (Hne Ha). }
      split; [exact (c_img TfibB HEV a HGa)|].
      split; [intros Hr'; exact (c_rom_apart TfibB HEV a Hr' HGa) | exact (HOWN a HGa)]. }
  (* relay_add (W_relay_add.v:638), at ra_spec_g_x's G *)
  (* the room round (ide-15's F3): at RPi, its RPF / RMM laws by RP_cf's fields rp_RPF / rp_RMM *)
  assert (RA_x : ra_spec_g_x TfibB [] ARX MT RPi fr_globals CTX_AREALLOC (BASE + AF_fr_relay_add)).
  { intros Gc HGc _.
    refine (W_relay_add.pb_relay_add_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX Gc fr_globals ARX_laws
      ARX_hp0 TL TLF (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE SMALLOC OWNLOW IMGC BLKN ASM0 ASF FFL
      MLAW MO_FR (rp_RPF RPi) (rp_RMM RPi) HGc _ ALOCK AUNLOCK CTX_AREALLOC ARE_x _ AMEMSET_x _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - (* GW: RA_G's cells lie in a writable segment *)
      intros Hh m a Ha _. apply wr_of_seg. apply segwb_ok.
      eapply (rng_all_in (segwb segs)); [| exact Ha]. vm_compute. reflexivity.
    - (* HMMAX *) apply Z.ltb_lt. vm_compute. reflexivity.
    - (* HV6 *) vm_compute. reflexivity.
    - (* HLA *) vm_compute. reflexivity.
    - (* HV7 *) vm_compute. reflexivity.
    - (* HV16 *) vm_compute. reflexivity.
    - (* HV8 *) vm_compute. reflexivity.
    - (* HV4 *) vm_compute. reflexivity.
    - (* HH30 *) vm_compute. reflexivity.
    - (* HH31 *) vm_compute. reflexivity.
    - (* HH32 *) vm_compute. reflexivity.
    - (* HIG *) c1_forall.
    - (* HEO *) intros i Hi Hex. rewrite (@ts_owned TfibB TfibB_syms), (@ts_errno TfibB TfibB_syms) in Hex.
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok TFIB_ERRNO 4 Tfib_owned_static ltac:(vm_compute; reflexivity) _ Hex
        ltac:(lia)).
    - (* HWKI *) intros i Hi. apply segin_ok.
      apply (rng_all_in (segin segs) [(rg_wake fr_globals + 4, 4)]); [vm_compute; reflexivity|].
      apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
    - (* HWKO *) intros i Hi Hex. rewrite (@ts_owned TfibB TfibB_syms) in Hex.
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (rg_wake fr_globals + 4) 4 Tfib_owned_static
        ltac:(vm_compute; reflexivity) _ Hex ltac:(lia)).
    - (* HSEPG *) c1_seps. }
  (* relay_event (W_relay_event.v:230), at _event's own G et_GRE *)
  assert (RE_x : re_spec_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX (et_GRE TfibB) fr_RG
    (BASE + AF_fr_relay_event)).
  { refine (W_relay_event.pb_relay_event_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX (et_GRE TfibB) fr_RG
      ARX_laws ARX_hp0 BLKR (c_gx_ok_GRE TfibB HEV HOWN (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms)) SL_x ALOCK AUNLOCK ASTRLEN_x _ _ _ _ _ _ _).
    - (* HV6 *) vm_compute. reflexivity.
    - (* HLA *) vm_compute. reflexivity.
    - (* HLD: the lock is apart from send_line's G *) intros a Ha Hg.
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (rg_lock fr_RG) 12 (G_SL TfibB fr_RG)
        ltac:(vm_compute; reflexivity) a Hg Ha).
    - (* HLRW *) intros a Ha Hr. exact (c_rom_apart TfibB HEV a Hr (c_HGlock TfibB a Ha)).
    - (* HAOD *) intros a Ha. cbn [fr_RG fr_globals rg_lock rg_send_max rg_client rg_send_dead] in *. lia.
    - (* HAO3 *) cbn [fr_RG fr_globals rg_send_max rg_client rg_send_dead]. lia.
    - (* HLPST *) intros a _ H. inversion H. }
  (* relay_finish (W_relay_finish_h.v:3671), at SEG_EXIT's G: RF_G and send_line's G *)
  assert (RF_x : rf_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG) fr_RG
    AG_THREAD_UP AG_LISTEN CTX_AFREE (BASE + AF_fr_relay_finish)).
  { assert (HGRF : gx_ok segs TfibB (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG)).
    { intros a Ha. unfold inG in Ha. apply Exists_app in Ha as [Ha | Ha];
        [pose proof (c_HG_RF TfibB a Ha) as Hg | pose proof (c_HG_SL TfibB a Ha) as Hg];
        exact (conj (c_img TfibB HEV a Hg) (conj (HOWN a Hg) (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms a Hg))). }
    refine (W_relay_finish_h.pb_relay_finish_h_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX
      (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG) fr_RG AG_THREAD_UP AG_LISTEN CTX_AFREE ARX_laws ARX_hp0 TL TLF MLAW
      IMGC BLKN OWNLOW (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE SMALLOC ASM0 ASF FFL HGRF ALOCK
      AUNLOCK AFREE_x AFREE0_x GSE_x MO_FR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - (* HV3 *) vm_compute. reflexivity.
    - (* HV6 *) vm_compute. reflexivity.
    - (* HV7 *) vm_compute. reflexivity.
    - (* HV8 *) vm_compute. reflexivity.
    - (* HH9 *) vm_compute. reflexivity.
    - (* HH11 *) vm_compute. reflexivity.
    - (* HH12 *) vm_compute. reflexivity.
    - (* HIG *) c1_forall.
    - (* HSEPG *) c1_seps.
    - (* HPLAIN *) intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). vm_compute in Hr.
      do 7 (destruct Hr as [<- | Hr]; [c1_plain Hz |]). destruct Hr.
    - (* HWSEG *) intros a Ha. apply segwb_ok. eapply (rng_all_in (segwb segs)); [| exact Ha]. vm_compute. reflexivity.
    - (* RGAL *) vm_compute. reflexivity.
    - (* HIGO *) c1_forall.
    - (* HSEPO *) c1_seps.
    - (* HPLAINO *) intros a [Ha | Ha];
        [change (in_zr a (rg_send_max fr_RG, 8)) in Ha | change (in_zr a (rg_send_dead fr_RG, 1)) in Ha]; c1_plain Ha.
    - (* HROMG *) intros a Ha Hr. apply (c_rom_apart TfibB HEV a Hr).
      destruct Ha as [Ha | [Ha | [Ha | Ha]]];
        [exact (c_HG_RF TfibB a Ha) | exact (c_HG_SL TfibB a Ha) | exact (c_HG_smax TfibB a Ha)
        | exact (c_HG_sdead TfibB a Ha)].
    - (* HE5R *) intros a Ha. change (Z.of_nat (length END5)) with 5 in Ha.
      eapply W_LLVMFuzzerTestOneInput_exit.xe_romseg_ok; [| exact Ha]. vm_compute. reflexivity.
    - (* HROMO *) apply (W_LLVMFuzzerTestOneInput_pro.pro_rom_out TfibB HEV ROMPIN).
      intros a Hr Hg. exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg)).
    - (* HWSEGE *) intros a Ha. apply segwb_ok. rewrite (@ts_errno TfibB TfibB_syms) in Ha.
      apply (rng_all_in (segwb segs) [(TFIB_ERRNO, 4)]); [vm_compute; reflexivity|].
      apply inG_cons. left. exact Ha.
    - (* PSTR *) intros a _ H. inversion H.
    - (* PSTC *) intros a _ H. inversion H.
    - (* PSTO *) intros a _ H. inversion H. }
  (* op_add at the instance: W2's pb_op_add_g_x, its image facts as in addI's zz_OA_from_W2 *)
  assert (OA : oa_spec_g_x (PI := PB_fr) TfibB [] ARX MT RPi (BASE + AF_fr_op_add)).
  { refine (pb_op_add_g_x TfibB [] ARX _ MT RPi ARX_laws HPST TL MLAW (rp_RMM RPi) CfParamsReply.fr_MMAX HMMAX _ _ _ _ _
      CTX_AMALLOC _ AMA_x SR_x CTX_AREALLOC _ RA_x).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. repeat split; first [left; discriminate | right; discriminate |
        left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H].
    - intros a Ha. split; [|split].
      + apply segin_ok. apply (rng_all_in (segin segs) [(rg_wake fr_globals + 4, 4)]); [vm_compute; reflexivity|].
        apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + rewrite (@ts_owned TfibB TfibB_syms). intros Hex.
        exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (rg_wake fr_globals + 4) 4 Tfib_owned_static
          ltac:(vm_compute; reflexivity) a Hex ltac:(lia)).
      + rewrite (@ts_errno TfibB TfibB_syms). cbn [fr_globals rg_wake] in Ha. unfold TFIB_ERRNO. lia.
    - assert (E : [BASE + AF_fr_op_add + 0xcc] = [0x84fdc]) by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AMALLOC. vm_compute. repeat (first [left; reflexivity | right]).
    - assert (E : [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] = [0x82a9c; 0x85018])
        by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]). }
  (* list_push at the instance: W2's pb_list_push_g_x at WR_MMAX = fr_MMAX *)
  assert (LP : lp_spec_g_x (PI := PB_fr) TfibB [] ARX MT RPi WR_MMAX (BASE + AF_fr_list_push)).
  { refine (pb_list_push_g_x TfibB [] ARX ARX_laws ARX_hp0 TL MT RPi MLAW WR_MMAX wr_HMMAX IMGC BLKN CTX_AREALLOC ARE_x _
      CTX_AMALLOC AMA_x AMEMCPY_x _).
    - assert (E : [BASE + AF_fr_list_push + 0xac] = [0x8513c]) by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]).
    - assert (E : [BASE + AF_fr_list_push + 0xd0] = [0x85160]) by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AMALLOC. vm_compute. repeat (first [left; reflexivity | right]). }
  (* drain at ARX: a Theorem Labs lane's pb_drain_x (W_drain_pb.v), at top_x's ARX / RPi / fr_MMAX / fr_RG; its premises are
     top_x's own MLAW / ARE_x / AFREE_x / ASTRNDUP_x, SL_x and LP above, BLKN, and Qed lemmas (W_drain_pb.v's drain_*
     instance facts, TopX_RT / RT3 / RT4 / INTRIN, TopxDrainLit, W_ERRL_x.errno_azs, ARX_laws / ARX_hp0) *)
  assert (DR_x : dr_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_drain)).
  { pose proof ARX_laws. pose proof ARX_hp0. pose proof (palib_tfib TfibB TfibB_syms).
    pose proof TopX_INTRIN.topx_AMEMCPY_x_W. pose proof TopX_RT3.topx_AMEMMOVE_W. pose proof TopX_RT3.topx_AMEMCHR_W.
    pose proof topx_ASTRLEN_x_W. pose proof TopX_RT4.topx_AERRNO_W. pose proof TopX_RT4.topx_ASTRRCHR_W.
    pose proof TopX_RT4.topx_ASTRNCMP_W. pose proof TopX_RT4.topx_ASTRCMP_W.
    pose proof (LP : lp_spec_g_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX (BASE + AF_fr_list_push)).
    pose proof (fun S k k' H => rp_RMM RPi S k' k H). pose proof CfParamsReply.reply_HMMAX.
    pose proof (dlit_at_x_of_rt _ _ TopxDrainLit.topx_HLIT5_x). pose proof (dlit_at_x_of_rt _ _ TopxDrainLit.topx_HLIT6_x).
    pose proof (dlit_at_x_of_rt _ _ TopxDrainLit.topx_HLIT7_x).
    pose proof W_drain_pb.drain_hctx_re1. pose proof W_drain_pb.drain_hctx_re2.
    pose proof W_drain_pb.drain_hctx_fr1. pose proof W_drain_pb.drain_hctx_fr2. pose proof W_drain_pb.drain_hctx_sd.
    pose proof W_drain_pb.drain_HCROM. pose proof W_drain_pb.drain_HVS.
    pose proof W_drain_pb.drain_HV9. pose proof W_drain_pb.drain_HV12.
    pose proof W_drain_pb.drain_HGSB. pose proof W_drain_pb.drain_HSM.
    pose proof W_drain_pb.drain_HRGD. pose proof W_drain_pb.drain_HERRW.
    pose proof W_drain_pb.drain_HG. pose proof W_drain_pb.drain_HGO.
    pose proof W_drain_pb.drain_HGR. pose proof W_drain_pb.drain_HROMO.
    pose proof W_drain_pb.drain_HERRNO. pose proof W_drain_pb.drain_HGSZ.
    pose proof W_drain_pb.drain_PSTR. pose proof W_drain_pb.drain_PSTG. pose proof W_drain_pb.drain_PSTO.
    eapply W_drain_pb.pb_drain_x; eassumption. }
  (* relay_remove at ARX (W_relay_remove.v:149 pb_relay_remove_x): the frame and law facts above (ASM0 its
     __asan_stack_malloc_0), DR_x / GSE_x, the free rules AFREE_x / AFREE0_x, the runtime rows ALOCK / AUNLOCK /
     AMEMCPY_x and AMEMCPYS_x, TopxRelayFacts.v's instance facts, and PSTR / PSTG at PST = [] *)
  assert (RR_x : rr_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG CTX_AFREE (BASE + AF_fr_relay_remove)).
  { pose proof ARX_laws. pose proof ARX_hp0.
    pose proof TopxRelayFacts.topx_rr_HG. pose proof TopxRelayFacts.topx_rr_HROMO.
    pose proof TopxRelayFacts.topx_HH59. pose proof TopxRelayFacts.topx_HH60. pose proof TopxRelayFacts.topx_HV4.
    pose proof TopxRelayFacts.topx_HRGP. pose proof TopxRelayFacts.topx_HRGI. pose proof TopxRelayFacts.topx_HEND5L.
    eapply (W_relay_remove.pb_relay_remove_x (PI := PB_fr)); try eassumption;
      let h := fresh "Hpst" in intros ? _ h; inversion h. }
  (* relay_instance_gone at ARX (W_relay_instance_gone.v:140 pb_relay_instance_gone_x): the same frame and law facts
     (ASM1 its __asan_stack_malloc_1), DR_x / GE_x, AFREE_x, ALOCK / AUNLOCK, snprintf SNP_x with HGOTG_x, strlen
     ASTRLEN_x, strncmp TopX_RT4.topx_ASTRNCMP_W, the laws' granule tail W_drain_cx_x.alloc_tail_x, the literals'
     location SnpNarrowSites.HLITGOT_PB_fr, TopxRelayFacts.v's instance facts, and PSTR / PSTG at PST = [] *)
  assert (RIG_x : rig_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG CTX_AFREE
    (BASE + AF_fr_relay_instance_gone)).
  { pose proof ARX_laws. pose proof ARX_hp0. pose proof TopX_RT4.topx_ASTRNCMP_W.
    pose proof (W_drain_cx_x.alloc_tail_x segs TfibB ARX ARX_laws) as ALLOC_TAIL.
    pose proof TopxRelayFacts.topx_rig_HGRIG. pose proof TopxRelayFacts.topx_rig_HROMO.
    pose proof TopxRelayFacts.topx_HH44. pose proof TopxRelayFacts.topx_HH45.
    pose proof TopxRelayFacts.topx_HRGP. pose proof TopxRelayFacts.topx_HRGI. pose proof TopxRelayFacts.topx_HEND5L.
    pose proof TopxRelayFacts.topx_HCANR. pose proof (glit_at_x_of_rt _ _ TopxRelayFacts.topx_HLIT20_x).
    pose proof (glit_at_x_of_rt _ _ TopxRelayFacts.topx_HLIT21_x).
    pose proof (glit_at_x_of_rt _ _ TopxRelayFacts.topx_HLIT31_x).
    pose proof SnpNarrowSites.HLITGOT_PB_fr.
    eapply (W_relay_instance_gone.pb_relay_instance_gone_x (PI := PB_fr)); try eassumption;
      let h := fresh "Hpst" in intros ? _ h; inversion h. }
  assert (HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
    ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G a).
  { intros a Ha.
    assert (HK : inG [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8);
        (FF_meta_mem, 8)] a).
    { unfold aenv_addr in Ha. cbn [tfib_K ak_threaded ak_need_locks ak_ofl_lock ak_canary ak_meta_ptr ak_meta_mem] in Ha.
      unfold inG. rewrite Exists_exists.
      destruct Ha as [[-> | [-> | [Ha | Ha]]] | [Ha | Ha]];
        [ exists (A_threaded, 1) | exists (A_need_locks, 1) | exists (A_ofl_lock, 16) | exists (FF_canary, 8)
        | exists (FF_meta_ptr, 8) | exists (FF_meta_mem, 8) ];
        (split; [cbn [In]; repeat (first [left; reflexivity | right]) | unfold in_zr; cbn [fst snd]; lia]). }
    assert (Hd : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 64) &&
        forallb (fun g => (fst r + snd r <=? fst g) || (fst g + snd g <=? fst r)) (G_fr_obj ++ [(TFIB_ERRNO_A, 4)]))
      [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8); (FF_meta_mem, 8)] = true)
      by (vm_compute; reflexivity).
    unfold inG in HK. apply Exists_exists in HK as (r & Hr & Hz). rewrite forallb_forall in Hd. specialize (Hd r Hr).
    apply andb_prop in Hd as [Eb Hd]. apply andb_prop in Eb as [E0 E1]. apply Z.leb_le in E0, E1. unfold in_zr in Hz.
    split; [lia|].
    intros HinG. unfold G_fr_c in HinG. rewrite HEV in HinG. unfold inG in HinG.
    apply Exists_exists in HinG as (g & Hg & Hzg). rewrite forallb_forall in Hd. specialize (Hd g Hg).
    unfold in_zr in Hzg. apply orb_prop in Hd as [Hd | Hd]; apply Z.leb_le in Hd; lia. }
  (* ARM_remove's instance facts.  relay_remove's two caller contexts (rr_spec_x's last premise at its call 0x849dc:
     relay_remove + 436 = 0x83f98, then 0x849e0, then [] or the entry's return 0x821e8), rows of K0's CTX_AFREE *)
  assert (HCTX_rr0 : In [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1] CTX_AFREE).
  { assert (E : [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1] = [0x83f98; 0x849e0])
      by (vm_compute; reflexivity).
    rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). }
  assert (HCTX_rr1 : In [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1; RA_LLVMF]
    CTX_AFREE).
  { assert (E : [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1; RA_LLVMF] =
      [0x83f98; 0x849e0; 0x821e8]) by (vm_compute; reflexivity).
    rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). }
  (* the relay's placement (W_contract.v rg_place) at TfibB / fr_RG: W_rg_place.v's fr_rg_place, its geometry by
     vm_compute there; its five ranges are G_fr_c objects (in the image, not owned: zz_HOWN, not errno), g_lock and
     g_nsrc lie in a writable segment, and the five are apart from A_OBJ 0 / 1 / 32 and the uar cell (decided) *)
  assert (RG5 : forall a, rg_rng fr_RG a -> inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_src fr_RG, 8);
      (rg_wake fr_RG + 4, 4); (rg_s fr_RG, 4 * ASRC)] a).
  { intros a Ha. unfold rg_rng in Ha. unfold inG.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
      repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact (conj (proj1 Ha) (proj2 Ha))
                    | apply Exists_cons_tl]). }
  assert (RGO : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_src fr_RG, 8); (rg_wake fr_RG + 4, 4);
      (rg_s fr_RG, 4 * ASRC)] a -> inG G_fr_obj a).
  { apply inG_sub.
    repeat (apply Forall_cons; [intros a Ha; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  assert (RGP_c : rg_place (PI := PB_fr) TfibB fr_RG).
  { apply (W_rg_place.fr_rg_place TfibB).
    - intros a Ha. pose proof (RGO a (RG5 a Ha)) as Ho.
      exact (conj (c_img TfibB HEV a (obj_c TfibB a Ho))
        (conj (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms a (obj_c TfibB a Ho)) (c_obj_noerr TfibB HEV a Ho))).
    - intros Hh m a Ha _. apply wr_of_seg. apply segwb_ok.
      assert (Hl : inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4)] a).
      { unfold inG. destruct Ha as [Ha|Ha];
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact (conj (proj1 Ha) (proj2 Ha))
                        | apply Exists_cons_tl]). }
      revert Hl. apply rng_all_in. vm_compute. reflexivity.
    - intros a Ha. pose proof (RG5 a Ha) as H5.
      split; [|split; [|split]]; revert H5; apply apart_of_b; vm_compute; reflexivity. }
  (* source_reset's G at slot si (_remove_x.v HGP, gx_prog_x): _G.v's c_HGP proof over ARX, its shadow-hull clause
     by XR_GSHV (GSHV_x on g_s) *)
  assert (HGP_c : forall si, (si < 4)%nat ->
      gx_prog_x (PI := PB_fr) TfibB ARX [(W_LLVMFuzzerTestOneInput_remove.rm_HA si, ASRC)]).
  { intros si Hsi. unfold W_LLVMFuzzerTestOneInput_remove.rm_HA.
    assert (Hsub : forall a, inG [(rg_s fr_RG + ASRC * Z.of_nat si, ASRC)] a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
    { intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr in Ha. cbn [fst snd] in Ha. clear - Ha Hsi. unfold ASRC in *. lia. }
    assert (Hgs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG [(rg_s fr_RG, 4 * ASRC)] a)
      by (intros a Ha; apply inG_cons; left; unfold in_zr; cbn [fst snd]; exact Ha).
    split.
    { intros a Ha. pose proof (c_HGs TfibB a (Hsub a Ha)) as Hg.
      exact (conj (c_img TfibB HEV a Hg) (conj (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms a Hg)
        (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms a Hg))). }
    split; [eapply gx_rt_sub; [|exact (c_HGRT_s TfibB HEV)]; intros a Ha; exact (Hgs a (Hsub a Ha))|].
    split.
    { intros a Ha. destruct (c_rom_noerr TfibB HEV a Ha) as [He Hh]. split; [|exact (conj (ROMPIN a Ha) (conj He Hh))].
      intros HGa. apply (c_rom_apart TfibB HEV a Ha). exact (c_HGs TfibB a (Hsub a HGa)). }
    split.
    { intros a Ha.
      assert (Hf : forallb (rng_all (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end))
        [(rg_s fr_RG, 4 * ASRC)] = true) by (vm_compute; reflexivity).
      pose proof (rng_all_in _ _ a Hf (Hgs a (Hsub a Ha))) as Hx.
      cbv beta in Hx. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate Hx]. }
    split.
    { intros a Ha m.
      assert (Hf : forallb (rng_all (segwb segs)) [(rg_s fr_RG, 4 * ASRC)] = true) by (vm_compute; reflexivity).
      pose proof (segwb_ok segs a (rng_all_in _ _ a Hf (Hgs a (Hsub a Ha)))) as Hw.
      unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact Hw]. }
    intros ly S Hp W mem md a n HAR Hn Hx. apply (XR_GSHV ly S Hp W mem md a n HAR Hn).
    intros x Hxr. exact (Hsub x (Hx x Hxr)). }
  (* ARM_gone's FRMF (W_frame_x.v:105): a live fake frame's alignment, from YG0scf.v's frame_facts_cf on ARX's
     ARcf (its ARmcf conjunct) *)
  assert (FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARX ly S Hp W mem md -> In (cid, pos) (frames S) ->
    ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0).
  { intros ly S Hp W mem md cid pos [[M _] _] Hin.
    destruct (YG0scf.frame_facts_cf (cp := CfParams_reply) _ ly S Hp _ cid pos M Hin)
      as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
    split; [exact Hpg|]. split; [exact Hoff|]. split; [exact H64 | exact Hb]. }
  (* ---- W3's check_shape_event and check_shape_ends at ARX (ARM_event; ARM_remove, ARM_gone, SEG_EXIT), with their
     callees at the instance ---- *)
  (* next_line (W_next_line.v:384): W1's walk, memchr by topx_AMEMCHR_W (a Theorem Labs lane's TopX_RT3.v, QMm W1), the
     placement by W_w1_place.v *)
  assert (NL_x : nl_spec_x TfibB [] ARX (BASE + AF_fr_next_line))
    by exact (W_next_line.pb_next_line_x (PI := PB_fr) TfibB [] ARX ARX_laws TL W_w1_place.nl_objs_apart_fr
      TopX_RT3.topx_AMEMCHR_W W_w1_place.nl_crom_fr).
  (* list_find (W_list_find.v:958): W1's walk, bcmp by topx_ABCMP_W; at every G *)
  pose proof (W_list_find.pb_list_find_x (PI := PB_fr) TfibB [] ARX ARX_laws ARX_hp0 TL TopX_RT3.topx_ABCMP_W)
    as LFIND_x.
  (* check_shape_event (W_check_shape_event.v:292) *)
  assert (CSE_x : cse_spec_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_check_shape_event))
    by exact (W_check_shape_event.pb_check_shape_event_x (PI := PB_fr) TfibB [] ARX ARX_laws TL ASTRLEN_x
      TopX_RT3.topx_ABCMP_W NL_x).
  (* check_shape_ends (W_cshe_top.v:133) at every G with gx_ok: list_drop's step by W1's alist_at_drop, memmove by
     topx_AMEMMOVE_W, the two free sites' contexts and the placement by W_w3_place_fr.v *)
  assert (CSHE_x : forall Gc, gx_ok segs TfibB Gc -> cshe_spec_x TfibB [] ARX MT RPi Gc (BASE + AF_fr_check_shape_ends)).
  { intros Gc HGc.
    exact (W_cshe_top.pb_check_shape_ends_x (PI := PB_fr) TfibB [] ARX MT RPi Gc ARX_laws ARX_hp0 IMGC BLKN HPST FRMF
      MLAW HGc TL ASTRLEN_x TopX_RT3.topx_ABCMP_W TopX_RT3.topx_AMEMMOVE_W CTX_AFREE AFREE_x
      W_w3_place_fr.check_shape_ends_HCTX_cshe_l2_fr W_w3_place_fr.check_shape_ends_HCTX_cshe_l3_fr NL_x (LFIND_x Gc)
      (W_list_drop.alist_at_drop (PI := PB_fr) TfibB)
      W_w3_place_fr.check_shape_ends_PLACEG0_fr W_w3_place_fr.check_shape_ends_PLACEG32_fr
      W_w3_place_fr.check_shape_ends_HGR_fr W_w3_place_fr.check_shape_ends_HGRR_fr
      W_w3_place_fr.check_shape_ends_ROMNS_fr W_w3_place_fr.check_shape_ends_HEND5R_fr
      (ashp_x_of_rt _ _ W_w3_place_fr.check_shape_ends_HEND5S_fr) W_w3_place_fr.check_shape_ends_HGS_fr). }
  (* gesture_model at ARX (W_gesture_model_g.v:85 pb_gesture_model_g_x, room form; its _cf instance is stated at the
     pre-W1 relation, so the generic walk is applied at ARX): bcmp by topx_ABCMP_W, the three literals' shadow facts by
     W_shadow_pin_x, list_find by LFIND_x, list_push by LP (WR_MMAX is fr_MMAX), list_drop at every G with gx_ok / gx_rt
     / rom_out by the caller-context walk (W_list_drop_top.v:907 pb_list_drop_ro_cx_x, room form) at K0's CTX_AFREE:
     its free context [list_drop + 0x60] is W_w3_place_fr.list_drop_HCTX_fr *)
  pose proof (W_list_drop_top.pb_list_drop_ro_cx_x (PI := PB_fr) TfibB [] ARX ARX_laws ARX_hp0 MT RPi CTX_AFREE
    W_w3_place_fr.list_drop_HCTX_fr TL AFREE_x TopX_RT3.topx_AMEMMOVE_W) as LDROP_RO.
  pose proof (W_gesture_model_g.pb_gesture_model_g_x (PI := PB_fr) TfibB MT RPi CfParamsReply.fr_MMAX [] ARX ARX_laws
    ARX_hp0 TL MLAW TopX_RT3.topx_ABCMP_W (W_shadow_pin_x.ashp_gesture_13_fr_x TfibB TfibB_syms ARX ARX_laws)
    (W_shadow_pin_x.ashp_begin_5_fr_x TfibB TfibB_syms ARX ARX_laws)
    (W_shadow_pin_x.ashp_end_3_fr_x TfibB TfibB_syms ARX ARX_laws) (fun Gc _ _ => LFIND_x Gc) LP LDROP_RO) as GM_x.
  (* check_no_loss (W_check_no_loss.v:3662) at every G with gx_ok / gx_rt (its gx_rt is not used): the sink head's
     read-only clause by W_rom_place_fr.v, the free site's context and the placement by W_w3_place_fr.v *)
  assert (CNL_x : forall Gc, gx_ok segs TfibB Gc -> gx_rt TfibB Gc ->
    cnl_spec_x TfibB [] ARX MT RPi Gc CfParamsReply.fr_MMAX (BASE + AF_fr_check_no_loss)).
  { intros Gc HGc _.
    exact (W_check_no_loss.pb_check_no_loss_x (PI := PB_fr) TfibB [] ARX MT RPi Gc CfParamsReply.fr_MMAX ARX_laws
      ARX_hp0 IMGC BLKN HPST TL HGc W_w3_place_fr.check_no_loss_CNLAP_fr MLAW W_w3_place_fr.check_no_loss_HGR_fr
      W_w3_place_fr.check_no_loss_HGRR_fr W_w3_place_fr.check_no_loss_ROMNS_fr W_rom_place_fr.ofl_head_rom_fr NL_x GM_x
      TopX_RT3.topx_ABCMP_W TopX_RT3.topx_AMEMMOVE_W CTX_AFREE AFREE_x W_w3_place_fr.check_no_loss_HCTX_cnl_free_fr
      (W_list_drop.alist_at_drop (PI := PB_fr) TfibB)). }
  refine (lf_contract_of_segments_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP []
    ARX ARX_laws GX_ok LSx RINV _ _ _ _ _ _ _ _ _
    _ _ _ _ _).
  - exact (lf_seg_pro_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP NPF MO_FR OA TL TLF OWNLOW (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL
      SMALLOC ASM1 FFL (c_glob_wr TfibB HEV) ERRL_x HEV HZS (W_LLVMFuzzerTestOneInput_addI.zz_HGOBJ TfibB)
      (c_rom_apart TfibB HEV) ROMPIN GSHV_x HFP_pro LS_pro_oa RI_pro LS_pro LS_cnt_pro BLKN HPST).
  - exact (lf_seg_head_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok
      LSx RINV (c_HGnout TfibB) (c_HERRNO TfibB HEV) RI_head_nout LS_head_nout HZS RI_head_skip LS_head_skip).
  - exact (lf_arm_add_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws GX_ok LSx RINV RPi RP_NP OA HEV HZS (W_LLVMFuzzerTestOneInput_addI.zz_HGOBJ TfibB) ERRL_x ROMPIN GSHV_x HPST
      BLKN RI_add_pre RI_add_open RI_add_none LS_add_room LS_add_open LS_add_none LS_cnt_add).
  - exact (lf_arm_write_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP TL LP (c_glob_wr TfibB HEV) ERRL_x (c_HGs TfibB) HZS (c_HGW TfibB)
      (c_HERRS TfibB HEV) (c_ROM_ERR TfibB HEV) ROMPIN BLKN (fun a _ H => ltac:(inversion H)) (fun a _ H => ltac:(inversion H))
      RI_write_skip LS_write_skip RI_write_push LS_write_room LS_write_push LS_cnt_write).
  - exact (lf_arm_drain_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX TL RPi RP_NP DR_x ALOCK AUNLOCK CSD_x CNLR_x CNL_x
      (c_HGs TfibB) (c_HG_DR TfibB) (c_HGlock TfibB) HG_GK (c_HERRHI TfibB HEV) ERRL_x (c_rom_out TfibB TfibB_syms HEV)
      (c_glob_wr TfibB HEV) HZS c_HAP HPST BLKR RI_drain_skip RI_drain_step DR_CNT_grow RI_src RI_fds RI_pair
      RI_event_live LS_drain_pre LS_cnl_pre LS_drain_skip LS_drain_step
      (fun h P => ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P) DR_CNT_cnl LS_cnt_drain).
  - exact (lf_arm_close_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV
      (c_HGs TfibB) (W_LLVMFuzzerTestOneInput_addI.zz_HZS TfibB TfibB_syms) TL (c_HERRHI TfibB HEV) RI_close LS_close).
  - exact (W_LLVMFuzzerTestOneInput_remove_x.lf_arm_remove_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post
      fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP CfParamsReply.fr_MMAX TL MLAW CTX_AFREE
      HCTX_rr0 HCTX_rr1 RGP_c (c_HGs TfibB) (c_HGlock TfibB) (c_HGnsrc TfibB) (c_HG_DR TfibB) HZS c_HAP
      (c_HGRT_s TfibB HEV) (c_rom_out TfibB TfibB_syms HEV)
      (c_HMG TfibB HEV (fun a Ha => W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms a (obj_c TfibB a (c_mglob_obj a Ha))))
      RI_rm_found RI_fds RI_rm_rr_pair RI_rm_src LS_rm_rr_pre RI_rm_cnl_pre LS_rm_cnl_pre RI_rm_cnlr_eof RI_rm_cshe_pre
      LS_rm_cshe_pre RI_rm_csd LS_rm_sr_pre RI_rm_step LS_rm_step LS_cnt_remove RM_CNT_cnl RM_CNT_cshe RM_CNT_sr
      RR_x CSD_x CNLR_x CNL_x CSHE_x SR_x HGP_c ERRL_x
      (ashp_x_of_rt _ _ W_shadow_pin_x.ashp_str2_1_fr_cf) BLKR (fun a _ H => ltac:(inversion H))
      (fun a _ _ H => ltac:(inversion H))).
  - exact (W_LLVMFuzzerTestOneInput_gone_x.lf_arm_gone_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV (c_ERRNO_LOW TfibB HEV) TL HZS RI_gone_read SNP_x HGOTG_x GN_LITS_x
      CfParamsReply.fr_MMAX RPi RIG_x RGP_c (c_HG_RIG TfibB) RI_gone_pairs RI_fds LS_gone_rig ReplyLScnt.pk_gone RP_NP
      CNT_gone_rig LS_cnt_gone (c_HGcells TfibB) (c_glob_wr TfibB HEV) ROMPIN (c_CELLS_ERRNO TfibB HEV)
      (c_ROM_ERR TfibB HEV) CNL_x (fun Gc Hok _ => CSHE_x Gc Hok) (c_HGs TfibB) RI_gone_step RI_gone_end CNT_gone_step
      MLAW CNLR_x CSD_x BLKN HPST FRMF).
  - exact (lf_arm_eintr_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV
      (c_HGs TfibB) (W_LLVMFuzzerTestOneInput_addI.zz_HZS TfibB TfibB_syms) TL (c_HERRHI TfibB HEV) RI_eintr LS_eintr).
  - exact (lf_arm_event_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX RPi RP_NP TL (c_glob_wr TfibB HEV) ERRL_x
      (c_rom_out TfibB TfibB_syms HEV) (c_HGlock TfibB) (c_HG_SL TfibB) (c_HG_carry TfibB) (c_HERR_AP TfibB HEV) AMA_x
      AFREE_x AMEMCPY_x ASTRNLEN_x RE_x CSE_x BLKN HPST RI_event_live RI_event_step LS_event_malloc LS_event_relay
      LS_event_free LS_event_step LS_cnt_event).
  - exact (lf_arm_sendmax_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok
      LSx RINV (c_HG_smax TfibB) (c_HG_seintr TfibB) TL (c_HERRHI TfibB HEV) RI_sendmax LS_sendmax).
  - exact (lf_arm_default_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok
      LSx RINV (c_HG_sdead TfibB) (c_HG_gone TfibB) (c_HG_client TfibB) (c_HGlock TfibB) TL (c_HERRHI TfibB HEV)
      ALOCK AUNLOCK RI_default LS_default).
  - exact (lf_seg_latch_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws GX_ok LSx RINV CBX (c_ERRNO_LOW TfibB HEV)).
  - exact (W_LLVMFuzzerTestOneInput_exit_x.lf_seg_exit_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
      LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV TL MLAW ASF FFL ERRL_x
      (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE CfParamsReply.fr_MMAX (c_HG_SL TfibB) HZS RPi RP_NP
      CSD_x SR_x CSHE_x RF_x (c_XRF_ERRNO TfibB HEV) (c_rom_out TfibB TfibB_syms HEV) LS_rf_room LS_exit_budget
      (W_LLVMFuzzerTestOneInput_Gx.c_XR_HGM TfibB) XR_GSHV (c_glob_wr TfibB HEV) XE_LIT_S_x RI_exit_slots RI_exit_ends
      LS_exit_end LS_exit_cnt LS_exit_cap LS_cnt_exit FP_SINK (AD1u.tfib_AIL TfibB TfibB_syms) HG_K HPST BLKN BLKM).
Qed.

(* ---- route R (a Theorem Labs lane 2026-10-30 22:14Z: a Theorem Labs lane writes A top_x at R).  A free inside a call re-hides the dead
   shadow, so at the re-hiding instance R := wle' pa_segs RZ_cf a call step gives only `R W W'`, and the entry contract is
   cut_x's fr_lib_contract_cf_xR (a Theorem Labs lane).  fr_contract_top_xR is cut_x's lf_contract_of_segments_xR over the
   fourteen segment / arm R twins (a Theorem Labs lane's lf twins; branches and bullets: lfR-landed.md (sha256 9ee70faf236a; internal record)),
   each applied with its strict bullet's arguments without the callee specs it takes at R, then R R_refl R_trans WLE_R
   and those R specs:
     SEG_PRO_R     lf_seg_pro_xR (OA_R)           SEG_HEAD_R    lf_seg_head_xR
     ARM_add_R     lf_arm_add_xR (OA_R)           ARM_write_R   lf_arm_write_xR (LP_R: the arm calls list_push)
     ARM_drain_R   lf_arm_drain_xR (DR_R, CNL_R)  ARM_close_R   lf_arm_close_xR
     ARM_remove_R  lf_arm_remove_xR (RR_R, CNL_R, CSHE_R, SR_R)
     ARM_gone_R    lf_arm_gone_xR (RIG_R, CNL_R, CSHE_R)
     ARM_eintr_R   lf_arm_eintr_xR                ARM_event_R   lf_arm_event_xR (RO, RO_ARx, AMA_R, AFREE_R, RE_R)
     ARM_sendmax_R lf_arm_sendmax_xR              ARM_default_R lf_arm_default_xR
     SEG_LATCH_R   lf_seg_latch_xR                SEG_EXIT_R    lf_seg_exit_xR (CSD_R, SR_R, CSHE_R, RF_R, LS_exit_end_R)
   The R callee specs are built in the proof, as fr_contract_top_x builds the strict ones, from the R walks in the tree,
   each given the R forms of its own callee specs: op_add (W_op_add.v pb_op_add_g_xR), source_reset (W_source_reset.v
   pb_source_reset_gc_xR), list_free (W_list_free.v pb_list_free_g_xR), list_push (W_list_push.v pb_list_push_g_xR),
   list_drop (W_list_drop_top.v pb_list_drop_ro_cx_xR), gesture_model (W_gesture_model_g.v pb_gesture_model_g_xR),
   check_no_loss (W_check_no_loss.v pb_check_no_loss_xR), check_shape_done (W_check_shape_done.v
   pb_check_shape_done_xR), __asan_memset (W_sites_x.v aintrin_realizes_xR_of_x), send_line (W_send_line_x.v
   pb_send_line_xR), gesture_end / gestures_end (W_gesture_end.v pb_gesture_end_xR, W_gestures_end_top.v
   pb_gestures_end_closed_xR), relay_add / relay_event / relay_finish (W_relay_add.v pb_relay_add_xR, W_relay_event.v
   pb_relay_event_xR, W_relay_finish_h.v pb_relay_finish_h_xR), drain (W_drain_pb.v pb_drain_xR), relay_remove /
   relay_instance_gone (W_relay_remove.v pb_relay_remove_xR, W_relay_instance_gone.v pb_relay_instance_gone_xR) and
   check_shape_ends (W_cshe_top.v pb_check_shape_ends_xR, its loops at R by a Theorem Labs lane's W_cshe_l2w.v cshe_l2_run_xR /
   W_cshe_l3.v cshe_l3_top_xR).  strndup's rule at R is Section topx's strict ASTRNDUP_x lifted by
   CfRBridgeRulesRh.astrndup_cf_rule_c_xR_lift (strndup frees nothing).  The leaves that free nothing (lock, unlock,
   strlen, strnlen, memcpy, bcmp, memmove, memchr, strrchr, strncmp, strcmp, errno_location, next_line, list_find,
   check_shape_event, check_no_loss_read, check_bounded) stay at their strict contracts, as the twins and walks take
   them.  What no closed R walk in the tree gives is this Section's hypotheses; their dischargers are listed at the end
   of the Section.  The strict rules of Section topx at the four allocator calls (AMA_x, ARE_x, AFREE_x, AFREE0_x) and
   the strict LS_exit_end are not used here. *)
Section topxR.
Variable R : YA0n.world W_kit.pa_segs -> YA0n.world W_kit.pa_segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* ---- the R rules' call-boundary premise RO (QMm fit (1); part 3c took memnorm out of the rules) at the call memory,
   from the call state's ARX (the walks' texts, W_check_no_loss.v Section wR), and realloc's hull admission
   (W_list_push.v Section wR's texts) ---- *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> RO mem.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
(* ---- the cf instance's allocator rules at R (W_journal_x.v Section hc's R texts), each at its strict rule's K0 table,
   MMAX and RPi ---- *)
Hypothesis AMA_R : amalloc_cf_rule_c_xR segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi RO CTX_AMALLOC R.
Hypothesis ARE_R : arealloc_cf_rule_c_xR segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi RO HA CTX_AREALLOC R
  (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).
Hypothesis AFREE_R : afree_cf_rule_c_xR segs TfibB [] ARX MT RPi RO CTX_AFREE R.
Hypothesis AFREE0_R : afree_null_cf_rule_c_xR segs TfibB [] ARX MT RPi RO CTX_AFREE R.
(* ---- relay_remove's walk takes one fact of R itself (W_relay_remove.v:184 pb_relay_remove_xR, its R_IMG text): R
   hides no image byte that its first world shows ---- *)
(* holds at R := wle' pa_segs RZ_cf: wle' hides a new byte only inside RZ_cf (YA0nH.v:151), which lies above the image *)
Hypothesis R_IMG : forall (W W' : world segs) (a : word), R W W' -> in_img segs (bv_unsigned a) -> w_H W' a = true ->
  w_H W a = true.
(* ---- SEG_EXIT's model rule LS_exit_end at R (W_LLVMFuzzerTestOneInput_exit_x.v:5318 LS_exit_end_R): Section topx's
   LS_exit_end with the walk's journal from the entry at R (W_journal_x.ajournal_gx_xR .. R ..); every other premise and
   the conclusion verbatim ---- *)
Hypothesis LS_exit_end_R : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  W_journal_x.ajournal_gx_xR segs TfibB [] ARX R G 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Theorem fr_contract_top_xR :
  @fr_lib_contract_cf_xR fx rc checksum_shape TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP
    G fr_FP [] ARX R.
Proof.
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms) as HEV.
  pose proof (palib_tfib TfibB TfibB_syms) as TL.
  (* ---- the plugs and instance facts the R twins and walks take at their strict texts: fr_contract_top_x's, by the
     same lemmas ---- *)
  assert (RP_NP : forall S k, rp_RM RPi S k <-> NP S) by (intros S k; exact (iff_refl _)).
  assert (NPF : forall S f, NP S -> NP (set_fs f S)) by exact YGcfRoomLive.room_live_set_fs.
  assert (ERRL_x : errno_law_x TfibB ARX) by exact (W_ERRL_x.errno_law_x_holds TfibB TfibB_syms ARX).
  assert (GSHV_x : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
    (forall x, a <= x < a + n -> inG ad_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n)
    by (intros ly S Hp W mem md a n H; exact (TopxImage.topx_GSHV_x ly S Hp W mem md a n (ARX_rt_of _ _ _ _ _ _ H))).
  assert (TLF : PALibF TfibB) by exact TopxImage.topx_TLF.
  assert (XE_LIT_S_x : ashp_x ARX (VAL W_LLVMFuzzerTestOneInput_exit.AX_lit_empty) 1)
    by exact (ashp_x_of_rt _ _ TopxImage.topx_XE_LIT_S_x).
  assert (HGOTG_x : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
    rdword (aview segs (w_H W) mem) W_sites.FR_GOT_GUARD = Some W_sites.FR_GUARD)
    by (intros ly S Hp W mem md H; exact (TopxImage.topx_HGOTG_x ly S Hp W mem md (ARX_rt_of _ _ _ _ _ _ H))).
  assert (GN_LITS_x : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 7 /\
    shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 20)) 7 /\
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 21)) 14 /\
    shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 21)) 14)
    by (intros ly S Hp W mem md H; exact (TopxImage.topx_GN_LITS_x ly S Hp W mem md (ARX_rt_of _ _ _ _ _ _ H))).
  assert (ALOCK : alock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_lock)) by exact topx_ALOCK_W.
  assert (AUNLOCK : aunlock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_unlock)) by exact topx_AUNLOCK_W.
  assert (ASTRLEN_x : astrlen_realizes_x TfibB ARX (SIGMA WS_strlen)) by exact topx_ASTRLEN_x_W.
  assert (AMEMCPY_x : aintrin_realizes_x segs TfibB ARX OCpy (SIGMA WS_asan_memcpy))
    by exact TopX_INTRIN.topx_AMEMCPY_x_W.
  assert (AMEMSET_x : aintrin_realizes_x segs TfibB ARX OSet (SIGMA WS_asan_memset))
    by exact TopX_INTRIN.topx_AMEMSET_x_W.
  assert (ASTRNLEN_x : et_strnlen_spec_x TfibB ARX 0x10350 0x10370 (SIGMA WS_strnlen))
    by (unfold et_strnlen_spec_x; exact TopX_RT2.topx_ASTRNLEN_x_W).
  assert (ASM1 : astack_malloc_pres_x segs TfibB ARX 1) by exact AsmTopX.asm1_pres_ARX.
  (* bcmp / memmove at ARX (a Theorem Labs lane's TopX_RT3.v QMm W1 lifts, at ARX_rtW: this file's ARX, by delta), named
     once *)
  assert (ABCMP : abcmp_realizes_x segs TfibB ARX (SIGMA WS_bcmp)) by exact TopX_RT3.topx_ABCMP_W.
  assert (AMOVE : amemmove_realizes_x TfibB ARX (SIGMA WS_asan_memmove)) by exact TopX_RT3.topx_AMEMMOVE_W.
  assert (CSD_x : csd_spec_x TfibB [] ARX (BASE + AF_fr_check_shape_done))
    by exact (W_check_shape_done.pb_check_shape_done_x (PI := PB_fr) TfibB [] ARX ARX_laws TL).
  assert (CNLR_x : cnlr_spec_x TfibB [] ARX (BASE + AF_fr_check_no_loss_read))
    by exact (W_check_no_loss_read.pb_check_no_loss_read_x (PI := PB_fr) TfibB [] ARX ARX_laws TL).
  pose proof (W_img_x.fr_img_cover_x TfibB ARX ARX_laws) as IMGC.
  assert (BLKN : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn). lia. }
  pose proof (TopxEntry.hfp_pro_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX fr_FP
    (fun ly S Hp W mem md p n H => TopxEntry.arcf_blk ly S Hp W mem md p n (ARX_rt_of ly S Hp W mem md H)) FPCOV)
    as HFP_pro.
  pose proof (@pb_check_bounded_x fx rc AE2k.tfib_sink_head PB_fr TfibB [] ARX _ ARX_laws ARX_hp0 TL fr_CBAP IMGC BLKN)
    as CBX.
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HZS TfibB TfibB_syms) as HZS.
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_ROMPIN TfibB TfibB_syms) as ROMPIN.
  assert (HPST : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  assert (HMMAX : APARTIAL < CfParamsReply.fr_MMAX) by (unfold APARTIAL; apply Z.ltb_lt; vm_compute; reflexivity).
  assert (OWNLOW : ARx_owned_low_law segs TfibB ARX).
  { intros ly S Hp W mem md a H Ho.
    exact (ARx_owned_low_law_cf_x (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
      ly S Hp W mem md a (proj1 H) Ho). }
  assert (WFL : ARx_wf_law segs ARX (Wf_cf (cp := CfParams_reply) (as_universe TfibB))).
  { intros ly S Hp W mem md H. exact (ARx_wf_law_cf_x (cp := CfParams_reply) segs TfibB ly S Hp W mem md (proj1 H)). }
  assert (SMALLOC : forall s cid, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> 0 <= cid <= 10 ->
    count_cid cid (frames s) < fs_frames cid ->
    exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
    frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s)).
  { intros s cid HWF Hcid Hcnt.
    destruct (stack_malloc_progress_cf (cp := CfParams_reply) _ s cid HWF Hcid Hcnt) as (pos & s' & Hpath).
    pose proof (stack_malloc_ok_cf (cp := CfParams_reply) _ s cid HWF Hcid) as HTOK.
    destruct (atok_apath _ _ _ [] (PFake cid pos, s') HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post_cf in HQ.
    destruct HQ as (_ & Hf & _ & _ & Hfrs & Hfresh).
    exists pos, s'. split; [exact Hpath|]. split; [exact Hf|]. split; [exact Hfrs | exact Hfresh]. }
  assert (HG_GK : forall a, inG DR_GK a -> inG G a).
  { apply inG_sub. unfold DR_GK.
    repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  assert (BLKR : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n < 2 ^ 30).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)) as Hb. lia. }
  (* the stack_free law over ARX, as fr_contract_top_x's ASF (QMm W1: arodata_ok_cf at mem' from the kept-bytes frame) *)
  assert (ASF : astack_free_law_x segs TfibB ARX).
  { intros ly S Hp W mem md mem' md' cid pos H Hin HF HO HV Hvm Hlz He HK HKEPT. unfold ARX in H |- *.
    destruct H as (HAR & HH & HQ).
    split; [|split; [exact HH | exact (ReplyKeptAroA.arodata_kept_A mem mem' HQ HKEPT)]].
    exact (YG0tcf.astack_free_law_ok_cf (cp := CfParams_reply) segs TfibB ly S Hp W mem md mem' md' cid pos HAR
      Hin HF HO HV Hvm Hlz He HK). }
  assert (SFREE : forall s cid pos, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> In (cid, pos) (frames s) ->
    exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2).
  { intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf (cp := CfParams_reply) _ s cid pos HWF Hin)). }
  assert (BLKM : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    n < 2 ^ 30).
  { intros ly S Hp W mem md p n H Hin. exact (proj2 (BLKR ly S Hp W mem md p n H Hin)). }
  assert (XR_GSHV : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
    (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
    shadow_hull_vis (aview segs (w_H W) mem) a n).
  { intros ly S Hp W mem md a n H Hn Hx. apply (GSHV_x ly S Hp W mem md a n H Hn).
    intros x Hx'. unfold ad_G. cbn [app]. apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact (Hx x Hx'). }
  assert (HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
    ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G a).
  { intros a Ha.
    assert (HK : inG [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8);
        (FF_meta_mem, 8)] a).
    { unfold aenv_addr in Ha. cbn [tfib_K ak_threaded ak_need_locks ak_ofl_lock ak_canary ak_meta_ptr ak_meta_mem] in Ha.
      unfold inG. rewrite Exists_exists.
      destruct Ha as [[-> | [-> | [Ha | Ha]]] | [Ha | Ha]];
        [ exists (A_threaded, 1) | exists (A_need_locks, 1) | exists (A_ofl_lock, 16) | exists (FF_canary, 8)
        | exists (FF_meta_ptr, 8) | exists (FF_meta_mem, 8) ];
        (split; [cbn [In]; repeat (first [left; reflexivity | right]) | unfold in_zr; cbn [fst snd]; lia]). }
    assert (Hd : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 64) &&
        forallb (fun g => (fst r + snd r <=? fst g) || (fst g + snd g <=? fst r)) (G_fr_obj ++ [(TFIB_ERRNO_A, 4)]))
      [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8); (FF_meta_mem, 8)] = true)
      by (vm_compute; reflexivity).
    unfold inG in HK. apply Exists_exists in HK as (r & Hr & Hz). rewrite forallb_forall in Hd. specialize (Hd r Hr).
    apply andb_prop in Hd as [Eb Hd]. apply andb_prop in Eb as [E0 E1]. apply Z.leb_le in E0, E1. unfold in_zr in Hz.
    split; [lia|].
    intros HinG. unfold G_fr_c in HinG. rewrite HEV in HinG. unfold inG in HinG.
    apply Exists_exists in HinG as (g & Hg & Hzg). rewrite forallb_forall in Hd. specialize (Hd g Hg).
    unfold in_zr in Hzg. apply orb_prop in Hd as [Hd | Hd]; apply Z.leb_le in Hd; lia. }
  (* ARM_remove's instance facts (fr_contract_top_x's): relay_remove's two caller contexts, rows of K0's CTX_AFREE;
     the relay's placement; source_reset's G at slot si *)
  assert (HCTX_rr0 : In [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1] CTX_AFREE).
  { assert (E : [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1] = [0x83f98; 0x849e0])
      by (vm_compute; reflexivity).
    rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). }
  assert (HCTX_rr1 : In [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1; RA_LLVMF]
    CTX_AFREE).
  { assert (E : [BASE + AF_fr_relay_remove + 436; BASE + W_LLVMFuzzerTestOneInput_remove.RET_RR1; RA_LLVMF] =
      [0x83f98; 0x849e0; 0x821e8]) by (vm_compute; reflexivity).
    rewrite E. unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). }
  assert (RG5 : forall a, rg_rng fr_RG a -> inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_src fr_RG, 8);
      (rg_wake fr_RG + 4, 4); (rg_s fr_RG, 4 * ASRC)] a).
  { intros a Ha. unfold rg_rng in Ha. unfold inG.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
      repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact (conj (proj1 Ha) (proj2 Ha))
                    | apply Exists_cons_tl]). }
  assert (RGO : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_src fr_RG, 8); (rg_wake fr_RG + 4, 4);
      (rg_s fr_RG, 4 * ASRC)] a -> inG G_fr_obj a).
  { apply inG_sub.
    repeat (apply Forall_cons; [intros a Ha; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  assert (RGP_c : rg_place (PI := PB_fr) TfibB fr_RG).
  { apply (W_rg_place.fr_rg_place TfibB).
    - intros a Ha. pose proof (RGO a (RG5 a Ha)) as Ho.
      exact (conj (c_img TfibB HEV a (obj_c TfibB a Ho))
        (conj (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms a (obj_c TfibB a Ho)) (c_obj_noerr TfibB HEV a Ho))).
    - intros Hh m a Ha _. apply wr_of_seg. apply segwb_ok.
      assert (Hl : inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4)] a).
      { unfold inG. destruct Ha as [Ha|Ha];
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact (conj (proj1 Ha) (proj2 Ha))
                        | apply Exists_cons_tl]). }
      revert Hl. apply rng_all_in. vm_compute. reflexivity.
    - intros a Ha. pose proof (RG5 a Ha) as H5.
      split; [|split; [|split]]; revert H5; apply apart_of_b; vm_compute; reflexivity. }
  assert (HGP_c : forall si, (si < 4)%nat ->
      gx_prog_x (PI := PB_fr) TfibB ARX [(W_LLVMFuzzerTestOneInput_remove.rm_HA si, ASRC)]).
  { intros si Hsi. unfold W_LLVMFuzzerTestOneInput_remove.rm_HA.
    assert (Hsub : forall a, inG [(rg_s fr_RG + ASRC * Z.of_nat si, ASRC)] a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
    { intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr in Ha. cbn [fst snd] in Ha. clear - Ha Hsi. unfold ASRC in *. lia. }
    assert (Hgs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG [(rg_s fr_RG, 4 * ASRC)] a)
      by (intros a Ha; apply inG_cons; left; unfold in_zr; cbn [fst snd]; exact Ha).
    split.
    { intros a Ha. pose proof (c_HGs TfibB a (Hsub a Ha)) as Hg.
      exact (conj (c_img TfibB HEV a Hg) (conj (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms a Hg)
        (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms a Hg))). }
    split; [eapply gx_rt_sub; [|exact (c_HGRT_s TfibB HEV)]; intros a Ha; exact (Hgs a (Hsub a Ha))|].
    split.
    { intros a Ha. destruct (c_rom_noerr TfibB HEV a Ha) as [He Hh]. split; [|exact (conj (ROMPIN a Ha) (conj He Hh))].
      intros HGa. apply (c_rom_apart TfibB HEV a Ha). exact (c_HGs TfibB a (Hsub a HGa)). }
    split.
    { intros a Ha.
      assert (Hf : forallb (rng_all (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end))
        [(rg_s fr_RG, 4 * ASRC)] = true) by (vm_compute; reflexivity).
      pose proof (rng_all_in _ _ a Hf (Hgs a (Hsub a Ha))) as Hx.
      cbv beta in Hx. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate Hx]. }
    split.
    { intros a Ha m.
      assert (Hf : forallb (rng_all (segwb segs)) [(rg_s fr_RG, 4 * ASRC)] = true) by (vm_compute; reflexivity).
      pose proof (segwb_ok segs a (rng_all_in _ _ a Hf (Hgs a (Hsub a Ha)))) as Hw.
      unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact Hw]. }
    intros ly S Hp W mem md a n HAR Hn Hx. apply (XR_GSHV ly S Hp W mem md a n HAR Hn).
    intros x Hxr. exact (Hsub x (Hx x Hxr)). }
  (* ARM_gone's FRMF (fr_contract_top_x's) *)
  assert (FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARX ly S Hp W mem md -> In (cid, pos) (frames S) ->
    ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0).
  { intros ly S Hp W mem md cid pos [[M _] _] Hin.
    destruct (YG0scf.frame_facts_cf (cp := CfParams_reply) _ ly S Hp _ cid pos M Hin)
      as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
    split; [exact Hpg|]. split; [exact Hoff|]. split; [exact H64 | exact Hb]. }
  (* next_line, list_find and check_shape_event at ARX (fr_contract_top_x's: they free nothing, so the twins and walks
     take them strict) *)
  assert (NL_x : nl_spec_x TfibB [] ARX (BASE + AF_fr_next_line))
    by exact (W_next_line.pb_next_line_x (PI := PB_fr) TfibB [] ARX ARX_laws TL W_w1_place.nl_objs_apart_fr
      TopX_RT3.topx_AMEMCHR_W W_w1_place.nl_crom_fr).
  pose proof (W_list_find.pb_list_find_x (PI := PB_fr) TfibB [] ARX ARX_laws ARX_hp0 TL ABCMP) as LFIND_x.
  assert (CSE_x : cse_spec_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_check_shape_event))
    by exact (W_check_shape_event.pb_check_shape_event_x (PI := PB_fr) TfibB [] ARX ARX_laws TL ASTRLEN_x ABCMP NL_x).
  (* the facts the relay / drain / send_line R walks take at their strict texts, as fr_contract_top_x builds them *)
  pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms) as HOWN.
  assert (ASM0 : astack_malloc_pres_x segs TfibB ARX 0) by exact AsmTopX.asm0_pres_ARX.
  assert (AMEMCPYS_x : amemcpy_same_realizes_x TfibB ARX (SIGMA WS_asan_memcpy)) by exact TopX_MEMCPYS.topx_AMEMCPYS_W.
  pose proof (W_ERRL_x.errno_azs TfibB TfibB_syms) as HERRZ.
  assert (HGSL : gx_ok segs TfibB (G_SL TfibB fr_RG)).
  { intros a Ha. pose proof (c_HG_SL TfibB a Ha) as Hg. exact (conj (c_img TfibB HEV a Hg)
      (conj (HOWN a Hg) (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms a Hg))). }
  assert (HROMO_SL : rom_out segs TfibB (G_SL TfibB fr_RG)).
  { apply (W_LLVMFuzzerTestOneInput_pro.pro_rom_out TfibB HEV ROMPIN).
    intros a Hr Hg. exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg)). }
  assert (HE5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom segs a).
  { intros a Ha. eapply W_LLVMFuzzerTestOneInput_exit.xe_romseg_ok; [| exact Ha]. vm_compute. reflexivity. }
  assert (HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img segs a).
  { intros a Ha. apply segin_ok. apply (rng_all_in (segin segs) [(VAL A_lit_end5, 5)]); [vm_compute; reflexivity|].
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Ha. }
  assert (HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
    ~ inG (G_SL TfibB fr_RG) a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { intros a Ha. pose proof (HE5R a Ha) as Hr. split; [intros Hg; exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg))|].
    split; [|exact (c_ROM_ERR TfibB HEV a Hr)].
    rewrite (@ts_owned TfibB TfibB_syms). intros Hex.
    exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (VAL A_lit_end5) 5 Tfib_owned_static ltac:(vm_compute; reflexivity) a Hex
      ltac:(unfold in_zr; cbn [fst snd]; exact Ha)). }
  assert (HGRF : gx_ok segs TfibB (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG)).
  { intros a Ha. unfold inG in Ha. apply Exists_app in Ha as [Ha | Ha];
      [pose proof (c_HG_RF TfibB a Ha) as Hg | pose proof (c_HG_SL TfibB a Ha) as Hg];
      exact (conj (c_img TfibB HEV a Hg) (conj (HOWN a Hg) (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms a Hg))). }
  (* ---- the R callee specs, from the R walks ---- *)
  (* __asan_memset at R: the strict intrinsic contract (it frees nothing), lifted by WLE_R *)
  assert (AMEMSET_R : aintrin_realizes_xR segs TfibB ARX R OSet (SIGMA WS_asan_memset))
    by exact (aintrin_realizes_xR_of_x segs TfibB ARX WLE_R OSet (SIGMA WS_asan_memset) AMEMSET_x).
  (* list_free at R (W_list_free.v:2744 pb_list_free_g_xR): the free rules at R at K0's CTX_AFREE, memmove strict, its
     two free contexts rows of CTX_AFREE (decided, as fr_contract_top_x's source_reset rows) *)
  assert (LF_R : W_contract_srlf_xR.lf_spec_g_xR TfibB [] ARX R MT RPi (BASE + AF_fr_list_free)).
  { refine (W_list_free.pb_list_free_g_xR (PI := PB_fr) TfibB [] ARX MT RPi ARX_laws ARX_hp0 IMGC BLKN
      (fun a _ H => ltac:(inversion H)) MLAW CTX_AFREE _ _ TL AMOVE R R_refl R_trans WLE_R RO RO_ARx AFREE_R AFREE0_R).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). }
  (* source_reset at R (W_source_reset.v:2574 pb_source_reset_gc_xR): list_free at R, the free rules at R, memset at R,
     its free context a row of CTX_AFREE *)
  assert (SR_R : W_contract_srlf_xR.sr_spec_g_xR TfibB [] ARX R MT RPi (BASE + AF_fr_source_reset)).
  { refine (W_source_reset.pb_source_reset_gc_xR (PI := PB_fr) TfibB [] ARX R R_refl R_trans WLE_R ARX_laws BLKN HPST TL
      MT RPi MLAW RO RO_ARx LF_R CTX_AFREE AFREE_R AFREE0_R AMEMSET_R _).
    unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). }
  (* relay_add at R (W_relay_add.v:685 pb_relay_add_xR), at ra_spec_g_xR's G as RA_x (no _g form exists): RA_x's
     arguments without the strict realloc rule, then realloc at R (ARE_R) with its hull admission (HA_call; the walk's
     HA_ra also has 1 <= n, unused) *)
  assert (RA_R : W_contract_srlf_xR.ra_spec_g_xR TfibB [] ARX R MT RPi fr_globals CTX_AREALLOC (BASE + AF_fr_relay_add)).
  { intros Gc HGc _.
    refine (W_relay_add.pb_relay_add_xR (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX Gc fr_globals ARX_laws
      ARX_hp0 TL TLF (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE SMALLOC OWNLOW IMGC BLKN ASM0 ASF FFL
      MLAW MO_FR (rp_RPF RPi) (rp_RMM RPi) HGc _ ALOCK AUNLOCK CTX_AREALLOC _ AMEMSET_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
      R R_refl R_trans WLE_R RO RO_ARx HA (fun lyc Sc regsT ch p n _ H => HA_call lyc Sc regsT ch p n H) ARE_R).
    - (* GW: RA_G's cells lie in a writable segment *)
      intros Hh m a Ha _. apply wr_of_seg. apply segwb_ok.
      eapply (rng_all_in (segwb segs)); [| exact Ha]. vm_compute. reflexivity.
    - (* HMMAX *) apply Z.ltb_lt. vm_compute. reflexivity.
    - (* HV6 *) vm_compute. reflexivity.
    - (* HLA *) vm_compute. reflexivity.
    - (* HV7 *) vm_compute. reflexivity.
    - (* HV16 *) vm_compute. reflexivity.
    - (* HV8 *) vm_compute. reflexivity.
    - (* HV4 *) vm_compute. reflexivity.
    - (* HH30 *) vm_compute. reflexivity.
    - (* HH31 *) vm_compute. reflexivity.
    - (* HH32 *) vm_compute. reflexivity.
    - (* HIG *) c1_forall.
    - (* HEO *) intros i Hi Hex. rewrite (@ts_owned TfibB TfibB_syms), (@ts_errno TfibB TfibB_syms) in Hex.
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok TFIB_ERRNO 4 Tfib_owned_static ltac:(vm_compute; reflexivity) _ Hex
        ltac:(lia)).
    - (* HWKI *) intros i Hi. apply segin_ok.
      apply (rng_all_in (segin segs) [(rg_wake fr_globals + 4, 4)]); [vm_compute; reflexivity|].
      apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
    - (* HWKO *) intros i Hi Hex. rewrite (@ts_owned TfibB TfibB_syms) in Hex.
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (rg_wake fr_globals + 4) 4 Tfib_owned_static
        ltac:(vm_compute; reflexivity) _ Hex ltac:(lia)).
    - (* HSEPG *) c1_seps. }
  (* op_add at R (W_op_add.v:2981 pb_op_add_g_xR): malloc at R, source_reset at R, relay_add at R (RA_R); its image
     facts and caller contexts as fr_contract_top_x's OA *)
  assert (OA_R : W_op_add.oa_spec_g_xR (PI := PB_fr) TfibB [] ARX R MT RPi (BASE + AF_fr_op_add)).
  { refine (pb_op_add_g_xR TfibB [] ARX R R_refl R_trans WLE_R _ MT RPi RO RO_ARx ARX_laws HPST TL MLAW
      (rp_RMM RPi) CfParamsReply.fr_MMAX HMMAX _ _ _ _ _ CTX_AMALLOC _ AMA_R SR_R CTX_AREALLOC _ RA_R).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. repeat split; first [left; discriminate | right; discriminate |
        left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H].
    - intros a Ha. split; [|split].
      + apply segin_ok. apply (rng_all_in (segin segs) [(rg_wake fr_globals + 4, 4)]); [vm_compute; reflexivity|].
        apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + rewrite (@ts_owned TfibB TfibB_syms). intros Hex.
        exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (rg_wake fr_globals + 4) 4 Tfib_owned_static
          ltac:(vm_compute; reflexivity) a Hex ltac:(lia)).
      + rewrite (@ts_errno TfibB TfibB_syms). cbn [fr_globals rg_wake] in Ha. unfold TFIB_ERRNO. lia.
    - assert (E : [BASE + AF_fr_op_add + 0xcc] = [0x84fdc]) by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AMALLOC. vm_compute. repeat (first [left; reflexivity | right]).
    - assert (E : [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] = [0x82a9c; 0x85018])
        by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]). }
  (* list_push at R (W_list_push.v:1629 pb_list_push_g_xR) at WR_MMAX = fr_MMAX: realloc and malloc at R, memcpy
     strict, realloc's hull admission HA_call; caller contexts as fr_contract_top_x's LP *)
  assert (LP_R : W_contract_xR.lp_spec_g_xR (PI := PB_fr) TfibB [] ARX R MT RPi WR_MMAX (BASE + AF_fr_list_push)).
  { refine (W_list_push.pb_list_push_g_xR (PI := PB_fr) TfibB [] ARX ARX_laws ARX_hp0 TL MT RPi MLAW WR_MMAX wr_HMMAX
      IMGC BLKN CTX_AREALLOC _ CTX_AMALLOC AMEMCPY_x _ R R_refl R_trans WLE_R RO RO_ARx HA HA_call ARE_R AMA_R).
    - assert (E : [BASE + AF_fr_list_push + 0xac] = [0x8513c]) by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]).
    - assert (E : [BASE + AF_fr_list_push + 0xd0] = [0x85160]) by (vm_compute; reflexivity).
      rewrite E. unfold CTX_AMALLOC. vm_compute. repeat (first [left; reflexivity | right]). }
  (* list_drop at R at every G with gx_ok / gx_rt / rom_out (W_list_drop_top.v:923 pb_list_drop_ro_cx_xR), the free
     rule at R at K0's CTX_AFREE, memmove strict *)
  pose proof (W_list_drop_top.pb_list_drop_ro_cx_xR (PI := PB_fr) TfibB [] ARX ARX_laws ARX_hp0 MT RPi CTX_AFREE
    W_w3_place_fr.list_drop_HCTX_fr TL AMOVE R R_refl R_trans WLE_R RO RO_ARx AFREE_R) as LDROP_RO_R.
  (* gesture_model at R: W_gesture_model_g.v:109 pb_gesture_model_g_xR at list_push and list_drop at R (LP_R,
     LDROP_RO_R), bcmp and list_find strict, the literals' shadow facts by W_shadow_pin_x *)
  assert (GM_R : W_contract_xR_g6.gm_spec_g_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX
    (BASE + AF_fr_gesture_model))
    by exact (W_gesture_model_g.pb_gesture_model_g_xR (PI := PB_fr) TfibB MT RPi CfParamsReply.fr_MMAX [] ARX ARX_laws
      ARX_hp0 TL MLAW ABCMP (W_shadow_pin_x.ashp_gesture_13_fr_x TfibB TfibB_syms ARX ARX_laws)
      (W_shadow_pin_x.ashp_begin_5_fr_x TfibB TfibB_syms ARX ARX_laws)
      (W_shadow_pin_x.ashp_end_3_fr_x TfibB TfibB_syms ARX ARX_laws) (fun Gc _ _ => LFIND_x Gc)
      R R_refl R_trans WLE_R LP_R LDROP_RO_R).
  (* check_no_loss at R at every G with gx_ok / gx_rt (W_check_no_loss.v:6031 pb_check_no_loss_xR): the free rule and
     gesture_model at R; next_line, bcmp and memmove strict; placement and free context as fr_contract_top_x's CNL_x *)
  assert (CNL_R : forall Gc, gx_ok segs TfibB Gc -> gx_rt TfibB Gc ->
    W_contract_xR_g6.cnl_spec_xR TfibB [] ARX R MT RPi Gc CfParamsReply.fr_MMAX (BASE + AF_fr_check_no_loss)).
  { intros Gc HGc _.
    exact (W_check_no_loss.pb_check_no_loss_xR (PI := PB_fr) TfibB [] ARX MT RPi Gc CfParamsReply.fr_MMAX ARX_laws
      ARX_hp0 IMGC BLKN HPST TL HGc W_w3_place_fr.check_no_loss_CNLAP_fr MLAW W_w3_place_fr.check_no_loss_HGR_fr
      W_w3_place_fr.check_no_loss_HGRR_fr W_w3_place_fr.check_no_loss_ROMNS_fr W_rom_place_fr.ofl_head_rom_fr NL_x ABCMP
      AMOVE CTX_AFREE W_w3_place_fr.check_no_loss_HCTX_cnl_free_fr (W_list_drop.alist_at_drop (PI := PB_fr) TfibB)
      R R_refl R_trans WLE_R RO RO_ARx AFREE_R GM_R). }
  (* check_shape_done at R (W_check_shape_done.v:194 pb_check_shape_done_xR): the strict walk lifted by WLE_R *)
  assert (CSD_R : W_contract_srlf_xR.csd_spec_xR TfibB [] ARX R (BASE + AF_fr_check_shape_done))
    by exact (W_check_shape_done.pb_check_shape_done_xR (PI := PB_fr) TfibB [] ARX ARX_laws TL R WLE_R).
  (* send_line at R (W_send_line_x.v:127 pb_send_line_xR): SL_x's arguments without the strict realloc rule, then
     realloc at R (ARE_R) with RO / HA *)
  assert (SL_R : W_send_line_xR.sl_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_send_line)).
  { exact (W_send_line_x.pb_send_line_xR (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG ARX_laws ARX_hp0
      BLKM HGSL W_send_line_x_top.slx_HGR HROMO_SL W_send_line_x_top.slx_HGO MLAW TL TopX_RT4.topx_AERRNO_W AMEMCPY_x
      CTX_AREALLOC W_send_line_x_top.slx_HCTX_slr W_send_line_x_top.slx_HERRNO HERRZ
      W_send_line_x_top.slx_HV9 W_send_line_x_top.slx_HV10 W_send_line_x_top.slx_HV11 W_send_line_x_top.slx_HV12
      W_send_line_x_top.slx_HV13 W_send_line_x_top.slx_HV14 W_send_line_x_top.slx_HV15 W_send_line_x_top.slx_HH17
      W_send_line_x_top.slx_HH19 W_send_line_x_top.slx_HH21 W_send_line_x_top.slx_HSM W_send_line_x_top.slx_HH22
      W_send_line_x_top.slx_HH23 W_send_line_x_top.slx_HH24 W_send_line_x_top.slx_HRGD
      R R_refl R_trans WLE_R RO HA RO_ARx HA_call ARE_R). }
  (* gesture_end at R (W_gesture_end.v:363 pb_gesture_end_xR): GE_x's arguments without SL_x, then send_line at R *)
  assert (GE_R : W_contract_xR.ge_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_gesture_end)).
  { refine (W_gesture_end.pb_gesture_end_xR (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG ARX_laws
      ARX_hp0 BLKN HGSL ASTRLEN_x HEND5I (W_shadow_pin_x.ashp_end5_5_fr_x TfibB TfibB_syms ARX ARX_laws)
      (fun a _ H => ltac:(inversion H)) (fun a _ H => ltac:(inversion H)) MLAW _ HEND5G HROMO_SL R R_refl R_trans WLE_R
      SL_R).
    intros r Hr. unfold aout_fp in Hr. rewrite HEV in Hr. vm_compute in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbn [fst snd]; lia |]). destruct Hr. }
  (* gestures_end at R (W_gestures_end_top.v:116 pb_gestures_end_closed_xR): GSE_x's arguments without GE_x and the
     strict free rules, then gesture_end and the free rules at R *)
  assert (GSE_R : W_contract_xR.gse_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG
    (BASE + AF_fr_gestures_end)).
  { refine (W_gestures_end_top.pb_gestures_end_closed_xR (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG
      ARX_laws ARX_hp0 TL HGSL MLAW CTX_AFREE _ _ HROMO_SL _ HEND5I HEND5G
      (fun a _ H => ltac:(inversion H)) (fun a _ H => ltac:(inversion H)) IMGC BLKN R R_refl R_trans WLE_R GE_R RO RO_ARx
      AFREE_R AFREE0_R).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
    - unfold CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]).
    - (* HOUTG: the stream's cells other than errno are G_fr_c's (_G.v), so image, not read-only, not owned *)
      intros r a Hr Ha Hne. cbn [In aout_fp Z.eqb] in Hr.
      assert (HGa : inG G a).
      { destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]; cbn [fst snd] in Ha.
        + exact (c_HG_smax TfibB a Ha).
        + apply (c_HG_SL TfibB). unfold G_SL, inG.
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
        + apply (c_HG_SL TfibB). unfold G_SL, inG.
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
        + apply (c_HG_SL TfibB). unfold G_SL, inG.
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
        + exact (c_HG_client TfibB a Ha).
        + exact (c_HG_cbroken TfibB a Ha).
        + exact (c_HG_sdead TfibB a Ha).
        + exact (c_HG_seintr TfibB a Ha).
        + exfalso. exact (Hne Ha). }
      split; [exact (c_img TfibB HEV a HGa)|].
      split; [intros Hr'; exact (c_rom_apart TfibB HEV a Hr' HGa) | exact (HOWN a HGa)]. }
  (* relay_event at R (W_relay_event.v:250 pb_relay_event_xR), at _event's own G et_GRE: RE_x's arguments without
     SL_x, then send_line at R *)
  assert (RE_R : W_contract_xR.re_spec_xR (PI := PB_fr) TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX (et_GRE TfibB) fr_RG
    (BASE + AF_fr_relay_event)).
  { refine (W_relay_event.pb_relay_event_xR (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX (et_GRE TfibB) fr_RG
      ARX_laws ARX_hp0 BLKR (c_gx_ok_GRE TfibB HEV HOWN (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms))
      ALOCK AUNLOCK ASTRLEN_x _ _ _ _ _ _ _ R R_refl R_trans WLE_R SL_R).
    - (* HV6 *) vm_compute. reflexivity.
    - (* HLA *) vm_compute. reflexivity.
    - (* HLD: the lock is apart from send_line's G *) intros a Ha Hg.
      exact (W_LLVMFuzzerTestOneInput_add.ad_apart_ok (rg_lock fr_RG) 12 (G_SL TfibB fr_RG)
        ltac:(vm_compute; reflexivity) a Hg Ha).
    - (* HLRW *) intros a Ha Hr. exact (c_rom_apart TfibB HEV a Hr (c_HGlock TfibB a Ha)).
    - (* HAOD *) intros a Ha. cbn [fr_RG fr_globals rg_lock rg_send_max rg_client rg_send_dead] in *. lia.
    - (* HAO3 *) cbn [fr_RG fr_globals rg_send_max rg_client rg_send_dead]. lia.
    - (* HLPST *) intros a _ H. inversion H. }
  (* relay_finish at R (W_relay_finish_h.v:6560 pb_relay_finish_h_xR), at SEG_EXIT's G: RF_x's arguments without the
     strict free rules and GSE_x, then the free rules and gestures_end at R *)
  assert (RF_R : W_contract_xR.rf_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX
    (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG) fr_RG AG_THREAD_UP AG_LISTEN CTX_AFREE (BASE + AF_fr_relay_finish)).
  { refine (W_relay_finish_h.pb_relay_finish_h_xR (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX
      (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG) fr_RG AG_THREAD_UP AG_LISTEN CTX_AFREE ARX_laws ARX_hp0 TL TLF MLAW
      IMGC BLKN OWNLOW (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE SMALLOC ASM0 ASF FFL HGRF ALOCK
      AUNLOCK MO_FR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R_refl R_trans WLE_R RO RO_ARx AFREE_R AFREE0_R GSE_R).
    - (* HV3 *) vm_compute. reflexivity.
    - (* HV6 *) vm_compute. reflexivity.
    - (* HV7 *) vm_compute. reflexivity.
    - (* HV8 *) vm_compute. reflexivity.
    - (* HH9 *) vm_compute. reflexivity.
    - (* HH11 *) vm_compute. reflexivity.
    - (* HH12 *) vm_compute. reflexivity.
    - (* HIG *) c1_forall.
    - (* HSEPG *) c1_seps.
    - (* HPLAIN *) intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). vm_compute in Hr.
      do 7 (destruct Hr as [<- | Hr]; [c1_plain Hz |]). destruct Hr.
    - (* HWSEG *) intros a Ha. apply segwb_ok. eapply (rng_all_in (segwb segs)); [| exact Ha]. vm_compute. reflexivity.
    - (* RGAL *) vm_compute. reflexivity.
    - (* HIGO *) c1_forall.
    - (* HSEPO *) c1_seps.
    - (* HPLAINO *) intros a [Ha | Ha];
        [change (in_zr a (rg_send_max fr_RG, 8)) in Ha | change (in_zr a (rg_send_dead fr_RG, 1)) in Ha]; c1_plain Ha.
    - (* HROMG *) intros a Ha Hr. apply (c_rom_apart TfibB HEV a Hr).
      destruct Ha as [Ha | [Ha | [Ha | Ha]]];
        [exact (c_HG_RF TfibB a Ha) | exact (c_HG_SL TfibB a Ha) | exact (c_HG_smax TfibB a Ha)
        | exact (c_HG_sdead TfibB a Ha)].
    - (* HE5R *) intros a Ha. change (Z.of_nat (length END5)) with 5 in Ha.
      eapply W_LLVMFuzzerTestOneInput_exit.xe_romseg_ok; [| exact Ha]. vm_compute. reflexivity.
    - (* HROMO *) apply (W_LLVMFuzzerTestOneInput_pro.pro_rom_out TfibB HEV ROMPIN).
      intros a Hr Hg. exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg)).
    - (* HWSEGE *) intros a Ha. apply segwb_ok. rewrite (@ts_errno TfibB TfibB_syms) in Ha.
      apply (rng_all_in (segwb segs) [(TFIB_ERRNO, 4)]); [vm_compute; reflexivity|].
      apply inG_cons. left. exact Ha.
    - (* PSTR *) intros a _ H. inversion H.
    - (* PSTC *) intros a _ H. inversion H.
    - (* PSTO *) intros a _ H. inversion H. }
  (* strndup's rule at R: Section topx's strict ASTRNDUP_x (strndup frees nothing) lifted by CfRBridgeRulesRh.v:174
     astrndup_cf_rule_c_xR_lift over ARX's laws and the image's low bound (W_kit.v pa_segs_low) *)
  assert (ASTRNDUP_R : astrndup_cf_rule_c_xR segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi ACej.CTX_strndup R
    (SIGMA WS_strndup))
    by exact (CfRBridgeRulesRh.astrndup_cf_rule_c_xR_lift segs TfibB [] ARX ARX_laws
      (@pa_segs_low _ fr_prog_listing PB_fr) R WLE_R R_trans MT CfParamsReply.fr_MMAX RPi ACej.CTX_strndup _ ASTRNDUP_x).
  (* drain at R (W_drain_pb.v:239 pb_drain_xR): DR_x's facts, then realloc / free / strndup at R (ARE_R, AFREE_R,
     ASTRNDUP_R) and send_line / list_push at R (SL_R; LP_R at WR_MMAX = fr_MMAX) *)
  assert (DR_R : W_contract_xR.dr_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_drain)).
  { pose proof ARX_laws. pose proof ARX_hp0. pose proof (palib_tfib TfibB TfibB_syms).
    pose proof TopX_INTRIN.topx_AMEMCPY_x_W. pose proof TopX_RT3.topx_AMEMMOVE_W. pose proof TopX_RT3.topx_AMEMCHR_W.
    pose proof topx_ASTRLEN_x_W. pose proof TopX_RT4.topx_AERRNO_W. pose proof TopX_RT4.topx_ASTRRCHR_W.
    pose proof TopX_RT4.topx_ASTRNCMP_W. pose proof TopX_RT4.topx_ASTRCMP_W.
    pose proof (LP_R : W_contract_xR.lp_spec_g_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX (BASE + AF_fr_list_push)).
    pose proof (fun S k k' H => rp_RMM RPi S k' k H). pose proof CfParamsReply.reply_HMMAX.
    pose proof (dlit_at_x_of_rt _ _ TopxDrainLit.topx_HLIT5_x). pose proof (dlit_at_x_of_rt _ _ TopxDrainLit.topx_HLIT6_x).
    pose proof (dlit_at_x_of_rt _ _ TopxDrainLit.topx_HLIT7_x).
    pose proof W_drain_pb.drain_hctx_re1. pose proof W_drain_pb.drain_hctx_re2.
    pose proof W_drain_pb.drain_hctx_fr1. pose proof W_drain_pb.drain_hctx_fr2. pose proof W_drain_pb.drain_hctx_sd.
    pose proof W_drain_pb.drain_HCROM. pose proof W_drain_pb.drain_HVS.
    pose proof W_drain_pb.drain_HV9. pose proof W_drain_pb.drain_HV12.
    pose proof W_drain_pb.drain_HGSB. pose proof W_drain_pb.drain_HSM.
    pose proof W_drain_pb.drain_HRGD. pose proof W_drain_pb.drain_HERRW.
    pose proof W_drain_pb.drain_HG. pose proof W_drain_pb.drain_HGO.
    pose proof W_drain_pb.drain_HGR. pose proof W_drain_pb.drain_HROMO.
    pose proof W_drain_pb.drain_HERRNO. pose proof W_drain_pb.drain_HGSZ.
    pose proof W_drain_pb.drain_PSTR. pose proof W_drain_pb.drain_PSTG. pose proof W_drain_pb.drain_PSTO.
    eapply W_drain_pb.pb_drain_xR; eassumption. }
  (* relay_remove at R (W_relay_remove.v:184 pb_relay_remove_xR): RR_x's facts, then gestures_end at R, R_IMG, the
     free rules at R and drain at R *)
  assert (RR_R : W_contract_xR_relay.rr_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG CTX_AFREE
    (BASE + AF_fr_relay_remove)).
  { pose proof ARX_laws. pose proof ARX_hp0.
    pose proof TopxRelayFacts.topx_rr_HG. pose proof TopxRelayFacts.topx_rr_HROMO.
    pose proof TopxRelayFacts.topx_HH59. pose proof TopxRelayFacts.topx_HH60. pose proof TopxRelayFacts.topx_HV4.
    pose proof TopxRelayFacts.topx_HRGP. pose proof TopxRelayFacts.topx_HRGI. pose proof TopxRelayFacts.topx_HEND5L.
    eapply (W_relay_remove.pb_relay_remove_xR (PI := PB_fr)); try eassumption;
      let h := fresh "Hpst" in intros ? _ h; inversion h. }
  (* relay_instance_gone at R (W_relay_instance_gone.v:167 pb_relay_instance_gone_xR): RIG_x's facts, then the free
     rule, drain and gesture_end at R *)
  assert (RIG_R : W_contract_xR_relay.rig_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG CTX_AFREE
    (BASE + AF_fr_relay_instance_gone)).
  { pose proof ARX_laws. pose proof ARX_hp0. pose proof TopX_RT4.topx_ASTRNCMP_W.
    pose proof (W_drain_cx_x.alloc_tail_x segs TfibB ARX ARX_laws) as ALLOC_TAIL.
    pose proof TopxRelayFacts.topx_rig_HGRIG. pose proof TopxRelayFacts.topx_rig_HROMO.
    pose proof TopxRelayFacts.topx_HH44. pose proof TopxRelayFacts.topx_HH45.
    pose proof TopxRelayFacts.topx_HRGP. pose proof TopxRelayFacts.topx_HRGI. pose proof TopxRelayFacts.topx_HEND5L.
    pose proof TopxRelayFacts.topx_HCANR. pose proof (glit_at_x_of_rt _ _ TopxRelayFacts.topx_HLIT20_x).
    pose proof (glit_at_x_of_rt _ _ TopxRelayFacts.topx_HLIT21_x).
    pose proof (glit_at_x_of_rt _ _ TopxRelayFacts.topx_HLIT31_x).
    pose proof SnpNarrowSites.HLITGOT_PB_fr.
    eapply (W_relay_instance_gone.pb_relay_instance_gone_xR (PI := PB_fr)); try eassumption;
      let h := fresh "Hpst" in intros ? _ h; inversion h. }
  (* check_shape_ends at R at every G with gx_ok (W_cshe_top.v:417 pb_check_shape_ends_xR): CSHE_x's placement facts,
     and its loops 2 and 3 at R (L2R / L3R) by a Theorem Labs lane's W_cshe_l2w.v:4424 cshe_l2_run_xR and W_cshe_l3.v:5350
     cshe_l3_top_xR over the free rule at R at K0's CTX_AFREE *)
  assert (CSHE_R : forall Gc, gx_ok segs TfibB Gc ->
    W_contract_xR_g6.cshe_spec_xR TfibB [] ARX R MT RPi Gc (BASE + AF_fr_check_shape_ends)).
  { intros Gc HGc.
    pose proof ARX_laws as LAWS. pose proof ARX_hp0 as HP0. pose proof (LFIND_x Gc) as LFIND.
    pose proof (W_list_drop.alist_at_drop (PI := PB_fr) TfibB) as ALDROP.
    pose proof W_w3_place_fr.check_shape_ends_HCTX_cshe_l2_fr as HCTX2.
    pose proof W_w3_place_fr.check_shape_ends_HCTX_cshe_l3_fr as HCTX3.
    pose proof W_w3_place_fr.check_shape_ends_PLACEG0_fr as PLACEG0.
    pose proof W_w3_place_fr.check_shape_ends_PLACEG32_fr as PLACEG32.
    pose proof W_w3_place_fr.check_shape_ends_HGR_fr as HGR. pose proof W_w3_place_fr.check_shape_ends_HGRR_fr as HGRR.
    pose proof W_w3_place_fr.check_shape_ends_ROMNS_fr as ROMNS.
    pose proof W_w3_place_fr.check_shape_ends_HEND5R_fr as HEND5R.
    pose proof (ashp_x_of_rt _ _ W_w3_place_fr.check_shape_ends_HEND5S_fr) as HEND5S.
    pose proof W_w3_place_fr.check_shape_ends_HGS_fr as HGS.
    refine (W_cshe_top.pb_check_shape_ends_xR (PI := PB_fr) TfibB [] ARX MT RPi Gc ARX_laws ARX_hp0 IMGC BLKN MLAW HGc TL
      ASTRLEN_x ABCMP PLACEG0 PLACEG32 HGR HGRR HGS R R_trans WLE_R _ _).
    - (* L2R (PF named: else eassumption takes it from the first `0 < _` hypothesis, 0 < hl_n (hs_held h)) *)
      intros. eapply (W_cshe_l2w.cshe_l2_run_xR (PI := PB_fr)) with (PF := PF); eassumption.
    - (* L3R *) intros. eapply (W_cshe_l3.cshe_l3_top_xR (PI := PB_fr)); eassumption. }
  refine (lf_contract_of_segments_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP []
    ARX ARX_laws GX_ok LSx RINV R R_refl R_trans WLE_R _ _ _ _ _ _ _ _ _
    _ _ _ _ _).
  - exact (lf_seg_pro_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP NPF MO_FR TL TLF OWNLOW (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL
      SMALLOC ASM1 FFL (c_glob_wr TfibB HEV) ERRL_x HEV HZS (W_LLVMFuzzerTestOneInput_addI.zz_HGOBJ TfibB)
      (c_rom_apart TfibB HEV) ROMPIN GSHV_x HFP_pro LS_pro_oa RI_pro LS_pro LS_cnt_pro BLKN HPST R R_refl R_trans WLE_R OA_R).
  - exact (lf_seg_head_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok
      LSx RINV (c_HGnout TfibB) (c_HERRNO TfibB HEV) RI_head_nout LS_head_nout HZS RI_head_skip LS_head_skip
      R R_refl R_trans WLE_R).
  - exact (lf_arm_add_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws GX_ok LSx RINV RPi RP_NP HEV HZS (W_LLVMFuzzerTestOneInput_addI.zz_HGOBJ TfibB) ERRL_x ROMPIN GSHV_x HPST
      BLKN RI_add_pre RI_add_open RI_add_none LS_add_room LS_add_open LS_add_none LS_cnt_add R R_refl R_trans WLE_R OA_R).
  - exact (lf_arm_write_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP TL (c_glob_wr TfibB HEV) ERRL_x (c_HGs TfibB) HZS (c_HGW TfibB)
      (c_HERRS TfibB HEV) (c_ROM_ERR TfibB HEV) ROMPIN BLKN (fun a _ H => ltac:(inversion H)) (fun a _ H => ltac:(inversion H))
      RI_write_skip LS_write_skip RI_write_push LS_write_room LS_write_push LS_cnt_write R R_refl R_trans WLE_R LP_R).
  - exact (lf_arm_drain_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX TL RPi RP_NP ALOCK AUNLOCK CSD_x CNLR_x
      (c_HGs TfibB) (c_HG_DR TfibB) (c_HGlock TfibB) HG_GK (c_HERRHI TfibB HEV) ERRL_x (c_rom_out TfibB TfibB_syms HEV)
      (c_glob_wr TfibB HEV) HZS c_HAP HPST BLKR RI_drain_skip RI_drain_step DR_CNT_grow RI_src RI_fds RI_pair
      RI_event_live LS_drain_pre LS_cnl_pre LS_drain_skip LS_drain_step
      (fun h P => ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P) DR_CNT_cnl LS_cnt_drain
      R R_refl R_trans WLE_R DR_R CNL_R).
  - exact (lf_arm_close_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV
      (c_HGs TfibB) (W_LLVMFuzzerTestOneInput_addI.zz_HZS TfibB TfibB_syms) TL (c_HERRHI TfibB HEV) RI_close LS_close
      R R_refl R_trans WLE_R).
  - exact (W_LLVMFuzzerTestOneInput_remove_x.lf_arm_remove_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post
      fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP CfParamsReply.fr_MMAX TL MLAW CTX_AFREE
      HCTX_rr0 HCTX_rr1 RGP_c (c_HGs TfibB) (c_HGlock TfibB) (c_HGnsrc TfibB) (c_HG_DR TfibB) HZS c_HAP
      (c_HGRT_s TfibB HEV) (c_rom_out TfibB TfibB_syms HEV)
      (c_HMG TfibB HEV (fun a Ha => W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms a (obj_c TfibB a (c_mglob_obj a Ha))))
      RI_rm_found RI_fds RI_rm_rr_pair RI_rm_src LS_rm_rr_pre RI_rm_cnl_pre LS_rm_cnl_pre RI_rm_cnlr_eof RI_rm_cshe_pre
      LS_rm_cshe_pre RI_rm_csd LS_rm_sr_pre RI_rm_step LS_rm_step LS_cnt_remove RM_CNT_cnl RM_CNT_cshe RM_CNT_sr
      CSD_x CNLR_x HGP_c ERRL_x
      (ashp_x_of_rt _ _ W_shadow_pin_x.ashp_str2_1_fr_cf) BLKR (fun a _ H => ltac:(inversion H))
      (fun a _ _ H => ltac:(inversion H))
      R R_refl R_trans WLE_R RR_R CNL_R CSHE_R SR_R).
  - exact (W_LLVMFuzzerTestOneInput_gone_x.lf_arm_gone_xR TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV (c_ERRNO_LOW TfibB HEV) TL HZS RI_gone_read SNP_x HGOTG_x GN_LITS_x
      CfParamsReply.fr_MMAX RPi RGP_c (c_HG_RIG TfibB) RI_gone_pairs RI_fds LS_gone_rig ReplyLScnt.pk_gone RP_NP
      CNT_gone_rig LS_cnt_gone (c_HGcells TfibB) (c_glob_wr TfibB HEV) ROMPIN (c_CELLS_ERRNO TfibB HEV)
      (c_ROM_ERR TfibB HEV) (c_HGs TfibB) RI_gone_step RI_gone_end CNT_gone_step
      MLAW CNLR_x CSD_x BLKN HPST FRMF R R_refl R_trans WLE_R RIG_R CNL_R (fun Gc Hok _ => CSHE_R Gc Hok)).
  - exact (lf_arm_eintr_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV
      (c_HGs TfibB) (W_LLVMFuzzerTestOneInput_addI.zz_HZS TfibB TfibB_syms) TL (c_HERRHI TfibB HEV) RI_eintr LS_eintr
      R R_refl R_trans WLE_R).
  - exact (lf_arm_event_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX RPi RP_NP TL (c_glob_wr TfibB HEV) ERRL_x
      (c_rom_out TfibB TfibB_syms HEV) (c_HGlock TfibB) (c_HG_SL TfibB) (c_HG_carry TfibB) (c_HERR_AP TfibB HEV)
      AMEMCPY_x ASTRNLEN_x CSE_x BLKN HPST RI_event_live RI_event_step LS_event_malloc LS_event_relay
      LS_event_free LS_event_step LS_cnt_event R R_refl R_trans WLE_R RO RO_ARx AMA_R AFREE_R RE_R).
  - exact (lf_arm_sendmax_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok
      LSx RINV (c_HG_smax TfibB) (c_HG_seintr TfibB) TL (c_HERRHI TfibB HEV) RI_sendmax LS_sendmax R R_refl R_trans WLE_R).
  - exact (lf_arm_default_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok
      LSx RINV (c_HG_sdead TfibB) (c_HG_gone TfibB) (c_HG_client TfibB) (c_HGlock TfibB) TL (c_HERRHI TfibB HEV)
      ALOCK AUNLOCK RI_default LS_default R R_refl R_trans WLE_R).
  - exact (lf_seg_latch_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX
      ARX_laws GX_ok LSx RINV CBX (c_ERRNO_LOW TfibB HEV) R R_refl R_trans WLE_R).
  - exact (W_LLVMFuzzerTestOneInput_exit_x.lf_seg_exit_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
      LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV TL MLAW ASF FFL ERRL_x
      (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE CfParamsReply.fr_MMAX (c_HG_SL TfibB) HZS RPi RP_NP
      (c_XRF_ERRNO TfibB HEV) (c_rom_out TfibB TfibB_syms HEV) LS_rf_room LS_exit_budget
      (W_LLVMFuzzerTestOneInput_Gx.c_XR_HGM TfibB) XR_GSHV (c_glob_wr TfibB HEV) XE_LIT_S_x RI_exit_slots RI_exit_ends
      LS_exit_cnt LS_exit_cap LS_cnt_exit FP_SINK (AD1u.tfib_AIL TfibB TfibB_syms) HG_K HPST BLKN BLKM
      R R_refl R_trans WLE_R CSD_R SR_R CSHE_R RF_R LS_exit_end_R).
Qed.
(* ---- fr_contract_top_xR's hypotheses: this Section's, each with what discharges it (texts above) ----
   R / R_refl / R_trans / WLE_R  the instance R := wle' pa_segs RZ_cf, by wle'_refl / wle'_trans / wle_wle'
                                 (Reusable/YA0nH.v:156 / :159 / :164).
   RO / RO_ARx                   RO := arodata_ok_cf segs TfibB (QMm W1); RO_ARx is ARX's third conjunct.
   HA / HA_call                  HA := fun _ Sc _ _ _ n => cf_hull_adm Sc n; HA_call at MT_sec by a Theorem Labs lane's
                                 ReplyHullAdm.adm_charge_eq (a working branch 4668c68a7e7c), the step of its
                                 hull_adm_of_mo_reply, whose extra premise 1 <= n HA_call does not give.
   AMA_R / ARE_R / AFREE_R /     TOPK at route R after part 3c: a Theorem Labs lane's malloc / realloc half (a working branch
   AFREE0_R                      76a84b5b0b9f) and a Theorem Labs lane's free half (a working branch c9793e3d61f5),
                                 one TOPK_rh header for both halves.
   R_IMG                         at R := wle' pa_segs RZ_cf: wle' W W' gives, for a byte hidden in W', that it is hidden in W
                                 or RZ_cf holds of it (YA0nH.v:144-151 wle_in); an image byte is below 0x5fb000
                                 (W_kit.v pa_img_range) and RZ_cf (A/YGcfRehidePost.v:158) starts at
                                 shadow_addr 4096 - 4096 = 0x7fff7200, so the byte is hidden in W.
   LS_exit_end_R                 s5-r1d's ReplyLSI.lsi_LS_exit_end_xR at the instance's LS (a35949e2022).
   With them, the Section topx hypotheses the R twins and walks take at their strict texts (the RI_* / LS_* model rules
   and count rows, DR_CNT_* / RM_CNT_* / CNT_gone_*, MLAW, MO_FR, FFL, FPCOV, FP_SINK, SNP_x, and ASTRNDUP_x, which
   the proof lifts to R), discharged as for fr_contract_top_x; FFL, FP_SINK and SNP_x at ARX by their W1 lifts
   (the instance file's FFL / FP_SINK, lib/A/TopX_SNP_W.v) ---- *)
End topxR.
End topx.
