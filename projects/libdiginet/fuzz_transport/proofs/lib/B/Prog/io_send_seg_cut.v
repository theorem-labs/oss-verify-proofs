(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1878 of its 1989 lines of code are new or changed and 815 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_tail.v, with its module paths and module names changed; 459 of its 506 lines of code are new or changed and 1942 lines of the source are left out. *)
(* io_send_seg_cut: the cuts of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry 0x82ffc =
   TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), and the statement of every segment, as
   STATEMENTS only (each segment file proves one; the joining files compose them).

   The walk is a G-form caller-journal walk: it holds ajournal_gx G_HARNESS_B 0 [] (lib/A/W_journalG.v) from the
   entry to the return, its straight stretches are the symbolic runs of lib/A/Prog/PaShadow.v over that journal
   (lib/B/Prog/TransportGRunB.v paj_run_x), and its calls are lifted by lib/A/Prog/TransportGCg.v (the G-form
   contracts of spec_read_frame and check_latest_sent folded with dk_kept_trans_out_g, gx_call_cg for
   check_sent_frame and check_inflight_retry, gx_call_leaf for the eight leaves, gx_intrin_at for __asan_memcpy).
   The model side is image A's lib/A/Prog/io_send_segs.v (io_send_m reads no image: ios_m_arm_B below),
   lib/A/Prog/io_send_seg_frm.v and lib/A/Prog/io_send_seg_inv.v, all image-free.

   This file names the cut points (IOS_AT off, an offset from the entry) and the parts every segment shares:
   - ios_laws: exactly the premises of transport_io_send_cg_holds_stmt;
   - ios_fix: exactly the premises of transport_io_send_cg (fixed from the entry to the return);
   - ios_cur: what holds of the machine state at EVERY cut: the journal from the entry with no event, the caller's
     side-stack frames and blocks, the meter, and the running kept fact acall_kept_g over io_send's own stack window
     and iosend_wr. ios_rom_cur: at every cut the read-only image bytes check_latest_sent reads are as at the entry.
   The cut points (offsets from 0x82ffc; the statement's header gives the code at each):
     IOS_SRF     +0x058  0x83054  the return of spec_read_frame;
     IOS_CSF     +0x068  0x83064  the return of check_sent_frame: the dispatch on f.cmd begins (a0 = f.cmd);
     IOS_CTRL    +0x0c4  0x830c0  the shared call of check_latest_control the ACK and E3 arms join at;
     IOS_E2DATA  +0x0d0  0x830cc  the E2 / DATA arm's head (f.retry is read there; a0 = f.cmd);
     IOS_RTY     +0x0d8  0x830d4  the retry arm;
     IOS_E2T     +0x10c  0x83108  f.cmd against 0xe2;
     IOS_E2ARM   +0x114  0x83110  the E2 arm;
     IOS_DATA    +0x14c  0x83148  the DATA arm;
     IOS_LOOP    +0x19c  0x83198  the command count loop (s2 = 0, s7 = 0, then its rounds from 0x831a0);
     IOS_CMDS    +0x224  0x83220  the loop's exit and the two shortcuts, s2 = cmds (a0 = sp + 8, a1 = s2 next);
     IOS_KA      +0x258  0x83254  the keepalive case of the DATA tail;
     IOS_SENT    +0x290  0x8328c  the check_latest_sent case of the DATA tail (a0 = g_raw);
     IOS_FLY     +0x2c4  0x832c0  the frame in flight: the stores into M.fly and the call of __asan_memcpy;
     IOS_EPI     +0x314  0x83310  the epilogue: a0 = -EIO when bit 0 of the entry g_fail_next is set, else 0.
   The unimp word is IOS_TRAP (+0x35c, 0x83358).

   The segments (one statement each, below, in pc order) and their files:
     ios_entry_stmt       entry .. IOS_SRF        io_send_seg_entry.v  (prologue, g_fail_next, spec_read_frame)
     ios_csf_seg_stmt     IOS_SRF .. IOS_CSF      io_send_seg_csf.v    (check_sent_frame)
     ios_ack_seg_stmt     IOS_CSF .. E2DATA / EPI io_send_seg_ack.v    (dispatch, ACK, E3)
     ios_e2_head_stmt     E2DATA .. RTY / E2T     io_send_seg_e2.v     (f.retry)
     ios_e2_test_stmt     E2T .. DATA / E2ARM     io_send_seg_e2.v     (f.cmd against 0xe2)
     ios_rty_arm_stmt     RTY .. EPI              io_send_seg_rty.v    (check_inflight_retry, M.fly.retries / .sent)
     ios_e2_arm_stmt      E2ARM .. FLY / EPI      io_send_seg_e2a.v    (check_state_wake, check_latest_control, GOT.e2)
     iod_head_stmt        DATA .. CMDS / LOOP     io_send_seg_data.v   (body[0], check_inflight_new, g_raw)
     ios_loop_stmt        LOOP .. CMDS            io_send_seg_loop.v   (the count loop, tagged_of)
     iod_mid_stmt         CMDS .. KA / SENT       io_send_seg_dmid.v   (check_latest_frame, two stores)
     ios_tail_seg_stmt    KA / SENT .. FLY        io_send_seg_tail.v   (keepalive; check_latest_sent, display)
     ios_fly_seg_stmt     FLY .. EPI              io_send_seg_fly.v    (M.fly, __asan_memcpy)
     ios_epi_stmt         EPI .. return           io_send_seg_epi.v
   joined by io_send_seg_head.v, io_send_seg_e2w.v, io_send_seg_join.v, io_send_seg_dpost.v and io_send_cgW.v. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBList DgnTransportBPa DgnTransportBImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB m_set_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  spec_read_frame_cg check_sent_frame_cg check_inflight_retry_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  check_ack_frame_cg check_latest_control_cg check_state_wake_cg check_inflight_new_cg tagged_of_cg
  check_latest_frame_cg check_keepalive_due_cg check_latest_display_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_frame_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_control_cg.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_cg.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_new_cg.
Module LTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_frame_cg.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_due_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_display_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The cut points                                                      *)
(* ------------------------------------------------------------------ *)

(* An offset from io_send's entry, as a listing offset (the runs are taken at the listing's base). *)
Definition IOS_AT (off : Z) : Z := DgnTransportBList.AF_io_send + off.
Definition IOS_SRF : Z := IOS_AT 0x058.
Definition IOS_CSF : Z := IOS_AT 0x068.
Definition IOS_CTRL : Z := IOS_AT 0x0c4.
Definition IOS_E2DATA : Z := IOS_AT 0x0d0.
Definition IOS_RTY : Z := IOS_AT 0x0d8.
Definition IOS_E2T : Z := IOS_AT 0x10c.
Definition IOS_E2ARM : Z := IOS_AT 0x114.
Definition IOS_DATA : Z := IOS_AT 0x14c.
Definition IOS_LOOP : Z := IOS_AT 0x19c.
Definition IOS_CMDS : Z := IOS_AT 0x224.
Definition IOS_KA : Z := IOS_AT 0x258.
Definition IOS_SENT : Z := IOS_AT 0x290.
Definition IOS_FLY : Z := IOS_AT 0x2c4.
Definition IOS_EPI : Z := IOS_AT 0x314.
Definition IOS_TRAP : Z := IOS_AT 0x35c.

(* Each cut point is the address the statement's header names. *)
Lemma ios_cut_addrs :
  transportb_text + IOS_AT 0 = 0x82ffc /\ transportb_text + IOS_AT 0 = TI.ti_io_send timg_B /\
  transportb_text + IOS_SRF = 0x83054 /\ transportb_text + IOS_CSF = 0x83064 /\
  transportb_text + IOS_CTRL = 0x830c0 /\ transportb_text + IOS_E2DATA = 0x830cc /\
  transportb_text + IOS_RTY = 0x830d4 /\ transportb_text + IOS_E2T = 0x83108 /\
  transportb_text + IOS_E2ARM = 0x83110 /\ transportb_text + IOS_DATA = 0x83148 /\
  transportb_text + IOS_LOOP = 0x83198 /\ transportb_text + IOS_CMDS = 0x83220 /\
  transportb_text + IOS_KA = 0x83254 /\ transportb_text + IOS_SENT = 0x8328c /\
  transportb_text + IOS_FLY = 0x832c0 /\ transportb_text + IOS_EPI = 0x83310 /\
  transportb_text + IOS_TRAP = 0x83358.
Proof. repeat split; reflexivity. Qed.

(* The words the prologue saves, as (distance below the entry sp, register): ra, s0 .. s7
   (0x83000 - 0x83020, loaded back at 0x8331c - 0x8333c). *)
Definition IOS_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23)].

(* io_send's own frame cells: the int display at sp + 4 (the store of 0 at 0x83178, then check_latest_sent's), and
   the struct spec_frame f at sp + 8 (SF_SIZE = 80 bytes, written by spec_read_frame). *)
Definition IOS_DISP_OFF : Z := 4.
Definition IOS_F_OFF : Z := 8.

(* s6 from 0x83180 on: the auipc value the listing names A_HI 57, g_raw + 1056 (`lw a0, -1056(s6)` at 0x83230
   reads g_raw again). *)
Definition IOS_S6 : Z := TB_g_raw + 1056.
Lemma ios_s6_val {fx : YK11.FPState} {rc : YM05.RunCeil} :
  @DgnTransportBPa.pa_val _ DgnTransportBList.transportb_listing DgnTransportBImg.PI_transportb (A_HI 57) = IOS_S6.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The model side                                                      *)
(* ------------------------------------------------------------------ *)

(* io_send_m reads no image (its timg argument is unused), so image A's split of it holds at timg_B. *)
Lemma io_send_m_timg : forall I J Bw frame, TC.io_send_m I Bw frame = TC.io_send_m J Bw frame.
Proof. intros I J Bw frame. reflexivity. Qed.

Lemma ios_m_arm_B : forall Bw frame Bw' r,
  TC.io_send_m timg_B Bw frame = Some (Bw', r) ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) /\
  ios_arm Bw frame = Some (Bw', tt) /\ r = ios_ret Bw.
Proof.
  intros Bw frame Bw' r H. apply (ios_m_arm Bw frame Bw' r).
  rewrite (io_send_m_timg _ timg_B). exact H.
Qed.

(* check_sent_frame's length test: len = max (60, 30 + body_len), body_len = numbytes - 16 < 2^16. *)
Lemma ios_len_lt32 : forall Bm frame B',
  TC.check_sent_frame_m Bm frame = Some (B', tt) -> Z.of_nat (length frame) < 2 ^ 32.
Proof.
  intros Bm frame B' H.
  pose proof (ios_sf_code _ _ _ H) as HOK.
  destruct (ios_fields frame HOK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fblen & _).
  pose proof (DSpec.be16_range frame 14) as Rnb.
  unfold TC.check_sent_frame_m in H. cbv zeta in H.
  match type of H with context [if ?c then None else _] => destruct c eqn:C1 end;
    cbv beta iota in H; [discriminate H|].
  match type of H with context [if ?c then None else _] => destruct c eqn:C2 end;
    cbv beta iota in H; [discriminate H|].
  apply orb_false_iff in C2. destruct C2 as [C2 _].
  apply orb_false_iff in C2. destruct C2 as [C2 _].
  apply negb_false_iff, Z.eqb_eq in C2. rewrite C2.
  rewrite Fblen. unfold DSpec.fr_body_len, DSpec.fr_numbytes.
  destruct (DSpec.SPEC_BODY_AT + (DSpec.be16 frame 14 - 16) <? TC.SPEC_MIN_FRAME);
    unfold TC.SPEC_MIN_FRAME, DSpec.SPEC_BODY_AT in *; lia.
Qed.

(* The keepalive flag of :854 as the machine holds it in s5 (0x83174 / 0x83350). *)
Definition ios_kaz (frame : list byte) : Z := if ios_ka frame then 1 else 0.

(* f.retry, the field the E2 / DATA head tests. *)
Definition ios_e2_rty (frame : list byte) : Z := DSpec.sf_retry (TC.rf frame).

(* The world after the two stores of the DATA arm (:867-868), check_latest_sent's world. *)
Definition ios_B5 (Bw frame : list byte) : list byte :=
  TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) (DSpec.sf_send (TC.rf frame)))
    (DSpec.sf_send (TC.rf frame)).

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* ------------------------------------------------------------------ *)
(* What every segment is given                                         *)
(* ------------------------------------------------------------------ *)

(* The premises of transport_io_send_cg_holds_stmt, in its order. *)
Definition ios_laws : Prop :=
  transport_cells B /\ trans_iosend_cells B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B /\
  (forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame)) /\
  (forall fx' : YK11.FPState, @transport_check_sent_frame_cg fx' rc B MT (transportb_sigma TB_check_sent_frame)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LAF.transport_check_ack_frame_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') /\
  (forall fx' : YK11.FPState,
     @transport_check_inflight_retry_cg fx' rc B MT (transportb_sigma TB_check_inflight_retry)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_check_inflight_new_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LTO.transport_tagged_of_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLF.transport_check_latest_frame_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKD.transport_check_keepalive_due_cg) fx') /\
  (forall fx' : YK11.FPState,
     @transport_check_latest_sent_cg fx' rc B MT (transportb_sigma TB_check_latest_sent)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_display_cg) fx') /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)).

(* The premises of transport_io_send_cg: the caller's journal and the facts of the entry state. *)
Definition ios_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (Bw : list byte) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 11 = w64 p /\ YK11.getr regs 12 = w64 (Z.of_nat (length frame)) /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - IOSEND_STK /\ spZ regs <= sp0 /\
  0 < p /\
  garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz frame) /\
  trans_src_ok B lyc Sc W memc p (Z.of_nat (length frame)) /\
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) /\
  iosend_frame_at p (Z.of_nat (length frame)) /\
  TW.g_fail_next Bw <= 1 /\
  trans_rom_view_rd W memc /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
  st_nev S + k + IOSEND_EV <= EV_MAX.

(* What holds at every cut: the journal from the entry (no event: IOSEND_EV = 0), the caller's side-stack frames
   and blocks, the meter, and the running kept fact over io_send's own stack window and the bytes some path of the
   call stores into G. *)
Definition ios_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (frame : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 0) /\
  frames S2 = frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2
    (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))).

(* The nine saved words still in io_send's frame at a cut, and the sp of every run between the prologue and the
   epilogue (the entry sp less IOSEND_FRAME). *)
Definition ios_saved (W2 : world segs) (mem2 : word -> option byte) (regs : bvmap 5 word) : Prop :=
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
            Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) IOS_SAVED.

(* The registers the code after a cut reads: sp, gp, tp (kept by every callee), s0 = len, s1 = p, s3 = the byte of
   g_fail_next the entry read, s4 = the shadow base. *)
Definition ios_regs (regs regs2 : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z) : Prop :=
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) /\
  YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (Z.of_nat (length frame)) /\ YK11.getr regs2 9 = w64 p /\
  YK11.getr regs2 19 = w64 fail /\ YK11.getr regs2 20 = w64 SHADOW_OFF.

(* The post of the whole walk, as the statement states it (lib/B/Prog/io_send_cg.v
   transport_io_send_post at the model's world Bw' and result r). *)
Definition ios_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (frame : list byte) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_io_send_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    (Z.of_nat (length frame)) Bw' r.

(* At every cut the bytes of TRANS_RO_RD (HOST, the constant-pool word TRANS_K_SENT check_latest_sent reads) are
   the image's: ios_cur's kept fact keeps every image byte outside G that is neither an owned static nor errno, and
   every TRANS_RO_RD byte is one (trans_ro_rd_scoped), below G (trans_ro_rd_bounds). *)
Lemma ios_rom_kept : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W2 mem2.
Proof.
  intros HRU HRE lyc Sc W memc W2 mem2 slo shi E (_ & _ & K3 & _) HR a Ha.
  rewrite <- (HR a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TransportGB.G_HARNESS_B_LO in Gh. lia.
Qed.

Lemma ios_rom_cur : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
    p frame Bw ly2 S2 (W2 : world segs) mem2 md2,
  ios_laws ->
  ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 ->
  trans_rom_view_rd W2 mem2.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 HL HF HC.
  destruct HL as (_ & _ & HRU & HRE & _).
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROM & _).
  destruct HC as (_ & _ & _ & _ & HK).
  exact (ios_rom_kept HRU HRE lyc Sc W memc W2 mem2 _ _ _ HK HROM).
Qed.

(* ------------------------------------------------------------------ *)
(* The cuts                                                            *)
(* ------------------------------------------------------------------ *)

(* The cut IOS_SRF (0x83054, the return of spec_read_frame), as io_send_seg_entry.v reaches it from the entry
   (0x82ffc .. 0x83050: the frame, the nine saves, s0 = len, s1 = p, the shadow base into s4, the byte of
   g_fail_next into s3 and the store of 0 there, a0 = p, a1 = len, a2 = sp + 8, the call of spec_read_frame):
   - ios_cur (the struct's 80 bytes and the saves are bytes of io_send's window; g_fail_next is iosend_wr's first
     field);
   - ios_saved; ios_regs with fail = the entry byte of g_fail_next (s3); s8 .. s11 as at the entry;
   - the struct spec_frame f at sp + 8 holding rf frame (spec_read_frame's X: sf_bytes p (rf frame), read field by
     field as check_sent_frame_cg.v trans_sframe_at);
   - the frame's bytes (garr8) and placement (trans_src_ok) at the cut's state;
   - the world relation at io_send_segs.v ios_B0 Bw = set_g_fail_next Bw 0 (spec_read_frame keeps G). *)
Definition ios_at_srf (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) : Prop :=
  ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 /\
  ios_saved W2 mem2 regs /\
  ios_regs regs regs2 p frame (TW.g_fail_next Bw) /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
  trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame) /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) (ios_B0 Bw).

(* The state at a cut of the E2 / DATA stretch and at IOS_CSF, at its own world W2 and the model's world Bx: the
   running facts, the nine saved words, the registers (ios_regs with fail the entry byte of g_fail_next, s8 .. s11
   as at the entry), the struct f at sp + 8 holding rf frame and placed in the machine stack (trans_src_ok of its
   SF_SIZE bytes), the frame's bytes and placement at the cut's state, and the world relation at Bx. *)
Definition ios_e2_at (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) (Bx : list byte) : Prop :=
  ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 /\
  ios_saved W2 mem2 regs /\
  ios_regs regs regs2 p frame fail /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
  trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame) /\
  trans_src_ok B ly2 S2 W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bx.

(* The cut IOS_CSF (0x83064, the return of check_sent_frame) and every cut of the dispatch and of the DATA arm's
   head: ios_e2_at at the world ios_B0 Bw (check_sent_frame keeps G) with the entry byte of g_fail_next. *)
Definition ios_at_csf (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) : Prop :=
  ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
    ly2 S2 W2 mem2 md2 regs2 (ios_B0 Bw).

(* The DATA arm's running cut, from the return of check_inflight_new (0x83180) to IOS_CMDS: ios_at_csf (the world
   is still ios_B0 Bw: check_inflight_new and tagged_of are leaves), s5 = the keepalive flag, s6 = IOS_S6. *)
Definition iod_at (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) : Prop :=
  ios_at_csf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 /\
  YK11.getr regs2 21 = w64 (ios_kaz frame) /\
  YK11.getr regs2 22 = w64 IOS_S6.

(* What holds at IOS_KA / IOS_SENT (the DATA tail's entries) and at IOS_FLY, at a state (ly2, S2, W2, mem2, md2)
   and the model's world Bx there: ios_cur and ios_saved, the struct f at sp + 8 holding rf frame, the frame's
   bytes and placement at this state, the frame apart from io_send's window and placed as iosend_frame_at says,
   and the world relation at Bx. *)
Definition ios_tail_at (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (Bx : list byte) : Prop :=
  ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 /\
  ios_saved W2 mem2 regs /\
  trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame) /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) /\
  iosend_frame_at p (Z.of_nat (length frame)) /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bx.

(* ------------------------------------------------------------------ *)
(* The segment statements                                              *)
(* ------------------------------------------------------------------ *)

(* entry .. IOS_SRF: the prologue (0x82ffc - 0x83020), s0 = len, s1 = p (0x83024 - 0x83028), the shadow base into
   s4 (0x8302c - 0x83038), s3 = g_fail_next and the store of 0 there (0x8303c - 0x83040), a2 = sp + 8, a0 = p,
   a1 = len (0x83044 - 0x8304c), the call of spec_read_frame at 0x83050 (its G-form post folded into ios_cur). *)
Definition ios_entry_stmt : Prop :=
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
         p frame Bw (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    (forall ly2 S2 (W2 : world segs) mem2 md2 regs2,
       ios_at_srf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_SRF) regs2 mem2 md2) Q) ->
    SRr segs W (@cfg_at fx segs (TI.ti_io_send timg_B) regs memc mdc) Q.

(* IOS_SRF .. IOS_CSF: a2 = sp + 8, a0 = p, a1 = len (0x83054 - 0x8305c) and the call of check_sent_frame at
   0x83060 (gx_call_cg). *)
Definition ios_csf_seg_stmt : Prop :=
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
         p frame Bw ly2 S2 (W2 : world segs) mem2 md2 regs2 (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    ios_at_srf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
    (forall ly3 S3 (W3 : world segs) mem3 md3 regs3,
       ios_at_csf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W3 mem3 md3 regs3 ->
       SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_CSF) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_SRF) regs2 mem2 md2) Q.

(* IOS_CSF .. the exits of the dispatch on f.cmd (0x83064 - 0x830c8):
   - f.cmd = 0 or 0xe2: IOS_E2DATA, the cut's facts at a memory equal to the cut's, a0 = f.cmd;
   - f.cmd = 0xa0 (ACK: GOT.acks + 1 with its overflow branch to the trap word, check_ack_frame,
     check_latest_control), 0xe3 (E3: GOT.e3 + 1, the same branch, check_latest_control) or any other value:
     IOS_EPI with what ios_epi_stmt reads, at the world ios_arm leaves. *)
Definition ios_ack_seg_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw Bw' : list byte)
         ly2 S2 (W2 : world segs) mem2 md2 (rg : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_at_csf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 rg ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    ios_arm Bw frame = Some (Bw', tt) ->
    (forall rg2 mem3 md3,
       (DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2 \/ DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA) ->
       ios_at_csf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 rg2 ->
       YK11.getr rg2 10 = w64 (DSpec.sf_cmd (TC.rf frame)) ->
       (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
       (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_E2DATA) rg2 mem3 md3) Q) ->
    (forall rg2 mem3 md3,
       ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3 ->
       ios_saved W2 mem3 regs ->
       ios_regs regs rg2 p frame (TW.g_fail_next Bw) ->
       (forall r, 24 <= r <= 27 -> YK11.getr rg2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
       tw_at TMAP_B (aview segs (w_H W2) mem3) Bw' ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_EPI) rg2 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CSF) rg mem2 md2) Q.

(* IOS_E2DATA .. : the 2-byte load of f.retry at sp + 38 and `beq a1, zero` (0x830cc - 0x830d0): f.retry <> 0
   goes on to IOS_RTY, f.retry = 0 to IOS_E2T with a0 = f.cmd still. No store. *)
Definition ios_e2_head_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw : list byte) (fail cmd : Z)
         ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem3 md3 regs3 Bx ->
    YK11.getr regs3 10 = w64 cmd ->
    (forall mem4 md4 regs4,
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem4 md4 regs4 Bx ->
       ios_e2_rty frame <> 0 ->
       SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_RTY) regs4 mem4 md4) Q) ->
    (forall mem4 md4 regs4,
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem4 md4 regs4 Bx ->
       YK11.getr regs4 10 = w64 cmd -> ios_e2_rty frame = 0 ->
       SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_E2T) regs4 mem4 md4) Q) ->
    SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_E2DATA) regs3 mem3 md3) Q.

(* IOS_E2T .. : `li a1, 0xe2` and `bne a0, a1` (0x83108 - 0x8310c): a0 <> 0xe2 goes to IOS_DATA, else on to
   IOS_E2ARM. No store. *)
Definition ios_e2_test_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw : list byte) (fail cmd : Z)
         ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem3 md3 regs3 Bx ->
    YK11.getr regs3 10 = w64 cmd -> 0 <= cmd < 256 ->
    (forall mem4 md4 regs4,
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem4 md4 regs4 Bx ->
       cmd <> TC.SPEC_CMD_E2 ->
       SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_DATA) regs4 mem4 md4) Q) ->
    (forall mem4 md4 regs4,
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem4 md4 regs4 Bx ->
       cmd = TC.SPEC_CMD_E2 ->
       SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_E2ARM) regs4 mem4 md4) Q) ->
    SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_E2T) regs3 mem3 md3) Q.

(* IOS_RTY .. IOS_EPI, the retry arm (0x830d4 - 0x83104): a2 = sp + 8, a0 = p, a1 = len, the call of
   check_inflight_retry at 0x830e0 (gx_call_cg; its premise M_fly_len <= 1514 from ios_fix's guarded run invariant),
   M.fly.retries + 1 stored back (4 bytes, M + 108), g_now stored at M + 112 (M.fly.sent), `j` to IOS_EPI; at the
   world Bw' the dispatch leaves (io_send_segs.v ios_arm_retry). *)
Definition ios_rty_arm_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame : list byte) (Bw Bw' : list byte)
         ly3 S3 (W3 : world segs) mem4 md4 (regs4 : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_at_csf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W3 mem4 md4 regs4 ->
    (DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2 \/ DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA) ->
    ios_e2_rty frame <> 0 ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    ios_arm Bw frame = Some (Bw', tt) ->
    (forall ly5 S5 (W5 : world segs) mem5 md5 regs5,
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
         ly5 S5 W5 mem5 md5 regs5 Bw' ->
       SRr segs W5 (@cfg_at fx segs (transportb_text + IOS_EPI) regs5 mem5 md5) Q) ->
    SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_RTY) regs4 mem4 md4) Q.

(* IOS_E2ARM .., the E2 arm (0x83110 - 0x83144): check_state_wake at 0x83110, a0 = sp + 8, check_latest_control at
   0x83118, GOT.e2 + 1 with its overflow branch to the trap word, stored back, f.send stored at g_last_counter;
   bit 0 of s3 clear goes to IOS_FLY (at the world B5 of io_send_segs.v ios_arm_e2, Bw' = ios_fly frame B5), set
   to IOS_EPI (Bw' = B5). *)
Definition ios_e2_arm_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame
         Bw Bw' ly3 S3 (W2 : world segs) mem4 md4 regs4 (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_at_csf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W2 mem4 md4 regs4 ->
    DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2 ->
    ios_e2_rty frame = 0 ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    ios_arm Bw frame = Some (Bw', tt) ->
    (forall ly5 S5 mem5 md5 regs5 B5,
       TC.truth (TW.g_fail_next Bw) = false -> Bw' = ios_fly frame B5 ->
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
         ly5 S5 W2 mem5 md5 regs5 B5 ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_FLY) regs5 mem5 md5) Q) ->
    (forall ly5 S5 (W5 : world segs) mem5 md5 regs5,
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
         ly5 S5 W5 mem5 md5 regs5 Bw' ->
       SRr segs W5 (@cfg_at fx segs (transportb_text + IOS_EPI) regs5 mem5 md5) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_E2ARM) regs4 mem4 md4) Q.

(* IOS_DATA .. , the DATA arm's head (0x83148 - 0x83198, 0x83214 - 0x8321c, 0x83348 - 0x83354): s5 = the
   keepalive flag (body_len = 1, the CHECKED 1-byte load of body[0] at f.body = p + 30 is 0, f.ncmds = 1; the
   branch on f.body = 0 to the trap word refuted by p + 30 <> 0, the slow path of the check and its error call
   unreached), the 4-byte store of 0 at sp + 4, the call of check_inflight_new at 0x8317c (a leaf), s6 = IOS_S6,
   the load of g_raw and the three branches:
   - g_raw <> 0 or s5 <> 0: IOS_CMDS with s2 = f.ncmds (0x83214);
   - body_len = 0: IOS_CMDS with s2 = 0 (0x8321c);
   - else IOS_LOOP with a1 = body_len. *)
Definition iod_head_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
         ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA ->
    TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
    TC.check_inflight_new_m (ios_B0 Bw) = Some (ios_B0 Bw, tt) ->
    ios_at_csf STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
    (forall mem3 md3 regs3,
       iod_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 regs3 ->
       YK11.getr regs3 18 = w64 (DSpec.sf_ncmds (TC.rf frame)) ->
       (TC.truth (TW.g_raw (ios_B0 Bw)) = true \/ ios_ka frame = true) ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs3 mem3 md3) Q) ->
    (forall mem3 md3 regs3,
       iod_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 regs3 ->
       YK11.getr regs3 18 = w64 0 ->
       TC.truth (TW.g_raw (ios_B0 Bw)) = false -> ios_ka frame = false -> ios_blen frame = 0 ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs3 mem3 md3) Q) ->
    (forall mem3 md3 regs3,
       iod_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 regs3 ->
       YK11.getr regs3 11 = w64 (ios_blen frame) ->
       TC.truth (TW.g_raw (ios_B0 Bw)) = false -> ios_ka frame = false -> ios_blen frame <> 0 ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_LOOP) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_DATA) regs2 mem2 md2) Q.

(* IOS_LOOP .. IOS_CMDS, the command count loop (0x83198 - 0x83210, :858-862): s2 = cmds = 0, s7 = at = 0; each
   round from 0x831a0: a0 = f.body + at (its two pointer checks to the trap word refuted), a1 = body_len - at, the
   call of tagged_of at 0x831c0 (a leaf); its result t = 0 gives step = body_len - at, else (the alignment check of t
   refuted) the CHECKED load of t->len at t + 36 = g_cmd + 40 s + 36; at += step, cmds += 1 (addiw), at < body_len
   goes round again. The model's loop is TCb.v cmds_loop from at = 0, cmds = 0 at the world ios_B0 Bw. *)
Definition ios_loop_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw : list byte) (final : Z)
         ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    iod_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
    YK11.getr regs2 11 = w64 (ios_blen frame) -> 0 < ios_blen frame ->
    TC.cmds_loop (Datatypes.S (Z.to_nat (ios_blen frame))) (ios_B0 Bw) (ios_body frame) (ios_blen frame) 0 0 = Some final ->
    (forall mem3 md3 regs3,
       iod_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem3 md3 regs3 ->
       YK11.getr regs3 18 = w64 (bv_swrap 32 final) -> 0 <= final < 2 ^ 32 ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_LOOP) regs2 mem2 md2) Q.

(* IOS_CMDS .. IOS_KA / IOS_SENT (0x83220 - 0x83250): a0 = sp + 8, a1 = s2, the call of check_latest_frame at
   0x83228 (a leaf); a1 = f.send, a0 = g_raw (through s6), s2 = M, the 4-byte stores of f.send at M + 84
   (M.host_counter) and at g_last_counter (the world ios_B5 Bw frame), a2 = (g_raw = 0) & s5: set goes to IOS_KA,
   clear to IOS_SENT with a0 = g_raw. *)
Definition iod_mid_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw : list byte) (cmds : Z)
         ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    iod_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
    YK11.getr regs2 18 = w64 (bv_swrap 32 cmds) -> 0 <= cmds < 2 ^ 32 ->
    TC.check_latest_frame_m (ios_B0 Bw) frame cmds = Some (ios_B0 Bw, tt) ->
    (forall mem3 md3 regs3 (pc : Z),
       ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem3 md3
         (ios_B5 Bw frame) ->
       YK11.getr regs3 2 = w64 (spZ regs - IOSEND_FRAME) ->
       YK11.getr regs3 3 = YK11.getr regs 3 -> YK11.getr regs3 4 = YK11.getr regs 4 ->
       YK11.getr regs3 8 = w64 (Z.of_nat (length frame)) -> YK11.getr regs3 9 = w64 p ->
       YK11.getr regs3 19 = w64 (TW.g_fail_next Bw) ->
       (forall r, 24 <= r <= 27 -> YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
       YK11.getr regs3 18 = w64 TB_M ->
       (pc = IOS_KA /\ TC.truth (TW.g_raw (ios_B5 Bw frame)) = false /\ ios_ka frame = true \/
        pc = IOS_SENT /\ YK11.getr regs3 10 = w64 (TW.g_raw (ios_B5 Bw frame)) /\
          (TC.truth (TW.g_raw (ios_B5 Bw frame)) = false -> ios_ka frame = false)) ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + pc) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs2 mem2 md2) Q.

(* IOS_KA / IOS_SENT .. IOS_FLY, the DATA arm's tail (0x83254 - 0x832bc, :869-879), from the cut facts at the
   world B5 to the cut facts at the world io_send_segs.v ios_B6 frame B5 gives, every callee-saved register as at
   the start:
   - IOS_KA (g_raw clear, the frame a keepalive): check_keepalive_due (a leaf), M.next_ka + keepalive_ms * 1000
     stored at M + 48, `bltu` on g_now, whose fall-through stores g_now + keepalive_ms * 1000 there;
   - IOS_SENT (a0 = g_raw): `bnez a0` to IOS_FLY; else a0 = f.body, a1 = f.body_len, a2 = sp + 4, the call of
     check_latest_sent at 0x8329c (G form, out cell sp + 4; its premise trans_rom_view_rd from ios_rom_cur, its
     command-length invariant at B5 from ios_fix's by io_send_seg_inv.v ios_cmdinv_B5), the int at sp + 4 = 0 goes
     to IOS_FLY; else check_latest_display (a leaf) and the stores of g_now at M + 64 and of 1 at M + 72. *)
Definition ios_tail_seg_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) p frame Bw ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) B5 B6 (pc : Z)
         (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 B5 ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
    YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
    YK11.getr regs2 18 = w64 TB_M ->
    ios_B6 frame B5 = Some (B6, tt) ->
    (forall s, 0 <= s < TW.g_ncmd B5 -> TW.Cmd_st B5 s = TC.PENDING -> TW.Cmd_len B5 s <= DSpec.SPEC_CMD_MAX) ->
    (pc = IOS_KA /\ TC.truth (TW.g_raw B5) = false /\ ios_ka frame = true \/
     pc = IOS_SENT /\ YK11.getr regs2 10 = w64 (TW.g_raw B5) /\
       (TC.truth (TW.g_raw B5) = false -> ios_ka frame = false)) ->
    (forall ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word),
       ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 B6 ->
       aregs_preserved regs2 regs3 ->
       SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_FLY) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + pc) regs2 mem2 md2) Q.

(* IOS_FLY .. IOS_EPI, the frame in flight (0x832c0 - 0x8330c, :883-889): a3 = f.send (sp + 40), a4 = f.cmd
   (sp + 48), the stores of g_now at M + 112, 1 at M + 96, f.cmd at M + 100, f.send at M + 104, 0 at M + 108,
   s0 = min (len, 1514) stored at M + 1640, and __asan_memcpy (M + 120, p, s0) at 0x8330c (gx_intrin_at); at the
   world io_send_segs.v ios_fly frame Bx. *)
Definition ios_fly_seg_stmt : Prop :=
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) p frame Bw Bx ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word)
         (Q : world segs -> config -> Prop),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 Bx ->
    60 <= Z.of_nat (length frame) -> Z.of_nat (length frame) < 2 ^ 32 ->
    YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
    YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
    YK11.getr regs2 8 = w64 (Z.of_nat (length frame)) -> YK11.getr regs2 9 = w64 p ->
    YK11.getr regs2 19 = w64 (TW.g_fail_next Bw) ->
    (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
    (forall mem3 md3 (regs3 : bvmap 5 word),
       ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3 ->
       ios_saved W2 mem3 regs ->
       YK11.getr regs3 2 = w64 (spZ regs - IOSEND_FRAME) ->
       YK11.getr regs3 3 = YK11.getr regs 3 -> YK11.getr regs3 4 = YK11.getr regs 4 ->
       YK11.getr regs3 19 = w64 (TW.g_fail_next Bw) ->
       (forall r, 24 <= r <= 27 -> YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
       tw_at TMAP_B (aview segs (w_H W2) mem3) (ios_fly frame Bx) ->
       SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_EPI) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_FLY) regs2 mem2 md2) Q.

(* IOS_EPI .. the return (0x83310 - 0x83344): `slli s3, 63; srai a0, s3, 63; andi a0, -5` (a0 = -EIO when bit 0
   of s3 is set, else 0, :898), the nine reloads of IOS_SAVED, sp + 160, `ret`: the walk's post at the model's
   world Bw' and result ios_ret Bw. *)
Definition ios_epi_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame Bw Bw' : list byte)
         ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word),
    ios_laws ->
    ios_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 ->
    ios_saved W2 mem2 regs ->
    YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
    YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
    YK11.getr regs2 19 = w64 (TW.g_fail_next Bw) ->
    (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' ->
    SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_EPI) regs2 mem2 md2)
      (ios_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame Bw' (ios_ret Bw)).

End cut.
