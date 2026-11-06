(* io_send_seg_cut: the cuts of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry 0x82d60 =
   TImgA.v ti_io_send timg_A; the statement is lib/A/Prog/io_send_cg.v), as STATEMENTS only.

   The walk is a G-form caller-journal walk: it holds ajournal_gx G_HARNESS 0 [] (lib/A/W_journalG.v) from the entry
   to the return, its straight stretches are the symbolic runs of lib/A/Prog/PaShadow.v over that journal
   (TransportGRunA.v paj_run_x), and its twelve calls are lifted by lib/A/Prog/TransportGCg.v (gx_call_cg for
   check_sent_frame and check_inflight_retry, gx_call_leaf for the seven leaves, gx_intrin_at for __asan_memset and
   __asan_memcpy, transport_cg_post_out_fold for check_latest_sent). The model side is lib/A/Prog/io_send_segs.v.

   This file names the cut points (IOS_AT off, an offset from the entry, as the statement's header measures them)
   and the three parts every segment shares:
   - ios_laws: the record facts, the allocator and meter laws and the twelve callee contracts, exactly the premises
     of transport_io_send_cg_holds_stmt;
   - ios_fix: the caller's journal and the entry facts, exactly the premises of transport_io_send_cg (the walk fixes
     them once and carries them to the return);
   - ios_cur: what holds of the machine state at EVERY cut: the journal from the entry to the cut with no event, the
     caller's side-stack frames and blocks, the meter, and the running kept fact acall_kept_g over io_send's own
     stack window and iosend_wr (the bytes some path stores into G). A cut adds its own register and frame facts.

   The cut points (offsets from 0x82d60; the statement's header gives the code at each):
     IOS_PARSE   +0x058  the return of __asan_memset: f cleared, the parse of the frame begins;
     IOS_CSF     +0x328  the return of check_sent_frame: the dispatch on f.cmd begins;
     IOS_EPI     +0x624  the epilogue: a0 = -EIO when bit 0 of the entry g_fail_next is set, else 0;
     IOS_FLY     +0x5d8  the frame in flight: the six stores into M.fly and the call of __asan_memcpy;
     IOS_CTRL    +0x37c  the shared call of check_latest_control the ACK and E3 arms join at;
     IOS_E2DATA  +0x388  the E2 / DATA arm's head (f.retry is read there);
     IOS_LOOP    +0x448  the head of the command count loop;
     IOS_CMDS    +0x53c  the loop's exit, a1 = cmds;
     IOS_TAIL    +0x5b8  the return of check_latest_sent. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportList.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  check_sent_frame_cg check_inflight_retry_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_ack_frame_cg check_latest_control_cg check_state_wake_cg check_inflight_new_cg check_latest_frame_cg
  check_keepalive_due_cg check_latest_display_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require io_send_segs.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_cg.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_cg.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_cg.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The cut points                                                      *)
(* ------------------------------------------------------------------ *)

(* An offset from io_send's entry, as a listing offset (the runs are taken at the listing's base). *)
Definition IOS_AT (off : Z) : Z := DgnTransportList.AF_io_send + off.
Definition IOS_PARSE : Z := IOS_AT 0x058.
Definition IOS_CSF : Z := IOS_AT 0x328.
Definition IOS_CTRL : Z := IOS_AT 0x37c.
Definition IOS_E2DATA : Z := IOS_AT 0x388.
Definition IOS_LOOP : Z := IOS_AT 0x448.
Definition IOS_CMDS : Z := IOS_AT 0x53c.
Definition IOS_TAIL : Z := IOS_AT 0x5b8.
Definition IOS_FLY : Z := IOS_AT 0x5d8.
Definition IOS_EPI : Z := IOS_AT 0x624.

(* Each cut point is the address the statement's header names. *)
Lemma ios_cut_addrs :
  transport_text + IOS_AT 0 = 0x82d60 /\ transport_text + IOS_PARSE = 0x82db8 /\
  transport_text + IOS_CSF = 0x83088 /\ transport_text + IOS_CTRL = 0x830dc /\
  transport_text + IOS_E2DATA = 0x830e8 /\ transport_text + IOS_LOOP = 0x831a8 /\
  transport_text + IOS_CMDS = 0x8329c /\ transport_text + IOS_TAIL = 0x83318 /\
  transport_text + IOS_FLY = 0x83338 /\ transport_text + IOS_EPI = 0x83384.
Proof. repeat split; reflexivity. Qed.

(* The words the prologue saves, as (distance below the entry sp, register): ra, s0 .. s7
   (0x82d64 - 0x82d84, loaded back at 0x83390 - 0x833b0). *)
Definition IOS_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23)].

(* io_send's own frame cells: the int at sp + 4 check_latest_sent writes through a pointer, and the struct
   spec_frame f at sp + 8 (SF_SIZE = 80 bytes). *)
Definition IOS_DISP_OFF : Z := 4.
Definition IOS_F_OFF : Z := 8.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* ------------------------------------------------------------------ *)
(* What every segment is given                                         *)
(* ------------------------------------------------------------------ *)

(* The premises of transport_io_send_cg_holds_stmt: the record facts, the allocator and meter laws, G inside the
   image and outside the allocator's statics and errno, and the twelve callee contracts (pc order). *)
Definition ios_laws : Prop :=
  transport_cells B /\ trans_iosend_cells B /\
  AR_laws segs B /\ ameter_laws MT /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) /\
  (forall fx' : YK11.FPState, @transport_check_sent_frame_cg fx' rc B MT (transport_sigma TS_check_sent_frame)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LAF.transport_check_ack_frame_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') /\
  (forall fx' : YK11.FPState,
     @transport_check_inflight_retry_cg fx' rc B MT (transport_sigma TS_check_inflight_retry)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_check_inflight_new_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLF.transport_check_latest_frame_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKD.transport_check_keepalive_due_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_check_latest_sent_cg fx' rc B MT (transport_sigma TS_check_latest_sent)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_display_cg) fx') /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)).

(* The premises of transport_io_send_cg: the caller's journal and the facts of the entry state. *)
Definition ios_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (Bw : list byte) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
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
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\
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
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 0) /\
  frames S2 = frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2
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

(* The post of the whole walk, as the statement states it (lib/A/Prog/io_send_cg.v
   transport_io_send_post at the model's world Bw' and result r). *)
Definition ios_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (frame : list byte) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_io_send_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    (Z.of_nat (length frame)) Bw' r.

(* The cut IOS_PARSE (0x82db8, the return of __asan_memset), as lib/A/Prog/io_send_seg_entry.v ios_entry reaches
   it from the entry (0x82d60 .. 0x82db4: the frame, the nine saves, s0 = len, s1 = p, the shadow base into s4, the
   byte of g_fail_next into s3 and the store of 0 there, the memset of f), at a state (ly2, S2, W2, mem2, md2) with
   registers regs2:
   - ios_cur: the journal from the entry (no event), the caller's frames and blocks, the meter, and acall_kept_g over
     io_send's stack window [sp - IOSEND_STK, sp) and iosend_wr (the stretch stored its frame and g_fail_next, the
     first field of iosend_wr);
   - ios_saved: ra, s0 .. s7 of the entry in their nine slots below the entry sp;
   - ios_regs with fail = the entry byte of g_fail_next (s3), and s8 .. s11 as at the entry (io_send saves only
     s0 .. s7, so these four must reach the return untouched);
   - the SF_SIZE = 80 bytes of the struct spec_frame f at sp - IOSEND_FRAME + IOS_F_OFF are 0;
   - the world relation at io_send_segs.v ios_B0 Bw = set_g_fail_next Bw 0;
   - the frame's facts at the cut's memory: its bytes (garr8), where it lies (trans_src_ok at the cut's state), and
     the read-only image bytes check_sent_frame compares (trans_rom_view_rd). *)
Definition ios_at_parse (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) : Prop :=
  ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 /\
  ios_saved W2 mem2 regs /\
  ios_regs regs regs2 p frame (TW.g_fail_next Bw) /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
  (forall i, 0 <= i < SF_SIZE ->
     aview segs (w_H W2) mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF + i) = Some 0) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (io_send_segs.ios_B0 Bw) /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  trans_rom_view_rd W2 mem2.

(* The join IOS_AT 0x314 (0x83074, where the parse's arms meet; on the path the model allows the body-sum stretch,
   lib/A/Prog/io_send_seg_sum.v, ends there with a0 = 0), as lib/A/Prog/io_send_seg_csf.v ios_csf_seg takes it:
   the running facts, the nine saved words, the registers (ios_regs, s8 .. s11 as at the entry, a0 = 0), the struct
   spec_frame f at sp + 8 holding rf frame (check_sent_frame_cg.v trans_sframe_at; its code field is already
   sf_code (rf frame) = 0, which the store at 0x83074 writes again), the frame's bytes and placement, the read-only
   image bytes check_sent_frame compares, and the world relation at ios_B0 Bw. *)
Definition ios_at_join (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) : Prop :=
  ios_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 /\
  ios_saved W2 mem2 regs /\
  ios_regs regs regs2 p frame (TW.g_fail_next Bw) /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
  YK11.getr regs2 10 = w64 0 /\
  trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame) /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  trans_rom_view_rd W2 mem2 /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (io_send_segs.ios_B0 Bw).

(* The cut IOS_CSF (0x83088, the return of check_sent_frame), as lib/A/Prog/io_send_seg_csf.v ios_csf_seg leaves
   it: the running facts, the nine saved words, the registers (ios_regs, s8 .. s11 as at the entry; a0 .. a7 not
   stated), the struct f at sp + 8 still holding rf frame (trans_sframe_at) and placed in the machine stack
   (trans_src_ok of its SF_SIZE bytes), the frame's bytes (garr8) and placement (trans_src_ok) at the cut's state,
   and the world relation at ios_B0 Bw (check_sent_frame keeps every byte of G). The read-only image bytes
   (trans_rom_view_rd) are NOT carried: no later callee of io_send reads them, and keeping them across a callee
   needs the record facts trans_ro_rd_unowned / trans_rom_no_errno, which the statement does not give. *)
Definition ios_at_csf (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
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
  trans_src_ok B ly2 S2 W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (io_send_segs.ios_B0 Bw).

End cut.
