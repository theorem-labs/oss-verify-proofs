(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 163 of its 234 lines of code are new or changed and 372 lines of the source are left out. *)
(* diginet_session_wake_seg_cut: the cuts of the walk of diginet_session_wake (fuzz_transport.asan 0x866fc =
   transport_sigma TS_diginet_session_wake, AF_diginet_session_wake = 0x5498 of lib/A/Prog/DgnTransportList.v), as
   STATEMENTS only, and the composition wake_holds_of: the statement transport_diginet_session_wake_cg_holds_stmt of
   lib/A/Prog/diginet_session_wake_cg.v from the five piece Props. The walk holds the CALLER's G journal
   (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) from the entry to the return, with (WAKE_CID, pos) :: own while
   the class-2 frame is live. It has five pieces, in pc order:

     head  +0x000 .. +0x260  the frame (`addi sp, sp, -128`), the zero word at sp, the 13 saves, s0 = the entry sp,
                             the realign into s1 (sp1), s4 = now, the two runtime cells (the flag word 1, so
                             `beqz a2` at +0x068 is not taken), s10 = the shadow base, s3 = s,
                             `jal __asan_stack_malloc_2` (+0x070; lib/A/Prog/TransportGFrame.v gx_stack_malloc_at),
                             s2 = s9 = the frame F, `bnez s2` taken (the real-stack arm at +0x088 is dead), the frame
                             word at s1 + 8, the 24-byte header, s8 = F's shadow address and the frame's 32 shadow
                             bytes, a0 = -1 and `beqz s3` (+0x168, not taken: s = TA_g_s), the checked load of
                             s + 116 and `beqz` (+0x184: S_desk_known Bw = 0 goes to the release cut with a0 = -1),
                             the checked load of s + 136, s5 = s + 18224, `beqz` (+0x1ac: S_foreign Bw <> 0 falls into
                             the refused path +0x1b0 .. +0x1d4, which bumps stats.refused, sets a0 = -10 and jumps to
                             the release cut), the three checked stores of :129-131 (s + 140, s + 144, s + 152),
                             s6 = e2 = F + 144, the frame's shadow bytes 18 .. 25 := 0, .., 0, 4 (e2 usable), the
                             arguments of :134-136 and `jal send_control` (+0x25c), then `bltz a0` (+0x260): a
                             negative result goes to the e2 cut with a0 = r, a non-negative one to the mid cut.
                             Prop: wake_head_stmt.
     mid   +0x264 .. +0x34c  `ld s7, 16(s1)` (e2_len = 60, which send_control stored), `jal __asan_memcpy` (+0x274;
                             s + 216, e2, 60), the checked stores of :140-141 (s + 1736, s + 18224) and of
                             inflight_start :113-116 (s + 212, s + 1744, s + 1748, s + 1752) with the checked load of
                             s + 160 between, s5 = s + 112, s6 = its shadow address, the checked load of s + 112 into
                             s7, s11 = 1 and `bne s7, s11` (+0x344): a state that is already S_WAKING falls through
                             to `li a0, 0` and the e2 cut, any other state goes to the notice cut.
                             Prop: wake_mid_stmt.
     ntc   +0x350 .. +0x40c  s4 = p = F + 32, the notice's shadow bytes 4 .. 12 := 0, `jal __asan_memset` (+0x384;
                             p + 16, 0, 56), the stores of 0x0000000100000002 at p, of s7 at p + 8 and of s11 at
                             p + 12, the checked store of 1 at s + 112, the checked loads of s + 96 (notify) and
                             s + 104 (ctx), `jalr a2` (+0x3e0: notice at TI.ti_notice timg_A), a0 = 0 and the
                             notice's shadow bytes 4 .. 12 := 0xf8, then the e2 cut. Prop: wake_ntc_stmt.
     e2    +0x410 .. +0x430  the frame's shadow bytes 18 .. 25 := 0xf8 (e2 out of scope), then the release cut.
                             Prop: wake_e2_stmt.
     rel   +0x434 .. +0x590  the header word 0x45e0360e at the frame, `beqz s2` not taken, the frame's 32 shadow bytes
                             := 0xf5, the flag pointer from the frame's last word, the store of 0 at it (the release:
                             TransportGFrame.v gx_flag_store_pi), `j +0x554`, sp = s0 - 128, the 13 reloads,
                             sp = sp + 128, `ret`. Prop: wake_rel_stmt.

   Each cut holds the caller's facts (wake_fix), the journal and the facts carried at the cut (wake_cur and the
   per-cut wake_mid_cur / wake_ntc_cur / wake_rel_cur), and the registers the code after the cut reads
   (wake_regs_core and its three extensions); each concludes the statement's post (diginet_session_wake_cg.v
   transport_wake_post) at the cut's pc. a0 carries the model's result from the branch that fixes it to the return,
   so the e2 and release cuts take it in wake_regs_rel. The frame word the head stores at s1 + 8 (+0x0a4) and the
   zero word at the entry sp - 128 (+0x004) are read by no later instruction, so no cut carries them.

   The e2 cut and the release cut carry the same state (wake_rel_cur): the eight shadow stores of +0x410 .. +0x430
   change no byte either cut's state speaks of. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The four cut points and the return, as offsets from the listing's base. *)
Definition WAKE_MID : Z := AF_diginet_session_wake + 0x264.
Definition WAKE_NTC : Z := AF_diginet_session_wake + 0x350.
Definition WAKE_E2 : Z := AF_diginet_session_wake + 0x410.
Definition WAKE_REL : Z := AF_diginet_session_wake + 0x434.
Definition WAKE_RET : Z := AF_diginet_session_wake + 0x590.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 120 ..
   sp + 24 after `addi sp, sp, -128`). *)
Definition WAKE_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-2 frame's size, and the two variables in it: the struct diginet_notice at F + 32 (72 bytes) and e2 at
   F + 144 (60 bytes); e2_len lies at sp1 + 16 in the machine frame. *)
Definition WAKE_FBYTES : Z := 256.
Definition WAKE_NTCOFF : Z := 32.
Definition WAKE_E2OFF : Z := 144.
Definition WAKE_KLPOFF : Z := 16.
Lemma wake_fbytes : fs_frame_bytes WAKE_CID = WAKE_FBYTES.
Proof. reflexivity. Qed.
(* The window relations the cuts need: the realigned sp lies at most 160 below the entry sp, the callees' windows fit
   inside the call's, and ESTACK fits. *)
Lemma wake_stk_bounds :
  WAKE_STK = WAKE_FRAME + WAKE_ALIGN + SENDCTL_STK /\
  160 + NOTICE_STK <= WAKE_STK /\ 160 + SENDCTL_STK <= WAKE_STK + 16 /\ 160 + ESTACK <= WAKE_STK /\
  WAKE_FRAME = 128 /\ WAKE_ALIGN = 16.
Proof.
  unfold WAKE_STK, WAKE_FRAME, WAKE_ALIGN, NOTICE_STK, SENDCTL_STK, ESTACK.
  repeat split; vm_compute; try reflexivity; try discriminate.
Qed.
(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma wake_some_inv : forall (Bx By : list byte) (rx ry : Z), Some (Bx, rx) = Some (By, ry) -> Bx = By /\ rx = ry.
Proof.
  intros Bx By rx ry H. split.
  - exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H).
  - exact (f_equal (fun o => match o with Some (_, v) => v | None => rx end) H).
Qed.
Lemma wake_some_inv_u : forall (Bx By : list byte), Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma wake_cut_pcs :
  BASE + AF_diginet_session_wake = transport_sigma TS_diginet_session_wake /\
  BASE + WAKE_MID = 0x86960 /\ BASE + WAKE_NTC = 0x86a4c /\ BASE + WAKE_E2 = 0x86b0c /\
  BASE + WAKE_REL = 0x86b30 /\ BASE + WAKE_RET = 0x86c8c.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_diginet_session_wake_cg_holds_stmt that are
   not callee contracts, with gx_ok / gx_noerrno (DgnTransportCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno from the
   first two of the four trans_* record facts). *)
Definition wake_laws : Prop :=
  pc_stack_malloc (as_code B) WAKE_CID = transport_sigma TS___asan_stack_malloc_2 /\
  transport_cells B /\ trans_wake_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\ trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS.

(* The caller's facts (the premises of transport_diginet_session_wake_cg at the entry registers regs), and what the
   head fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -128`, `andi sp, sp, -32`); pos,
   the slot of the class-2 frame the stack malloc gave; F, that frame's address. *)
Definition wake_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 WAKE_S /\ YK11.getr regs 11 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - WAKE_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.diginet_session_wake_m timg_A TF Bw now = Some (Bw', r) /\
  trans_tframe_at B lyc Sc W memc regs WAKE_STK TF /\
  trans_tf_off_g TF /\
  trans_rom_view_rd W memc /\
  wake_apart TF Bw /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
  count_cid WAKE_CID (frames Sc) + 2 < fs_frames WAKE_CID /\
  st_nev S + k + WAKE_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - WAKE_FRAME) / 32) /\
  F = frame_addr lyc WAKE_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + WAKE_FBYTES <= alloc_ceiling /\ in_app F WAKE_FBYTES.


(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range wake_wr Bw); the 13 saved words below the entry sp; the frame's last word, the address of its flag
   byte (astack_malloc_realizes' rdword). *)
Definition wake_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= WAKE_EV /\
  frames S2 = (WAKE_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) WAKE_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + WAKE_FBYTES - 8) = Some (flag_addr lyc WAKE_CID pos).

(* The state at the release cut (+0x434) and at the e2 cut (+0x410), which the eight shadow stores between them do
   not change: wake_cur, and the post's X already holds (the world relation at the model's world Bw' and
   g_fail_next Bw' <= 1); a0 holds the model's result, in wake_regs_rel. *)
Definition wake_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  wake_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The state at the mid cut (+0x264), reached from the head when send_control answered r >= 0: its world B1 and the
   60 bytes e2 it built, what it kept of the model's world (the keep lemma), the bytes at e2 and at e2_len in the
   machine frame, the read facts of e2's range (__asan_memcpy's source check), and the branch the model took to get
   here. The current heap frame and the read-only image bytes the notice reads are not carried: the notice piece
   rebuilds them from wake_fix's trans_tframe_at, trans_tf_off_g, wake_apart and trans_rom_view_rd through wake_cur's
   acall_kept_g. *)
Definition wake_mid_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (TF : option TI.tframe) (Bw B1 e2 : list byte) (rs : Z) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  wake_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  TW.S_desk_known Bw <> 0 /\ TW.S_foreign Bw = 0 /\
  TSS.send_control_m timg_A TF (wake_w1 Bw now) TS0.DIGINET_CMD_WAKE 0 = Some (B1, (rs, e2)) /\
  0 <= rs /\ length e2 = 60%nat /\
  TW.S_state B1 = TW.S_state Bw /\ TW.GOT_n B1 = TW.GOT_n Bw /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) B1 /\ TW.g_fail_next B1 <= 1 /\
  garr8 segs (mrestrict (w_H W2) mem2) (F + WAKE_E2OFF) (TW.zs e2) /\
  decode_rd_ok W2 mem2 (F + WAKE_E2OFF) SENDCTL_F /\
  garr8 segs (mrestrict (w_H W2) mem2) (sp1 + WAKE_KLPOFF) (TW.zs (TW.put 8 60)).

(* The state at the notice cut (+0x350), reached from the mid cut when the state is not S_WAKING: the world after the
   stores of :139-142, what the model's set_state_m leaves (its notice at the world the store of s + 112 makes, the
   session's notify pointer there, and the result), and the facts the notice's premises read at Bw (the keep lemma
   through wake_w3 and set_S_state). *)
Definition wake_ntc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' B1 e2 : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  wake_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  length e2 = 60%nat /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (wake_w3 B1 e2 now) /\
  TW.S_state (wake_w3 B1 e2 now) = TW.S_state Bw /\
  TW.S_state Bw <> TS0.DIGINET_S_WAKING /\
  TW.GOT_n (TW.set_S_state (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING) = TW.GOT_n Bw /\
  TW.S_notify (TW.set_S_state (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING) = TI.ti_notice timg_A /\
  TC.notice_m timg_A TF (TW.set_S_state (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING) (wake_ntc Bw) = Some (Bw', tt) /\
  TW.g_fail_next Bw' <= 1 /\
  r = DLib.DIGINET_OK.

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s9 = the
   frame, s8 = the frame's shadow address. *)
Definition wake_regs_core (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 24 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 25 = w64 F.
(* The e2 and release cuts also carry the model's result in a0. *)
Definition wake_regs_rel (regs regs2 : bvmap 5 word) (sp1 F r : Z) : Prop :=
  wake_regs_core regs regs2 sp1 F /\ YK11.getr regs2 10 = w64 r.
(* The mid cut also reads s3 = s, s4 = now, s5 = s + 18224 (g_s.stats.tx_wakes), s6 = e2 and s10 = the shadow base. *)
Definition wake_regs_mid (regs regs2 : bvmap 5 word) (sp1 F now : Z) : Prop :=
  wake_regs_core regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 WAKE_S /\ YK11.getr regs2 20 = w64 now /\
  YK11.getr regs2 21 = w64 (WAKE_S + (TW.A_S_stats_tx_wakes - TW.OFF_g_s)) /\
  YK11.getr regs2 22 = w64 (F + WAKE_E2OFF) /\ YK11.getr regs2 26 = w64 SHADOW_OFF.
(* The notice cut also reads s3 = s, s5 = s + 112, s6 = its shadow address, s7 = the state the code loaded (`lw`:
   sign-extended, and the keep lemma makes it S_state Bw), s10 = the shadow base, s11 = 1. *)
Definition wake_regs_ntc (regs regs2 : bvmap 5 word) (sp1 F : Z) (Bw : list byte) : Prop :=
  wake_regs_core regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 WAKE_S /\
  YK11.getr regs2 21 = w64 (WAKE_S + (TW.A_S_state - TW.OFF_g_s)) /\
  YK11.getr regs2 22 = w64 (SHADOW_OFF + (WAKE_S + (TW.A_S_state - TW.OFF_g_s)) / 8) /\
  YK11.getr regs2 23 = w64 (TW.S_state Bw) /\
  YK11.getr regs2 26 = w64 SHADOW_OFF /\ YK11.getr regs2 27 = w64 1.

(* The release cut, +0x434: from the state wake_rel_cur, the post. *)
Definition wake_rel_at : Prop :=
  wake_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    wake_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    wake_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    wake_regs_rel regs regs2 sp1 F r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKE_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_wake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The e2 cut, +0x410: the same state, eight shadow stores earlier. *)
Definition wake_e2_at : Prop :=
  wake_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    wake_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    wake_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    wake_regs_rel regs regs2 sp1 F r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKE_E2)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_wake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The notice cut, +0x350: from the state wake_ntc_cur, the post; the memset and notice contracts are its callees'. *)
Definition wake_ntc_at : Prop :=
  wake_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' B1 e2 : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    wake_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    wake_ntc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' B1 e2 pos sp1 F
      ly2 S2 W2 mem2 md2 e ->
    wake_regs_ntc regs regs2 sp1 F Bw ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKE_NTC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_wake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The mid cut, +0x264: from the state wake_mid_cur, the post. The memcpy contract is its own callee's; the memset
   and notice contracts are the notice cut's, which this piece enters, so it passes them on. *)
Definition wake_mid_at : Prop :=
  wake_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' B1 e2 : list byte) (rs : Z) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    wake_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    wake_mid_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now TF Bw B1 e2 rs pos sp1 F
      ly2 S2 W2 mem2 md2 e ->
    wake_regs_mid regs regs2 sp1 F now ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKE_MID)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_wake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The five pieces. rel: +0x434 .. the return. e2: +0x410 .. +0x430, then the release cut. ntc: +0x350 .. +0x40c,
   then the e2 cut. mid: +0x264 .. +0x34c, then the notice cut or the e2 cut. head: the entry .. +0x260, then the
   release cut (the two early exits and the refused path), the e2 cut (send_control answered r < 0) or the mid cut. *)
Definition wake_rel_stmt : Prop := wake_rel_at.
Definition wake_e2_stmt : Prop := wake_rel_at -> wake_e2_at.
Definition wake_ntc_stmt : Prop := wake_e2_at -> wake_ntc_at.
Definition wake_mid_stmt : Prop := wake_ntc_at -> wake_e2_at -> wake_mid_at.
Definition wake_head_stmt : Prop :=
  wake_mid_at -> wake_e2_at -> wake_rel_at -> @transport_diginet_session_wake_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma wake_holds_of : wake_head_stmt -> wake_mid_stmt -> wake_ntc_stmt -> wake_e2_stmt -> wake_rel_stmt ->
  @transport_diginet_session_wake_cg_holds_stmt fx rc B MT.
Proof.
  intros HEAD MID NTC E2 REL.
  pose proof (E2 REL) as E2a.
  exact (HEAD (MID (NTC E2a) E2a) E2a REL).
Qed.
End cut.
