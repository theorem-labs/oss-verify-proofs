(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 397 of its 445 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBCut.v, with its module names changed; 129 of its 198 lines of code are new or changed and 376 lines of the source are left out. *)
(* diginet_session_wake_seg_cut (image B): the cuts of the walk of diginet_session_wake on fuzz_transport.asan-ubsan
   (41113a03c82f) at 0x86a38 = transportb_sigma TB_diginet_session_wake (AF_diginet_session_wake = 0x5798 of
   lib/B/Prog/DgnTransportBList.v), as STATEMENTS only, and the composition wakeb_holds_of: the statement
   transport_diginet_session_wake_cg_holds_stmt of lib/B/Prog/diginet_session_wake_cg.v from the four piece Props. The
   walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) from the entry to the
   return, with (WAKE_CID, pos) :: own while the class-1 frame is live. Four pieces, in pc order:

     head  +0x000 .. +0x220  the frame (`addi sp, sp, -128`), the zero word at sp, the 12 saves (ra, s0 .. s10),
                             s0 = the entry sp, the realign into s1 (sp1), s3 = now, the two runtime cells (the flag
                             word 1, so `beqz a2` at +0x064 is not taken), s10 = the shadow base, s4 = s,
                             `jal __asan_stack_malloc_1` (+0x06c), s2 = s9 = the frame F, `bnez s2` taken (the
                             real-stack arm at +0x084 is dead), the frame word at s1 + 16, the 24-byte header, s8 = F's
                             shadow address and the frame's 16 shadow bytes, a0 = -1 and `beqz s4` (+0x120, not taken:
                             s = TB_g_s), the UBSan alignment check `andi a1, s4, 7; bnez a1` (+0x128, not taken: s is a
                             multiple of 8, so the trap word at +0x3fc is unreached), the checked load of s + 116 and
                             `beqz` (+0x144: S_desk_known Bw = 0 goes to the release cut with a0 = -1), the checked load
                             of s + 136, s5 = s + 18224, `beqz` (+0x16c: S_foreign Bw <> 0 falls into the refused path
                             +0x170 .. +0x194, which bumps stats.refused, sets a0 = -10 and jumps to the release cut),
                             the three checked stores of :129-131 (s + 140, s + 144, s + 152), s6 = e2 = F + 32, the
                             frame's shadow bytes 4 .. 11 := 0, .., 0, 4 (e2 usable), the arguments of :134-136 and
                             `jal send_control` (+0x21c), then `bltz a0` (+0x220): a negative result goes to the e2 cut
                             with a0 = r, a non-negative one to the mid cut. Prop: wakeb_head_stmt.
     mid   +0x224 .. +0x2f8  `ld s7, 24(s1)` (e2_len = 60, which send_control stored), `jal __asan_memcpy` (+0x234;
                             s + 216, e2, 60), the checked stores of :140-141 (s + 1736, s + 18224) and of
                             inflight_start :113-116 (s + 212, s + 1744, s + 1748, s + 1752) with the checked load of
                             s + 160 between, the arguments of :142 and `jal set_state` (+0x2f4; s, S_WAKING, R_WAKE),
                             `li a0, 0`, then the e2 cut. Prop: wakeb_mid_stmt.
     e2    +0x2fc .. +0x31c  the frame's shadow bytes 4 .. 11 := 0xf8 (e2 out of scope), then the release cut.
                             Prop: wakeb_e2_stmt.
     rel   +0x320 .. +0x3f8  the header word 0x45e0360e at the frame, `beqz s2` not taken, the frame's 16 shadow bytes
                             := 0xf5, the flag pointer from the frame's last word (F + 120), the store of 0 at it (the
                             release), `j +0x3c0`, sp = s0 - 128, the 12 reloads, sp = sp + 128, `ret`.
                             Prop: wakeb_rel_stmt.

   Each cut holds the caller's facts (wakeb_fix), the journal and the facts carried at the cut (wakeb_cur and the
   per-cut wakeb_mid_cur / wakeb_rel_cur), and the registers the code after the cut reads (wakeb_regs_core and its two
   extensions); each concludes the statement's post (diginet_session_wake_cg.v transport_wake_post) at the cut's pc.
   The e2 cut and the release cut carry the same state (wakeb_rel_cur): the eight shadow stores between them change no
   byte either state speaks of. The frame word at s1 + 16 (+0x0a0) and the zero word at the entry sp - 128 (+0x004)
   are read by no later instruction, so no cut carries them. The current heap frame and the read-only image bytes
   set_state reads are not carried either: the mid piece rebuilds them from wakeb_fix (trans_tframe_at,
   trans_tf_off_g, wake_apart, trans_rom_view_rd) through wakeb_cur's acall_kept_g. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
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

(* The three cut points and the return, as offsets from the listing's base. *)
Definition WAKEB_MID : Z := AF_diginet_session_wake + 0x224.
Definition WAKEB_E2 : Z := AF_diginet_session_wake + 0x2fc.
Definition WAKEB_REL : Z := AF_diginet_session_wake + 0x320.
Definition WAKEB_RET : Z := AF_diginet_session_wake + 0x3f8.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s10 (sd at sp + 120 ..
   sp + 32 after `addi sp, sp, -128`). *)
Definition WAKEB_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26)].
(* The class-1 frame's size, e2 at F + 32 (60 bytes) in it, and e2_len at sp1 + 24 in the machine frame. *)
Definition WAKEB_FBYTES : Z := 128.
Definition WAKEB_E2OFF : Z := 32.
Definition WAKEB_KLPOFF : Z := 24.
Lemma wakeb_fbytes : fs_frame_bytes WAKE_CID = WAKEB_FBYTES.
Proof. reflexivity. Qed.
(* The window relations the cuts need: the callees' windows fit inside the call's below a realigned sp at most 160
   below the entry sp, and ESTACK fits. *)
Lemma wakeb_stk_bounds :
  WAKE_STK = WAKE_FRAME + WAKE_ALIGN + SENDCTL_STK /\
  160 + SSTATE_STK <= WAKE_STK /\ 160 + SENDCTL_STK <= WAKE_STK + 16 /\ 160 + ESTACK <= WAKE_STK /\
  WAKE_FRAME = 128 /\ WAKE_ALIGN = 16.
Proof.
  unfold WAKE_STK, WAKE_FRAME, WAKE_ALIGN, SSTATE_STK, SENDCTL_STK, ESTACK.
  repeat split; vm_compute; try reflexivity; try discriminate.
Qed.
(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma wakeb_some_inv : forall (Bx By : list byte) (rx ry : Z), Some (Bx, rx) = Some (By, ry) -> Bx = By /\ rx = ry.
Proof.
  intros Bx By rx ry H. split.
  - exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H).
  - exact (f_equal (fun o => match o with Some (_, v) => v | None => rx end) H).
Qed.
Lemma wakeb_some_inv_u : forall (Bx By : list byte), Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma wakeb_cut_pcs :
  BASE + AF_diginet_session_wake = transportb_sigma TB_diginet_session_wake /\
  BASE + WAKEB_MID = 0x86c5c /\ BASE + WAKEB_E2 = 0x86d34 /\ BASE + WAKEB_REL = 0x86d58 /\
  BASE + WAKEB_RET = 0x86e30.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_diginet_session_wake_cg_holds_stmt that are
   not callee contracts, with gx_ok / gx_noerrno (DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno from the
   first two of the four trans_* record facts). *)
Definition wakeb_laws : Prop :=
  pc_stack_malloc (as_code B) WAKE_CID = transportb_sigma TB___asan_stack_malloc_1 /\
  transport_cells B /\ trans_wake_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\ trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B.

(* The caller's facts (the premises of transport_diginet_session_wake_cg at the entry registers regs), and what the
   head fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -128`, `andi sp, sp, -32`); pos,
   the slot of the class-1 frame the stack malloc gave; F, that frame's address. *)
Definition wakeb_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 WAKE_S /\ YK11.getr regs 11 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - WAKE_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.diginet_session_wake_m timg_B TF Bw now = Some (Bw', r) /\
  trans_tframe_at B lyc Sc W memc regs WAKE_STK TF /\
  trans_tf_off_g TF /\
  trans_rom_view_rd W memc /\
  wake_apart TF Bw /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
  count_cid WAKE_CID (frames Sc) < fs_frames WAKE_CID /\
  count_cid SENDCTL_CID (frames Sc) + 1 < fs_frames SENDCTL_CID /\
  st_nev S + k + WAKE_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - WAKE_FRAME) / 32) /\
  F = frame_addr lyc WAKE_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + WAKEB_FBYTES <= alloc_ceiling /\ in_app F WAKEB_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range wake_wr Bw); the 12 saved words below the entry sp; the frame's last word, the address of its flag
   byte (astack_malloc_realizes' rdword). *)
Definition wakeb_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= WAKE_EV /\
  frames S2 = (WAKE_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) WAKEB_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + WAKEB_FBYTES - 8) = Some (flag_addr lyc WAKE_CID pos).

(* The state at the release cut (+0x320) and at the e2 cut (+0x2fc): wakeb_cur, and the post's X already holds (the
   world relation at the model's world Bw' and g_fail_next Bw' <= 1); a0 holds the model's result, in
   wakeb_regs_rel. *)
Definition wakeb_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  wakeb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The state at the mid cut (+0x224), reached from the head when send_control answered r >= 0: its world B1 and the
   60 bytes e2 it built, what it kept of the model's world (the keep lemma), the bytes at e2 and at e2_len in the
   machine frame, the read facts of e2's range (__asan_memcpy's source check), and the branch the model took. *)
Definition wakeb_mid_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (TF : option TI.tframe) (Bw B1 e2 : list byte) (rs : Z) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  wakeb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  TW.S_desk_known Bw <> 0 /\ TW.S_foreign Bw = 0 /\
  TSS.send_control_m timg_B TF (wake_w1 Bw now) TS0.DIGINET_CMD_WAKE 0 = Some (B1, (rs, e2)) /\
  0 <= rs /\ length e2 = 60%nat /\
  TW.S_state B1 = TW.S_state Bw /\ TW.GOT_n B1 = TW.GOT_n Bw /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B1 /\ TW.g_fail_next B1 <= 1 /\
  garr8 segs (mrestrict (w_H W2) mem2) (F + WAKEB_E2OFF) (TW.zs e2) /\
  decode_rd_ok W2 mem2 (F + WAKEB_E2OFF) SENDCTL_F /\
  garr8 segs (mrestrict (w_H W2) mem2) (sp1 + WAKEB_KLPOFF) (TW.zs (TW.put 8 60)).

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s9 = the
   frame, s8 = the frame's shadow address, and s11, which image B's code neither saves nor writes, so it reaches the
   return as the caller's. *)
Definition wakeb_regs_core (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 24 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 25 = w64 F /\
  YK11.getr regs2 27 = YK11.getr regs 27.
(* The e2 and release cuts also carry the model's result in a0. *)
Definition wakeb_regs_rel (regs regs2 : bvmap 5 word) (sp1 F r : Z) : Prop :=
  wakeb_regs_core regs regs2 sp1 F /\ YK11.getr regs2 10 = w64 r.
(* The mid cut also reads s3 = now, s4 = s, s5 = s + 18224 (g_s.stats.tx_wakes), s6 = e2 and s10 = the shadow
   base. *)
Definition wakeb_regs_mid (regs regs2 : bvmap 5 word) (sp1 F now : Z) : Prop :=
  wakeb_regs_core regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 now /\ YK11.getr regs2 20 = w64 WAKE_S /\
  YK11.getr regs2 21 = w64 (WAKE_S + (TW.A_S_stats_tx_wakes - TW.OFF_g_s)) /\
  YK11.getr regs2 22 = w64 (F + WAKEB_E2OFF) /\ YK11.getr regs2 26 = w64 SHADOW_OFF.

(* The release cut, +0x320: from the state wakeb_rel_cur, the post. *)
Definition wakeb_rel_at : Prop :=
  wakeb_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    wakeb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    wakeb_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    wakeb_regs_rel regs regs2 sp1 F r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKEB_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_wake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The e2 cut, +0x2fc: the same state, eight shadow stores earlier. *)
Definition wakeb_e2_at : Prop :=
  wakeb_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    wakeb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    wakeb_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    wakeb_regs_rel regs regs2 sp1 F r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKEB_E2)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_wake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The mid cut, +0x224: from the state wakeb_mid_cur, the post; the memcpy and set_state contracts are its callees'. *)
Definition wakeb_mid_at : Prop :=
  wakeb_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' B1 e2 : list byte) (rs : Z) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    wakeb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    wakeb_mid_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now TF Bw B1 e2 rs pos sp1 F
      ly2 S2 W2 mem2 md2 e ->
    wakeb_regs_mid regs regs2 sp1 F now ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKEB_MID)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_wake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The four pieces. rel: +0x320 .. the return. e2: +0x2fc .. +0x31c, then the release cut. mid: +0x224 .. +0x2f8,
   then the e2 cut. head: the entry .. +0x220, then the release cut (the two early exits and the refused path), the e2
   cut (send_control answered r < 0) or the mid cut. *)
Definition wakeb_rel_stmt : Prop := wakeb_rel_at.
Definition wakeb_e2_stmt : Prop := wakeb_rel_at -> wakeb_e2_at.
Definition wakeb_mid_stmt : Prop := wakeb_e2_at -> wakeb_mid_at.
Definition wakeb_head_stmt : Prop :=
  wakeb_mid_at -> wakeb_e2_at -> wakeb_rel_at -> @transport_diginet_session_wake_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma wakeb_holds_of : wakeb_head_stmt -> wakeb_mid_stmt -> wakeb_e2_stmt -> wakeb_rel_stmt ->
  @transport_diginet_session_wake_cg_holds_stmt fx rc B MT.
Proof.
  intros HEAD MID E2 REL.
  pose proof (E2 REL) as E2a.
  exact (HEAD (MID E2a) E2a REL).
Qed.
End cut.
