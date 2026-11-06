(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module paths and module names changed; 141 of its 208 lines of code are new or changed and 376 lines of the source are left out. *)
(* diginet_session_close_segs: the cuts of the walk of diginet_session_close (fuzz_transport.asan 0x8713c =
   transport_sigma TS_diginet_session_close, AF_diginet_session_close = 0x5ed8 of lib/A/Prog/DgnTransportList.v), as
   STATEMENTS only, and the composition close_holds_of: the statement transport_diginet_session_close_cg_holds_stmt of
   lib/A/Prog/diginet_session_close_cg.v from the five piece Props. The walk holds the CALLER's G journal
   (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) from the entry to the return, with (CLOSE_CID, pos) :: own while
   the class-2 frame is live. The pieces:
     head  +0x000 .. +0x184  the frame (`addi sp, sp, -160`), the zero word at sp, the 13 saves, s0, the realign into
                             s1, the two runtime cells (the flag word 1, so `beqz a2` is not taken), s9 = the shadow
                             base, s3 = s, `jal __asan_stack_malloc_2` (+0x06c; lib/A/Prog/TransportGFrame.v
                             gx_stack_malloc_at), s2 = s8 = the frame, `bnez s2` taken, the frame word at s1 + 48, the
                             frame's header and its 20 shadow bytes (s7 = their address), `beqz s3` not taken, the checked
                             loads of s + 116, s + 136 and s + 112 (s5 = s + 112) and the three tests of :153 (close_go):
                             close_go Bw = false runs `mv a3, zero` (+0x188) to the join cut (close_join_at), else the
                             send cut (close_send_at). Prop: close_head_stmt.
     send  +0x3c4 .. +0x3e0  a1 = 0xe3, a0 = s3, a2 = a3 = a4 = 0, `jal send_control` (+0x3d8; send_control_cg.v
                             transport_send_control_cg, a G-form callee in the same G journal), a3 = a0, `j` to the
                             join cut. Prop: close_send_stmt.
     join  +0x18c .. +0x1bc  the checked store of 0 at s + 212 (close_w1 B1), s10 = the shadow address of s + 112, the
                             checked load of s11 = S_state (close_w1 B1), s4 = 3 and `beq s11, s4`: S_CLOSED goes to the
                             release cut (close_rel_at), any other state to the notice cut (close_ntc_at).
                             Prop: close_join_stmt.
     ntc   +0x1c0 .. +0x28c  the 8-byte store of a3 at s1 + 24, s6 = p = frame + 32, the notice's shadow bytes 4 .. 12
                             := 0, `jal __asan_memset` (+0x1f8; p + 16, 0, 56), the stores of 0x0000000300000002 (8 bytes)
                             at p, of s11 at p + 8 and of 8 at p + 12, the checked store of 3 at s + 112 (close_w2 B1),
                             the checked loads of s + 96 (notify) and s + 104 (ctx), `jalr a2` (+0x258: notice at
                             TI.ti_notice timg_A), the shadow bytes 4 .. 12 := 0xf8, a3 = the 8-byte load at s1 + 24,
                             `j` to the release cut. Prop: close_ntc_stmt.
     rel   +0x290 .. +0x3c0  the header word 0x45e0360e at the frame, `beqz s2` not taken, the frame's 32 shadow bytes
                             := 0xf5, the flag pointer from the frame's last word, the store of 0 at it (the release:
                             TransportGFrame.v gx_flag_store_pi), `j +0x380`, a0 = a3, sp = s0 - 160, the 13 reloads,
                             sp = sp + 160, `ret`. Prop: close_rel_stmt.
   Each cut holds the caller's facts (close_fix), the journal and the facts carried at the cut (close_send_cur,
   close_join_cur, close_ntc_cur, close_rel_cur, each over close_cur), the registers the code after the cut reads
   (close_regs_send, close_regs_join, close_regs_ntc, close_regs_rel), and concludes the statement's post
   (diginet_session_close_cg.v transport_close_post) at the cut's pc. The world at the join cut is B1 with
   close_sent timg_A TF Bw = Some (B1, r): send_control's world when close_go Bw holds, else Bw (and r = 0). The frame
   word the head stores at s1 + 48 (+0x0a0) and the zero word at the entry sp - 160 (+0x004) are read by no later
   instruction, so no cut carries them. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The four cut points, as offsets from the listing's base: the send path's first instruction (`li a1, 0xe3`, the
   target of `bne a0, a1` at +0x184), the join (`addi a0, s3, 0xd4`: the instruction after `mv a3, zero` at +0x188 and
   the target of the send path's `j` at +0x3e0), the notice path's first instruction (`sd a3, 24(s1)`, the
   fall-through of `beq s11, s4` at +0x1bc) and the release (`lui a0, 0x45e03`, the target of that branch and of the
   notice path's `j` at +0x288). *)
Definition CLOSE_SEND : Z := AF_diginet_session_close + 0x3c4.
Definition CLOSE_JOIN : Z := AF_diginet_session_close + 0x18c.
Definition CLOSE_NTC : Z := AF_diginet_session_close + 0x1c0.
Definition CLOSE_REL : Z := AF_diginet_session_close + 0x290.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 152 ..
   sp + 56 after `addi sp, sp, -160`). *)
Definition CLOSE_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-2 frame's size. *)
Definition CLOSE_FBYTES : Z := 256.
Lemma close_fbytes : fs_frame_bytes CLOSE_CID = CLOSE_FBYTES.
Proof. reflexivity. Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma close_cut_pcs :
  BASE + AF_diginet_session_close = transport_sigma TS_diginet_session_close /\ BASE + CLOSE_SEND = 0x87500 /\
  BASE + CLOSE_JOIN = 0x872c8 /\ BASE + CLOSE_NTC = 0x872fc /\ BASE + CLOSE_REL = 0x873cc.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_diginet_session_close_cg_holds_stmt that
   are not callee contracts, then gx_ok and gx_noerrno of G (DgnTransportCg.v G_HARNESS_gx_ok and
   G_HARNESS_gx_noerrno give them from trans_g_unowned and trans_g_no_errno). *)
Definition close_laws : Prop :=
  pc_stack_malloc (as_code B) CLOSE_CID = transport_sigma TS___asan_stack_malloc_2 /\
  transport_cells B /\ trans_close_cells B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS /\
  trans_g_unowned B /\ trans_g_no_errno B.

(* The caller's facts (the premises of transport_diginet_session_close_cg at the entry registers regs), and what the
   head fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -160`, `andi sp, sp, -32`); pos,
   the slot of the class-2 frame the stack malloc gave; F, the frame's address. *)
Definition close_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 CLOSE_S /\ YK11.getr regs 11 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - CLOSE_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.diginet_session_close_m timg_A TF Bw now = Some (Bw', r) /\
  trans_tframe_at B lyc Sc W memc regs CLOSE_STK TF /\
  trans_rom_view_rd W memc /\
  close_apart TF Bw /\
  trans_tf_off_g TF /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
  count_cid CLOSE_CID (frames Sc) + 2 < fs_frames CLOSE_CID /\
  st_nev S + k + CLOSE_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - CLOSE_FRAME) / 32) /\
  F = frame_addr lyc CLOSE_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + CLOSE_FBYTES <= alloc_ceiling /\ in_app F CLOSE_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range close_wr TF Bw); the 13 saved words below the entry sp; the frame's last word, the address of its
   flag byte (astack_malloc_realizes' rdword). *)
Definition close_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((CLOSE_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= CLOSE_EV /\
  frames S2 = (CLOSE_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + CLOSE_FBYTES - 8) = Some (flag_addr lyc CLOSE_CID pos).

(* The state at the send cut (+0x3c4), reached from the head only, when close_go Bw holds: the layout, the world and
   the event count are the call's; the blocks are the call's exactly (the stack malloc changes st_fs only); the memory
   relates to the world Bw (no store of the head reaches G). *)
Definition close_send_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw : list byte) (pos F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  close_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  tw_at TMAP_A (aview segs (w_H W) mem2) Bw /\
  close_go Bw = true.

(* The state at the join cut (+0x18c), from the head (close_go Bw false: B1 = Bw, r = 0, the call's layout, world
   and event count) or after send_control returns: close_cur; the model's send (close_sent) gave B1 and r; the memory
   relates to the world B1; g_fail_next B1 <= 1. *)
Definition close_join_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw B1 : list byte) (r pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  close_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2 W2 mem2 md2 e /\
  close_sent timg_A TF Bw = Some (B1, r) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) B1 /\ TW.g_fail_next B1 <= 1.

(* The state at the notice cut (+0x1c0), from the join only: the memory relates to the world close_w1 B1 (after the
   store at s + 212), whose state the code loaded and found not S_CLOSED. *)
Definition close_ntc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw B1 : list byte) (r pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  close_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2 W2 mem2 md2 e /\
  close_sent timg_A TF Bw = Some (B1, r) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (close_w1 B1) /\ TW.g_fail_next B1 <= 1 /\
  TW.S_state (close_w1 B1) <> TS0.DIGINET_S_CLOSED.

(* The state at the release cut (+0x290), from the join (S_CLOSED: Bw' = close_w1 B1) or after notice returns:
   close_cur, and the post's X but a0 already holds: the world relation at the model's world Bw' and
   g_fail_next Bw' <= 1. *)
Definition close_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  close_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The registers every cut holds: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s8 = the frame, s7 = the frame's
   shadow address. *)
Definition close_regs_base (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 23 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 24 = w64 F.
(* The release also reads a3 = r. *)
Definition close_regs_rel (regs regs2 : bvmap 5 word) (r sp1 F : Z) : Prop :=
  close_regs_base regs regs2 sp1 F /\ YK11.getr regs2 13 = w64 r.
(* The send path reads s3 = s, and hands on s5 = s + 112 and s9 = the shadow base to the join. *)
Definition close_regs_send (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  close_regs_base regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 CLOSE_S /\ YK11.getr regs2 21 = w64 (CLOSE_S + 112) /\ YK11.getr regs2 25 = w64 SHADOW_OFF.
(* The join reads s3, s5, s9 and hands on a3 = r. *)
Definition close_regs_join (regs regs2 : bvmap 5 word) (r sp1 F : Z) : Prop :=
  close_regs_send regs regs2 sp1 F /\ YK11.getr regs2 13 = w64 r.
(* The notice path also reads s3 = s, s4 = 3, s9 = the shadow base, s10 = the shadow address of s + 112 and s11 =
   the state the code loaded (`lw`: sign-extended). *)
Definition close_regs_ntc (regs regs2 : bvmap 5 word) (r : Z) (B1 : list byte) (sp1 F : Z) : Prop :=
  close_regs_rel regs regs2 r sp1 F /\
  YK11.getr regs2 19 = w64 CLOSE_S /\ YK11.getr regs2 20 = w64 3 /\
  YK11.getr regs2 25 = w64 SHADOW_OFF /\ YK11.getr regs2 26 = w64 (SHADOW_OFF + (CLOSE_S + 112) / 8) /\
  YK11.getr regs2 27 = w64 (TW.S_state (close_w1 B1)).

(* The release cut, +0x290: from the state close_rel_cur, the post. *)
Definition close_rel_at : Prop :=
  close_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    close_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    close_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    close_regs_rel regs regs2 r sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_close_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The notice cut, +0x1c0: from the state close_ntc_cur, the post; the memset and notice contracts are its callees'. *)
Definition close_ntc_at : Prop :=
  close_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' B1 : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    close_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    close_ntc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw B1 r pos F ly2 S2 W2 mem2 md2 e ->
    close_regs_ntc regs regs2 r B1 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_NTC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_close_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The join cut, +0x18c: from the state close_join_cur, the post; the notice path's callees are its callees'. *)
Definition close_join_at : Prop :=
  close_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' B1 : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    close_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    close_join_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw B1 r pos F ly2 S2 W2 mem2 md2 e ->
    close_regs_join regs regs2 r sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_JOIN)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_close_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The send cut, +0x3c4: from the state close_send_cur, the post; send_control's contract and the join's callees. *)
Definition close_send_at : Prop :=
  close_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transport_sigma TS_send_control)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate) (mem2 : word -> option byte)
         (md2 : Model) (regs2 : bvmap 5 word),
    close_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    close_send_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F S2 mem2 md2 ->
    close_regs_send regs regs2 sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_SEND)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_close_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The five pieces. rel: +0x290 .. the return. ntc: +0x1c0 .. +0x28c, then the release cut. join: +0x18c .. +0x1bc,
   then the release or the notice cut. send: +0x3c4 .. +0x3e0, then the join cut. head: the entry .. +0x188, then the
   send or the join cut. *)
Definition close_rel_stmt : Prop := close_rel_at.
Definition close_ntc_stmt : Prop := close_rel_at -> close_ntc_at.
Definition close_join_stmt : Prop := close_ntc_at -> close_rel_at -> close_join_at.
Definition close_send_stmt : Prop := close_join_at -> close_send_at.
Definition close_head_stmt : Prop :=
  close_send_at -> close_join_at -> @transport_diginet_session_close_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma close_holds_of : close_head_stmt -> close_send_stmt -> close_join_stmt -> close_ntc_stmt -> close_rel_stmt ->
  @transport_diginet_session_close_cg_holds_stmt fx rc B MT.
Proof.
  intros HEAD SEND JOIN NTC REL.
  pose proof (JOIN (NTC REL) REL) as J.
  exact (HEAD (SEND J) J).
Qed.
End cut.
