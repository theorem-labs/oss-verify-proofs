(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 397 of its 445 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBCut.v, with its module paths and module names changed; 402 of its 478 lines of code are new or changed and 369 lines of the source are left out. *)
(* TickCutB: the cuts of the walk of diginet_session_tick on fuzz_transport.asan-ubsan (0x8909c = transportb_sigma
   TB_diginet_session_tick, AF_diginet_session_tick = 0x7dfc of lib/B/Prog/DgnTransportBList.v, 660 words), as
   STATEMENTS only, and the composition tick_holds_of: the statement transport_diginet_session_tick_cg_holds_stmt of
   lib/B/Prog/diginet_session_tick_cg.v from the eleven piece Props. It is image B's twin of lib/A/Prog/TickCut.v: the
   same cuts at image B's pcs, registers and names, and one more cut (lost) where image B calls set_state. The walk
   holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) from the entry to the return,
   with (TICK_CID, pos) :: own while the class-5 frame is live. The pieces (offsets from the entry; each cut is the
   first instruction of its block):
     head   +0x000 .. +0x1c4, +0x24c .. +0x25c  the frame, the 13 saves, s0, the realign into s1, now at s1 + 56, the
                         two runtime cells, s8 = the shadow base, s4 = s, `jal __asan_stack_malloc_5` (+0x070), the
                         frame word at s1 + 64, the frame's header, its shadow bytes 0 .. 19, s6, `jal
                         __asan_set_shadow_f8` (+0x13c), the right guard, `beqz s4` (not taken), the UBSan alignment
                         check of s (+0x194, not taken), s7 = s + 112, s5 = its shadow address, s9 = S_state Bw, s10 = 0
                         and the state dispatch. Exits: S_WAKING to wake, S_ONLINE to online, S_IDLE / S_CLOSED to epi
                         (s10 = 0), any other state to step. Prop: tick_head_stmt.
     wake   +0x1c8 .. +0x240  the wake timeout test; no timeout to step; else the stores of 0 at s + 212, s + 168,
                         a2 = 6 and `j` to lost. Prop: tick_wake_stmt.
     online +0x260 .. +0x2a0, +0x444 .. +0x474  the silence test; no silence to step; else the stores of 0 at s + 212,
                         s + 168, a2 = 4, falling into lost. Prop: tick_online_stmt.
     lost   +0x478 .. +0x484, +0x604  a0 = s, a1 = 0, `jal set_state` (+0x480), `j` +0x604 (s10 = 0), to epi.
                         Prop: tick_lost_stmt.
     step   +0x2a4 .. +0x348  t0 = s + 212, t1 = its shadow address, the inflight test (a7 = s + 18144 before it), the
                         ack-timeout test, the retry test, t0 and t1 saved at s1 + 48 and s1 + 40. Exits: no inflight
                         or no timeout to tail, retries left to retx, else to ackl. Prop: tick_step_stmt.
     retx   +0x34c .. +0x440, +0x594 .. +0x5bc  retransmit's stores with the two UBSan pointer-overflow checks (+0x364,
                         +0x388, not taken), `jalr a4` +0x424 = io_send, t0 / t1 / a7 back; a negative result to epi
                         (s10 = r), else (after stats.tx_frames on 0) to tail. Prop: tick_retx_stmt.
     ackl   +0x488 .. +0x590  the store of 0 at s + 212, stats.ack_lost, the notice at frame + 32 (memset +0x4f0,
                         `jalr a2` +0x558 = notice), a7 / t0 / t1 back, to tail. Prop: tick_ackl_stmt.
     tail   +0x5c0 .. +0x600, +0x678 .. +0x694, +0x604  the state / inflight / backoff tests (+0x604: s10 = 0, to epi),
                         the keepalive test (a3, a4 for ka). Exits: epi, ka, queue. Prop: tick_tail_stmt.
     ka     +0x714 .. +0x7a4  ka's shadow byte, next_keepalive_us, stats.tx_keepalives, `jal send_data` +0x794,
                         s10 = its result, to epi. Prop: tick_ka_stmt.
     queue  +0x698 .. +0x710, +0x7a8 .. +0x840  the queued test (0 runs +0x604, s10 = 0, to epi), the display test,
                         `jal __asan_set_shadow_00` +0x7b8, `jal take` +0x7d8, the display stores, `jal send_data`
                         +0x824, `jal __asan_set_shadow_f8` +0x83c, to epi. Prop: tick_queue_stmt.
     epi    +0x608 .. +0x674  the header word, `beqz s2` (not taken), `jal __asan_stack_free_5` +0x620, a0 = s10,
                         sp = s0 - 192, the 13 reloads, sp = sp + 192, `ret`. Prop: tick_epi_stmt.
   Each cut holds the caller's facts (tick_fix), the journal and the facts carried at the cut (tick_cur and its
   refinements), the registers the code after the cut reads or must hand on (the tick_regs_ predicates), and
   concludes the statement's post (diginet_session_tick_cg.v transport_tick_post) at the cut's pc. The cuts before the
   first program callee (wake, online, lost, step, retx, ackl) are at the call's world W and layout lyc: there the
   pieces that call set_state (lost) or notice (ackl) derive TF's trans_tframe_at at the call from the entry's. The
   frame word at s1 + 64 and the zero word at the entry sp - 192 are read by no later instruction, so no cut carries
   them. Every _at takes the record facts (tick_laws) and the whole callee bundle (tick_callees: the ten contracts of
   the holds statement, in its order): a piece's continuation is a later _at, which asks the contracts of the pieces
   after it. The image-free definitions of lib/A/Prog/TickCut.v (tick_runinv, tick_ka_w, tick_queue_m, tick_some_inv,
   TICK_SAVED, TICK_FBYTES) are Required from it and named here by abbreviations, not restated. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut.
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
Module TCA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TickCut.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The image-free definitions of lib/A/Prog/TickCut.v, by their names there: the run invariants (1), (2), (4) and (5)
   at a world (tick_runinv), the keepalive's world (tick_ka_w), the model's rest at the queue cut (tick_queue_m), the
   result read off an equation of two results without injection (tick_some_inv), the class-5 frame's size
   (TICK_FBYTES), and the words the prologue saves (TICK_SAVED: image B's prologue, 0x890a4 - 0x890d4, saves ra, s0,
   s1, s2 .. s11 at the same distances below the entry sp as image A's). *)
Abbreviation tick_runinv := TCA.tick_runinv.
Abbreviation tick_ka_w := TCA.tick_ka_w.
Abbreviation tick_queue_m := TCA.tick_queue_m.
Abbreviation tick_some_inv := TCA.tick_some_inv.
Abbreviation TICK_FBYTES := TCA.TICK_FBYTES.
Abbreviation TICK_SAVED := TCA.TICK_SAVED.

(* The ten cut points, as offsets from the listing's base:
   wake   `addi a1, s4, 0x98`  the fall-through of `bne s9, a0` at +0x1c4 (s9 = 1);
   online `addi a1, s4, 0xb0`  the target of `beq s9, a0` at +0x250 (s9 = 2);
   lost   `mv a0, s4`          the target of `j` at +0x240 (wake's lost arm, a2 = 6) and the fall-through of +0x474
                               (online's lost arm, a2 = 4);
   step   `addi t0, s4, 0xd4`  the target of +0x1c4 (s9 < 0), +0x208 (no wake timeout) and +0x258 (s9 >= 4), and the
                               fall-through of `bgeu` at +0x2a0 (no silence);
   retx   `lb a2, 0(a4)`       the fall-through of `bgeu t2, a2` at +0x348 (retries left);
   ackl   `lb a0, 0(t1)`       the target of that branch;
   tail   `lb a0, 0(s5)`       the target of +0x2c8, +0x30c, +0x43c, +0x590 and the fall-through of +0x5bc;
   queue  `srli a0, a7, 3`     the fall-through of `bgeu a1, a4` at +0x694;
   ka     `addi a1, s11, 0x90` the target of that branch;
   epi    `lui a0, 0x45e03`    the join of every return path (+0x1bc, +0x25c, +0x440, +0x7a4, +0x840, and the
                               fall-through of +0x604, which lost, tail and queue reach; +0x248, the s = 0 arm, is not
                               run). *)
Definition TICK_WAKE : Z := AF_diginet_session_tick + 0x1c8.
Definition TICK_ONLINE : Z := AF_diginet_session_tick + 0x260.
Definition TICK_LOST : Z := AF_diginet_session_tick + 0x478.
Definition TICK_STEP : Z := AF_diginet_session_tick + 0x2a4.
Definition TICK_RETX : Z := AF_diginet_session_tick + 0x34c.
Definition TICK_ACKL : Z := AF_diginet_session_tick + 0x488.
Definition TICK_TAIL : Z := AF_diginet_session_tick + 0x5c0.
Definition TICK_QUEUE : Z := AF_diginet_session_tick + 0x698.
Definition TICK_KA : Z := AF_diginet_session_tick + 0x714.
Definition TICK_EPI : Z := AF_diginet_session_tick + 0x608.
Lemma tick_fbytes : fs_frame_bytes TICK_CID = TICK_FBYTES.
Proof. reflexivity. Qed.

(* ---- the model at the cuts (diginet_session_tick_cg.v tick_model, tick_step, tick_tail) ---- *)

(* What remains at the step cut: the step of :430-443, then the tail unless the step returned. *)
Definition tick_go (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z) : option (list byte * Z) :=
  match tick_step I F Bw now with
  | None => None
  | Some (inl (B, r)) => Some (B, r)
  | Some (inr B) => tick_tail I F B now
  end.
(* What remains at the retx cut: retransmit (:432), its negative result returned (:433-434), else the tail. *)
Definition tick_retx_m (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z) : option (list byte * Z) :=
  match TSS.retransmit_m I F Bw now with
  | None => None
  | Some (B, r) => if r <? 0 then Some (B, r) else tick_tail I F B now
  end.
(* What remains at the ackl cut: the ack-lost notice at tick_ack_w1 Bw (:436-441), then the tail. *)
Definition tick_ackl_m (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z) : option (list byte * Z) :=
  match TSS.call_notify I F (tick_ack_w1 Bw) (tick_ack_ntc Bw) with
  | None => None
  | Some (B, _) => tick_tail I F B now
  end.
(* What remains at the lost cut: a lost arm of tick_model (session_lost_m at Bw with why, :422 / :426), returning
   DIGINET_OK. *)
Definition tick_lost_m (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (why : Z) : option (list byte * Z) :=
  match TSS.session_lost_m I F Bw why with
  | None => None
  | Some (B, _) => Some (B, DLib.DIGINET_OK)
  end.

(* tick_model at the wake and online cuts, in the terms of the cuts after them (lost or step). *)
Lemma tick_model_wake : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z),
  TW.S_state Bw = TS0.DIGINET_S_WAKING ->
  TSS.diginet_session_tick_m I F Bw now =
  if TS0.ms_m (TW.S_cfg_wake_timeout_ms Bw) <=? TS0.u64 (now - TW.S_wake_sent_us Bw)
  then tick_lost_m I F Bw TS0.DIGINET_R_WAKE_TIMEOUT else tick_go I F Bw now.
Proof.
  intros I F Bw now Hs. rewrite tick_model. cbv zeta. rewrite Hs.
  assert (E1 : (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_CLOSED) || (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_IDLE) = false)
    by reflexivity.
  assert (E2 : (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_WAKING) = true) by reflexivity.
  assert (E3 : (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_ONLINE) = false) by reflexivity.
  rewrite E1, E2, E3. cbn [andb].
  destruct (TS0.ms_m (TW.S_cfg_wake_timeout_ms Bw) <=? TS0.u64 (now - TW.S_wake_sent_us Bw));
    [unfold tick_lost_m | unfold tick_go]; reflexivity.
Qed.
Lemma tick_model_online : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z),
  TW.S_state Bw = TS0.DIGINET_S_ONLINE ->
  TSS.diginet_session_tick_m I F Bw now =
  if TS0.ms_m (TW.S_cfg_offline_ms Bw) <=? TS0.u64 (now - TW.S_last_rx_us Bw)
  then tick_lost_m I F Bw TS0.DIGINET_R_SILENCE else tick_go I F Bw now.
Proof.
  intros I F Bw now Hs. rewrite tick_model. cbv zeta. rewrite Hs.
  assert (E1 : (TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_CLOSED) || (TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_IDLE) = false)
    by reflexivity.
  assert (E2 : (TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_WAKING) = false) by reflexivity.
  assert (E3 : (TS0.DIGINET_S_ONLINE =? TS0.DIGINET_S_ONLINE) = true) by reflexivity.
  rewrite E1, E2, E3. cbn [andb].
  destruct (TS0.ms_m (TW.S_cfg_offline_ms Bw) <=? TS0.u64 (now - TW.S_last_rx_us Bw));
    [unfold tick_lost_m | unfold tick_go]; reflexivity.
Qed.
(* The lost cut's model fact read as set_state's (slost_model_sstate): the call's model premise and the arm's
   result DIGINET_OK. *)
Lemma tick_lost_inv : forall (I : TI.timg) (F : option TI.tframe) (Bw Bw' : list byte) (why r : Z),
  tick_lost_m I F Bw why = Some (Bw', r) ->
  TSS.set_state_m I F (slost_w1 Bw) TS0.DIGINET_S_IDLE why = Some (Bw', tt) /\ r = DLib.DIGINET_OK.
Proof.
  intros I F Bw Bw' why r H. unfold tick_lost_m in H. rewrite slost_model_sstate in H.
  destruct (TSS.set_state_m I F (slost_w1 Bw) TS0.DIGINET_S_IDLE why) as [[B1 u]|]; [|discriminate H].
  destruct (tick_some_inv B1 Bw' DLib.DIGINET_OK r H) as [E1 E2].
  destruct u. split; [rewrite E1; reflexivity | symmetry; exact E2].
Qed.
(* tick_go and tick_tail by branch, in the terms of the cuts after them. *)
Lemma tick_go_eq : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (now : Z),
  tick_go I F Bw now =
  if negb (TW.S_inflight Bw =? 0) &&
     (TS0.ms_m (TW.S_cfg_ack_timeout_ms Bw) <=? TS0.u64 (now - TW.S_inflight_sent_us Bw)) then
    if TW.S_inflight_retries Bw <? TW.S_cfg_max_retries Bw then tick_retx_m I F Bw now else tick_ackl_m I F Bw now
  else tick_tail I F Bw now.
Proof.
  intros I F Bw now. unfold tick_go, tick_step, tick_retx_m, tick_ackl_m.
  destruct (negb (TW.S_inflight Bw =? 0) &&
            (TS0.ms_m (TW.S_cfg_ack_timeout_ms Bw) <=? TS0.u64 (now - TW.S_inflight_sent_us Bw))); [|reflexivity].
  destruct (TW.S_inflight_retries Bw <? TW.S_cfg_max_retries Bw).
  - destruct (TSS.retransmit_m I F Bw now) as [[B0 r0]|]; [destruct (r0 <? 0)|]; reflexivity.
  - destruct (TSS.call_notify I F (tick_ack_w1 Bw) (tick_ack_ntc Bw)) as [[B0 u]|]; reflexivity.
Qed.
Lemma tick_tail_eq : forall (I : TI.timg) (F : option TI.tframe) (B : list byte) (now : Z),
  tick_tail I F B now =
  if negb (TW.S_state B =? TS0.DIGINET_S_ONLINE) || negb (TW.S_inflight B =? 0) ||
     (now <? TW.S_backoff_until_us B) then Some (B, DLib.DIGINET_OK)
  else if TW.S_next_keepalive_us B <=? now then TSS.send_data_m I F (tick_ka_w B now) [DSpec.b8 0] 1 now
  else tick_queue_m I F B now.
Proof. intros I F B now. unfold tick_tail, TCA.tick_ka_w, TCA.tick_queue_m. reflexivity. Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma tick_cut_pcs :
  BASE + AF_diginet_session_tick = transportb_sigma TB_diginet_session_tick /\
  BASE + TICK_WAKE = 0x89264 /\ BASE + TICK_ONLINE = 0x892fc /\ BASE + TICK_LOST = 0x89514 /\
  BASE + TICK_STEP = 0x89340 /\ BASE + TICK_RETX = 0x893e8 /\ BASE + TICK_ACKL = 0x89524 /\
  BASE + TICK_TAIL = 0x8965c /\ BASE + TICK_QUEUE = 0x89734 /\ BASE + TICK_KA = 0x897b0 /\
  BASE + TICK_EPI = 0x896a4.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_diginet_session_tick_cg_holds_stmt that are
   not callee contracts, and gx_ok / gx_noerrno of G_HARNESS_B (DgnTransportBCg.v G_HARNESS_gx_ok,
   G_HARNESS_gx_noerrno: the head gives them from trans_g_unowned and trans_g_no_errno). *)
Definition tick_laws : Prop :=
  pc_stack_malloc (as_code B) TICK_CID = transportb_sigma TB___asan_stack_malloc_5 /\
  transport_cells B /\ trans_tick_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B.

(* The callee contracts of the holds statement, all ten in its order (pc order of the first call):
   __asan_stack_malloc_5 (head), __asan_set_shadow_f8 (head, queue), io_send (retx), set_state (lost),
   __asan_memset (ackl), notice (ackl), __asan_stack_free_5 (epi), __asan_set_shadow_00 (queue), send_data (ka,
   queue), take (queue). The head builds the bundle from the statement's premises as they stand. *)
Definition tick_callees : Prop :=
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B TICK_CID) /\
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_f8) 0xf8) /\
  (forall fx' : YK11.FPState, @transport_io_send_cg fx' rc B MT (TI.ti_io_send timg_B)) /\
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) /\
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_B)) /\
  (forall fx' : YK11.FPState,
     @astack_free_cls_realizes fx' rc segs B (transportb_sigma TB___asan_stack_free_5) TICK_CID) /\
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_00) 0) /\
  (forall fx' : YK11.FPState, @transport_send_data_cg fx' rc B MT (transportb_sigma TB_send_data)) /\
  (forall fx' : YK11.FPState, @transport_take_cg fx' rc B MT (transportb_sigma TB_take)).

(* The caller's facts (the premises of transport_diginet_session_tick_cg at the entry registers regs, the four run
   invariants as tick_runinv Bw; the two index bounds beside (2) and (4) are not carried: no cut needs them, as on
   image A), and what the head fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -192`,
   `andi sp, sp, -32`); pos, the slot of the class-5 frame the stack malloc gave; F, the frame's address. *)
Definition tick_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 TICK_S /\ YK11.getr regs 11 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - TICK_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.diginet_session_tick_m timg_B TF Bw now = Some (Bw', r) /\
  trans_tframe_at B lyc Sc W memc regs TICK_STK TF /\
  trans_rom_view_rd W memc /\
  tick_apart TF Bw /\
  tick_runinv Bw /\
  count_cid TICK_CID (frames Sc) < fs_frames TICK_CID /\
  count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID /\
  count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID /\
  st_nev S + k + TICK_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - TICK_FRAME) / 32) /\
  F = frame_addr lyc TICK_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + TICK_FBYTES <= alloc_ceiling /\ in_app F TICK_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range tick_wr Bw); the 13 saved words below the entry sp; the frame's last word, the address of its flag
   byte (astack_malloc_realizes' rdword; __asan_stack_free_5's premise). *)
Definition tick_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= TICK_EV /\
  frames S2 = (TICK_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) TICK_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + TICK_FBYTES - 8) = Some (flag_addr lyc TICK_CID pos).

(* Every cut but lost and epi also carries now, stored at s1 + 56 (+0x048) and read back by every piece but lost and
   epi. *)
Definition tick_run_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (Bw : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  tick_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 56) = Some now.

(* The state at a cut before the first program callee and before any store into G (wake, online, step, retx, ackl),
   reached from the head, from wake or online without a store (no timeout), or from step: the layout, the world and
   the event count are the call's; the blocks are the call's exactly (the stack malloc changes st_fs only); every byte
   of G is the call's (no store into G yet: the stack malloc's acall_kept keeps G, TransportGCg.v
   gx_kept_of_acall_kept, and the head's own stores are in the frame, its shadow and the window); the memory relates
   to the world Bw. *)
Definition tick_pre_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (Bw : list byte) (pos sp1 F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  tick_run_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  gx_kept segs TG.G_HARNESS_B W memc W mem2 /\
  tw_at TMAP_B (aview segs (w_H W) mem2) Bw.

(* The words step saves at s1 + 48 (t0 = s + 212) and s1 + 40 (t1 = its shadow address) at +0x340 .. +0x344, which
   retx and ackl load back after their call. *)
Definition tick_t01_at (W2 : world segs) (mem2 : word -> option byte) (sp1 : Z) : Prop :=
  rdword (aview segs (w_H W2) mem2) (sp1 + 48) = Some (TICK_S + 212) /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 40) = Some (SHADOW_OFF + (TICK_S + 212) / 8).

(* The wake cut (+0x1c8) and the online cut (+0x260): the state the code loaded is S_WAKING / S_ONLINE. *)
Definition tick_wake_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (Bw : list byte) (pos sp1 F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  tick_pre_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 /\
  TW.S_state Bw = TS0.DIGINET_S_WAKING.
Definition tick_online_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (Bw : list byte) (pos sp1 F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  tick_pre_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 /\
  TW.S_state Bw = TS0.DIGINET_S_ONLINE.

(* The lost cut (+0x478), reached from wake (why = R_WAKE_TIMEOUT) or online (why = R_SILENCE) after the two stores
   of 0 at s + 212 and s + 168 (:162-163): the layout, the world and the event count are still the call's (no program
   callee yet), the blocks the call's exactly; every byte of G outside tick_wr Bw is the call's (the two stores are
   rows of tick_wr: TransportGCg.v gx_kept_ex, which image A's TickSrcKit.v trans_tframe_at_top, read at image B,
   takes for set_state's TF); the memory relates to slost_w1 Bw; the model's result is the lost arm's (tick_lost_m;
   tick_lost_inv reads it as set_state's premise and r = DIGINET_OK). now is not read after this cut. *)
Definition tick_lost_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos F why : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  tick_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  gx_kept_ex segs TG.G_HARNESS_B (tick_wr Bw) W memc W mem2 /\
  tw_at TMAP_B (aview segs (w_H W) mem2) (slost_w1 Bw) /\
  (why = TS0.DIGINET_R_WAKE_TIMEOUT \/ why = TS0.DIGINET_R_SILENCE) /\
  tick_lost_m timg_B TF Bw why = Some (Bw', r).

(* The step cut (+0x2a4): the dispatch of :418-427 chose neither a return nor a lost arm, so the model's result is
   tick_go's. *)
Definition tick_step_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  tick_pre_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 /\
  tick_go timg_B TF Bw now = Some (Bw', r).

(* The retx cut (+0x34c): t0 / t1 saved; the inflight frame is pending (S_inflight Bw <> 0, which neither retransmit
   nor io_send writes: TOpsKeep.v send_raw_m_keep), and the model's result is tick_retx_m's. *)
Definition tick_retx_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  tick_pre_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 /\
  tick_t01_at W mem2 sp1 /\
  TW.S_inflight Bw <> 0 /\
  tick_retx_m timg_B TF Bw now = Some (Bw', r).

(* The ackl cut (+0x488): t0 / t1 saved, and the model's result is tick_ackl_m's. *)
Definition tick_ackl_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  tick_pre_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 /\
  tick_t01_at W mem2 sp1 /\
  tick_ackl_m timg_B TF Bw now = Some (Bw', r).

(* The tail cut (+0x5c0), reached from step (B0 = Bw), retx (after io_send) or ackl (after notice): the memory relates
   to the world B0, g_fail_next B0 <= 1, the model's result is tick_tail's at B0, and when the inflight frame is done
   (S_inflight B0 = 0, the only case in which the tail calls take or send_data) the four run invariants hold at B0.
   From retx the guard is false (S_inflight B0 = S_inflight Bw <> 0). *)
Definition tick_tail_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' B0 : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  tick_run_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B0 /\ TW.g_fail_next B0 <= 1 /\
  tick_tail timg_B TF B0 now = Some (Bw', r) /\
  (TW.S_inflight B0 = 0 -> tick_runinv B0).

(* The keepalive cut (+0x714): the tail's tests passed (so S_inflight B0 = 0 and the invariants hold), and the model's
   result is send_data's at the keepalive's world (tick_tail_eq). *)
Definition tick_ka_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' B0 : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  tick_run_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B0 /\ TW.g_fail_next B0 <= 1 /\
  tick_runinv B0 /\
  TSS.send_data_m timg_B TF (tick_ka_w B0 now) [DSpec.b8 0] 1 now = Some (Bw', r).

(* The queue cut (+0x698): as the keepalive's, with the model's result tick_queue_m's (tick_tail_eq). *)
Definition tick_queue_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' B0 : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  tick_run_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B0 /\ TW.g_fail_next B0 <= 1 /\
  tick_runinv B0 /\
  tick_queue_m timg_B TF B0 now = Some (Bw', r).

(* The epilogue cut (+0x608), reached from every return path: tick_cur, and the post's X already holds (but a0): the
   world relation at the model's world Bw' and g_fail_next Bw' <= 1. *)
Definition tick_epi_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  tick_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* ---- the registers at the cuts ---- *)

(* What every cut holds and the epilogue reads: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s11 = the frame. *)
Definition tick_regs_base (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 27 = w64 F.
(* The epilogue also reads s10 = the result. *)
Definition tick_regs_epi (regs regs2 : bvmap 5 word) (sp1 F r : Z) : Prop :=
  tick_regs_base regs regs2 sp1 F /\ YK11.getr regs2 26 = w64 r.
(* lost: s4 = s (a0 of set_state, +0x478) and a2 = why (set by wake at +0x23c, by online at +0x474). *)
Definition tick_regs_lost (regs regs2 : bvmap 5 word) (sp1 F why : Z) : Prop :=
  tick_regs_base regs regs2 sp1 F /\ YK11.getr regs2 20 = w64 TICK_S /\ YK11.getr regs2 12 = w64 why.
(* Every other cut: s3 = the frame's shadow address, s4 = s, s5 = the shadow address of s + 112, s6 = the shadow
   address of the body (frame + 160: the frame's shadow byte 20), s7 = s + 112, s8 = the shadow base; none of them
   changes before the queue piece (which reuses s5 and s7 at +0x6b4, +0x6c8). *)
Definition tick_regs_run (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  tick_regs_base regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 20 = w64 TICK_S /\
  YK11.getr regs2 21 = w64 (SHADOW_OFF + (TICK_S + 112) / 8) /\
  YK11.getr regs2 22 = w64 (SHADOW_OFF + F / 8 + 20) /\ YK11.getr regs2 23 = w64 (TICK_S + 112) /\
  YK11.getr regs2 24 = w64 SHADOW_OFF.
(* wake, online and step: s9 = the state the code loaded at +0x1ac (`lw`: sign-extended), which ackl stores into its
   notice (+0x500). *)
Definition tick_regs_disp (regs regs2 : bvmap 5 word) (Bw : list byte) (sp1 F : Z) : Prop :=
  tick_regs_run regs regs2 sp1 F /\ YK11.getr regs2 25 = w64 (TW.S_state Bw).
(* retx: t2 = the retries step loaded (`lw` at +0x334), a3 = the shadow address of s + 1752, a4 = that of s + 1748
   (step's checks, read again at +0x34c and +0x3a4), a7 = s + 18144. *)
Definition tick_regs_retx (regs regs2 : bvmap 5 word) (Bw : list byte) (sp1 F : Z) : Prop :=
  tick_regs_run regs regs2 sp1 F /\
  YK11.getr regs2 7 = w64 (bv_swrap 32 (TW.S_inflight_retries Bw)) /\
  YK11.getr regs2 13 = w64 (SHADOW_OFF + (TICK_S + 1752) / 8) /\
  YK11.getr regs2 14 = w64 (SHADOW_OFF + (TICK_S + 1748) / 8) /\
  YK11.getr regs2 17 = w64 (TICK_S + 18144).
(* ackl: s9 = the state, t1 = the shadow address of s + 212, t2 = the retries, a7 = s + 18144. *)
Definition tick_regs_ackl (regs regs2 : bvmap 5 word) (Bw : list byte) (sp1 F : Z) : Prop :=
  tick_regs_run regs regs2 sp1 F /\
  YK11.getr regs2 25 = w64 (TW.S_state Bw) /\
  YK11.getr regs2 6 = w64 (SHADOW_OFF + (TICK_S + 212) / 8) /\
  YK11.getr regs2 7 = w64 (bv_swrap 32 (TW.S_inflight_retries Bw)) /\
  YK11.getr regs2 17 = w64 (TICK_S + 18144).
(* tail: t0 = s + 212, t1 = its shadow address, a7 = s + 18144. *)
Definition tick_regs_tail (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  tick_regs_run regs regs2 sp1 F /\
  YK11.getr regs2 5 = w64 (TICK_S + 212) /\
  YK11.getr regs2 6 = w64 (SHADOW_OFF + (TICK_S + 212) / 8) /\
  YK11.getr regs2 17 = w64 (TICK_S + 18144).
(* ka: a3 = the shadow address of s + 184, a4 = S_next_keepalive_us B0 (the tail's load at +0x68c), a7. *)
Definition tick_regs_ka (regs regs2 : bvmap 5 word) (B0 : list byte) (sp1 F : Z) : Prop :=
  tick_regs_run regs regs2 sp1 F /\
  YK11.getr regs2 13 = w64 (SHADOW_OFF + (TICK_S + 184) / 8) /\
  YK11.getr regs2 14 = w64 (TW.S_next_keepalive_us B0) /\
  YK11.getr regs2 17 = w64 (TICK_S + 18144).
(* queue: a7 = s + 18144. *)
Definition tick_regs_queue (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  tick_regs_run regs regs2 sp1 F /\ YK11.getr regs2 17 = w64 (TICK_S + 18144).

(* ---- the cuts: from the cut's state, the post ---- *)

Definition tick_epi_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_epi_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    tick_regs_epi regs regs2 sp1 F r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_EPI)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_ka_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B0 : list byte) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_ka_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' B0 pos sp1 F
      ly2 S2 W2 mem2 md2 e ->
    tick_regs_ka regs regs2 B0 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_KA)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_queue_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B0 : list byte) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_queue_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' B0 pos sp1 F
      ly2 S2 W2 mem2 md2 e ->
    tick_regs_queue regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_QUEUE)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_tail_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B0 : list byte) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_tail_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' B0 pos sp1 F
      ly2 S2 W2 mem2 md2 e ->
    tick_regs_tail regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_TAIL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_retx_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_retx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2 ->
    tick_regs_retx regs regs2 Bw sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_RETX)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_ackl_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_ackl_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2 ->
    tick_regs_ackl regs regs2 Bw sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_ACKL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_step_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_step_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2 ->
    tick_regs_disp regs regs2 Bw sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_STEP)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_lost_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F why : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_lost_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs r TF Bw Bw' pos F why S2 mem2 md2 ->
    tick_regs_lost regs regs2 sp1 F why ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_LOST)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_wake_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_wake_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 ->
    tick_regs_disp regs regs2 Bw sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_WAKE)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

Definition tick_online_at : Prop :=
  tick_laws -> tick_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    tick_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_online_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 ->
    tick_regs_disp regs regs2 Bw sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_ONLINE)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* ---- the eleven pieces, in continuation form: the cuts a piece can reach, then its own cut ---- *)
Definition tick_epi_stmt : Prop := tick_epi_at.
Definition tick_ka_stmt : Prop := tick_epi_at -> tick_ka_at.
Definition tick_queue_stmt : Prop := tick_epi_at -> tick_queue_at.
Definition tick_tail_stmt : Prop := tick_epi_at -> tick_ka_at -> tick_queue_at -> tick_tail_at.
Definition tick_retx_stmt : Prop := tick_tail_at -> tick_epi_at -> tick_retx_at.
Definition tick_ackl_stmt : Prop := tick_tail_at -> tick_ackl_at.
Definition tick_step_stmt : Prop := tick_tail_at -> tick_retx_at -> tick_ackl_at -> tick_step_at.
Definition tick_lost_stmt : Prop := tick_epi_at -> tick_lost_at.
Definition tick_wake_stmt : Prop := tick_step_at -> tick_lost_at -> tick_wake_at.
Definition tick_online_stmt : Prop := tick_step_at -> tick_lost_at -> tick_online_at.
Definition tick_head_stmt : Prop :=
  tick_wake_at -> tick_online_at -> tick_step_at -> tick_epi_at ->
  @transport_diginet_session_tick_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma tick_holds_of : tick_head_stmt -> tick_wake_stmt -> tick_online_stmt -> tick_lost_stmt -> tick_step_stmt ->
  tick_retx_stmt -> tick_ackl_stmt -> tick_tail_stmt -> tick_ka_stmt -> tick_queue_stmt -> tick_epi_stmt ->
  @transport_diginet_session_tick_cg_holds_stmt fx rc B MT.
Proof.
  intros HEAD WAKE ONLINE LOST STEP RETX ACKL TAIL KA QUEUE EPI.
  exact (let T := TAIL EPI (KA EPI) (QUEUE EPI) in
         let St := STEP T (RETX T EPI) (ACKL T) in
         let Lo := LOST EPI in
         HEAD (WAKE St Lo) (ONLINE St Lo) St EPI).
Qed.
End cut.
