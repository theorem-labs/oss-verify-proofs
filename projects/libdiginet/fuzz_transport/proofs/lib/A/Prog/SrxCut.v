(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module paths, module names and numbers changed; 402 of its 476 lines of code are new or changed and 369 lines of the source are left out. *)
(* SrxCut: the cuts of the walk of diginet_session_rx (fuzz_transport.asan 0x87594 = transport_sigma
   TS_diginet_session_rx, AF_diginet_session_rx = 0x6330 of lib/A/Prog/DgnTransportList.v, 312 words), as STATEMENTS
   only, the composition srx_holds_of (the statement transport_diginet_session_rx_cg_holds_stmt of
   lib/A/Prog/diginet_session_rx_cg.v from the piece Props), and the model facts the pieces share. The walk holds the
   CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) from the entry to the return, with
   (SRX_CID, pos) :: own while the class-1 frame is live. Offsets are from the listing's base (BASE + 0x6330 =
   0x87594); every cut is at an instruction that is not a call. The pieces:
     head   +0x000 .. +0x12c  the frame (`addi sp, sp, -160`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into s1,
                              s3 = now, s7 = len, s8 = buf, the flag word through its GOT word (1, so `beq a2, zero` is
                              not taken), s11 = the shadow base, s4 = s, `jal __asan_stack_malloc_1` (+0x78; through
                              lib/A/Prog/TransportGFrame.v gx_stack_malloc_at), `bne s2, zero` taken, the frame word at
                              s1 + 48, the frame's header (3 words) and its 16 shadow bytes (0 .. 3 := 0xf1, 12 .. 15 :=
                              0xf3, 4 .. 11 := 0: f's 64 bytes usable), the two NULL tests (s = TA_g_s, 0 < buf: not
                              taken). Ends at the parse cut. Prop: srx_head_stmt.
     parse  +0x130 .. +0x16c  s5 = s + 18152, s6 = f = frame + 32, the call of diginet_frame_parse (+0x14c; a donor-form
                              callee through lib/A/Prog/TransportGCg.v gx_call_cg), `beq a0, zero`: fr_code b <> 0 goes
                              through the checked access at s + 18184 to the ignored cut (a0 = fr_code b), fr_code b = 0
                              to the MAC cut. Prop: srx_parse_stmt.
     mac    +0x170 .. +0x1c4  s7 = f + 6, the three bcmp calls (+0x180, +0x194, +0x1ac; abcmp_realizes through
                              TransportGCg.v gx_call_leaf) of :273-277: srx_mac_bad goes through the checked access at
                              s + 18184 to the ignored cut (a0 = 0), else to the desk cut. Prop: srx_mac_stmt.
     desk   +0x2d8 .. +0x320  s8 = s + 116, the checked load of desk_known (:278): 0 goes to the learn cut; else the bcmp
                              call at +0x300 against desk_mac (:279): equal goes to the closed cut (world Bw), else the
                              checked access at s + 18184 to the ignored cut (a0 = 0). Prop: srx_desk_stmt.
     learn  +0x324 .. +0x364  the 1-byte load of h.cmd at f + 30, the cmd test of :284 (not an announce: +0x388, a0 = 0,
                              to the release cut, world Bw), the slot s1 + 24, the leaf diginet_mac_is_digidesign
                              (+0x33c; :286; not Digidesign: +0x40c, the checked access at s + 18184 to the ignored cut),
                              __asan_memcpy (+0x350; TransportGCg.v gx_intrin_at; :290), the checked store of 1 at
                              s + 116 (:291), to the closed cut (world srx_learn Bw b). Prop: srx_learn_stmt.
     sw     +0x368 .. +0x3d8, +0x3f0 .. +0x3f8, +0x428 .. +0x438, +0x460 .. +0x47c, and +0x388 .. +0x38c
                              the checked load of the state (:293; S_CLOSED: +0x388, a0 = 0, to the release cut), the
                              checked load and store of stats.rx_frames (:296) and the checked store of now at
                              last_rx_us (:297), h.cmd, the switch of :298-316: the four arm cuts, the DISCONNECT test
                              of :310 (neither WAKING nor ONLINE: to the tick cut), the ignored arm of :313-315 (the
                              checked increment of stats.rx_ignored, then the tick cut). Prop: srx_sw_stmt.
     ann    +0x3dc .. +0x3ec  a0 = s, a1 = f, a2 = now, the call of on_announce (G form), `j` to the tick cut.
     ack    +0x3fc .. +0x408  a0 = s, a1 = f, the call of on_ack, `j` to the tick cut.
     lost   +0x43c .. +0x448  a1 = 7, a0 = s, the call of session_lost, `j` to the tick cut.
     data   +0x44c .. +0x45c  a0 = s, a1 = f, a2 = now, the call of on_data, `j` to the tick cut.
                              Props: srx_ann_stmt, srx_ack_stmt, srx_lost_stmt, srx_data_stmt.
     tick   +0x480 .. +0x48c  a0 = s, a1 = now, the call of diginet_session_tick (G form), `j` to the release cut with
                              a0 = its result. Prop: srx_tick_stmt.
     ign    +0x1c8 .. +0x1d0  the 8-byte load of stats.rx_ignored (a1 = s + 18184, checked before the jump), + 1, the
                              store back (srx_ign), on to the release cut. Prop: srx_ign_stmt.
     rel    +0x1d4 .. +0x2d4  the shadow bytes 4 .. 11 := 0xf8, the header word 0x45e0360e at the frame, `beq s2, zero`
                              not taken, the 16 shadow bytes := 0xf5, the flag pointer from the frame's last word
                              (frame + 120), the store of 0 at it (TransportGFrame.v gx_flag_store_pi), `j +0x298`,
                              sp = s0 - 160, the 13 reloads, sp = sp + 160, `ret`. Prop: srx_rel_stmt.
     inv    no code: the model fact that the run invariants the callees ask for (srx_inv) hold at the worlds the code
                    hands them (srx_learn, srx_w1, and the world srx_sw leaves). Prop: srx_inv_stmt.
   Each cut holds the caller's facts (srx_fix), the journal and what the call kept so far (srx_cur), the reads the
   later code hands to callees, carried at the cut's state (srx_rd: the bytes at buf, TF, the read-only bytes and the
   OW.dn body range), f's facts (decode_rd_ok of its 64 bytes from the head on; their values frame_f_bytes buf b fj
   from the parse on), the world relation at the cut's model world, the path the code took (fr_code b = 0,
   srx_mac_bad Bw b = false, ..., srx_pre_acc) and the registers the code after the cut reads (srx_regs_core and its
   extensions). Each piece Prop takes the cut Props it ends in, so srx_holds_of only threads them. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_mac_is_digidesign_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg.
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
Module LMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_mac_is_digidesign_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The cut points, the frame, the saved words                          *)
(* ------------------------------------------------------------------ *)

(* The cut points, as offsets from the listing's base. Each names the first instruction of the piece that starts
   there: parse `lui a0, 0x4` (+0x130, after the NULL tests), mac `addi s7, s6, 6` (+0x170, the target of `beq a0,
   zero` after diginet_frame_parse), desk `addi s8, s4, 116` (+0x2d8), learn `lbu a0, 30(s6)` (+0x324), closed
   `addi a0, s4, 112` (+0x368), the arms `addi a0, s4, 0` (+0x3dc on_announce, +0x3fc on_ack, +0x44c on_data) and
   `addi a1, zero, 7` (+0x43c session_lost), tick `addi a0, s4, 0` (+0x480), ign `ld a2, 0(a1)` (+0x1c8, the join of
   the four ignored paths of :269-289) and rel `addi a1, zero, -8` (+0x1d4, the join of every return). *)
Definition SRX_PARSE : Z := AF_diginet_session_rx + 0x130.
Definition SRX_MAC : Z := AF_diginet_session_rx + 0x170.
Definition SRX_DESK : Z := AF_diginet_session_rx + 0x2d8.
Definition SRX_LEARN : Z := AF_diginet_session_rx + 0x324.
Definition SRX_CLOSED : Z := AF_diginet_session_rx + 0x368.
Definition SRX_ANN : Z := AF_diginet_session_rx + 0x3dc.
Definition SRX_ACK : Z := AF_diginet_session_rx + 0x3fc.
Definition SRX_LOST : Z := AF_diginet_session_rx + 0x43c.
Definition SRX_DATA : Z := AF_diginet_session_rx + 0x44c.
Definition SRX_TICK : Z := AF_diginet_session_rx + 0x480.
Definition SRX_IGN : Z := AF_diginet_session_rx + 0x1c8.
Definition SRX_REL : Z := AF_diginet_session_rx + 0x1d4.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 152 ..
   sp + 56 after `addi sp, sp, -160`). *)
Definition SRX_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-1 frame's size; its last word (frame + 120) holds the address of its flag byte. *)
Definition SRX_FBYTES : Z := 128.
Lemma srx_fbytes_eq : fs_frame_bytes SRX_CID = SRX_FBYTES.
Proof. reflexivity. Qed.
(* The ignored counter's address, a1 at the ignored cut. *)
Definition SRX_RXIGN : Z := SRX_S + 18184.

(* ------------------------------------------------------------------ *)
(* The model facts the pieces share (no machine)                       *)
(* ------------------------------------------------------------------ *)

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma srx_some_inv : forall (Bx By : list byte) (x y : Z), Some (Bx, x) = Some (By, y) -> Bx = By /\ x = y.
Proof.
intros Bx By x y H. split.
- exact (f_equal (fun o : option (list byte * Z) => match o with Some (p, _) => p | None => Bx end) H).
- exact (f_equal (fun o : option (list byte * Z) => match o with Some (_, q) => q | None => x end) H).
Qed.
Lemma srx_some_inv_u : forall (Bx By : list byte), Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o : option (list byte * unit) => match o with Some (p, _) => p | None => Bx end) H). Qed.

(* The run invariants the callees ask for (the statement's premises (1), (2), (4), (5)), at one world, and the two
   array bounds that keep (2) and (4) about g_s.queue[] and g_cmd[]: g_ncmd <= CMDS_MAX and S_queued <= QUEUE_MAX.
   Without them the indexes of (2) and (4) run past the arrays, onto bytes the session callees write (an N_STATE
   notice's Cmd_st byte, the stats counters on_data and io_send increment), so the switch would not keep them. *)
Definition srx_inv (Bx : list byte) : Prop :=
  (TW.M_fly_on Bx <> 0 -> TW.M_fly_len Bx <= TC.SPEC_MAX_FRAME) /\
  (forall i, 0 <= i < TW.S_queued Bx -> TW.S_queue_len Bx i <= TS0.DIGINET_CMD_MAX_LEN) /\
  (forall s, 0 <= s < TW.g_ncmd Bx -> TW.Cmd_st Bx s = TC.PENDING -> TW.Cmd_len Bx s <= DSpec.SPEC_CMD_MAX) /\
  1 <= TW.S_cfg_max_cmds Bx /\ 1 <= TW.S_cfg_max_body Bx /\
  TW.g_ncmd Bx <= TC.CMDS_MAX /\ TW.S_queued Bx <= TC.QUEUE_MAX.

(* The model piece: the invariants hold at the world after the desk is learnt (:290-291), after the counters of
   :296-297, and at the world the switch of :298-316 leaves (each arm's callee, or the stores of the two arms that
   call none). *)
Definition srx_inv_stmt : Prop :=
  (forall Bx b, length Bx = Z.to_nat TW.W_LEN -> srx_inv Bx -> srx_inv (srx_learn Bx b)) /\
  (forall Bx now, length Bx = Z.to_nat TW.W_LEN -> srx_inv Bx -> srx_inv (srx_w1 Bx now)) /\
  (forall (TF : option TI.tframe) Bx b now B2, length Bx = Z.to_nat TW.W_LEN -> srx_inv Bx ->
     srx_sw timg_A TF Bx b now = Some (B2, tt) -> srx_inv B2).

(* The accepted path (:293-317) after the closed test: the switch, then diginet_session_tick. *)
Definition srx_after (I : TI.timg) (F : option TI.tframe) (Bs b : list byte) (now : Z) : option (list byte * Z) :=
  match srx_sw I F Bs b now with
  | None => None
  | Some (B2, _) => TSS.diginet_session_tick_m I F B2 now
  end.

(* The path to the closed test (:273-291): the frame parsed with code 0, the MACs not refused, and either the desk
   known and the source its MAC (the world Bw) or the desk unknown, an announce from a Digidesign MAC (the world after
   the desk is learnt). *)
Definition srx_pre_acc (Bw b Bx : list byte) : Prop :=
  DSpec.fr_code b = 0 /\ srx_mac_bad Bw b = false /\
  ((TW.S_desk_known Bw <> 0 /\ TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = true /\ Bx = Bw) \/
   (TW.S_desk_known Bw = 0 /\
    ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true /\
    DSpec.oui_of (DSpec.fr_src b) = true /\ Bx = srx_learn Bw b)).

(* diginet_session_rx_m on each path the code takes. *)
Lemma srx_m_code : forall I F Bw b now, DSpec.fr_code b <> 0 ->
  TSS.diginet_session_rx_m I F Bw b now = Some (srx_ign Bw, DSpec.fr_code b).
Proof.
intros I F Bw b now H0. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with false by (symmetry; apply Z.eqb_neq; exact H0).
reflexivity.
Qed.

Lemma srx_m_mac : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = true ->
  TSS.diginet_session_rx_m I F Bw b now = Some (srx_ign Bw, DLib.DIGINET_OK).
Proof.
intros I F Bw b now H0 HM. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with true by (symmetry; apply Z.eqb_eq; exact H0).
rewrite HM. reflexivity.
Qed.

Lemma srx_m_desk : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
  TW.S_desk_known Bw <> 0 -> TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = false ->
  TSS.diginet_session_rx_m I F Bw b now = Some (srx_ign Bw, DLib.DIGINET_OK).
Proof.
intros I F Bw b now H0 HM HK HQ. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with true by (symmetry; apply Z.eqb_eq; exact H0).
rewrite HM.
replace (TW.S_desk_known Bw =? 0) with false by (symmetry; apply Z.eqb_neq; exact HK).
rewrite HQ. reflexivity.
Qed.

Lemma srx_m_nocmd : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
  TW.S_desk_known Bw = 0 ->
  ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = false ->
  TSS.diginet_session_rx_m I F Bw b now = Some (Bw, DLib.DIGINET_OK).
Proof.
intros I F Bw b now H0 HM HK HC. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with true by (symmetry; apply Z.eqb_eq; exact H0).
rewrite HM.
replace (TW.S_desk_known Bw =? 0) with true by (symmetry; apply Z.eqb_eq; exact HK).
rewrite HC. reflexivity.
Qed.

Lemma srx_m_oui : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
  TW.S_desk_known Bw = 0 ->
  ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true ->
  DSpec.oui_of (DSpec.fr_src b) = false ->
  TSS.diginet_session_rx_m I F Bw b now = Some (srx_ign Bw, DLib.DIGINET_OK).
Proof.
intros I F Bw b now H0 HM HK HC HO. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with true by (symmetry; apply Z.eqb_eq; exact H0).
rewrite HM.
replace (TW.S_desk_known Bw =? 0) with true by (symmetry; apply Z.eqb_eq; exact HK).
rewrite HC, HO. reflexivity.
Qed.

Lemma srx_m_acc : forall I F Bw b now Bx, srx_pre_acc Bw b Bx ->
  TSS.diginet_session_rx_m I F Bw b now = srx_accept I F Bx b now.
Proof.
intros I F Bw b now Bx (H0 & HM & [(HK & HQ & ->) | (HK & HC & HO & ->)]); rewrite srx_model;
  (replace (DSpec.fr_code b =? DLib.DIGINET_OK) with true by (symmetry; apply Z.eqb_eq; exact H0));
  rewrite HM.
- replace (TW.S_desk_known Bw =? 0) with false by (symmetry; apply Z.eqb_neq; exact HK).
  rewrite HQ. reflexivity.
- replace (TW.S_desk_known Bw =? 0) with true by (symmetry; apply Z.eqb_eq; exact HK).
  rewrite HC, HO. reflexivity.
Qed.

Lemma srx_acc_closed : forall I F Bx b now, TW.S_state Bx = TS0.DIGINET_S_CLOSED ->
  srx_accept I F Bx b now = Some (Bx, DLib.DIGINET_OK).
Proof.
intros I F Bx b now H. unfold srx_accept.
replace (TW.S_state Bx =? TS0.DIGINET_S_CLOSED) with true by (symmetry; apply Z.eqb_eq; exact H).
reflexivity.
Qed.

Lemma srx_acc_open : forall I F Bx b now, TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
  srx_accept I F Bx b now = srx_after I F (srx_w1 Bx now) b now.
Proof.
intros I F Bx b now H. unfold srx_accept, srx_after.
replace (TW.S_state Bx =? TS0.DIGINET_S_CLOSED) with false by (symmetry; apply Z.eqb_neq; exact H).
reflexivity.
Qed.

(* The switch of :298-316 at each value of h.cmd. *)
Lemma srx_sw_ann : forall I F Bx b now,
  ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true ->
  srx_sw I F Bx b now = TSS.on_announce_m I F Bx b now.
Proof. intros I F Bx b now H. unfold srx_sw. rewrite H. reflexivity. Qed.

Lemma srx_sw_ack : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_ACK ->
  srx_sw I F Bx b now = TSS.on_ack_m I F Bx b.
Proof. intros I F Bx b now H. unfold srx_sw. rewrite H. reflexivity. Qed.

Lemma srx_sw_data : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA ->
  srx_sw I F Bx b now = TSS.on_data_m I F Bx b now.
Proof. intros I F Bx b now H. unfold srx_sw. rewrite H. reflexivity. Qed.

Lemma srx_sw_lost : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_DISCONNECT ->
  ((TW.S_state Bx =? TS0.DIGINET_S_ONLINE) || (TW.S_state Bx =? TS0.DIGINET_S_WAKING)) = true ->
  srx_sw I F Bx b now = TSS.session_lost_m I F Bx TS0.DIGINET_R_DESK_DISCONNECT.
Proof. intros I F Bx b now H HS. unfold srx_sw. rewrite H, HS. reflexivity. Qed.

Lemma srx_sw_stay : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_DISCONNECT ->
  ((TW.S_state Bx =? TS0.DIGINET_S_ONLINE) || (TW.S_state Bx =? TS0.DIGINET_S_WAKING)) = false ->
  srx_sw I F Bx b now = Some (Bx, tt).
Proof. intros I F Bx b now H HS. unfold srx_sw. rewrite H, HS. reflexivity. Qed.

Lemma srx_sw_other : forall I F Bx b now,
  ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = false ->
  (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ACK) = false -> (DSpec.fr_cmd b =? TS0.DIGINET_CMD_DATA) = false ->
  (DSpec.fr_cmd b =? TS0.DIGINET_CMD_DISCONNECT) = false ->
  srx_sw I F Bx b now = Some (srx_ign Bx, tt).
Proof. intros I F Bx b now H1 H2 H3 H4. unfold srx_sw. rewrite H1, H2, H3, H4. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The cut states                                                      *)
(* ------------------------------------------------------------------ *)

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma srx_cut_pcs :
  BASE + AF_diginet_session_rx = transport_sigma TS_diginet_session_rx /\
  BASE + SRX_PARSE = 0x876c4 /\ BASE + SRX_MAC = 0x87704 /\ BASE + SRX_DESK = 0x8786c /\
  BASE + SRX_LEARN = 0x878b8 /\ BASE + SRX_CLOSED = 0x878fc /\ BASE + SRX_ANN = 0x87970 /\
  BASE + SRX_ACK = 0x87990 /\ BASE + SRX_LOST = 0x879d0 /\ BASE + SRX_DATA = 0x879e0 /\
  BASE + SRX_TICK = 0x87a14 /\ BASE + SRX_IGN = 0x8775c /\ BASE + SRX_REL = 0x87768.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_diginet_session_rx_cg_holds_stmt that are
   not callee contracts, and gx_ok / gx_noerrno (DgnTransportCg.v G_HARNESS_gx_ok, G_HARNESS_gx_noerrno). *)
Definition srx_laws : Prop :=
  pc_stack_malloc (as_code B) SRX_CID = transport_sigma TS___asan_stack_malloc_1 /\
  transport_cells B /\ trans_srx_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS.

(* The callee contracts of the holds statement, in its order. *)
Definition srx_calls : Prop :=
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SRX_CID) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_frame_parse_cg fx' rc B MT (transport_sigma TS_diginet_frame_parse)) /\
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LMD.transport_diginet_mac_is_digidesign_cg) fx') /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) /\
  (forall fx' : YK11.FPState, @transport_on_announce_cg fx' rc B MT (transport_sigma TS_on_announce)) /\
  (forall fx' : YK11.FPState, @transport_on_ack_cg fx' rc B MT (transport_sigma TS_on_ack)) /\
  (forall fx' : YK11.FPState, @transport_session_lost_cg fx' rc B MT (transport_sigma TS_session_lost)) /\
  (forall fx' : YK11.FPState, @transport_on_data_cg fx' rc B MT (transport_sigma TS_on_data)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_session_tick_cg fx' rc B MT (transport_sigma TS_diginet_session_tick)).

(* The OW.dn body range on_data's notice reads (the statement's premise (3)), at the state (ly2, S2, W2, mem2),
   guarded by every condition of the path on which diginet_session_rx calls on_data: fr_code b = 0, h.cmd = DATA,
   the MACs not refused, the desk known and the source its MAC, the state not CLOSED (TSess.v diginet_session_rx_m),
   and on_data's own two (ondata_dup, fr_keepalive). A premise (3) guarded by any subset of these gives it. *)
Definition srx_ndata (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
    (regs : bvmap 5 word) (Bw b : list byte) : Prop :=
  DSpec.fr_code b = 0 -> DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA ->
  srx_mac_bad Bw b = false -> TW.S_desk_known Bw <> 0 ->
  TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = true -> TW.S_state Bw <> TS0.DIGINET_S_CLOSED ->
  ondata_dup Bw b = false -> DSpec.fr_keepalive b = false ->
    trans_src_ok B ly2 S2 W2 mem2 (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b) /\
    decode_off_win regs SRX_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b).

(* The caller's facts (the premises of transport_diginet_session_rx_cg at the entry registers regs, premise (3) as
   srx_ndata and premises (1), (2), (4), (5) with the bounds g_ncmd <= CMDS_MAX and S_queued <= QUEUE_MAX as
   srx_inv), and what the head fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -160`,
   `andi sp, sp, -32`); pos, the slot of the class-1 frame the stack malloc gave; F, the frame's address. *)
Definition srx_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (buf now r : Z) (b : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
    (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 SRX_S /\ YK11.getr regs 11 = w64 buf /\
  YK11.getr regs 12 = w64 (Z.of_nat (length b)) /\ YK11.getr regs 13 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - SRX_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\ 0 < buf /\
  garr8 segs (mrestrict (w_H W) memc) buf (TW.zs b) /\
  trans_src_ok B lyc Sc W memc buf (Z.of_nat (length b)) /\
  decode_off_win regs SRX_STK buf (Z.of_nat (length b)) /\
  srx_buf_off_g buf b /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.diginet_session_rx_m timg_A TF Bw b now = Some (Bw', r) /\
  trans_tframe_at B lyc Sc W memc regs SRX_STK TF /\
  trans_tf_off_g TF /\ trans_rom_view_rd W memc /\ srx_apart TF b /\
  srx_inv Bw /\ srx_ndata lyc Sc W memc regs Bw b /\
  count_cid SRX_CID (frames Sc) < fs_frames SRX_CID /\
  count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID /\
  count_cid TICK_CID (frames Sc) < fs_frames TICK_CID /\
  count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID /\
  count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID /\
  st_nev S + k + SRX_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - SRX_FRAME) / 32) /\
  F = frame_addr lyc SRX_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + SRX_FBYTES <= alloc_ceiling /\ in_app F SRX_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range srx_wr b); the 13 saved words below the entry sp; the frame's last word, the address of its flag
   byte (astack_malloc_realizes' rdword). *)
Definition srx_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= SRX_EV /\
  frames S2 = (SRX_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - SRX_STK) (spZ regs) (srx_wr b) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SRX_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + SRX_FBYTES - 8) = Some (flag_addr lyc SRX_CID pos).

(* The reads the code after the cut hands to its callees, at the current state: the bytes b at buf and their
   placement (diginet_frame_parse, and trans_dframe_at of the three session callees), the heap frame TF
   (trans_tframe_at, at the statement's window), the read-only bytes (trans_rom_view_rd), and the OW.dn body range
   (srx_ndata). *)
Definition srx_rd (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
    (regs : bvmap 5 word) (buf : Z) (b : list byte) (TF : option TI.tframe) (Bw : list byte) : Prop :=
  garr8 segs (mrestrict (w_H W2) mem2) buf (TW.zs b) /\
  trans_src_ok B ly2 S2 W2 mem2 buf (Z.of_nat (length b)) /\
  trans_tframe_at B ly2 S2 W2 mem2 regs SRX_STK TF /\
  trans_rom_view_rd W2 mem2 /\
  srx_ndata ly2 S2 W2 mem2 regs Bw b.

(* f = F + 32 after the parse: its 64 bytes are those diginet_frame_parse leaves (fj the 64 bytes before the call). *)
Definition srx_fbytes (W2 : world segs) (mem2 : word -> option byte) (F buf : Z) (b fj : list byte) : Prop :=
  length fj = 64%nat /\ garr8 segs (mrestrict (w_H W2) mem2) (F + SRX_F) (frame_f_bytes buf b fj).

(* The registers from the head on: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s10 = the frame, s3 = now,
   s4 = s, s9 = the frame's shadow address, s11 = the shadow base. *)
Definition srx_regs_core (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 19 = w64 now /\ YK11.getr regs2 20 = w64 SRX_S /\
  YK11.getr regs2 25 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 26 = w64 F /\
  YK11.getr regs2 27 = w64 SHADOW_OFF.
(* The parse cut adds s7 = len and s8 = buf. *)
Definition srx_regs_parse (regs regs2 : bvmap 5 word) (buf now : Z) (b : list byte) (sp1 F : Z) : Prop :=
  srx_regs_core regs regs2 now sp1 F /\
  YK11.getr regs2 23 = w64 (Z.of_nat (length b)) /\ YK11.getr regs2 24 = w64 buf.
(* From the mac cut on: s5 = s + 18152 (g_s.stats), s6 = f. *)
Definition srx_regs_base (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  srx_regs_core regs regs2 now sp1 F /\
  YK11.getr regs2 21 = w64 (SRX_S + 18152) /\ YK11.getr regs2 22 = w64 (F + SRX_F).
(* The desk cut adds s7 = f + 6 (the source MAC). *)
Definition srx_regs_desk (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  srx_regs_base regs regs2 now sp1 F /\ YK11.getr regs2 23 = w64 (F + SRX_F + 6).
(* The learn cut adds s8 = s + 116 (g_s.desk_known) and a2 = its shadow byte's address (the store check at +0x358
   reads it back from s1 + 24). *)
Definition srx_regs_learn (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  srx_regs_desk regs regs2 now sp1 F /\
  YK11.getr regs2 24 = w64 (SRX_S + 116) /\ YK11.getr regs2 12 = w64 (SHADOW_OFF + (SRX_S + 116) / 8).
(* The ignored cut: a0 = the result, a1 = s + 18184. *)
Definition srx_regs_ign (regs regs2 : bvmap 5 word) (now sp1 F r : Z) : Prop :=
  srx_regs_base regs regs2 now sp1 F /\ YK11.getr regs2 10 = w64 r /\ YK11.getr regs2 11 = w64 SRX_RXIGN.
(* The release cut: a0 = the result. *)
Definition srx_regs_rel (regs regs2 : bvmap 5 word) (now sp1 F r : Z) : Prop :=
  srx_regs_base regs regs2 now sp1 F /\ YK11.getr regs2 10 = w64 r.

(* The machine state at a cut pc. *)
Local Abbreviation srx_cfg pc regs2 mem2 md2 :=
  (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md2).

(* ------------------------------------------------------------------ *)
(* The cuts: from the cut's state, the post                            *)
(* ------------------------------------------------------------------ *)

(* The release cut, +0x1d4: the post's X already holds (the world relation at the model's world Bw',
   g_fail_next Bw' <= 1, a0 = r). *)
Definition srx_rel_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' -> TW.g_fail_next Bw' <= 1 ->
    srx_regs_rel regs regs2 now sp1 F r ->
    SRr segs W2 (srx_cfg SRX_REL regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The ignored cut, +0x1c8 (the shadow check of s + 18184 done before the jump): the model's world Bx, Bw' = srx_ign
   Bx, a0 = r. *)
Definition srx_ign_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bx -> TW.g_fail_next Bx <= 1 ->
    Bw' = srx_ign Bx ->
    srx_regs_ign regs regs2 now sp1 F r ->
    SRr segs W2 (srx_cfg SRX_IGN regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The tick cut, +0x480: the switch has run from the world Bs (srx_sw ... = Some (B2, tt)), the memory relates to
   B2, and diginet_session_tick_m at B2 is the call's result. TF and the read-only bytes at the current state. *)
Definition srx_tick_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' Bs B2 : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    trans_tframe_at B ly2 S2 W2 mem2 regs SRX_STK TF -> trans_rom_view_rd W2 mem2 ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) B2 -> TW.g_fail_next B2 <= 1 ->
    length Bs = Z.to_nat TW.W_LEN -> srx_inv Bs -> srx_sw timg_A TF Bs b now = Some (B2, tt) ->
    TSS.diginet_session_tick_m timg_A TF B2 now = Some (Bw', r) ->
    srx_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srx_cfg SRX_TICK regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* An arm cut of the switch (pc one of SRX_ANN, SRX_ACK, SRX_DATA, SRX_LOST): the counters of :296-297 are stored,
   the memory relates to Bs = srx_w1 Bx now, the path srx_pre_acc Bw b Bx and the state not CLOSED hold, and the
   model's result is srx_after at Bs; Cmd b Bs is the arm's fact (h.cmd, and for session_lost the state at Bs). *)
Definition srx_arm_at (pc : Z) (Cmd : list byte -> list byte -> Prop) : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srx_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srx_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) (srx_w1 Bx now) -> TW.g_fail_next (srx_w1 Bx now) <= 1 ->
    srx_inv (srx_w1 Bx now) ->
    srx_pre_acc Bw b Bx -> TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
    srx_after timg_A TF (srx_w1 Bx now) b now = Some (Bw', r) ->
    Cmd b (srx_w1 Bx now) ->
    srx_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srx_cfg pc regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The four arms: h.cmd = ANNOUNCE or ANNOUNCE_SESSION (on_announce), ACK (on_ack), DATA (on_data), DISCONNECT with
   the state of the switch's world WAKING or ONLINE (session_lost). *)
Definition srx_ann_at : Prop :=
  srx_arm_at SRX_ANN (fun b _ =>
    ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true).
Definition srx_ack_at : Prop :=
  srx_arm_at SRX_ACK (fun b _ => DSpec.fr_cmd b = TS0.DIGINET_CMD_ACK).
Definition srx_data_at : Prop :=
  srx_arm_at SRX_DATA (fun b _ => DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA).
Definition srx_lost_at : Prop :=
  srx_arm_at SRX_LOST (fun b Bs => DSpec.fr_cmd b = TS0.DIGINET_CMD_DISCONNECT /\
    ((TW.S_state Bs =? TS0.DIGINET_S_ONLINE) || (TW.S_state Bs =? TS0.DIGINET_S_WAKING)) = true).

(* The closed cut, +0x368: the path srx_pre_acc Bw b Bx (the memory relates to Bx: Bw, or srx_learn Bw b after the
   memcpy and the store of :290-291), and the invariants at Bx. *)
Definition srx_closed_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srx_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srx_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bx -> TW.g_fail_next Bx <= 1 -> srx_inv Bx ->
    srx_pre_acc Bw b Bx ->
    srx_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srx_cfg SRX_CLOSED regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The learn cut, +0x324: fr_code b = 0, the MACs not refused, the desk not known (the load at +0x2ec read 0); the
   memory relates to Bw. *)
Definition srx_learn_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srx_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srx_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw ->
    DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false -> TW.S_desk_known Bw = 0 ->
    srx_regs_learn regs regs2 now sp1 F ->
    SRr segs W2 (srx_cfg SRX_LEARN regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The desk cut, +0x2d8: fr_code b = 0 and the MACs not refused; the memory relates to Bw. *)
Definition srx_desk_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srx_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srx_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw ->
    DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
    srx_regs_desk regs regs2 now sp1 F ->
    SRr segs W2 (srx_cfg SRX_DESK regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The mac cut, +0x170: diginet_frame_parse returned 0 (fr_code b = 0) and left frame_f_bytes buf b fj at f; the
   memory relates to Bw. *)
Definition srx_mac_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srx_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srx_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw ->
    DSpec.fr_code b = 0 ->
    srx_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srx_cfg SRX_MAC regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The parse cut, +0x130: the frame's header and shadow bytes stored (f's 64 bytes usable: decode_rd_ok), nothing
   of G written (the memory relates to Bw). *)
Definition srx_parse_at : Prop :=
  srx_laws -> srx_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srx_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srx_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srx_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw ->
    srx_regs_parse regs regs2 buf now b sp1 F ->
    SRr segs W2 (srx_cfg SRX_PARSE regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* ------------------------------------------------------------------ *)
(* The pieces and the walk                                             *)
(* ------------------------------------------------------------------ *)

(* Each piece: the cut Props it ends in give its own cut (or, for the head, the statement). *)
Definition srx_rel_stmt : Prop := srx_rel_at.
Definition srx_ign_stmt : Prop := srx_rel_at -> srx_ign_at.
Definition srx_tick_stmt : Prop := srx_inv_stmt -> srx_rel_at -> srx_tick_at.
Definition srx_ann_stmt : Prop := srx_tick_at -> srx_ann_at.
Definition srx_ack_stmt : Prop := srx_tick_at -> srx_ack_at.
Definition srx_data_stmt : Prop := srx_tick_at -> srx_data_at.
Definition srx_lost_stmt : Prop := srx_tick_at -> srx_lost_at.
Definition srx_sw_stmt : Prop :=
  srx_inv_stmt -> srx_rel_at -> srx_ann_at -> srx_ack_at -> srx_data_at -> srx_lost_at -> srx_tick_at ->
  srx_closed_at.
Definition srx_learn_stmt : Prop := srx_inv_stmt -> srx_rel_at -> srx_ign_at -> srx_closed_at -> srx_learn_at.
Definition srx_desk_stmt : Prop := srx_ign_at -> srx_learn_at -> srx_closed_at -> srx_desk_at.
Definition srx_mac_stmt : Prop := srx_ign_at -> srx_desk_at -> srx_mac_at.
Definition srx_parse_stmt : Prop := srx_ign_at -> srx_mac_at -> srx_parse_at.
Definition srx_head_stmt : Prop := srx_parse_at -> @transport_diginet_session_rx_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Theorem srx_holds_of :
  srx_head_stmt -> srx_parse_stmt -> srx_mac_stmt -> srx_desk_stmt -> srx_learn_stmt -> srx_sw_stmt ->
  srx_ann_stmt -> srx_ack_stmt -> srx_data_stmt -> srx_lost_stmt -> srx_tick_stmt -> srx_ign_stmt ->
  srx_rel_stmt -> srx_inv_stmt ->
  @transport_diginet_session_rx_cg_holds_stmt fx rc B MT.
Proof.
intros HEAD PARSE MAC DESK LEARN SW ANN ACK DATA LOST TICK IGN REL INV.
pose proof (TICK INV REL) as T.
pose proof (IGN REL) as I.
pose proof (SW INV REL (ANN T) (ACK T) (DATA T) (LOST T) T) as C.
exact (HEAD (PARSE I (MAC I (DESK I (LEARN INV REL I C) C)))).
Qed.
End cut.
