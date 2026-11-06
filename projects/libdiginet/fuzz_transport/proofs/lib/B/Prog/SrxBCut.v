(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 397 of its 445 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBCut.v, with its module paths, module names and numbers changed; 402 of its 477 lines of code are new or changed and 370 lines of the source are left out. *)
(* SrxBCut: the cuts of the walk of diginet_session_rx on image B (fuzz_transport.asan-ubsan 0x87784 =
   transportb_sigma TB_diginet_session_rx, AF_diginet_session_rx = 0x64e4 of lib/B/Prog/DgnTransportBList.v, 337 words),
   as STATEMENTS only, the composition srxb_holds_of (the statement transport_diginet_session_rx_cg_holds_stmt of
   lib/B/Prog/diginet_session_rx_cg.v from the piece Props), and the model facts the pieces share. Image A's
   interface (lib/A/Prog/SrxCut.v) at image B's pcs, piece for piece, but for the disconnect arm. The walk holds the
   CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) from the entry to the return, with
   (SRX_CID, pos) :: own while the class-1 frame is live. Offsets are from the listing's base (BASE + 0x64e4 =
   0x87784); every cut is at an instruction that is not a call. The pieces:
     head   +0x000 .. +0x12c  the frame (`addi sp, sp, -160`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into s1,
                              s3 = now, s7 = len, s8 = buf, the flag word through its GOT word (1, so `beq a2, zero` is
                              not taken), s11 = the shadow base, s4 = s, `jal __asan_stack_malloc_1` (+0x78; through
                              lib/A/Prog/TransportGFrame.v gx_stack_malloc_at), `bne s2, zero` taken, the frame word at
                              s1 + 48, the frame's header (3 words) and its 16 shadow bytes (0 .. 3 := 0xf1, 12 .. 15 :=
                              0xf3, 4 .. 11 := 0: f's 64 bytes usable), the two NULL tests (s = TB_g_s, 0 < buf: not
                              taken). Ends at the parse cut. Prop: srxb_head_stmt.
     parse  +0x130 .. +0x178  s5 = s + 18152, s6 = f = frame + 32, the call of diginet_frame_parse (+0x14c; a donor-form
                              callee through lib/A/Prog/TransportGCg.v gx_call_cg), a1 = s & 7, `beq a0, zero`: on each
                              arm the UBSan test `bne a1, zero` to the trap word (+0x158, +0x178; s mod 8 = 0); fr_code
                              b <> 0 goes through the checked access at s + 18184 to the ignored cut (a0 = fr_code b),
                              fr_code b = 0 to the MAC cut. Prop: srxb_parse_stmt.
     mac    +0x17c .. +0x1d0  s7 = f + 6, the three bcmp calls (+0x18c, +0x1a0, +0x1b8; abcmp_realizes through
                              TransportGCg.v gx_call_leaf) of :273-277: srx_mac_bad goes through the checked access at
                              s + 18184 to the ignored cut (a0 = 0), else to the desk cut. Prop: srxb_mac_stmt.
     desk   +0x2e4 .. +0x32c, +0x4d4 .. +0x4dc
                              s8 = s + 116, the checked load of desk_known (:278): 0 goes to the learn cut; else the bcmp
                              call at +0x30c against desk_mac (:279): equal goes to the closed cut (world Bw), else the
                              checked access at s + 18184 to the ignored cut (a0 = 0). Prop: srxb_desk_stmt.
     learn  +0x330 .. +0x370, +0x394 .. +0x398, +0x418 .. +0x42c, +0x4f8 .. +0x500
                              the 1-byte load of h.cmd at f + 30, the cmd test of :284 (not an announce: +0x394, a0 = 0,
                              to the release cut, world Bw), the slot s1 + 24, the leaf diginet_mac_is_digidesign
                              (+0x348; :286; not Digidesign: +0x418, the checked access at s + 18184 to the ignored cut),
                              __asan_memcpy (+0x35c; TransportGCg.v gx_intrin_at; :290), the checked store of 1 at
                              s + 116 (:291), to the closed cut (world srx_learn Bw b). Prop: srxb_learn_stmt.
     sw     +0x374 .. +0x3e4, +0x394 .. +0x398, +0x3fc .. +0x404, +0x434 .. +0x444, +0x4a0 .. +0x4bc, +0x4e8 .. +0x4f0
                              the checked load of the state (:293; S_CLOSED: +0x394, a0 = 0, to the release cut), the
                              checked load and store of stats.rx_frames (:296) and the checked store of now at
                              last_rx_us (:297), h.cmd, the switch of :298-316: the four arm cuts, the DISCONNECT test
                              of :310 (neither WAKING nor ONLINE: to the tick cut), the ignored arm of :313-315 (the
                              checked increment of stats.rx_ignored, then the tick cut). Prop: srxb_sw_stmt.
     ann    +0x3e8 .. +0x3f8  a0 = s, a1 = f, a2 = now, the call of on_announce (G form), `j` to the tick cut.
     ack    +0x408 .. +0x414  a0 = s, a1 = f, the call of on_ack, `j` to the tick cut.
     lost   +0x448 .. +0x488, +0x50c .. +0x514, +0x51c .. +0x524
                              image B's disconnect arm, session_lost inlined (:311, :162-164): the checked stores of 0 at
                              s + 212 (inflight) and s + 168 (desk_counter_valid), a0 = s, a1 = 0 (S_IDLE), a2 = 7, the
                              call of set_state (+0x484; G form), `j` to the tick cut. Image A's lost piece is one call
                              of session_lost; this one is two stores and a call of set_state.
     data   +0x48c .. +0x49c  a0 = s, a1 = f, a2 = now, the call of on_data, `j` to the tick cut.
                              Props: srxb_ann_stmt, srxb_ack_stmt, srxb_lost_stmt, srxb_data_stmt.
     tick   +0x4c0 .. +0x4cc  a0 = s, a1 = now, the call of diginet_session_tick (G form), `j` to the release cut with
                              a0 = its result. Prop: srxb_tick_stmt.
     ign    +0x1d4 .. +0x1dc  the 8-byte load of stats.rx_ignored (a1 = s + 18184, checked before the jump), + 1, the
                              store back (srx_ign), on to the release cut. Prop: srxb_ign_stmt.
     rel    +0x1e0 .. +0x2e0  the shadow bytes 4 .. 11 := 0xf8, the header word 0x45e0360e at the frame, `beq s2, zero`
                              not taken, the 16 shadow bytes := 0xf5, the flag pointer from the frame's last word
                              (frame + 120), the store of 0 at it (lib/B/Prog/TransportGFrameB.v gx_flag_store_pi),
                              `j +0x2a4`, sp = s0 - 160, the 13 reloads, sp = sp + 160, `ret`. Prop: srxb_rel_stmt.
     inv    no code: the model fact that the run invariants the callees ask for (srxb_inv) hold at the worlds the code
                    hands them (srx_learn, srx_w1, and the world srx_sw leaves). Prop: srxb_inv_stmt.
   Each cut holds the caller's facts (srxb_fix), the journal and what the call kept so far (srxb_cur), the reads the
   later code hands to callees, carried at the cut's state (srxb_rd: the bytes at buf, TF, the read-only bytes and the
   OW.dn body range), f's facts (decode_rd_ok of its 64 bytes from the head on; their values frame_f_bytes buf b fj
   from the parse on), the world relation at the cut's model world, the path the code took (fr_code b = 0,
   srx_mac_bad Bw b = false, ..., srxb_pre_acc) and the registers the code after the cut reads (srxb_regs_core and its
   extensions). Each piece Prop takes the cut Props it ends in, so srxb_holds_of only threads them. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_mac_is_digidesign_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg.
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
Module LMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_mac_is_digidesign_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The cut points, the frame, the saved words                          *)
(* ------------------------------------------------------------------ *)

(* The cut points, as offsets from the listing's base. Each names the first instruction of the piece that starts
   there: parse `lui a0, 0x4` (+0x130, after the NULL tests), mac `addi s7, s6, 6` (+0x17c, after the UBSan test of s
   that follows `beq a0, zero` after diginet_frame_parse), desk `addi s8, s4, 116` (+0x2e4), learn `lbu a0, 30(s6)`
   (+0x330), closed `addi a0, s4, 112` (+0x374), the arms `addi a0, s4, 0` (+0x3e8 on_announce, +0x408 on_ack,
   +0x48c on_data) and `addi a0, s4, 212` (+0x448, the inlined session_lost), tick `addi a0, s4, 0` (+0x4c0), ign
   `ld a2, 0(a1)` (+0x1d4, the join of the four ignored paths of :269-289) and rel `addi a1, zero, -8` (+0x1e0, the
   join of every return). *)
Definition SRXB_PARSE : Z := AF_diginet_session_rx + 0x130.
Definition SRXB_MAC : Z := AF_diginet_session_rx + 0x17c.
Definition SRXB_DESK : Z := AF_diginet_session_rx + 0x2e4.
Definition SRXB_LEARN : Z := AF_diginet_session_rx + 0x330.
Definition SRXB_CLOSED : Z := AF_diginet_session_rx + 0x374.
Definition SRXB_ANN : Z := AF_diginet_session_rx + 0x3e8.
Definition SRXB_ACK : Z := AF_diginet_session_rx + 0x408.
Definition SRXB_LOST : Z := AF_diginet_session_rx + 0x448.
Definition SRXB_DATA : Z := AF_diginet_session_rx + 0x48c.
Definition SRXB_TICK : Z := AF_diginet_session_rx + 0x4c0.
Definition SRXB_IGN : Z := AF_diginet_session_rx + 0x1d4.
Definition SRXB_REL : Z := AF_diginet_session_rx + 0x1e0.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 152 ..
   sp + 56 after `addi sp, sp, -160`). *)
Definition SRXB_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-1 frame's size; its last word (frame + 120) holds the address of its flag byte. *)
Definition SRXB_FBYTES : Z := 128.
Lemma srxb_fbytes_eq : fs_frame_bytes SRX_CID = SRXB_FBYTES.
Proof. reflexivity. Qed.
(* The ignored counter's address, a1 at the ignored cut. *)
Definition SRXB_RXIGN : Z := SRX_S + 18184.

(* ------------------------------------------------------------------ *)
(* The model facts the pieces share (no machine)                       *)
(* ------------------------------------------------------------------ *)

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma srxb_some_inv : forall (Bx By : list byte) (x y : Z), Some (Bx, x) = Some (By, y) -> Bx = By /\ x = y.
Proof.
intros Bx By x y H. split.
- exact (f_equal (fun o : option (list byte * Z) => match o with Some (p, _) => p | None => Bx end) H).
- exact (f_equal (fun o : option (list byte * Z) => match o with Some (_, q) => q | None => x end) H).
Qed.
Lemma srxb_some_inv_u : forall (Bx By : list byte), Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o : option (list byte * unit) => match o with Some (p, _) => p | None => Bx end) H). Qed.

(* The run invariants the callees ask for (the statement's premises (1), (2), (4), (5)), at one world, and the two
   array bounds that keep (2) and (4) about g_s.queue[] and g_cmd[]: g_ncmd <= CMDS_MAX and S_queued <= QUEUE_MAX.
   Without them the indexes of (2) and (4) run past the arrays, onto bytes the session callees write (an N_STATE
   notice's Cmd_st byte, the stats counters on_data and io_send increment), so the switch would not keep them.
   Image A's lib/A/Prog/SrxCut.v srx_inv, term for term. *)
Definition srxb_inv (Bx : list byte) : Prop :=
  (TW.M_fly_on Bx <> 0 -> TW.M_fly_len Bx <= TC.SPEC_MAX_FRAME) /\
  (forall i, 0 <= i < TW.S_queued Bx -> TW.S_queue_len Bx i <= TS0.DIGINET_CMD_MAX_LEN) /\
  (forall s, 0 <= s < TW.g_ncmd Bx -> TW.Cmd_st Bx s = TC.PENDING -> TW.Cmd_len Bx s <= DSpec.SPEC_CMD_MAX) /\
  1 <= TW.S_cfg_max_cmds Bx /\ 1 <= TW.S_cfg_max_body Bx /\
  TW.g_ncmd Bx <= TC.CMDS_MAX /\ TW.S_queued Bx <= TC.QUEUE_MAX.

(* The model piece: the invariants hold at the world after the desk is learnt (:290-291), after the counters of
   :296-297, and at the world the switch of :298-316 leaves (each arm's callee, or the stores of the two arms that
   call none). *)
Definition srxb_inv_stmt : Prop :=
  (forall Bx b, length Bx = Z.to_nat TW.W_LEN -> srxb_inv Bx -> srxb_inv (srx_learn Bx b)) /\
  (forall Bx now, length Bx = Z.to_nat TW.W_LEN -> srxb_inv Bx -> srxb_inv (srx_w1 Bx now)) /\
  (forall (TF : option TI.tframe) Bx b now B2, length Bx = Z.to_nat TW.W_LEN -> srxb_inv Bx ->
     srx_sw timg_B TF Bx b now = Some (B2, tt) -> srxb_inv B2).

(* The accepted path (:293-317) after the closed test: the switch, then diginet_session_tick. *)
Definition srxb_after (I : TI.timg) (F : option TI.tframe) (Bs b : list byte) (now : Z) : option (list byte * Z) :=
  match srx_sw I F Bs b now with
  | None => None
  | Some (B2, _) => TSS.diginet_session_tick_m I F B2 now
  end.

(* The path to the closed test (:273-291): the frame parsed with code 0, the MACs not refused, and either the desk
   known and the source its MAC (the world Bw) or the desk unknown, an announce from a Digidesign MAC (the world after
   the desk is learnt). *)
Definition srxb_pre_acc (Bw b Bx : list byte) : Prop :=
  DSpec.fr_code b = 0 /\ srx_mac_bad Bw b = false /\
  ((TW.S_desk_known Bw <> 0 /\ TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = true /\ Bx = Bw) \/
   (TW.S_desk_known Bw = 0 /\
    ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true /\
    DSpec.oui_of (DSpec.fr_src b) = true /\ Bx = srx_learn Bw b)).

(* diginet_session_rx_m on each path the code takes. *)
Lemma srxb_m_code : forall I F Bw b now, DSpec.fr_code b <> 0 ->
  TSS.diginet_session_rx_m I F Bw b now = Some (srx_ign Bw, DSpec.fr_code b).
Proof.
intros I F Bw b now H0. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with false by (symmetry; apply Z.eqb_neq; exact H0).
reflexivity.
Qed.

Lemma srxb_m_mac : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = true ->
  TSS.diginet_session_rx_m I F Bw b now = Some (srx_ign Bw, DLib.DIGINET_OK).
Proof.
intros I F Bw b now H0 HM. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with true by (symmetry; apply Z.eqb_eq; exact H0).
rewrite HM. reflexivity.
Qed.

Lemma srxb_m_desk : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
  TW.S_desk_known Bw <> 0 -> TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = false ->
  TSS.diginet_session_rx_m I F Bw b now = Some (srx_ign Bw, DLib.DIGINET_OK).
Proof.
intros I F Bw b now H0 HM HK HQ. rewrite srx_model.
replace (DSpec.fr_code b =? DLib.DIGINET_OK) with true by (symmetry; apply Z.eqb_eq; exact H0).
rewrite HM.
replace (TW.S_desk_known Bw =? 0) with false by (symmetry; apply Z.eqb_neq; exact HK).
rewrite HQ. reflexivity.
Qed.

Lemma srxb_m_nocmd : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
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

Lemma srxb_m_oui : forall I F Bw b now, DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
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

Lemma srxb_m_acc : forall I F Bw b now Bx, srxb_pre_acc Bw b Bx ->
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

Lemma srxb_acc_closed : forall I F Bx b now, TW.S_state Bx = TS0.DIGINET_S_CLOSED ->
  srx_accept I F Bx b now = Some (Bx, DLib.DIGINET_OK).
Proof.
intros I F Bx b now H. unfold srx_accept.
replace (TW.S_state Bx =? TS0.DIGINET_S_CLOSED) with true by (symmetry; apply Z.eqb_eq; exact H).
reflexivity.
Qed.

Lemma srxb_acc_open : forall I F Bx b now, TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
  srx_accept I F Bx b now = srxb_after I F (srx_w1 Bx now) b now.
Proof.
intros I F Bx b now H. unfold srx_accept, srxb_after.
replace (TW.S_state Bx =? TS0.DIGINET_S_CLOSED) with false by (symmetry; apply Z.eqb_neq; exact H).
reflexivity.
Qed.

(* The switch of :298-316 at each value of h.cmd. *)
Lemma srxb_sw_ann : forall I F Bx b now,
  ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true ->
  srx_sw I F Bx b now = TSS.on_announce_m I F Bx b now.
Proof. intros I F Bx b now H. unfold srx_sw. rewrite H. reflexivity. Qed.

Lemma srxb_sw_ack : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_ACK ->
  srx_sw I F Bx b now = TSS.on_ack_m I F Bx b.
Proof. intros I F Bx b now H. unfold srx_sw. rewrite H. reflexivity. Qed.

Lemma srxb_sw_data : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA ->
  srx_sw I F Bx b now = TSS.on_data_m I F Bx b now.
Proof. intros I F Bx b now H. unfold srx_sw. rewrite H. reflexivity. Qed.

(* The disconnect arm on image B: session_lost is inlined, so its two stores are slost_w1 (diginet_session_tick_cg.v)
   and its set_state_m step is the call of set_state at slost_w1 of the switch's world (slost_model_sstate). *)
Lemma srxb_sw_lost : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_DISCONNECT ->
  ((TW.S_state Bx =? TS0.DIGINET_S_ONLINE) || (TW.S_state Bx =? TS0.DIGINET_S_WAKING)) = true ->
  srx_sw I F Bx b now = TSS.set_state_m I F (slost_w1 Bx) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT.
Proof.
intros I F Bx b now H HS. unfold srx_sw. rewrite H, HS.
exact (slost_model_sstate I F Bx TS0.DIGINET_R_DESK_DISCONNECT).
Qed.

Lemma srxb_sw_stay : forall I F Bx b now, DSpec.fr_cmd b = TS0.DIGINET_CMD_DISCONNECT ->
  ((TW.S_state Bx =? TS0.DIGINET_S_ONLINE) || (TW.S_state Bx =? TS0.DIGINET_S_WAKING)) = false ->
  srx_sw I F Bx b now = Some (Bx, tt).
Proof. intros I F Bx b now H HS. unfold srx_sw. rewrite H, HS. reflexivity. Qed.

Lemma srxb_sw_other : forall I F Bx b now,
  ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = false ->
  (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ACK) = false -> (DSpec.fr_cmd b =? TS0.DIGINET_CMD_DATA) = false ->
  (DSpec.fr_cmd b =? TS0.DIGINET_CMD_DISCONNECT) = false ->
  srx_sw I F Bx b now = Some (srx_ign Bx, tt).
Proof. intros I F Bx b now H1 H2 H3 H4. unfold srx_sw. rewrite H1, H2, H3, H4. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The cut states                                                      *)
(* ------------------------------------------------------------------ *)

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma srxb_cut_pcs :
  BASE + AF_diginet_session_rx = transportb_sigma TB_diginet_session_rx /\
  BASE + SRXB_PARSE = 0x878b4 /\ BASE + SRXB_MAC = 0x87900 /\ BASE + SRXB_DESK = 0x87a68 /\
  BASE + SRXB_LEARN = 0x87ab4 /\ BASE + SRXB_CLOSED = 0x87af8 /\ BASE + SRXB_ANN = 0x87b6c /\
  BASE + SRXB_ACK = 0x87b8c /\ BASE + SRXB_LOST = 0x87bcc /\ BASE + SRXB_DATA = 0x87c10 /\
  BASE + SRXB_TICK = 0x87c44 /\ BASE + SRXB_IGN = 0x87958 /\ BASE + SRXB_REL = 0x87964.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_diginet_session_rx_cg_holds_stmt that are
   not callee contracts, and gx_ok / gx_noerrno (DgnTransportBCg.v G_HARNESS_gx_ok, G_HARNESS_gx_noerrno). The .got
   rows of transport_cells are premises here as there; the record closes them. *)
Definition srxb_laws : Prop :=
  pc_stack_malloc (as_code B) SRX_CID = transportb_sigma TB___asan_stack_malloc_1 /\
  transport_cells B /\ trans_srx_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B.

(* The callee contracts of the holds statement, in its order (set_state where image A has session_lost). *)
Definition srxb_calls : Prop :=
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SRX_CID) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_frame_parse_cg fx' rc B MT (transportb_sigma TB_diginet_frame_parse)) /\
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LMD.transport_diginet_mac_is_digidesign_cg) fx') /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) /\
  (forall fx' : YK11.FPState, @transport_on_announce_cg fx' rc B MT (transportb_sigma TB_on_announce)) /\
  (forall fx' : YK11.FPState, @transport_on_ack_cg fx' rc B MT (transportb_sigma TB_on_ack)) /\
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) /\
  (forall fx' : YK11.FPState, @transport_on_data_cg fx' rc B MT (transportb_sigma TB_on_data)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_session_tick_cg fx' rc B MT (transportb_sigma TB_diginet_session_tick)).

(* The OW.dn body range on_data's notice reads (the statement's premise (3)), at the state (ly2, S2, W2, mem2),
   guarded by every condition of the path on which diginet_session_rx calls on_data, in the statement's order:
   fr_code b = 0, the MACs not refused, the desk known and the source its MAC, the state not CLOSED, h.cmd = DATA
   (TSess.v diginet_session_rx_m), and on_data's own two (ondata_dup, fr_keepalive). At the entry it is the
   statement's premise (3) itself (image A's srx_ndata has h.cmd = DATA second). *)
Definition srxb_ndata (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
    (regs : bvmap 5 word) (Bw b : list byte) : Prop :=
  DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false -> TW.S_desk_known Bw <> 0 ->
  TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = true -> TW.S_state Bw <> TS0.DIGINET_S_CLOSED ->
  DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA -> ondata_dup Bw b = false -> DSpec.fr_keepalive b = false ->
    trans_src_ok B ly2 S2 W2 mem2 (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b) /\
    decode_off_win regs SRX_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b).

(* The caller's facts (the premises of transport_diginet_session_rx_cg at the entry registers regs, premise (3) as
   srxb_ndata and premises (1), (2), (4), (5) with the bounds g_ncmd <= CMDS_MAX and S_queued <= QUEUE_MAX as
   srxb_inv; the class-1 count leaves room for diginet_session_wake's frame under on_announce), and what the head
   fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -160`, `andi sp, sp, -32`); pos, the
   slot of the class-1 frame the stack malloc gave; F, the frame's address. *)
Definition srxb_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (buf now r : Z) (b : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
    (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
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
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.diginet_session_rx_m timg_B TF Bw b now = Some (Bw', r) /\
  trans_tframe_at B lyc Sc W memc regs SRX_STK TF /\
  trans_tf_off_g TF /\ trans_rom_view_rd W memc /\ srx_apart TF b /\
  srxb_inv Bw /\ srxb_ndata lyc Sc W memc regs Bw b /\
  count_cid SRX_CID (frames Sc) + 1 < fs_frames SRX_CID /\
  count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID /\
  count_cid TICK_CID (frames Sc) < fs_frames TICK_CID /\
  count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID /\
  count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID /\
  st_nev S + k + SRX_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - SRX_FRAME) / 32) /\
  F = frame_addr lyc SRX_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + SRXB_FBYTES <= alloc_ceiling /\ in_app F SRXB_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range srx_wr b); the 13 saved words below the entry sp; the frame's last word, the address of its flag
   byte (astack_malloc_realizes' rdword). *)
Definition srxb_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= SRX_EV /\
  frames S2 = (SRX_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - SRX_STK) (spZ regs) (srx_wr b) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SRXB_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + SRXB_FBYTES - 8) = Some (flag_addr lyc SRX_CID pos).

(* The reads the code after the cut hands to its callees, at the current state: the bytes b at buf and their
   placement (diginet_frame_parse, and trans_dframe_at of the three session callees), the heap frame TF
   (trans_tframe_at, at the statement's window), the read-only bytes (trans_rom_view_rd), and the OW.dn body range
   (srxb_ndata). *)
Definition srxb_rd (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
    (regs : bvmap 5 word) (buf : Z) (b : list byte) (TF : option TI.tframe) (Bw : list byte) : Prop :=
  garr8 segs (mrestrict (w_H W2) mem2) buf (TW.zs b) /\
  trans_src_ok B ly2 S2 W2 mem2 buf (Z.of_nat (length b)) /\
  trans_tframe_at B ly2 S2 W2 mem2 regs SRX_STK TF /\
  trans_rom_view_rd W2 mem2 /\
  srxb_ndata ly2 S2 W2 mem2 regs Bw b.

(* f = F + 32 after the parse: its 64 bytes are those diginet_frame_parse leaves (fj the 64 bytes before the call). *)
Definition srxb_fbytes (W2 : world segs) (mem2 : word -> option byte) (F buf : Z) (b fj : list byte) : Prop :=
  length fj = 64%nat /\ garr8 segs (mrestrict (w_H W2) mem2) (F + SRX_F) (frame_f_bytes buf b fj).

(* The registers from the head on: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s10 = the frame, s3 = now,
   s4 = s, s9 = the frame's shadow address, s11 = the shadow base. *)
Definition srxb_regs_core (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 19 = w64 now /\ YK11.getr regs2 20 = w64 SRX_S /\
  YK11.getr regs2 25 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 26 = w64 F /\
  YK11.getr regs2 27 = w64 SHADOW_OFF.
(* The parse cut adds s7 = len and s8 = buf. *)
Definition srxb_regs_parse (regs regs2 : bvmap 5 word) (buf now : Z) (b : list byte) (sp1 F : Z) : Prop :=
  srxb_regs_core regs regs2 now sp1 F /\
  YK11.getr regs2 23 = w64 (Z.of_nat (length b)) /\ YK11.getr regs2 24 = w64 buf.
(* From the mac cut on: s5 = s + 18152 (g_s.stats), s6 = f. *)
Definition srxb_regs_base (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  srxb_regs_core regs regs2 now sp1 F /\
  YK11.getr regs2 21 = w64 (SRX_S + 18152) /\ YK11.getr regs2 22 = w64 (F + SRX_F).
(* The desk cut adds s7 = f + 6 (the source MAC). *)
Definition srxb_regs_desk (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  srxb_regs_base regs regs2 now sp1 F /\ YK11.getr regs2 23 = w64 (F + SRX_F + 6).
(* The learn cut adds s8 = s + 116 (g_s.desk_known) and a2 = its shadow byte's address (the store check at +0x360
   reads it back from s1 + 24). *)
Definition srxb_regs_learn (regs regs2 : bvmap 5 word) (now sp1 F : Z) : Prop :=
  srxb_regs_desk regs regs2 now sp1 F /\
  YK11.getr regs2 24 = w64 (SRX_S + 116) /\ YK11.getr regs2 12 = w64 (SHADOW_OFF + (SRX_S + 116) / 8).
(* The ignored cut: a0 = the result, a1 = s + 18184. *)
Definition srxb_regs_ign (regs regs2 : bvmap 5 word) (now sp1 F r : Z) : Prop :=
  srxb_regs_base regs regs2 now sp1 F /\ YK11.getr regs2 10 = w64 r /\ YK11.getr regs2 11 = w64 SRXB_RXIGN.
(* The release cut: a0 = the result. *)
Definition srxb_regs_rel (regs regs2 : bvmap 5 word) (now sp1 F r : Z) : Prop :=
  srxb_regs_base regs regs2 now sp1 F /\ YK11.getr regs2 10 = w64 r.

(* The machine state at a cut pc. *)
Local Abbreviation srxb_cfg pc regs2 mem2 md2 :=
  (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md2).

(* ------------------------------------------------------------------ *)
(* The cuts: from the cut's state, the post                            *)
(* ------------------------------------------------------------------ *)

(* The release cut, +0x1e0: the post's X already holds (the world relation at the model's world Bw',
   g_fail_next Bw' <= 1, a0 = r). *)
Definition srxb_rel_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' -> TW.g_fail_next Bw' <= 1 ->
    srxb_regs_rel regs regs2 now sp1 F r ->
    SRr segs W2 (srxb_cfg SRXB_REL regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The ignored cut, +0x1d4 (the shadow check of s + 18184 done before the jump): the model's world Bx, Bw' = srx_ign
   Bx, a0 = r. *)
Definition srxb_ign_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bx -> TW.g_fail_next Bx <= 1 ->
    Bw' = srx_ign Bx ->
    srxb_regs_ign regs regs2 now sp1 F r ->
    SRr segs W2 (srxb_cfg SRXB_IGN regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The tick cut, +0x4c0: the switch has run from the world Bs (srx_sw ... = Some (B2, tt)), the memory relates to
   B2, and diginet_session_tick_m at B2 is the call's result. TF and the read-only bytes at the current state. *)
Definition srxb_tick_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' Bs B2 : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    trans_tframe_at B ly2 S2 W2 mem2 regs SRX_STK TF -> trans_rom_view_rd W2 mem2 ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) B2 -> TW.g_fail_next B2 <= 1 ->
    length Bs = Z.to_nat TW.W_LEN -> srxb_inv Bs -> srx_sw timg_B TF Bs b now = Some (B2, tt) ->
    TSS.diginet_session_tick_m timg_B TF B2 now = Some (Bw', r) ->
    srxb_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srxb_cfg SRXB_TICK regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* An arm cut of the switch (pc one of SRXB_ANN, SRXB_ACK, SRXB_DATA, SRXB_LOST): the counters of :296-297 are
   stored, the memory relates to Bs = srx_w1 Bx now, the path srxb_pre_acc Bw b Bx and the state not CLOSED hold, and
   the model's result is srxb_after at Bs; Cmd b Bs is the arm's fact (h.cmd, and for the disconnect arm the state at
   Bs). *)
Definition srxb_arm_at (pc : Z) (Cmd : list byte -> list byte -> Prop) : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srxb_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) (srx_w1 Bx now) -> TW.g_fail_next (srx_w1 Bx now) <= 1 ->
    srxb_inv (srx_w1 Bx now) ->
    srxb_pre_acc Bw b Bx -> TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
    srxb_after timg_B TF (srx_w1 Bx now) b now = Some (Bw', r) ->
    Cmd b (srx_w1 Bx now) ->
    srxb_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srxb_cfg pc regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The four arms: h.cmd = ANNOUNCE or ANNOUNCE_SESSION (on_announce), ACK (on_ack), DATA (on_data), DISCONNECT with
   the state of the switch's world WAKING or ONLINE (the inlined session_lost: two stores and set_state,
   srxb_sw_lost). *)
Definition srxb_ann_at : Prop :=
  srxb_arm_at SRXB_ANN (fun b _ =>
    ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) || (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true).
Definition srxb_ack_at : Prop :=
  srxb_arm_at SRXB_ACK (fun b _ => DSpec.fr_cmd b = TS0.DIGINET_CMD_ACK).
Definition srxb_data_at : Prop :=
  srxb_arm_at SRXB_DATA (fun b _ => DSpec.fr_cmd b = TS0.DIGINET_CMD_DATA).
Definition srxb_lost_at : Prop :=
  srxb_arm_at SRXB_LOST (fun b Bs => DSpec.fr_cmd b = TS0.DIGINET_CMD_DISCONNECT /\
    ((TW.S_state Bs =? TS0.DIGINET_S_ONLINE) || (TW.S_state Bs =? TS0.DIGINET_S_WAKING)) = true).

(* The closed cut, +0x374: the path srxb_pre_acc Bw b Bx (the memory relates to Bx: Bw, or srx_learn Bw b after the
   memcpy and the store of :290-291), and the invariants at Bx. *)
Definition srxb_closed_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srxb_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bx -> TW.g_fail_next Bx <= 1 -> srxb_inv Bx ->
    srxb_pre_acc Bw b Bx ->
    srxb_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srxb_cfg SRXB_CLOSED regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The learn cut, +0x330: fr_code b = 0, the MACs not refused, the desk not known (the load at +0x2f8 read 0); the
   memory relates to Bw. *)
Definition srxb_learn_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srxb_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw ->
    DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false -> TW.S_desk_known Bw = 0 ->
    srxb_regs_learn regs regs2 now sp1 F ->
    SRr segs W2 (srxb_cfg SRXB_LEARN regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The desk cut, +0x2e4: fr_code b = 0 and the MACs not refused; the memory relates to Bw. *)
Definition srxb_desk_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srxb_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw ->
    DSpec.fr_code b = 0 -> srx_mac_bad Bw b = false ->
    srxb_regs_desk regs regs2 now sp1 F ->
    SRr segs W2 (srxb_cfg SRXB_DESK regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The mac cut, +0x17c: diginet_frame_parse returned 0 (fr_code b = 0) and left frame_f_bytes buf b fj at f, and the
   UBSan test of s at +0x178 is passed; the memory relates to Bw. *)
Definition srxb_mac_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srxb_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw ->
    DSpec.fr_code b = 0 ->
    srxb_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srxb_cfg SRXB_MAC regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* The parse cut, +0x130: the frame's header and shadow bytes stored (f's 64 bytes usable: decode_rd_ok), nothing
   of G written (the memory relates to Bw). *)
Definition srxb_parse_at : Prop :=
  srxb_laws -> srxb_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw ->
    srxb_regs_parse regs regs2 buf now b sp1 F ->
    SRr segs W2 (srxb_cfg SRXB_PARSE regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

(* ------------------------------------------------------------------ *)
(* The pieces and the walk                                             *)
(* ------------------------------------------------------------------ *)

(* Each piece: the cut Props it ends in give its own cut (or, for the head, the statement). *)
Definition srxb_rel_stmt : Prop := srxb_rel_at.
Definition srxb_ign_stmt : Prop := srxb_rel_at -> srxb_ign_at.
Definition srxb_tick_stmt : Prop := srxb_inv_stmt -> srxb_rel_at -> srxb_tick_at.
Definition srxb_ann_stmt : Prop := srxb_tick_at -> srxb_ann_at.
Definition srxb_ack_stmt : Prop := srxb_tick_at -> srxb_ack_at.
Definition srxb_data_stmt : Prop := srxb_tick_at -> srxb_data_at.
Definition srxb_lost_stmt : Prop := srxb_tick_at -> srxb_lost_at.
Definition srxb_sw_stmt : Prop :=
  srxb_inv_stmt -> srxb_rel_at -> srxb_ann_at -> srxb_ack_at -> srxb_data_at -> srxb_lost_at -> srxb_tick_at ->
  srxb_closed_at.
Definition srxb_learn_stmt : Prop := srxb_inv_stmt -> srxb_rel_at -> srxb_ign_at -> srxb_closed_at -> srxb_learn_at.
Definition srxb_desk_stmt : Prop := srxb_ign_at -> srxb_learn_at -> srxb_closed_at -> srxb_desk_at.
Definition srxb_mac_stmt : Prop := srxb_ign_at -> srxb_desk_at -> srxb_mac_at.
Definition srxb_parse_stmt : Prop := srxb_ign_at -> srxb_mac_at -> srxb_parse_at.
Definition srxb_head_stmt : Prop := srxb_parse_at -> @transport_diginet_session_rx_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Theorem srxb_holds_of :
  srxb_head_stmt -> srxb_parse_stmt -> srxb_mac_stmt -> srxb_desk_stmt -> srxb_learn_stmt -> srxb_sw_stmt ->
  srxb_ann_stmt -> srxb_ack_stmt -> srxb_data_stmt -> srxb_lost_stmt -> srxb_tick_stmt -> srxb_ign_stmt ->
  srxb_rel_stmt -> srxb_inv_stmt ->
  @transport_diginet_session_rx_cg_holds_stmt fx rc B MT.
Proof.
intros HEAD PARSE MAC DESK LEARN SW ANN ACK DATA LOST TICK IGN REL INV.
pose proof (TICK INV REL) as T.
pose proof (IGN REL) as I.
pose proof (SW INV REL (ANN T) (ACK T) (DATA T) (LOST T) T) as C.
exact (HEAD (PARSE I (MAC I (DESK I (LEARN INV REL I C) C)))).
Qed.
End cut.
