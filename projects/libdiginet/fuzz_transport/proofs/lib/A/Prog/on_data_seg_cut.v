(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module paths and module names changed; 291 of its 367 lines of code are new or changed and 367 lines of the source are left out. *)
(* on_data_seg_cut: the cuts of the walk of on_data (fuzz_transport.asan 0x888d0 = transport_sigma TS_on_data,
   AF_on_data = 0x766c of lib/A/Prog/DgnTransportList.v), as STATEMENTS only, and the composition od_top_of: the
   contract of on_data (lib/A/Prog/on_data_cg.v) at its entry, od_top_at, from the nine piece Props. The walk holds the
   CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) from the entry to the return, with
   (ONDATA_CID, pos) :: own while the class-2 frame is live. The pieces (offsets from AF_on_data):
     head   +0x000 .. +0x164  the frame (`addi sp, sp, -160`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into s1,
                              s7 = now, s4 = fp, the flag word and the shadow base through their GOT words (the flag
                              word is 1, so `beqz a2` is not taken), s3 = s, `jal __asan_stack_malloc_2` (+0x074;
                              lib/A/Prog/TransportGFrame.v gx_stack_malloc_at), s6 = s10 = the frame F, `bnez s6`
                              taken, the frame's header and its 20 shadow bytes, s5 = fp + 20, s2 = its shadow
                              address, the frame word at s1 + 48, the checked load of f + 20 into a2, s8 = s + 18160,
                              a1 = 0xa0, a0 = s, a3 = a4 = 0, `jal send_control` (+0x168): the cut od_sc_at at send_control's entry.
                              Prop: od_head_stmt.
     sc     send_control      the call of send_control from its entry (send_control_cg.v transport_send_control_cg,
                              a G-form callee composed in the same G journal) to its return (+0x16c). Prop: od_sc_stmt.
     acks   +0x16c .. +0x224  `bnez a0`, the checked increment of stats.tx_acks (r = 0), the frame word at s1 + 24,
                              the checked increment of stats.rx_data, s6 = fp + 28, a7 = its shadow address, the checked
                              load of fr_retry into a2, `beqz a2`, and when the retry is not 0 the checked increment of
                              stats.rx_desk_retries and the backoff store (the world ondata_w2 B1 b r now): the cut
                              od_dup_at (+0x228). Prop: od_acks_stmt.
     dup    +0x228 .. +0x290  the duplicate test of :249 (`beqz a4`, `beqz a2`, `bne a4, a2`): not a duplicate goes to
                              the cut od_set_at (+0x294); a duplicate does the checked increment of
                              stats.rx_duplicates and `j` to the release cut od_rel_at (+0x3f8). Prop: od_dup_stmt.
     set    +0x294 .. +0x2c8  the checked stores of fr_send at s + 164 and of 1 at s + 168 (the world
                              ondata_w3 (ondata_w2 B1 b r now) b), the word a7 at s1 + 16, a0 = fp, `jal
                              diginet_frame_is_keepalive` (+0x2cc): the cut od_ka_at at the leaf's entry.
                              Prop: od_set_stmt.
     ka     leaf .. +0x2d0    the call of the leaf from its entry (diginet_frame_is_keepalive_cg.v, through
                              TransportGCg.v gx_call_leaf and the leaf bridge), `bnez a0` (+0x2d0): a keepalive goes to
                              od_rel_at, else to the cut od_ntc_at (+0x2d4). Prop: od_ka_stmt.
     ntc    +0x2d4 .. +0x3c8  s7 = p = F + 32, the notice's shadow bytes 4 .. 12 := 0, the stores into the notice,
                              `jal __asan_memset` (+0x338; p + 24, 0, 24; TransportGCg.v gx_intrin_at), the checked
                              loads of f + 32, f + 40, f + 20, f + 28 and their stores into the notice, the checked
                              loads of s + 96 (notify) and s + 104 (ctx), a1 = p: the cut od_nc_at at the `jalr a2`
                              (+0x3cc). Prop: od_ntc_stmt.
     ncall  +0x3cc .. +0x3f4  the call of notice at TI.ti_notice timg_A (notice_cg.v transport_notice_cg, a G-form
                              callee composed in the same G journal), the notice's shadow bytes 4 .. 12 := 0xf8, to
                              od_rel_at. Prop: od_ncall_stmt.
     rel    +0x3f8 .. +0x528  the header word 0x45e0360e at the frame, the frame word at s1 + 24 (F, so `beqz a1` is
                              not taken), the frame's 32 shadow bytes := 0xf5, the flag pointer from the frame's last
                              word, the store of 0 at it (the release: TransportGFrame.v gx_flag_store_pi), `j`,
                              sp = s0 - 160, the 13 reloads, sp = sp + 160, `ret`. Prop: od_rel_stmt.
   Each cut holds the record facts (od_laws), the callee contracts (od_callees), the caller's facts and what the head
   fixed (od_fix), the journal and the facts carried at the cut (each cut's state, over od_cur), the registers the
   code after the cut reads (each cut's register predicate), and concludes the statement's post (on_data_cg.v
   transport_ondata_post) at the cut's pc. The frame words the head stores at sp - 160 (+0x004) and at s1 + 48 (+0x140)
   are read by no later instruction, so no cut carries them; the word at s1 + 24 (+0x190, the stack malloc's result) is
   read by the release (+0x404), and the word at s1 + 16 (+0x2b0, the shadow address of f + 28) by the notice path
   (+0x364).
   od_fix holds the statement's premise trans_tf_off_g TF (check_state_data_cg.v: no byte of TF is a byte of G; the
   notice call needs TF's bytes after send_control, whose post keeps no byte of G) beside od_pre, so od_top_at is the
   contract with its premises regrouped. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_frame_is_keepalive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_data_cg.
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
Module LKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_is_keepalive_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The cut points, as offsets from the listing's base: the return address of `jal send_control` (+0x168), the
   join after the backoff store (`addi a0, s3, 168`), the not-a-duplicate target (`lb a2, 0(s2)`), the return address
   of `jal diginet_frame_is_keepalive` (+0x2cc), the notice path's first instruction (`addi s7, s10, 32`), the `jalr a2`
   (notice) and the join of every path (`lui a0, 0x45e03`). The cuts od_sc_at and od_ka_at are at the callee's entry,
   after the `jal`, with ra its return address. *)
Definition OD_R1 : Z := AF_on_data + 0x16c.
Definition OD_DUP : Z := AF_on_data + 0x228.
Definition OD_SET : Z := AF_on_data + 0x294.
Definition OD_KAR : Z := AF_on_data + 0x2d0.
Definition OD_NTC : Z := AF_on_data + 0x2d4.
Definition OD_NC : Z := AF_on_data + 0x3cc.
Definition OD_REL : Z := AF_on_data + 0x3f8.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 152 ..
   sp + 56 after `addi sp, sp, -160`). *)
Definition OD_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-2 frame's size. *)
Definition OD_FBYTES : Z := 256.
Lemma od_fbytes : fs_frame_bytes ONDATA_CID = OD_FBYTES.
Proof. reflexivity. Qed.
(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma od_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma od_cut_pcs :
  BASE + AF_on_data = transport_sigma TS_on_data /\ BASE + OD_R1 = 0x88a3c /\
  BASE + OD_DUP = 0x88af8 /\ BASE + OD_SET = 0x88b64 /\ BASE + OD_KAR = 0x88ba0 /\ BASE + OD_NTC = 0x88ba4 /\
  BASE + OD_NC = 0x88c9c /\ BASE + OD_REL = 0x88cc8 /\
  transport_sigma TS_send_control = 0x86d5c /\ transport_sigma TS_diginet_frame_is_keepalive = 0x8b63c.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_on_data_cg_holds_stmt that are not callee
   contracts, and gx_ok / gx_noerrno of G (DgnTransportCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno). *)
Definition od_laws : Prop :=
  pc_stack_malloc (as_code B) ONDATA_CID = transport_sigma TS___asan_stack_malloc_2 /\
  transport_cells B /\ trans_ondata_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS.

(* The callee contracts of transport_on_data_cg_holds_stmt. *)
Definition od_callees : Prop :=
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B ONDATA_CID) /\
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transport_sigma TS_send_control)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKA.transport_diginet_frame_is_keepalive_cg) fx') /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) /\
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)).

(* The caller's facts: the premises of transport_on_data_cg at the entry registers regs, verbatim, but
   trans_tf_off_g TF, which od_top_at and od_fix state beside them. *)
Definition od_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 ONDATA_S /\ YK11.getr regs 11 = w64 fp /\ YK11.getr regs 12 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - ONDATA_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\
  trans_dframe_at B lyc Sc W memc regs ONDATA_STK fp buf b fj /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.on_data_m timg_A TF Bw b now = Some (Bw', tt) /\
  trans_tframe_at B lyc Sc W memc regs ONDATA_STK TF /\
  trans_rom_view_rd W memc /\
  ondata_apart TF Bw b /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
  (ondata_dup Bw b = false -> DSpec.fr_keepalive b = false ->
     trans_src_ok B lyc Sc W memc (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b) /\
     decode_off_win regs ONDATA_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b)) /\
  count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID /\
  st_nev S + k + ONDATA_EV <= EV_MAX.

(* The contract at TS_on_data, its caller's premises as od_pre and trans_tf_off_g TF. *)
Definition od_top_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    od_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' ->
    trans_tf_off_g TF ->
    SRr segs W (@cfg_at fx segs (transport_sigma TS_on_data) regs memc mdc)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The caller's facts and what the head fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp,
   -160`, `andi sp, sp, -32`); pos, the slot of the class-2 frame the stack malloc gave; F, the frame's address. *)
Definition od_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
    (pos sp1 F : Z) : Prop :=
  od_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' /\
  trans_tf_off_g TF /\
  sp1 = 32 * ((spZ regs - ONDATA_FRAME) / 32) /\
  F = frame_addr lyc ONDATA_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + OD_FBYTES <= alloc_ceiling /\ in_app F OD_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range ondata_wr Bw b); the 13 saved words below the entry sp; the frame's last word, the address of its
   flag byte (astack_malloc_realizes' rdword). *)
Definition od_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONDATA_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= ONDATA_EV /\
  frames S2 = (ONDATA_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - ONDATA_STK) (spZ regs) (ondata_wr Bw b) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) OD_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + OD_FBYTES - 8) = Some (flag_addr lyc ONDATA_CID pos).

(* The state at the send_control cut (+0x168), reached from the head only: the layout, the world and the event count
   are the call's; the blocks are the call's exactly (the stack malloc changes st_fs only); the memory relates to the
   world Bw (no store before the call reaches G). *)
Definition od_sc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (Bw : list byte) (pos F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  od_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  tw_at TMAP_A (aview segs (w_H W) mem2) Bw.

(* After send_control (+0x16c): its model call (B1, (r, f)), the world relation at B1 (its X), g_fail_next B1 <= 1. *)
Definition od_r1_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (TF : option TI.tframe) (Bw : list byte) (pos F : Z)
    (B1 : list byte) (r : Z) (f : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  od_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e /\
  TSS.send_control_m timg_A TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) = Some (B1, (r, f)) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) B1 /\ TW.g_fail_next B1 <= 1.

(* At the duplicate test (+0x228): the frame word at s1 + 24 is F, and the memory relates to ondata_w2 B1 b r now. *)
Definition od_dup_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (b : list byte) (TF : option TI.tframe) (Bw : list byte) (pos sp1 F : Z)
    (B1 : list byte) (r : Z) (f : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  od_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 24) = Some F /\
  TSS.send_control_m timg_A TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) = Some (B1, (r, f)) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (ondata_w2 B1 b r now) /\ TW.g_fail_next B1 <= 1.

(* At the not-a-duplicate target (+0x294): od_dup_cur, and the test said no. *)
Definition od_set_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (b : list byte) (TF : option TI.tframe) (Bw : list byte) (pos sp1 F : Z)
    (B1 : list byte) (r : Z) (f : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  od_dup_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now b TF Bw pos sp1 F B1 r f ly2 S2 W2 mem2 md2 e /\
  ondata_dup (ondata_w2 B1 b r now) b = false.

(* At the leaf call (+0x2cc): the frame word at s1 + 16 is the shadow address of f + 28, and the memory relates to
   ondata_w3 (ondata_w2 B1 b r now) b. *)
Definition od_ka_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (fp now : Z) (b : list byte) (TF : option TI.tframe) (Bw : list byte) (pos sp1 F : Z)
    (B1 : list byte) (r : Z) (f : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  od_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 24) = Some F /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 16) = Some (SHADOW_OFF + (fp + 28) / 8) /\
  TSS.send_control_m timg_A TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) = Some (B1, (r, f)) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (ondata_w3 (ondata_w2 B1 b r now) b) /\ TW.g_fail_next B1 <= 1 /\
  ondata_dup (ondata_w2 B1 b r now) b = false.

(* At the notice path (+0x2d4): od_ka_cur, and the frame is not a keepalive. *)
Definition od_ntc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (fp now : Z) (b : list byte) (TF : option TI.tframe) (Bw : list byte) (pos sp1 F : Z)
    (B1 : list byte) (r : Z) (f : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  od_ka_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp now b TF Bw pos sp1 F B1 r f ly2 S2 W2 mem2 md2 e /\
  DSpec.fr_keepalive b = false.

(* At the notice call (+0x3cc): the notice's shadow bytes 4 .. 12 are 0, and its 72 bytes at p = F + 32 hold the
   fields of ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b as trans_ntc_at reads them (the body pointer buf + 30,
   the announce pointer 0; bytes 16 .. 23 hold fp, which notice does not read). *)
Definition od_nc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (buf now : Z) (b : list byte) (TF : option TI.tframe) (Bw : list byte) (pos sp1 F : Z)
    (B1 : list byte) (r : Z) (f : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  od_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 24) = Some F /\
  TSS.send_control_m timg_A TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) = Some (B1, (r, f)) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) (ondata_w3 (ondata_w2 B1 b r now) b) /\ TW.g_fail_next B1 <= 1 /\
  ondata_dup (ondata_w2 B1 b r now) b = false /\ DSpec.fr_keepalive b = false /\
  (forall i, 4 <= i < 13 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0) /\
  exists NB : list byte,
    garr8 segs (mrestrict (w_H W2) mem2) (F + 32) (map DSpec.bz NB) /\ length NB = 72%nat /\
    TW.s32_at NB 0 = TS0.DIGINET_N_DATA /\ TW.s32_at NB 4 = TW.S_state (ondata_w3 (ondata_w2 B1 b r now) b) /\
    TW.s32_at NB 8 = 0 /\ TW.s32_at NB 12 = 0 /\ TW.u_at NB 24 8 = 0 /\ TW.u_at NB 32 8 = 0 /\
    TW.s32_at NB 40 = 0 /\ TW.u_at NB 48 8 = buf + 30 /\ TW.u_at NB 56 8 = DSpec.fr_body_len b /\
    TW.u_at NB 64 4 = DSpec.fr_send b /\ TW.u_at NB 68 2 = DSpec.fr_retry b.

(* At the release cut (+0x3f8), from the duplicate path, the keepalive path or after notice: od_cur, the frame word
   at s1 + 24, and the post's X already holds: the world relation at the model's world Bw' and g_fail_next Bw' <= 1. *)
Definition od_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (Bw Bw' : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  od_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 24) = Some F /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s9 = the frame's
   shadow address, s10 = the frame. *)
Definition od_regs_rel (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\
  YK11.getr regs2 25 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 26 = w64 F.
(* The callee-saved registers every cut before the notice path's own stores keeps: od_regs_rel, s2 = the shadow
   address of f + 20, s3 = s, s4 = fp, s5 = fp + 20, s11 = the shadow base. *)
Definition od_regs_s (regs regs2 : bvmap 5 word) (fp sp1 F : Z) : Prop :=
  od_regs_rel regs regs2 sp1 F /\
  YK11.getr regs2 18 = w64 (SHADOW_OFF + (fp + 20) / 8) /\ YK11.getr regs2 19 = w64 ONDATA_S /\
  YK11.getr regs2 20 = w64 fp /\ YK11.getr regs2 21 = w64 (fp + 20) /\ YK11.getr regs2 27 = w64 SHADOW_OFF.
(* At send_control's entry: ra = the return address, s6 = F, s7 = now, s8 = s + 18160, and the call's arguments
   a0 = s, a1 = 0xa0 (DIGINET_CMD_ACK), a2 = the sign extension of fr_send b (`lw`), a3 = a4 = 0. *)
Definition od_regs_sc (regs regs2 : bvmap 5 word) (fp now : Z) (b : list byte) (sp1 F : Z) : Prop :=
  od_regs_s regs regs2 fp sp1 F /\
  YK11.getr regs2 1 = w64 (@pa_val _ transport_listing PI_transport A_TEXT + OD_R1) /\
  YK11.getr regs2 22 = w64 F /\ YK11.getr regs2 23 = w64 now /\ YK11.getr regs2 24 = w64 (ONDATA_S + 18160) /\
  YK11.getr regs2 10 = w64 ONDATA_S /\ YK11.getr regs2 11 = w64 0xa0 /\
  YK11.getr regs2 12 = w64 (bv_swrap 32 (DSpec.fr_send b)) /\
  YK11.getr regs2 13 = w64 0 /\ YK11.getr regs2 14 = w64 0.
(* At send_control's return: s6 = F, s7 = now, s8 = s + 18160, a0 = r (its X). *)
Definition od_regs_r1 (regs regs2 : bvmap 5 word) (fp now r sp1 F : Z) : Prop :=
  od_regs_s regs regs2 fp sp1 F /\
  YK11.getr regs2 22 = w64 F /\ YK11.getr regs2 23 = w64 now /\ YK11.getr regs2 24 = w64 (ONDATA_S + 18160) /\
  YK11.getr regs2 10 = w64 r.
(* At the duplicate test: s6 = fp + 28, s8 = s + 18160, a2 = fr_retry b (`lhu`), a7 = the shadow address of
   fp + 28. *)
Definition od_regs_dup (regs regs2 : bvmap 5 word) (fp : Z) (b : list byte) (sp1 F : Z) : Prop :=
  od_regs_s regs regs2 fp sp1 F /\
  YK11.getr regs2 22 = w64 (fp + 28) /\ YK11.getr regs2 24 = w64 (ONDATA_S + 18160) /\
  YK11.getr regs2 12 = w64 (DSpec.fr_retry b) /\ YK11.getr regs2 17 = w64 (SHADOW_OFF + (fp + 28) / 8).
(* At the not-a-duplicate target: s6 = fp + 28, a0 = s + 168, a1 = s + 164, a3 = the shadow address of s + 168,
   a7 = the shadow address of fp + 28. *)
Definition od_regs_set (regs regs2 : bvmap 5 word) (fp sp1 F : Z) : Prop :=
  od_regs_s regs regs2 fp sp1 F /\
  YK11.getr regs2 22 = w64 (fp + 28) /\
  YK11.getr regs2 10 = w64 (ONDATA_S + 168) /\ YK11.getr regs2 11 = w64 (ONDATA_S + 164) /\
  YK11.getr regs2 13 = w64 (SHADOW_OFF + (ONDATA_S + 168) / 8) /\
  YK11.getr regs2 17 = w64 (SHADOW_OFF + (fp + 28) / 8).
(* At the leaf's entry: ra = the return address, s6 = fp + 28, a0 = fp. *)
Definition od_regs_ka (regs regs2 : bvmap 5 word) (fp sp1 F : Z) : Prop :=
  od_regs_s regs regs2 fp sp1 F /\
  YK11.getr regs2 1 = w64 (@pa_val _ transport_listing PI_transport A_TEXT + OD_KAR) /\
  YK11.getr regs2 22 = w64 (fp + 28) /\ YK11.getr regs2 10 = w64 fp.
(* At the notice path: s6 = fp + 28. *)
Definition od_regs_ntc (regs regs2 : bvmap 5 word) (fp sp1 F : Z) : Prop :=
  od_regs_s regs regs2 fp sp1 F /\ YK11.getr regs2 22 = w64 (fp + 28).
(* At the notice call: a1 = p = F + 32, a2 = S_notify of the world (the `ld` of s + 96). *)
Definition od_regs_nc (regs regs2 : bvmap 5 word) (now : Z) (b : list byte) (sp1 F : Z) (B1 : list byte) (r : Z)
    : Prop :=
  od_regs_rel regs regs2 sp1 F /\ YK11.getr regs2 11 = w64 (F + 32) /\
  YK11.getr regs2 12 = w64 (TW.S_notify (ondata_w3 (ondata_w2 B1 b r now) b)).

(* The cuts. Each: from the record facts, the callee contracts, the caller's facts and the cut's state, the post. *)
Definition od_rel_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 e ->
    od_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition od_nc_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (B1 : list byte) (r : Z) (f : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_nc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs buf now b TF Bw pos sp1 F B1 r f
      ly2 S2 W2 mem2 md2 e ->
    od_regs_nc regs regs2 now b sp1 F B1 r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_NC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition od_ntc_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (B1 : list byte) (r : Z) (f : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_ntc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp now b TF Bw pos sp1 F B1 r f
      ly2 S2 W2 mem2 md2 e ->
    od_regs_ntc regs regs2 fp sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_NTC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition od_ka_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (B1 : list byte) (r : Z) (f : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_ka_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp now b TF Bw pos sp1 F B1 r f
      ly2 S2 W2 mem2 md2 e ->
    od_regs_ka regs regs2 fp sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (transport_sigma TS_diginet_frame_is_keepalive)) mem2
      (YK11.seg_rom segs)) md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition od_set_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (B1 : list byte) (r : Z) (f : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_set_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now b TF Bw pos sp1 F B1 r f
      ly2 S2 W2 mem2 md2 e ->
    od_regs_set regs regs2 fp sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_SET)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition od_dup_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (B1 : list byte) (r : Z) (f : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_dup_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now b TF Bw pos sp1 F B1 r f
      ly2 S2 W2 mem2 md2 e ->
    od_regs_dup regs regs2 fp b sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_DUP)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition od_r1_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (B1 : list byte) (r : Z) (f : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_r1_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b TF Bw pos F B1 r f ly2 S2 W2 mem2 md2 e ->
    od_regs_r1 regs regs2 fp now r sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_R1)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

Definition od_sc_at : Prop :=
  od_laws -> od_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
         (S2 : astate) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    od_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    od_sc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F S2 mem2 md2 ->
    od_regs_sc regs regs2 fp now b sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (transport_sigma TS_send_control)) mem2 (YK11.seg_rom segs))
      md2)
      (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The nine pieces. *)
Definition od_rel_stmt : Prop := od_rel_at.
Definition od_ncall_stmt : Prop := od_rel_at -> od_nc_at.
Definition od_ntc_stmt : Prop := od_nc_at -> od_ntc_at.
Definition od_ka_stmt : Prop := od_ntc_at -> od_rel_at -> od_ka_at.
Definition od_set_stmt : Prop := od_ka_at -> od_set_at.
Definition od_dup_stmt : Prop := od_set_at -> od_rel_at -> od_dup_at.
Definition od_acks_stmt : Prop := od_dup_at -> od_r1_at.
Definition od_sc_stmt : Prop := od_r1_at -> od_sc_at.
Definition od_head_stmt : Prop := od_sc_at -> od_top_at.

(* The contract at the entry from the pieces. *)
Lemma od_top_of : od_head_stmt -> od_sc_stmt -> od_acks_stmt -> od_dup_stmt -> od_set_stmt -> od_ka_stmt ->
  od_ntc_stmt -> od_ncall_stmt -> od_rel_stmt -> od_top_at.
Proof.
intros HEAD SC ACKS DUP SET KA NTC NC REL.
exact (HEAD (SC (ACKS (DUP (SET (KA (NTC (NC REL)) REL)) REL)))).
Qed.

End cut.
