(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module paths and module names changed; 187 of its 255 lines of code are new or changed and 375 lines of the source are left out. *)
(* on_ack_segs: the cuts of the walk of on_ack (fuzz_transport.asan-ubsan 0x8858c = transportb_sigma TB_on_ack,
   AF_on_ack = 0x72ec of lib/B/Prog/DgnTransportBList.v, 1212 bytes), as STATEMENTS only, the model lemmas the pieces
   share, and the composition onack_holds_of: the statement transport_on_ack_cg_holds_stmt of
   lib/B/Prog/on_ack_cg.v from the five piece Props. Image B's twin of lib/A/Prog/on_ack_segs.v: the same cuts, the
   same carried facts and the same registers, at image B's offsets and names. The walk holds the CALLER's G journal
   (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) from the entry to the return, with (ONACK_CID, pos) :: own
   while the class-2 frame is live. It has five pieces:
     head  +0x000 .. +0x18c  the frame (`addi sp, sp, -128`, the zero word at sp, the 13 saves), s0, the realign into
                             s1, s4 = fp, the two runtime cells (the flag word 1, so `beqz a2` at +0x068 is not
                             taken), s9 = the shadow base, s3 = s, `jal __asan_stack_malloc_2` (+0x070;
                             lib/B/Prog/on_ack_seg_kit.v oak_gx_stack_malloc_at), s2 = s8 = the frame, `bnez s2`
                             taken, the frame's header and its 20 shadow bytes (s7 = their base), a1 = s & 7 and
                             `bnez a1` (+0x134: the UBSan alignment check of s; s = 0x5df640 is 8-aligned, so the trap
                             word at +0x418 is not reached), a3 = the shadow address of s + 212, the checked load of
                             S_inflight and `beqz a1` (+0x150: S_inflight Bw = 0 goes to the ignored cut), fp & 7 and
                             `bnez a1` (+0x158: the UBSan alignment check of f; trans_dframe_at's fp mod 8 = 0), the
                             checks of f + 24 and s + 1744, s10 = the 4-byte load at f + 24 (fr_ack b) and
                             `bne s10, a1` (+0x18c: fr_ack b <> S_inflight_counter Bw goes to the ignored cut, else the
                             notice cut). Prop: onack_head_stmt.
     ntc   +0x190 .. +0x258  the check of the store at s + 212 (its shadow byte through a3), s5 = p = frame + 32, the
                             store of 0 at s + 212 (:229), the notice's shadow bytes 4 .. 12 := 0, the store of 4
                             (N_ACKED) at p, s6 = s + 112 and s11 = its shadow address, the checked load of S_state,
                             the stores at p + 8 (8 zero bytes), p + 4 (the state) and p + 16 (fp),
                             `jal __asan_memset` (+0x1fc; p + 24, 0, 40), the store of fr_ack b at p + 64, the
                             checked 2-byte load at s + 1748 and the stores at p + 68 and p + 70, the checked loads
                             of s + 96 (notify) and s + 104 (ctx), `jalr a2` (+0x258: notice at TI.ti_notice timg_B),
                             then the after-notice cut. Prop: onack_ntc_stmt.
     aft   +0x25c .. +0x2bc  the check of the load at s + 112 (through s11) and `bne a0, a1` (+0x26c: a state other
                             than S_WAKING goes to the shadow join at +0x294), the check of the store at s + 144,
                             the store of 1 at s + 144 (:234), `jal maybe_online` (+0x290), the notice's shadow bytes
                             4 .. 12 := 0xf8 (out of scope again), `j +0x2e8`. Prop: onack_aft_stmt.
     ign   +0x2c0 .. +0x2e4  the ignored path (:226-227): a0 = s + 18184, one check of the 8-byte access, the load,
                             + 1 and the store back; falls into the release cut. Prop: onack_ign_stmt.
     rel   +0x2e8 .. +0x414  the header word 0x45e0360e at the frame, `beqz s2` not taken, the frame's 32 shadow
                             bytes := 0xf5, the flag pointer from the frame's last word, the store of 0 at it (the
                             release: on_ack_seg_kit.v oak_gx_flag_store_pi), `j +0x3d8`, sp = s0 - 128, the 13
                             reloads, sp = sp + 128, `ret`. Prop: onack_rel_stmt.
   Each cut holds the caller's facts (onack_fix), the journal and the facts carried at the cut (onack_ntc_cur,
   onack_aft_cur, onack_ign_cur, onack_rel_cur), the registers the code after the cut reads (onack_regs_ntc,
   onack_regs_aft, onack_regs_ign, onack_regs_rel), and concludes the statement's post (on_ack_cg.v
   transport_onack_post) at the cut's pc. The frame word the head stores at s1 + 16 (+0x0a4) and the zero word at the
   entry sp - 128 (+0x004) are read by no later instruction, so no cut carries them. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The cut points and the shape of the frame                        *)
(* ------------------------------------------------------------------ *)

(* The four cut points, as offsets from the listing's base: the notice path's first instruction (`lb a1, 0(a3)`, the
   fall-through of `bne s10, a1` at +0x18c), the instruction after the indirect call (`lb a0, 0(s11)`), the ignored
   path's first instruction (`lui a0, 4`, the target of the two tests), and the join (`lui a0, 0x45e03`). *)
Definition ONACK_NTC : Z := AF_on_ack + 0x190.
Definition ONACK_AFT : Z := AF_on_ack + 0x25c.
Definition ONACK_IGN : Z := AF_on_ack + 0x2c0.
Definition ONACK_REL : Z := AF_on_ack + 0x2e8.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 120 ..
   sp + 24 after `addi sp, sp, -128`). *)
Definition ONACK_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-2 frame's size. *)
Definition ONACK_FBYTES : Z := 256.
Lemma onack_fbytes : fs_frame_bytes ONACK_CID = ONACK_FBYTES.
Proof. reflexivity. Qed.
(* The notice struct the code fills: at frame + 32, 72 bytes. *)
Definition ONACK_POFF : Z := 32.

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma onack_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

(* The statement's premise that the current heap frame lies outside G (check_state_data_cg.v trans_tf_off_g, a
   premise of transport_on_ack_cg since the statement writer's fix of 2026-10-31; on_ack_cg.v:39-44 and :231-234 say
   how it carries TF across notice). The notice piece needs it and nothing else does: notice is a G-form callee, so
   its acall_kept_g keeps the image bytes OUTSIDE G only, and its X pins the bytes of G to the model world only; a TF
   inside G would therefore lose both its bytes and its placement there. The head piece takes the premise from the
   statement and puts it in the notice cut below. *)

(* ------------------------------------------------------------------ *)
(* 2. The model, as the pieces read it                                 *)
(* ------------------------------------------------------------------ *)

(* The ignored path's world (:226-227). *)
Definition onack_wign (Bw : list byte) : list byte :=
  TW.set_S_stats_rx_ignored Bw (TS0.u64 (TW.S_stats_rx_ignored Bw + 1)).

(* onack_ign Bw b = true: the model's world is onack_wign Bw. *)
Lemma onack_model_ign : forall I F Bw b Bw', onack_ign Bw b = true ->
  TSS.on_ack_m I F Bw b = Some (Bw', tt) -> Bw' = onack_wign Bw.
Proof.
intros I F Bw b Bw' Hi Hm. rewrite onack_model, Hi in Hm. symmetry. exact (onack_some_inv _ _ Hm).
Qed.

(* onack_ign Bw b = false: the call of notice answers, and then either the state is S_WAKING and maybe_online's
   world is the model's, or it is not and notice's world is. *)
Lemma onack_model_ntc : forall I F Bw b Bw', onack_ign Bw b = false ->
  TSS.on_ack_m I F Bw b = Some (Bw', tt) ->
  exists B2, TSS.call_notify I F (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt) /\
    (if TW.S_state B2 =? TS0.DIGINET_S_WAKING
     then TSS.maybe_online_m I F (TW.set_S_wake_acked B2 1) = Some (Bw', tt)
     else Bw' = B2).
Proof.
intros I F Bw b Bw' Hi Hm. rewrite onack_model, Hi in Hm.
destruct (TSS.call_notify I F (onack_w1 Bw) (onack_ntc Bw b)) as [[B2 u]|] eqn:EN; [|discriminate].
destruct u. exists B2. split; [reflexivity|].
destruct (TW.S_state B2 =? TS0.DIGINET_S_WAKING); [exact Hm | symmetry; exact (onack_some_inv _ _ Hm)].
Qed.

(* check_inflight_acked_m answers with the world it was given (TCb.v:391-394). *)
Lemma onack_cia_eq : forall Bx n By, TC.check_inflight_acked_m Bx n = Some (By, tt) -> By = Bx.
Proof.
intros Bx n By H. unfold TC.check_inflight_acked_m in H.
destruct ((TW.OW_acked Bx <? TW.GOT_acked Bx) || negb (TI.n_counter n =? TW.OW_acked_counter Bx)
          || negb (TI.n_retry n =? TW.OW_acked_retry Bx))%bool eqn:E;
  [discriminate H | symmetry; exact (onack_some_inv _ _ H)].
Qed.

(* The notice of this call is an N_ACKED notice, so notice_m's world is the one it was given with GOT.acked set:
   int_inc of GOT.acked, then check_inflight_acked_m, which answers with its own world. *)
Lemma onack_B2_eq : forall I F Bw b B2,
  TSS.call_notify I F (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt) ->
  exists a, B2 = TW.set_GOT_acked (onack_w1 Bw) a.
Proof.
intros I F Bw b B2 H. unfold TSS.call_notify in H.
destruct (TW.S_notify (onack_w1 Bw) =? TI.ti_notice I) eqn:EN; [|discriminate H].
assert (EK : TC.notice_m I F (onack_w1 Bw) (onack_ntc Bw b)
           = match TC.int_inc (TW.GOT_acked (onack_w1 Bw)) with
             | None => None
             | Some a => TC.check_inflight_acked_m (TW.set_GOT_acked (onack_w1 Bw) a) (onack_ntc Bw b)
             end) by reflexivity.
rewrite EK in H.
destruct (TC.int_inc (TW.GOT_acked (onack_w1 Bw))) as [a|]; [|discriminate H].
exists a. exact (onack_cia_eq _ _ _ H).
Qed.

(* The length of a world the relation holds of; every world lemma below needs it. *)
Lemma onack_wlen : forall rd Bw, tw_at TMAP_B rd Bw -> Z.of_nat (length Bw) = TW.W_LEN.
Proof. intros rd Bw H. rewrite (tw_len _ _ _ H). unfold TW.W_LEN. lia. Qed.


(* ------------------------------------------------------------------ *)
(* 3. The cuts                                                         *)
(* ------------------------------------------------------------------ *)

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma onack_cut_pcs :
  BASE + AF_on_ack = transportb_sigma TB_on_ack /\ BASE + ONACK_NTC = 0x8871c /\
  BASE + ONACK_AFT = 0x887e8 /\ BASE + ONACK_IGN = 0x8884c /\ BASE + ONACK_REL = 0x88874.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_on_ack_cg_holds_stmt that are not callee
   contracts, and the two facts DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give from them. *)
Definition onack_laws : Prop :=
  pc_stack_malloc (as_code B) ONACK_CID = transportb_sigma TB___asan_stack_malloc_2 /\
  transport_cells B /\ trans_onack_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B.

(* The caller's facts (the premises of transport_on_ack_cg at the entry registers regs), and what the head fixes
   before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -128`, `andi sp, sp, -32`); pos, the slot of
   the class-2 frame the stack malloc gave; F, the frame's address. *)
Definition onack_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
    (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 ONACK_S /\ YK11.getr regs 11 = w64 fp /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - ONACK_STK /\ spZ regs <= sp0 /\
  trans_dframe_at B lyc Sc W memc regs ONACK_STK fp buf b fj /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.on_ack_m timg_B TF Bw b = Some (Bw', tt) /\
  trans_tframe_at B lyc Sc W memc regs ONACK_STK TF /\
  trans_rom_view_rd W memc /\
  onack_apart TF Bw b /\
  count_cid ONACK_CID (frames Sc) + 1 < fs_frames ONACK_CID /\
  st_nev S + k + ONACK_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - ONACK_FRAME) / 32) /\
  F = frame_addr lyc ONACK_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + ONACK_FBYTES <= alloc_ceiling /\ in_app F ONACK_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames
   where the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's
   window and written range onack_wr Bw b); the 13 saved words below the entry sp; the frame's last word, the address
   of its flag byte (astack_malloc_realizes' rdword). *)
Definition onack_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONACK_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= ONACK_EV /\
  frames S2 = (ONACK_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + ONACK_FBYTES - 8) = Some (flag_addr lyc ONACK_CID pos).

(* The state at the notice cut (+0x190), reached from the head only: the layout, the world and the event count are
   the call's; the blocks are the call's exactly (the stack malloc changes st_fs only); every byte of G outside the
   written range is the call's; the memory still relates to the world Bw (the head stores no byte of G); the heap
   frame and the read-only bytes are as the call left them (carried across the stack malloc); and the test of :225
   does not hold. *)
Definition onack_ntc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (TF : option TI.tframe) (Bw : list byte) (pos F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  onack_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  gx_kept_ex segs TG.G_HARNESS_B (onack_wr Bw b) W memc W mem2 /\
  tw_at TMAP_B (aview segs (w_H W) mem2) Bw /\
  trans_tframe_at B lyc S2 W mem2 regs ONACK_STK TF /\
  trans_tf_off_g TF /\
  trans_rom_view_rd W mem2 /\
  onack_ign Bw b = false.

(* The state at the ignored cut (+0x2c0), reached from the head only (either test of :225): as the notice cut's,
   with the test holding. *)
Definition onack_ign_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (Bw : list byte) (pos F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  onack_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  gx_kept_ex segs TG.G_HARNESS_B (onack_wr Bw b) W memc W mem2 /\
  tw_at TMAP_B (aview segs (w_H W) mem2) Bw /\
  onack_ign Bw b = true.

(* The state after notice returns (+0x25c), reached from the notice cut only: onack_cur at the state notice left;
   the memory relates to notice's world B2; the heap frame and the read-only bytes carried across notice's
   acall_kept_g; the model facts of this path (the test of :225 false, notice's answer B2, and g_fail_next B2 at
   most 1, which maybe_online's statement asks). *)
Definition onack_aft_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (TF : option TI.tframe) (Bw B2 : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  onack_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B2 /\
  trans_tframe_at B ly2 S2 W2 mem2 regs ONACK_STK TF /\
  trans_rom_view_rd W2 mem2 /\
  onack_ign Bw b = false /\
  TSS.call_notify timg_B TF (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt) /\
  TW.g_fail_next B2 <= 1.

(* The state at the release cut (+0x2e8), reached from the after-notice cut (either arm) or from the ignored piece:
   onack_cur, and the post's X already holds: the world relation at the model's world Bw' and g_fail_next Bw' <= 1. *)
Definition onack_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b : list byte) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  onack_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* ------------------------------------------------------------------ *)
(* 4. The registers each cut hands on                                  *)
(* ------------------------------------------------------------------ *)

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s8 = the
   frame, s7 = the frame's shadow address. *)
Definition onack_regs_rel (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 23 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 24 = w64 F.
(* The ignored path also reads s3 = s and s9 = the shadow base. *)
Definition onack_regs_ign (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  onack_regs_rel regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 ONACK_S /\ YK11.getr regs2 25 = w64 SHADOW_OFF.
(* The after-notice path also reads s6 = s + 112 and s11 = its shadow address. *)
Definition onack_regs_aft (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  onack_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 22 = w64 (ONACK_S + 112) /\
  YK11.getr regs2 27 = w64 (SHADOW_OFF + (ONACK_S + 112) / 8).
(* The notice path also reads a3 = the shadow address of s + 212, s4 = fp and s10 = the 4-byte load at f + 24
   (the head loads it at +0x180 with `lw`, which SIGN-EXTENDS: the register holds bv_swrap 32 of fr_ack b, and the
   notice piece's `sw s10, 0x40(s5)` writes its low 32 bits, which are fr_ack b itself since fr_ack is a be32). *)
Definition onack_regs_ntc (regs regs2 : bvmap 5 word) (fp sp1 F : Z) (b : list byte) : Prop :=
  onack_regs_ign regs regs2 sp1 F /\
  YK11.getr regs2 13 = w64 (SHADOW_OFF + (ONACK_S + 212) / 8) /\
  YK11.getr regs2 20 = w64 fp /\
  YK11.getr regs2 26 = Z_to_bv 64 (bv_swrap 32 (DSpec.fr_ack b)).

(* ------------------------------------------------------------------ *)
(* 5. The four cut Props and the five pieces                           *)
(* ------------------------------------------------------------------ *)

(* The release cut, +0x2e8: from the state onack_rel_cur, the post. *)
Definition onack_rel_at : Prop :=
  onack_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    onack_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ->
    onack_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    onack_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONACK_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_onack_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The ignored cut, +0x2c0: from the state onack_ign_cur, the post. *)
Definition onack_ign_at : Prop :=
  onack_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onack_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ->
    onack_ign_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F S2 mem2 md2 ->
    onack_regs_ign regs regs2 sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONACK_IGN)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_onack_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The after-notice cut, +0x25c: from the state onack_aft_cur, the post; maybe_online's contract is its callee's. *)
Definition onack_aft_at : Prop :=
  onack_laws ->
  (forall fx' : YK11.FPState, @transport_maybe_online_cg fx' rc B MT (transportb_sigma TB_maybe_online)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' B2 : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    onack_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ->
    onack_aft_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b TF Bw B2 pos F ly2 S2 W2 mem2 md2 e ->
    onack_regs_aft regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONACK_AFT)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_onack_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The notice cut, +0x190: from the state onack_ntc_cur, the post; the memset and notice contracts are its
   callees'. *)
Definition onack_ntc_at : Prop :=
  onack_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_B)) ->
  (* the notice piece ends at the after-notice cut, which calls maybe_online, so it carries that contract on *)
  (forall fx' : YK11.FPState, @transport_maybe_online_cg fx' rc B MT (transportb_sigma TB_maybe_online)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word),
    onack_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ->
    onack_ntc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b TF Bw pos F S2 mem2 md2 ->
    onack_regs_ntc regs regs2 fp sp1 F b ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONACK_NTC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_onack_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).

(* The five pieces. rel: +0x2e8 .. the return. ign: +0x2c0 .. +0x2e4, then the release cut. aft: +0x25c .. +0x2bc,
   then the release cut. ntc: +0x190 .. +0x258, then the after-notice cut. head: the entry .. +0x18c, then the
   notice cut or the ignored cut. *)
Definition onack_rel_stmt : Prop := onack_rel_at.
Definition onack_ign_stmt : Prop := onack_rel_at -> onack_ign_at.
Definition onack_aft_stmt : Prop := onack_rel_at -> onack_aft_at.
Definition onack_ntc_stmt : Prop := onack_aft_at -> onack_ntc_at.
Definition onack_head_stmt : Prop :=
  onack_ntc_at -> onack_ign_at -> @transport_on_ack_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma onack_holds_of : onack_head_stmt -> onack_ntc_stmt -> onack_aft_stmt -> onack_ign_stmt -> onack_rel_stmt ->
  @transport_on_ack_cg_holds_stmt fx rc B MT.
Proof. intros HEAD NTC AFT IGN REL. exact (HEAD (NTC (AFT REL)) (IGN REL)). Qed.
End cut.
