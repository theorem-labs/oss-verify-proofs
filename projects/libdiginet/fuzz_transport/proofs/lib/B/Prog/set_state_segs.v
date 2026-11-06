(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 397 of its 445 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBCut.v, with its module names changed; 94 of its 152 lines of code are new or changed and 387 lines of the source are left out. *)
(* set_state_segs (image B): the cuts of the walk of set_state on fuzz_transport.asan-ubsan (41113a03c82f) at 0x872cc =
   transportb_sigma TB_set_state (AF_set_state = 0x602c of lib/B/Prog/DgnTransportBList.v), as STATEMENTS only, and
   the composition sstb_holds_of: the statement transport_set_state_cg_holds_stmt of lib/B/Prog/set_state_cg.v from
   the three piece Props. The walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 [])
   from the entry to the return, with (SSTATE_CID, pos) :: own while the class-2 frame is live. Image B's form of
   lib/A/Prog/SlostCut.v (image A inlines set_state into session_lost; the code here has no store before the test of
   the state and takes st as an argument). Three pieces, in pc order:

     head  +0x000 .. +0x150  the frame (`addi sp, sp, -160`), the zero word at sp, the 13 saves (ra, s0 .. s11),
                             s0 = the entry sp, the realign into s1 (sp1), s2 = why, s3 = st, the two runtime cells (the
                             flag word 1, so `beqz a2` at +0x06c is not taken), s10 = the shadow base, s4 = s,
                             `jal __asan_stack_malloc_2` (+0x074), s9 = the frame F (a0 keeps F), `bnez a0` taken (the
                             real-stack arm at +0x088 is dead), the frame word at s1 + 48, the 24-byte header, s8 = F's
                             shadow address and the frame's 20 shadow bytes, the UBSan alignment check `andi a1, s4, 7;
                             bnez a1` (+0x134, not taken: s is a multiple of 8, so the trap word at +0x344 is unreached),
                             s6 = s + 112, s11 = its shadow address, the checked load of s5 = S_state Bw and
                             `beq s5, s3` (+0x150): the state st goes to the release cut (sstb_rel_at) with a0 = F, any
                             other state to the notice cut (sstb_ntc_at). Prop: sstb_head_stmt.
     ntc   +0x154 .. +0x210  the frame word F at s1 + 24, s7 = p = F + 32, its shadow bytes 4 .. 12 := 0,
                             `jal __asan_memset` (+0x18c; p + 16, 0, 56), the stores of 2, st, S_state Bw and why (4 bytes
                             each) at p, p + 4, p + 8, p + 12, the checked store of st at s + 112, the checked loads of
                             s + 96 (notify) and s + 104 (ctx), `jalr a2` (+0x1e4: notice at TI.ti_notice timg_B), the
                             shadow bytes 4 .. 12 := 0xf8, a0 = F loaded back from s1 + 24, to the release cut.
                             Prop: sstb_ntc_stmt.
     rel   +0x214 .. +0x340  the header word 0x45e0360e at the frame (s9), `beqz a0` not taken, the frame's 32 shadow
                             bytes := 0xf5, the flag pointer from the frame's last word (a0 + 248), the store of 0 at it
                             (the release), `j +0x304`, sp = s0 - 160, the 13 reloads, sp = sp + 160, `ret`.
                             Prop: sstb_rel_stmt.

   Each cut holds the caller's facts (sstb_fix), the journal and the facts carried at the cut (sstb_cur and the per-cut
   sstb_ntc_cur / sstb_rel_cur), and the registers the code after the cut reads (sstb_regs_rel and its extension
   sstb_regs_ntc); each concludes the statement's post (set_state_cg.v transport_sstate_post) at the cut's pc. The
   frame word at s1 + 48 (+0x0a4) and the zero word at the entry sp - 160 (+0x004) are read by no later instruction, so
   no cut carries them; the frame word at s1 + 24 (+0x154) is the notice piece's own (it stores it before the call of
   notice and loads it back after). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The two cut points and the return, as offsets from the listing's base: the notice path's first instruction
   (`sd a0, 24(s1)`, the fall-through of `beq s5, s3` at +0x150), the join (`lui a1, 0x45e03`, the target of that
   branch and the end of the notice path) and the `ret`. *)
Definition SSTB_NTC : Z := AF_set_state + 0x154.
Definition SSTB_REL : Z := AF_set_state + 0x214.
Definition SSTB_RET : Z := AF_set_state + 0x340.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 152 ..
   sp + 56 after `addi sp, sp, -160`). *)
Definition SSTB_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-2 frame's size. *)
Definition SSTB_FBYTES : Z := 256.
Lemma sstb_fbytes : fs_frame_bytes SSTATE_CID = SSTB_FBYTES.
Proof. reflexivity. Qed.
(* The window relations the pieces need: notice's window and ESTACK fit below a realigned sp at most 176 below the
   entry sp. *)
Lemma sstb_stk_bounds :
  SSTATE_STK = SSTATE_FRAME + SSTATE_ALIGN + NOTICE_STK /\ SSTATE_FRAME = 160 /\ SSTATE_ALIGN = 16 /\
  NOTICE_STK = 8240 /\ ESTACK = 4096 /\ SSTATE_STK = 8416.
Proof. repeat split; reflexivity. Qed.
(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma sstb_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma sstb_cut_pcs :
  BASE + AF_set_state = transportb_sigma TB_set_state /\ BASE + SSTB_NTC = 0x87420 /\ BASE + SSTB_REL = 0x874e0 /\
  BASE + SSTB_RET = 0x8760c.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_set_state_cg_holds_stmt that are not callee
   contracts. *)
Definition sstb_laws : Prop :=
  pc_stack_malloc (as_code B) SSTATE_CID = transportb_sigma TB___asan_stack_malloc_2 /\
  transport_cells B /\ trans_sstate_cells B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B.

(* The caller's facts (the premises of transport_set_state_cg at the entry registers regs), and what the head fixes
   before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -160`, `andi sp, sp, -32`); pos, the slot of
   the class-2 frame the stack malloc gave; F, the frame's address. *)
Definition sstb_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (st why : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 SSTATE_S /\ YK11.getr regs 11 = w64 st /\ YK11.getr regs 12 = w64 why /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - SSTATE_STK /\ spZ regs <= sp0 /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.set_state_m timg_B TF Bw st why = Some (Bw', tt) /\
  0 <= st < 2 ^ 31 /\ 0 <= why < 2 ^ 31 /\
  trans_tframe_at B lyc Sc W memc regs SSTATE_STK TF /\
  trans_rom_view_rd W memc /\
  sstate_apart TF Bw st why /\
  count_cid SSTATE_CID (frames Sc) < fs_frames SSTATE_CID /\
  st_nev S + k + SSTATE_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - SSTATE_FRAME) / 32) /\
  F = frame_addr lyc SSTATE_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + SSTB_FBYTES <= alloc_ceiling /\ in_app F SSTB_FBYTES.

(* What both cuts carry while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range sstate_wr Bw st why); the 13 saved words below the entry sp; the frame's last word, the address of its
   flag byte (astack_malloc_realizes' rdword). *)
Definition sstb_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (st why : Z) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((SSTATE_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= SSTATE_EV /\
  frames S2 = (SSTATE_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - SSTATE_STK) (spZ regs) (sstate_wr Bw st why) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SSTB_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + SSTB_FBYTES - 8) = Some (flag_addr lyc SSTATE_CID pos).

(* The state at the notice cut (+0x154), reached from the head only: the layout, the world and the event count are the
   call's; the blocks are the call's exactly (the stack malloc changes st_fs only); every byte of G outside the written
   range is the call's; the memory relates to the world Bw (the head stores no byte of G); and the state the code loaded
   is not st. *)
Definition sstb_ntc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (st why : Z) (Bw : list byte) (pos F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  sstb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  gx_kept_ex segs TG.G_HARNESS_B (sstate_wr Bw st why) W memc W mem2 /\
  tw_at TMAP_B (aview segs (w_H W) mem2) Bw /\
  TW.S_state Bw <> st.

(* The state at the release cut (+0x214), reached from the head (S_state Bw = st: W2 = W, ly2 = lyc, e = 0) or after
   notice returns: sstb_cur, and the post's X already holds: the world relation at the model's world Bw' and
   g_fail_next Bw' <= 1. *)
Definition sstb_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (st why : Z) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  sstb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, a0 = s9 = the
   frame, s8 = the frame's shadow address. *)
Definition sstb_regs_rel (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 10 = w64 F /\
  YK11.getr regs2 24 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 25 = w64 F.
(* The notice path also reads s2 = why, s3 = st, s4 = s, s5 = the state the code loaded (`lw`: sign-extended),
   s6 = s + 112, s10 = the shadow base and s11 = the shadow address of s + 112. *)
Definition sstb_regs_ntc (regs regs2 : bvmap 5 word) (st why : Z) (Bw : list byte) (sp1 F : Z) : Prop :=
  sstb_regs_rel regs regs2 sp1 F /\
  YK11.getr regs2 18 = w64 why /\ YK11.getr regs2 19 = w64 st /\ YK11.getr regs2 20 = w64 SSTATE_S /\
  YK11.getr regs2 21 = w64 (TW.S_state Bw) /\ YK11.getr regs2 22 = w64 (SSTATE_S + 112) /\
  YK11.getr regs2 26 = w64 SHADOW_OFF /\ YK11.getr regs2 27 = w64 (SHADOW_OFF + (SSTATE_S + 112) / 8).

(* The release cut, +0x214: from the state sstb_rel_cur, the post. *)
Definition sstb_rel_at : Prop :=
  sstb_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (st why : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    sstb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw' pos sp1 F ->
    sstb_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    sstb_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SSTB_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_sstate_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' st why).

(* The notice cut, +0x154: from the state sstb_ntc_cur, the post; the memset and notice contracts are its callees'. *)
Definition sstb_ntc_at : Prop :=
  sstb_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_B)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (st why : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate) (mem2 : word -> option byte)
         (md2 : Model) (regs2 : bvmap 5 word),
    sstb_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw' pos sp1 F ->
    sstb_ntc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F S2 mem2 md2 ->
    sstb_regs_ntc regs regs2 st why Bw sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SSTB_NTC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_sstate_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' st why).

(* The three pieces. rel: +0x214 .. the return. ntc: +0x154 .. +0x210, then the release cut. head: the entry ..
   +0x150, then one of the two cuts. *)
Definition sstb_rel_stmt : Prop := sstb_rel_at.
Definition sstb_ntc_stmt : Prop := sstb_rel_at -> sstb_ntc_at.
Definition sstb_head_stmt : Prop :=
  sstb_ntc_at -> sstb_rel_at -> @transport_set_state_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma sstb_holds_of : sstb_head_stmt -> sstb_ntc_stmt -> sstb_rel_stmt ->
  @transport_set_state_cg_holds_stmt fx rc B MT.
Proof. intros HEAD NTC REL. exact (HEAD (NTC REL) REL). Qed.
End cut.
