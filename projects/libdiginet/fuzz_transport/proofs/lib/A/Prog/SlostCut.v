(* SlostCut: the cuts of the walk of session_lost (fuzz_transport.asan 0x88f08 = transport_sigma TS_session_lost,
   AF_session_lost = 0x7ca4 of lib/A/Prog/DgnTransportList.v), as STATEMENTS only, and the composition
   slost_holds_of: the statement transport_session_lost_cg_holds_stmt of lib/A/Prog/session_lost_cg.v from the three
   piece Props. The walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) from the entry
   to the return, with (SLOST_CID, pos) :: own while the class-2 frame is live. It has three pieces:
     head  +0x000 .. +0x178  the frame, the 13 saves, s0, the realign into s1, s4 = why, the two runtime cells (the flag
                             word 1, so `beq a2, zero` is not taken), s9 = the shadow base, s3 = s, `jal
                             __asan_stack_malloc_2` (+0x70; lib/A/Prog/TransportGFrame.v gx_stack_malloc_at), the
                             frame's header and its 20 shadow bytes, the frame word at s1 + 16, the checked stores of 0
                             at s + 212 and s + 168, s5 = s + 112, s10 = its shadow address, the checked load of s11 =
                             S_state (slost_w1 Bw) and `beq s11, zero` (+0x178): S_IDLE goes to the release cut
                             (slost_rel_at), any other state to the notice cut (slost_ntc_at). Prop: slost_head_stmt.
     ntc   +0x17c .. +0x22c  s6 = p = frame + 32, its shadow bytes 4 .. 12 := 0, `jal __asan_memset` (+0x1b0; p + 16,
                             0, 56), the stores of 2 (8 bytes) at p, of s11 at p + 8 and of why at p + 12, the checked
                             store of 0 at s + 112, the checked loads of s + 96 (notify) and s + 104 (ctx), `jalr a2`
                             (+0x204: notice at TI.ti_notice timg_A), the shadow bytes 4 .. 12 := 0xf8, to the release
                             cut. Prop: slost_ntc_stmt.
     rel   +0x230 .. +0x35c  the header word 0x45e0360e at the frame, `beq s2, zero` not taken, the frame's 32 shadow
                             bytes := 0xf5, the flag pointer from the frame's last word, the store of 0 at it (the
                             release: TransportGFrame.v gx_flag_store_pi), `j +0x320`, sp = s0 - 128, the 13 reloads,
                             sp = sp + 128, `ret`. Prop: slost_rel_stmt.
   Each cut holds the caller's facts (slost_fix), the journal and the facts carried at the cut (slost_ntc_cur,
   slost_rel_cur), the registers the code after the cut reads (slost_regs_ntc, slost_regs_rel), and concludes the
   statement's post (session_lost_cg.v transport_slost_post) at the cut's pc. The frame word the head stores at s1 + 16
   (+0x13c) is read by no later instruction of either path, so no cut carries it. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The two cut points, as offsets from the listing's base: the notice path's first instruction (`addi s6, s8, 32`,
   the fall-through of `beq s11, zero` at +0x178) and the join (`lui a0, 0x45e03`, the target of that branch). *)
Definition SLOST_NTC : Z := AF_session_lost + 0x17c.
Definition SLOST_REL : Z := AF_session_lost + 0x230.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 120 ..
   sp + 24 after `addi sp, sp, -128`). *)
Definition SLOST_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-2 frame's size. *)
Definition SLOST_FBYTES : Z := 256.
Lemma slost_fbytes : fs_frame_bytes SLOST_CID = SLOST_FBYTES.
Proof. reflexivity. Qed.
(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma slost_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma slost_cut_pcs :
  BASE + AF_session_lost = transport_sigma TS_session_lost /\ BASE + SLOST_NTC = 0x89084 /\ BASE + SLOST_REL = 0x89138.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_session_lost_cg_holds_stmt that are not
   callee contracts. *)
Definition slost_laws : Prop :=
  pc_stack_malloc (as_code B) SLOST_CID = transport_sigma TS___asan_stack_malloc_2 /\
  transport_cells B /\ trans_slost_cells B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS.

(* The caller's facts (the premises of transport_session_lost_cg at the entry registers regs), and what the head
   fixes before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -128`, `andi sp, sp, -32`); pos, the
   slot of the class-2 frame the stack malloc gave; F, the frame's address. *)
Definition slost_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (why : Z) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 SLOST_S /\ YK11.getr regs 11 = w64 why /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - SLOST_STK /\ spZ regs <= sp0 /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.session_lost_m timg_A TF Bw why = Some (Bw', tt) /\
  0 <= why < 2 ^ 31 /\
  trans_tframe_at B lyc Sc W memc regs SLOST_STK TF /\
  trans_rom_view_rd W memc /\
  slost_apart TF Bw why /\
  count_cid SLOST_CID (frames Sc) < fs_frames SLOST_CID /\
  st_nev S + k + SLOST_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - SLOST_FRAME) / 32) /\
  F = frame_addr lyc SLOST_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + SLOST_FBYTES <= alloc_ceiling /\ in_app F SLOST_FBYTES.

(* What both cuts carry while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range slost_wr Bw why); the 13 saved words below the entry sp; the frame's last word, the address of its
   flag byte (astack_malloc_realizes' rdword). *)
Definition slost_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (why : Z) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((SLOST_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= SLOST_EV /\
  frames S2 = (SLOST_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - SLOST_STK) (spZ regs) (slost_wr Bw why) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SLOST_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + SLOST_FBYTES - 8) = Some (flag_addr lyc SLOST_CID pos).

(* The state at the notice cut (+0x17c), reached from the head only: the layout, the world and the event count are the
   call's; the blocks are the call's exactly (the stack malloc changes st_fs only); every byte of G outside the written
   range is the call's; the memory relates to the world slost_w1 Bw (after the stores at s + 212 and s + 168); and the
   state the code loaded is not S_IDLE. *)
Definition slost_ntc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (why : Z) (Bw : list byte) (pos F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  slost_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  gx_kept_ex segs TG.G_HARNESS (slost_wr Bw why) W memc W mem2 /\
  tw_at TMAP_A (aview segs (w_H W) mem2) (slost_w1 Bw) /\
  TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE.

(* The state at the release cut (+0x230), reached from the head (S_IDLE: W2 = W, ly2 = lyc, e = 0) or after notice
   returns: slost_cur, and the post's X already holds: the world relation at the model's world Bw' and
   g_fail_next Bw' <= 1. *)
Definition slost_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (why : Z) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  slost_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s8 = the
   frame, s7 = the frame's shadow address. *)
Definition slost_regs_rel (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 23 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 24 = w64 F.
(* The notice path also reads s3 = s, s4 = why, s9 = the shadow base, s10 = the shadow address of s + 112 and s11 =
   the state the code loaded (`lw`: sign-extended). *)
Definition slost_regs_ntc (regs regs2 : bvmap 5 word) (why : Z) (Bw : list byte) (sp1 F : Z) : Prop :=
  slost_regs_rel regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 SLOST_S /\ YK11.getr regs2 20 = w64 why /\
  YK11.getr regs2 25 = w64 SHADOW_OFF /\ YK11.getr regs2 26 = w64 (SHADOW_OFF + (SLOST_S + 112) / 8) /\
  YK11.getr regs2 27 = w64 (TW.S_state (slost_w1 Bw)).

(* The release cut, +0x230: from the state slost_rel_cur, the post. *)
Definition slost_rel_at : Prop :=
  slost_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (why : Z) (TF : option TI.tframe)
         (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs)
         (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    slost_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw' pos sp1 F ->
    slost_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    slost_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SLOST_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_slost_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' why).

(* The notice cut, +0x17c: from the state slost_ntc_cur, the post; the memset and notice contracts are its callees'. *)
Definition slost_ntc_at : Prop :=
  slost_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (why : Z) (TF : option TI.tframe)
         (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    slost_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw' pos sp1 F ->
    slost_ntc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F S2 mem2 md2 ->
    slost_regs_ntc regs regs2 why Bw sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SLOST_NTC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_slost_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' why).

(* The three pieces. rel: +0x230 .. the return. ntc: +0x17c .. +0x22c, then the release cut. head: the entry ..
   +0x178, then one of the two cuts. *)
Definition slost_rel_stmt : Prop := slost_rel_at.
Definition slost_ntc_stmt : Prop := slost_rel_at -> slost_ntc_at.
Definition slost_head_stmt : Prop :=
  slost_ntc_at -> slost_rel_at -> @transport_session_lost_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma slost_holds_of : slost_head_stmt -> slost_ntc_stmt -> slost_rel_stmt ->
  @transport_session_lost_cg_holds_stmt fx rc B MT.
Proof. intros HEAD NTC REL. exact (HEAD (NTC REL) REL). Qed.
End cut.
