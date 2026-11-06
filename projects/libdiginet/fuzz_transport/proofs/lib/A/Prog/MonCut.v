(* MonCut: the cuts of the walk of maybe_online (fuzz_transport.asan 0x8b170 = transport_sigma TS_maybe_online,
   AF_maybe_online = 0x9f0c of lib/A/Prog/DgnTransportList.v), as STATEMENTS only, and the composition mon_holds_of:
   the statement transport_maybe_online_cg_holds_stmt of lib/A/Prog/maybe_online_cg.v from the three piece Props. The
   walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) from the entry to the return,
   with (MAYBEON_CID, pos) :: own while the class-2 frame is live. It has three pieces:
     head  +0x000 .. +0x1d0  the frame (`addi sp, sp, -96`), the zero word at sp, the 11 saves, s0, the realign into s1,
                             the two runtime cells (the flag word 1, so `beqz a2` at +0x05c is not taken), s8 = the
                             shadow base, s3 = s, `jal __asan_stack_malloc_2` (+0x064; lib/A/Prog/TransportGFrame.v
                             gx_stack_malloc_at), s2 = s7 = the frame, `bnez s2` taken, the frame's header and its 20
                             shadow bytes (s6 = their address), s4 = s + 112, s9 = its shadow address, the frame word
                             at s1 + 0, the checked loads of s + 112, s + 144, s + 140 and the three tests of :178
                             (`bne`, `beqz`, `beqz`: maybeon_go Bw = false goes to the release cut, mon_rel_at), the
                             checks of s + 176, s + 24 and s + 184, s5 = p = frame + 32, the store at s + 184 (:179),
                             then the notice cut (mon_ntc_at). Prop: mon_head_stmt.
     ntc   +0x1d4 .. +0x28c  the notice's shadow bytes 4 .. 12 := 0, `jal __asan_memset` (+0x204; p + 16, 0, 56), the
                             8-byte stores of 0x0000000200000002 at p and 0x0000000200000001 at p + 8, the checked store
                             of 2 at s + 112, the checked loads of s + 96 (notify) and s + 104 (ctx), `jalr a2`
                             (+0x264: notice at TI.ti_notice timg_A), the shadow bytes 4 .. 12 := 0xf8, to the release
                             cut. Prop: mon_ntc_stmt.
     rel   +0x290 .. +0x3b4  the header word 0x45e0360e at the frame, `beqz s2` not taken, the frame's 32 shadow bytes
                             := 0xf5, the flag pointer from the frame's last word, the store of 0 at it (the release:
                             TransportGFrame.v gx_flag_store_pi), `j +0x380`, sp = s0 - 96, the 11 reloads,
                             sp = sp + 96, `ret`. Prop: mon_rel_stmt.
   Each cut holds the caller's facts (mon_fix), the journal and the facts carried at the cut (mon_ntc_cur,
   mon_rel_cur), the registers the code after the cut reads (mon_regs_ntc, mon_regs_rel), and concludes the
   statement's post (maybe_online_cg.v transport_maybeon_post) at the cut's pc. The frame word the head stores at
   s1 + 0 (+0x130) and the zero word at the entry sp - 96 (+0x004) are read by no later instruction, so no cut carries
   them. The ntc piece's checks branch to the tail (+0x3fc and +0x418, +0x41c); +0x3fc returns to +0x228 when the
   shadow byte admits the access, so it reads s4 = s + 112. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import maybe_online_cg.
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

(* The two cut points, as offsets from the listing's base: the notice path's first instruction (`sb zero, 8(s6)`, the
   instruction after the store at s + 184) and the join (`lui a0, 0x45e03`, the target of the three tests). *)
Definition MON_NTC : Z := AF_maybe_online + 0x1d4.
Definition MON_REL : Z := AF_maybe_online + 0x290.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s9 (sd at sp + 88 ..
   sp + 8 after `addi sp, sp, -96`). *)
Definition MON_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24); (88, 25)].
(* The class-2 frame's size. *)
Definition MON_FBYTES : Z := 256.
Lemma mon_fbytes : fs_frame_bytes MAYBEON_CID = MON_FBYTES.
Proof. reflexivity. Qed.
(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma mon_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma mon_cut_pcs :
  BASE + AF_maybe_online = transport_sigma TS_maybe_online /\ BASE + MON_NTC = 0x8b344 /\ BASE + MON_REL = 0x8b400.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_maybe_online_cg_holds_stmt that are not
   callee contracts. *)
Definition mon_laws : Prop :=
  pc_stack_malloc (as_code B) MAYBEON_CID = transport_sigma TS___asan_stack_malloc_2 /\
  transport_cells B /\ trans_maybeon_cells B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS.

(* The caller's facts (the premises of transport_maybe_online_cg at the entry registers regs), and what the head fixes
   before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -96`, `andi sp, sp, -32`); pos, the slot of
   the class-2 frame the stack malloc gave; F, the frame's address. *)
Definition mon_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 MAYBEON_S /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - MAYBEON_STK /\ spZ regs <= sp0 /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.maybe_online_m timg_A TF Bw = Some (Bw', tt) /\
  trans_tframe_at B lyc Sc W memc regs MAYBEON_STK TF /\
  trans_rom_view_rd W memc /\
  maybeon_apart TF Bw /\
  count_cid MAYBEON_CID (frames Sc) < fs_frames MAYBEON_CID /\
  st_nev S + k + MAYBEON_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - MAYBEON_FRAME) / 32) /\
  F = frame_addr lyc MAYBEON_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + MON_FBYTES <= alloc_ceiling /\ in_app F MON_FBYTES.

(* What both cuts carry while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames where
   the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's window and
   written range maybeon_wr Bw); the 11 saved words below the entry sp; the frame's last word, the address of its flag
   byte (astack_malloc_realizes' rdword). *)
Definition mon_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((MAYBEON_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= MAYBEON_EV /\
  frames S2 = (MAYBEON_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - MAYBEON_STK) (spZ regs) (maybeon_wr Bw) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) MON_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + MON_FBYTES - 8) = Some (flag_addr lyc MAYBEON_CID pos).

(* The state at the notice cut (+0x1d4), reached from the head only, on the path where the test of :178 holds: the
   layout, the world and the event count are the call's; the blocks are the call's exactly (the stack malloc changes
   st_fs only); every byte of G outside the written range is the call's; the memory relates to the world
   maybeon_w1 Bw (after the store at s + 184); the test of :178 holds; and the state of maybeon_w1 Bw is S_WAKING
   (the store at s + 184 does not touch it), which the notice's old field (the constant 1 at p + 8) and the model's
   choice of call_notify read. *)
Definition mon_ntc_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw : list byte) (pos F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  mon_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  gx_kept_ex segs TG.G_HARNESS (maybeon_wr Bw) W memc W mem2 /\
  tw_at TMAP_A (aview segs (w_H W) mem2) (maybeon_w1 Bw) /\
  maybeon_go Bw = true /\
  TW.S_state (maybeon_w1 Bw) = TS0.DIGINET_S_WAKING.

(* The state at the release cut (+0x290), reached from the head (maybeon_go Bw = false: W2 = W, ly2 = lyc, e = 0) or
   after notice returns: mon_cur, and the post's X already holds: the world relation at the model's world Bw' and
   g_fail_next Bw' <= 1. *)
Definition mon_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  mon_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s7 = the
   frame, s6 = the frame's shadow address. *)
Definition mon_regs_rel (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 22 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 23 = w64 F /\
  YK11.getr regs2 26 = YK11.getr regs 26 /\ YK11.getr regs2 27 = YK11.getr regs 27.
(* The notice path also reads s3 = s, s4 = s + 112, s5 = p = the frame + 32, s8 = the shadow base and s9 = the shadow
   address of s + 112. *)
Definition mon_regs_ntc (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  mon_regs_rel regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 MAYBEON_S /\ YK11.getr regs2 20 = w64 (MAYBEON_S + 112) /\
  YK11.getr regs2 21 = w64 (F + 32) /\
  YK11.getr regs2 24 = w64 SHADOW_OFF /\ YK11.getr regs2 25 = w64 (SHADOW_OFF + (MAYBEON_S + 112) / 8).

(* The release cut, +0x290: from the state mon_rel_cur, the post. *)
Definition mon_rel_at : Prop :=
  mon_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (TF : option TI.tframe)
         (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs)
         (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    mon_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw' pos sp1 F ->
    mon_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    mon_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + MON_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_maybeon_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The notice cut, +0x1d4: from the state mon_ntc_cur, the post; the memset and notice contracts are its callees'. *)
Definition mon_ntc_at : Prop :=
  mon_laws ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (TF : option TI.tframe)
         (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    mon_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw' pos sp1 F ->
    mon_ntc_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F S2 mem2 md2 ->
    mon_regs_ntc regs regs2 sp1 F ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + MON_NTC)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_maybeon_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The three pieces. rel: +0x290 .. the return. ntc: +0x1d4 .. +0x28c, then the release cut. head: the entry ..
   +0x1d0, then one of the two cuts. *)
Definition mon_rel_stmt : Prop := mon_rel_at.
Definition mon_ntc_stmt : Prop := mon_rel_at -> mon_ntc_at.
Definition mon_head_stmt : Prop :=
  mon_ntc_at -> mon_rel_at -> @transport_maybe_online_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma mon_holds_of : mon_head_stmt -> mon_ntc_stmt -> mon_rel_stmt ->
  @transport_maybe_online_cg_holds_stmt fx rc B MT.
Proof. intros HEAD NTC REL. exact (HEAD (NTC REL) REL). Qed.
End cut.
