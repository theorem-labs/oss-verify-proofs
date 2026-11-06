(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths and names changed, the cell rows are this unit's AsanCells rows, and the read-only-image helper is dropped. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths and module names changed; 271 of its 440 lines of code are new or changed and 352 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportFevt.v, with its module paths and module names changed; 1511 of its 1595 lines of code are new or changed and 356 lines of the source are left out. *)
(* diginet_frame_build_walk: the image-A walk of diginet_frame_build (fuzz_transport.asan 0x8bcf8 =
   transport_sigma TS_diginet_frame_build), in the G form of lib/A/Prog/diginet_frame_build_cg.v.
   fb_cg_holds_of_segs proves transport_diginet_frame_build_cg_holds_stmt from the sixteen footprint statements of
   lib/A/Prog/diginet_frame_build_iface.v, taken as Section hypotheses; transport_diginet_frame_build_cg_holds, at
   the end of this file, applies it to the segment lemmas of diginet_frame_build_seg_a.v, _seg_h1.v, _seg_loop.v,
   _seg_h2a.v and _seg_h2b.v.

   The walk runs in the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []), with no journal of its
   own: out is a side-stack frame of the caller or a byte range of G, neither of which an inner journal's footprint
   could name. Between two cuts the state is fb_st: the caller's journal at count k, the call state's frames and
   blocks, no meter charge, the prologue's frame, and the post's two keep facts carried from the entry memory
   (TransportGCg.v acall_kept_g over [spZ regs - FRAME_FB_STK, spZ regs) and gx_kept_ex, outside out's range); and
   fb_rd: dst's, src's, the header's and (when not empty) the body's bytes placed by trans_src_ok with their entry
   views, and out's two shadow facts. The cut points (as in the iface):
     1. fb_seg1M (mode not 0 or 1: -1), fb_seg1L (body_len > 1484: -4), or fb_seg1: the 96-byte frame, the journal
        after its write (fb_entry, fb_aj_write);
     2. diginet_body_check (PBC.transport_diginet_body_check_cg, a donor-form callee lifted by TransportGCg.v
        gx_call_cg, fb_bc_call); the bytes read later keep their placement by DgnTransportCg.v trans_src_ok_acall_g;
        a0 = body_check bb (DgnSpec body_check_spec): -10 by fb_seg2R, else cap < len gives -5 by fb_seg2S, else
        fb_seg2C (fb_at_retbc);
     3. __asan_memcpy(out, dst, 6), fb_seg3, __asan_memcpy(out + 6, src, 6) (TransportGCg.v gx_intrin_at, fb_memcpy);
     4. fb_h1, fb_loop, fb_h2a, fb_h2b: the 18 header bytes, the journal after each write (fb_st_write);
     5. fb_seg4Z, or fb_seg4 and __asan_memcpy(out + 30, body, body_len); fb_seg5Z, or fb_seg5 and
        __asan_memset(out + 30 + body_len, 0, 30 - body_len) (fb_memset);
     6. fb_epi, the return and the post (fb_at_epi): the journal, the keep facts, the code build_code_w bb cap mode,
        and the cap bytes at out (build_out_w; diginet_frame_build_kit.v fbk_frame_bytes). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI04 YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame Cells Step ExecF PropExec Regs6ss MState.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Img0 AsanCells AE2k TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_build_c diginet_frame_build_w_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGRwA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_cg diginet_frame_build_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_body_check_cg diginet_frame_build_iface.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_frame_build_seg_a diginet_frame_build_seg_h1
  diginet_frame_build_seg_loop diginet_frame_build_seg_h2a diginet_frame_build_seg_h2b.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module PBuild := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_build_c.
Module PBuildW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_build_w_c.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_body_check_cg.
Module FBI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_build_iface.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- numbers of the image and of the statement ---- *)

Lemma fb_stk : 96 + ESTACK <= FRAME_FB_STK /\ 96 + PBC.TRANS_BC_STK <= FRAME_FB_STK /\ ESTACK = 4096.
Proof. unfold FRAME_FB_STK, FRAME_FB_FRAME. split; [lia | split; [lia | reflexivity]]. Qed.

(* The return addresses of the five calls: FB_RET_BC, FB_RET_C1, FB_RET_C2, FB_RET_C3, FB_EPI. *)
Lemma fb_ra : forall o, In o [0xa8; 0xe4; 0xf4; 0x3bc; 0x3d0] ->
  4096 <= FBI.FB_AT o < 2 ^ 63 /\ FBI.FB_AT o mod 2 = 0.
Proof.
  intros o Ho. cbn [In] in Ho.
  destruct Ho as [<- | [<- | [<- | [<- | [<- | []]]]]]; split; [split| |split| |split| |split| |split|];
    vm_compute; first [reflexivity | discriminate].
Qed.

Lemma fb_code_range : forall (bb : list byte) cap, - 2 ^ 31 <= build_code bb cap < 2 ^ 31.
Proof.
  intros bb cap. unfold build_code, frame_len.
  destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|].
  destruct (system_at bb); [lia|].
  destruct (Z.ltb_spec cap (Z.max 60 (30 + Z.of_nat (length bb)))); lia.
Qed.

Lemma fb_code_w_range : forall (bb : list byte) cap mode, - 2 ^ 31 <= PBuildW.build_code_w bb cap mode < 2 ^ 31.
Proof.
  intros bb cap mode. unfold PBuildW.build_code_w.
  destruct ((mode =? 0) || (mode =? 1)); [apply fb_code_range | lia].
Qed.

(* Mode 0 or 1: the wide code and bytes are build_code and build_out. *)
Lemma fb_w01 : forall dmac smac send ack retry cmd ncmds (bb : list byte) mode (oj : list byte),
  mode = 0 \/ mode = 1 ->
  PBuildW.build_code_w bb (Z.of_nat (length oj)) mode = build_code bb (Z.of_nat (length oj)) /\
  PBuildW.build_out_w dmac smac send ack retry cmd ncmds bb mode oj =
  PBuild.build_out dmac smac send ack retry cmd ncmds bb mode oj.
Proof. intros dmac smac send ack retry cmd ncmds bb mode oj [-> | ->]; split; reflexivity. Qed.

(* Any other mode: -1, and no byte written. *)
Lemma fb_wM : forall dmac smac send ack retry cmd ncmds (bb : list byte) mode (oj : list byte),
  mode <> 0 -> mode <> 1 ->
  PBuildW.build_code_w bb (Z.of_nat (length oj)) mode = -1 /\
  PBuildW.build_out_w dmac smac send ack retry cmd ncmds bb mode oj = oj.
Proof.
  intros dmac smac send ack retry cmd ncmds bb mode oj H0 H1.
  assert (E : PBuildW.build_code_w bb (Z.of_nat (length oj)) mode = -1).
  { unfold PBuildW.build_code_w. rewrite (proj2 (Z.eqb_neq mode 0) H0), (proj2 (Z.eqb_neq mode 1) H1). reflexivity. }
  split; [exact E|]. unfold PBuildW.build_out_w. cbv zeta. rewrite E. reflexivity.
Qed.

Lemma fb_ceil_val {rc : YM05.RunCeil} : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact (proj1 (@YM05.alloc_ceiling_val rc)). Qed.

(* A visible byte is not hidden. *)
Lemma fb_vis_h : forall (W1 : world tfibsegs) m1 a, aview tfibsegs (w_H W1) m1 a <> None -> w_H W1 (Z_to_bv 64 a) = false.
Proof.
  intros W1 m1 a H. destruct (aview tfibsegs (w_H W1) m1 a) as [v|] eqn:E; [exact (fbk_aview_vis W1 m1 a v E)|].
  exfalso. exact (H eq_refl).
Qed.

(* A present byte stays present when the memory grows. *)
Lemma fb_pres_grow : forall (H : word -> bool) (m1 m2 : word -> option byte) a,
  YK1b.mem_grows m1 m2 -> apresent H m1 a -> apresent H m2 a.
Proof.
  intros H m1 m2 a MG [Hh [b Hb]]. split; [exact Hh|].
  destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply (MG (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
Qed.

(* rw_cells from garr8 of visible bytes whose footprint view is writable (a present byte, or a byte of G). *)
Lemma fb_rw_of_garr8 : forall (H : word -> bool) (m : word -> option byte) A cs,
  LCells.cells_wf cs -> 0 <= A -> A + Z.of_nat (LCells.cells_size cs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (LCells.cells_size cs) ->
     H (Z_to_bv 64 (A + i)) = false /\ wview AImg0.rsegs m (LMem.wa (A + i)) <> None) ->
  garr8 tfibsegs (mrestrict H m) A (map (fun b : byte => bv_unsigned b) (LCells.cells_bytes cs)) ->
  LStep.rw_cells AImg0.rsegs m A cs.
Proof.
  intros H m A cs Hwf H0 H1 Hp Hg. pose proof (LCells.cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|] |].
  - apply (decode_garr8_bytes H m A); [exact H0 | rewrite L; exact H1 | | exact Hg].
    intros j Hj. rewrite L in Hj. exact (proj1 (Hp (Z.of_nat j) ltac:(lia))).
  - split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (proj2 (Hp i Hi)).
Qed.

(* The two shadow facts of [q, q + n) read only the shadow band [kLowMemEnd, kHighShadowEnd) (DgnTransportCg.v
   trans_rd_ok_view). *)
Lemma fb_ra_band : forall (W1 W2 : world tfibsegs) m1 m2 q n, amem_range q n -> 0 <= q ->
  range_addressable (aview tfibsegs (w_H W1) m1) SHADOW_OFF q n ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs (w_H W2) m2 s = aview tfibsegs (w_H W1) m1 s) ->
  range_addressable (aview tfibsegs (w_H W2) m2) SHADOW_OFF q n.
Proof.
  intros W1 W2 m1 m2 q n R4 R5 R2 K2.
  assert (Hq : q + n <= kHighMemEnd - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  unfold kHighMemEnd in Hq.
  intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite K2; [exact Hs|]. unfold shadow_of_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

Lemma fb_hull_band : forall (W1 W2 : world tfibsegs) m1 m2 q n, amem_range q n -> 0 <= q ->
  shadow_hull_vis (aview tfibsegs (w_H W1) m1) q n ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs (w_H W2) m2 s = aview tfibsegs (w_H W1) m1 s) ->
  shadow_hull_vis (aview tfibsegs (w_H W2) m2) q n.
Proof.
  intros W1 W2 m1 m2 q n R4 R5 R3 K2.
  assert (Hq : q + n <= kHighMemEnd - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  unfold kHighMemEnd in Hq.
  intros s Hs. rewrite K2; [exact (R3 s Hs)|]. unfold shadow_addr, SHADOW_OFF in Hs.
  unfold kLowMemEnd, kHighShadowEnd.
  pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.

Ltac fb_kp HP := etransitivity; [apply HP; unfold acallee_saved; lia | eassumption].
Ltac fb_regs := repeat match goal with |- _ /\ _ => split end;
  (etransitivity; [eassumption | first [reflexivity | eassumption]]).
Ltac fb_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section Segs.
Hypothesis SEG1 : FBI.fb_seg1_stmt.
Hypothesis SEG1L : FBI.fb_seg1L_stmt.
Hypothesis SEG1M : FBI.fb_seg1M_stmt.
Hypothesis SEG2R : FBI.fb_seg2R_stmt.
Hypothesis SEG2S : FBI.fb_seg2S_stmt.
Hypothesis SEG2C : FBI.fb_seg2C_stmt.
Hypothesis SEG3 : FBI.fb_seg3_stmt.
Hypothesis H1S : FBI.fb_h1_stmt.
Hypothesis LOOPS : FBI.fb_loop_stmt.
Hypothesis H2AS : FBI.fb_h2a_stmt.
Hypothesis H2BS : FBI.fb_h2b_stmt.
Hypothesis SEG4Z : FBI.fb_seg4Z_stmt.
Hypothesis SEG4 : FBI.fb_seg4_stmt.
Hypothesis SEG5Z : FBI.fb_seg5Z_stmt.
Hypothesis SEG5 : FBI.fb_seg5_stmt.
Hypothesis EPI : FBI.fb_epi_stmt.

Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation ajournalG := (@ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 []).

Lemma fb_ceil : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact (@fb_ceil_val rc). Qed.

Section Walk.
Hypothesis HCELLS : transport_cells B.
Hypothesis HROU : trans_ro_rd_unowned B.
Hypothesis HROE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGU : trans_g_unowned B.
Hypothesis HGE : trans_g_no_errno B.
Hypothesis AMEMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis AMEMSET : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset).
Hypothesis ABC : forall fx' : YK11.FPState,
  @PBC.transport_diginet_body_check_cg fx' rc B MT (transport_sigma TS_diginet_body_check).

Lemma fb_GOK : gx_ok segs B G.
Proof. exact (G_HARNESS_gx_ok B HGU). Qed.

Lemma fb_GNE : gx_noerrno B G.
Proof. exact (G_HARNESS_gx_noerrno B HGE). Qed.

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (out dst src hp body mode send ack retry cmd ncmds : Z) (dmac smac bb oj : list byte).
Hypothesis HJ : ajournalG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 out.
Hypothesis H11 : YK11.getr regs 11 = w64 (Z.of_nat (length oj)).
Hypothesis H12 : YK11.getr regs 12 = w64 dst.
Hypothesis H13 : YK11.getr regs 13 = w64 src.
Hypothesis H14 : YK11.getr regs 14 = w64 hp.
Hypothesis H15 : YK11.getr regs 15 = w64 body.
Hypothesis H16 : YK11.getr regs 16 = w64 (Z.of_nat (length bb)).
Hypothesis H17 : YK11.getr regs 17 = w64 mode.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - FRAME_FB_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hout0 : out <> 0.
Hypothesis Hdst0 : dst <> 0.
Hypothesis Hsrc0 : src <> 0.
Hypothesis Hhp0 : hp <> 0.
Hypothesis Hbody0 : body <> 0 \/ length bb = 0%nat.
Hypothesis Hmode : - 2 ^ 31 <= mode < 2 ^ 31.
Hypothesis Hsend : 0 <= send < 2 ^ 32.
Hypothesis Hack : 0 <= ack < 2 ^ 32.
Hypothesis Hretry : 0 <= retry < 2 ^ 16.
Hypothesis Hcmd : 0 <= cmd < 2 ^ 8.
Hypothesis Hncmds : 0 <= ncmds < 2 ^ 8.
Hypothesis Hout : trans_out_ok B lyc Sc W memc out (Z.of_nat (length oj)).
Hypothesis Htwr : transport_twr_ok_g segs B G STK sp0 FP ly S lyc Sc own W memc (spZ regs - FRAME_FB_FRAME)
  out (Z.of_nat (length oj)).
Hypothesis Goj : garr8 segs (mrestrict (w_H W) memc) out (map bz oj).
Hypothesis Ldmac : length dmac = 6%nat.
Hypothesis Tdst : trans_src_ok B lyc Sc W memc dst 6.
Hypothesis Odst : decode_off_win regs FRAME_FB_STK dst 6.
Hypothesis Gdmac : garr8 segs (mrestrict (w_H W) memc) dst (map bz dmac).
Hypothesis Lsmac : length smac = 6%nat.
Hypothesis Tsrc : trans_src_ok B lyc Sc W memc src 6.
Hypothesis Osrc : decode_off_win regs FRAME_FB_STK src 6.
Hypothesis Gsmac : garr8 segs (mrestrict (w_H W) memc) src (map bz smac).
Hypothesis Tbody : trans_src_ok B lyc Sc W memc body (Z.of_nat (length bb)).
Hypothesis Obody : decode_off_win regs FRAME_FB_STK body (Z.of_nat (length bb)).
Hypothesis Gbb : garr8 segs (mrestrict (w_H W) memc) body (map bz bb).
Hypothesis Fhdr : decode_in_fake lyc Sc (hp + 4) 12.
Hypothesis Rhdr : decode_rd_ok W memc (hp + 4) 12.
Hypothesis Ohdr : decode_off_win regs FRAME_FB_STK (hp + 4) 12.
Hypothesis Ghdr : garr8 segs (mrestrict (w_H W) memc) (hp + 4) (frame_fb_hdr_bytes send ack retry cmd ncmds).
Hypothesis Ddst : out + Z.of_nat (length oj) <= dst \/ dst + 6 <= out.
Hypothesis Dsrc : out + Z.of_nat (length oj) <= src \/ src + 6 <= out.
Hypothesis Dhdr : out + Z.of_nat (length oj) <= hp + 4 \/ hp + 16 <= out.
Hypothesis Dbody : out + Z.of_nat (length oj) <= body \/ body + Z.of_nat (length bb) <= out.
Hypothesis Hcid : count_cid PBC.TRANS_BC_CID (frames Sc) < fs_frames PBC.TRANS_BC_CID.
Hypothesis Hnev : st_nev S + k + FRAME_FB_EV <= EV_MAX.

(* lia with the statement's disjunctive premises (the four disjointness premises and the five nonzero premises)
   cleared from the subgoal: lia splits each disjunction of its context. *)
Ltac fb_lia := try clear Ddst Dsrc Dhdr Dbody Hbody0 Hout0 Hdst0 Hsrc0 Hhp0; lia.

Local Abbreviation cap := (Z.of_nat (length oj)).
Local Abbreviation blen := (Z.of_nat (length bb)).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).
Local Abbreviation RNGW W1 := (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W1).
Local Abbreviation POST := (@frame_fb_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs out dmac
  smac send ack retry cmd ncmds bb mode oj).
Local Abbreviation AJ ly1 S1 W1 m1 md1 := (ajournalG STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k).
Local Abbreviation Eout := (fun a : Z => out <= a < out + Z.of_nat (length oj)).
Local Abbreviation KP W1 m1 := (acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W1 m1 (spZ regs - FRAME_FB_STK)
  (spZ regs) (fun a : Z => out <= a < out + Z.of_nat (length oj))).
Local Abbreviation KX W1 m1 := (gx_kept_ex segs TG.G_HARNESS (fun a : Z => out <= a < out + Z.of_nat (length oj))
  W memc W1 m1).

(* The frame of the prologue: the caller's s10, s9, ..., s0 and ra at [spZ regs - 96, spZ regs). *)
Definition fb_frame (m : word -> option byte) : Prop :=
  LStep.rw_cells AImg0.rsegs m (spZ regs - 96)
    (FBI.fb_fr (GR regs 26) (GR regs 25) (GR regs 24) (GR regs 23) (GR regs 22) (GR regs 21) (GR regs 20)
       (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)).

(* The state between two cuts. *)
Definition fb_st (ly1 : alayout) (S1 : astate) (W1 : world segs) (m1 : word -> option byte) (md1 : Model) : Prop :=
  AJ ly1 S1 W1 m1 md1 /\ frames S1 = frames Sc /\ Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) /\
  mo_le MT Sc S1 0 /\ fb_frame m1 /\ KP W1 m1 /\ KX W1 m1.

(* A range the function reads: placed by trans_src_ok at the state, with its entry bytes. *)
Definition fb_sv (ly1 : alayout) (S1 : astate) (W1 : world segs) (m1 : word -> option byte) (q : Z) (l : list byte)
  : Prop :=
  trans_src_ok B ly1 S1 W1 m1 q (Z.of_nat (length l)) /\
  forall j, (j < length l)%nat -> aview segs (w_H W1) m1 (q + Z.of_nat j) = Some (bz (nth j l (b8 0))).

(* What the function reads at a state: dmac, smac, the body (when not empty), the 12 header bytes, and out's two
   shadow facts. *)
Definition fb_rd (ly1 : alayout) (S1 : astate) (W1 : world segs) (m1 : word -> option byte) : Prop :=
  fb_sv ly1 S1 W1 m1 dst dmac /\ fb_sv ly1 S1 W1 m1 src smac /\
  ((0 < length bb)%nat -> fb_sv ly1 S1 W1 m1 body bb) /\
  fb_sv ly1 S1 W1 m1 (hp + 4) (FBI.fb_hdr_in send ack retry cmd ncmds) /\
  range_addressable (aview segs (w_H W1) m1) SHADOW_OFF out cap /\
  (0 < cap -> shadow_hull_vis (aview segs (w_H W1) m1) out cap).

Definition fb_stR ly1 S1 W1 m1 md1 : Prop := fb_st ly1 S1 W1 m1 md1 /\ fb_rd ly1 S1 W1 m1.

(* The cap bytes at out, as views. *)
Definition fb_outv (W1 : world segs) (m1 : word -> option byte) (l : list byte) : Prop :=
  length l = length oj /\
  forall j, (j < length l)%nat -> aview segs (w_H W1) m1 (out + Z.of_nat j) = Some (bz (nth j l (b8 0))).

(* The registers every cut keeps: sp at the frame, gp, tp, s11. *)
Definition fb_k4 (rg : bvmap 5 word) : Prop :=
  GR rg 2 = Z_to_bv 64 (spZ regs - 96) /\ GR rg 3 = GR regs 3 /\ GR rg 4 = GR regs 4 /\ GR rg 27 = GR regs 27.
(* The saved registers after diginet_body_check: s0 = out, s1 = body_len, s2 = body, s3 = hp, s4 = mode, s5 = src,
   s6 = dst, s7 = cap, s10 = the shadow offset; from fb_seg2C on also s8 = len and s9 = 30 + body_len. *)
Definition fb_s9 (rg : bvmap 5 word) : Prop :=
  fb_k4 rg /\ GR rg 8 = Z_to_bv 64 out /\ GR rg 9 = Z_to_bv 64 blen /\ GR rg 18 = Z_to_bv 64 body /\
  GR rg 19 = Z_to_bv 64 hp /\ GR rg 20 = Z_to_bv 64 mode /\ GR rg 21 = Z_to_bv 64 src /\
  GR rg 22 = Z_to_bv 64 dst /\ GR rg 23 = Z_to_bv 64 cap /\ GR rg 26 = Z_to_bv 64 FC.ASAN_K.
Definition fb_sregs (rg : bvmap 5 word) : Prop :=
  fb_s9 rg /\ GR rg 24 = Z_to_bv 64 (FBI.fb_len blen) /\ GR rg 25 = Z_to_bv 64 (30 + blen).

(* The bytes at out after each write of the success path. *)
Definition fb_L1 : list byte := FBI.fb_put oj 0 dmac.
Definition fb_L2 : list byte := FBI.fb_put fb_L1 6 smac.
Definition fb_L3 : list byte := FBI.fb_put fb_L2 12 (put16 0x885f ++ put16 (16 + Z.of_nat (length bb))).
Definition fb_L4 : list byte := FBI.fb_put fb_L3 16 (put16 (FBI.fb_sum bb mode) ++ put32 send).
Definition fb_L5 : list byte := FBI.fb_put fb_L4 22 (put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds]).
Definition fb_L6 : list byte := FBI.fb_put fb_L5 30 bb.
Definition fb_L7 : list byte := FBI.fb_put fb_L6 (30 + length bb) (repeat (b8 0) (30 - length bb)).

(* ---- registers ---- *)

Lemma fb_k4_pres : forall r1 r2, fb_k4 r1 -> aregs_preserved r1 r2 -> fb_k4 r2.
Proof.
  intros r1 r2 (K2 & K3 & K4 & K27) HP. unfold fb_k4.
  split; [fb_kp HP|]. split; [fb_kp HP|]. split; [fb_kp HP|]. fb_kp HP.
Qed.

Lemma fb_s9_pres : forall r1 r2, fb_s9 r1 -> aregs_preserved r1 r2 -> fb_s9 r2.
Proof.
  intros r1 r2 (HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) HP. unfold fb_s9.
  split; [exact (fb_k4_pres r1 r2 HK HP)|].
  repeat match goal with |- _ /\ _ => split end; fb_kp HP.
Qed.

Lemma fb_sregs_pres : forall r1 r2, fb_sregs r1 -> aregs_preserved r1 r2 -> fb_sregs r2.
Proof.
  intros r1 r2 (H9 & K24 & K25) HP. unfold fb_sregs.
  split; [exact (fb_s9_pres r1 r2 H9 HP)|]. split; fb_kp HP.
Qed.

(* ---- the entry state ---- *)

Lemma fb_HARc : AR segs B lyc Sc W memc mdc.
Proof. exact (ajournal_gx_AR segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ). Qed.

Lemma fb_sp : alloc_ceiling + FRAME_FB_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ sp0 mod 16 = 0.
Proof.
  destruct (gx_open segs B G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (memS & J & _ & _).
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16' & _ & Hc & Hlo & Hhi & H47 & _) & _).
  fb_lia.
Qed.

(* The stack window of the call is present at every state of the caller's journal. *)
Lemma fb_win : forall ly1 S1 W1 m1 md1, AJ ly1 S1 W1 m1 md1 ->
  forall a, spZ regs - FRAME_FB_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 HJ1 a Ha.
  destruct (gx_open segs B G STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k HJ1) as (memS & J & _ & _).
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). apply Hp. fb_lia.
Qed.

(* Every state of the caller's journal has the call state's frame addresses and machine stack (YG0f.v layout_le from
   the journal's start). *)
Lemma fb_ly : forall ly1 S1 W1 m1 md1, AJ ly1 S1 W1 m1 md1 ->
  (forall cid pos, frame_addr ly1 cid pos = frame_addr lyc cid pos) /\
  ly_stk_lo ly1 = ly_stk_lo lyc /\ ly_stk_hi ly1 = ly_stk_hi lyc.
Proof.
  intros ly1 S1 W1 m1 md1 HJ1.
  destruct (gx_open segs B G STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k HJ1) as (memS1 & J1 & _ & _).
  destruct (gx_open segs B G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (memS0 & J0 & _ & _).
  destruct J1 as (_ & (_ & _ & _ & _ & _ & F1 & _ & _ & _ & L1 & U1 & _) & _).
  destruct J0 as (_ & (_ & _ & _ & _ & _ & F0 & _ & _ & _ & L0 & U0 & _) & _).
  split; [intros cid pos; unfold frame_addr; rewrite F1, F0; reflexivity|]. split; congruence.
Qed.

Lemma fb_out_bnd : 0 <= out /\ out + cap <= 2 ^ 63 /\ amem_range out cap.
Proof. destruct Hout as (_ & (_ & _ & _ & R4 & R5 & R6)). split; [exact R5|]. split; [exact R6 | exact R4]. Qed.

Lemma fb_out_far : 0 < cap -> 4096 <= out /\ out + cap <= alloc_ceiling /\ (out + cap <= kLowShadowBeg \/ kHighMemBeg <= out).
Proof. intros Hc. exact (trans_out_ok_far B LAWS lyc Sc W memc mdc out cap fb_HARc Hout Hc). Qed.

Lemma fb_out_place : decode_in_fake lyc Sc out cap \/ (forall a, out <= a < out + cap -> inG G a).
Proof. destruct Hout as ([HF | (HG & _)] & _); [left; exact HF | right; exact HG]. Qed.

(* out read as a range of trans_src_ok (a side-stack frame, or G with trans_sh_any). *)
Lemma fb_out_src : trans_src_ok B lyc Sc W memc out cap.
Proof.
  destruct Hout as ([HF | (HG & Hsh)] & Hrd); right; split; [left; exact HF | exact Hrd | |exact Hrd].
  right. left. split; [exact HG | exact Hsh].
Qed.

Lemma fb_hdr_fr : exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= hp + 4 /\
  hp + 16 <= frame_addr lyc cid pos + fs_frame_bytes cid /\ 4096 <= frame_addr lyc cid pos /\
  frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling.
Proof.
  destruct Fhdr as (cid & pos & Hin & H1 & H2). exists cid, pos.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos fb_HARc Hin) as (Hb1 & Hb2 & _).
  split; [exact Hin|]. split; [fb_lia|]. split; [fb_lia|]. split; fb_lia.
Qed.

Lemma fb_bnd : 0 < dst /\ dst + 6 <= 2 ^ 47 /\ 0 < src /\ src + 6 <= 2 ^ 47 /\ 4092 <= hp /\ hp + 16 <= alloc_ceiling /\
  ((0 < length bb)%nat -> 0 < body /\ body + blen <= 2 ^ 47).
Proof.
  clear Ddst Dsrc Dhdr Dbody Hout0 Hhp0.
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc dst 6 fb_HARc Tdst ltac:(lia)) as (_ & _ & _ & D4 & D5 & _).
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc src 6 fb_HARc Tsrc ltac:(lia)) as (_ & _ & _ & S4 & S5 & _).
  destruct fb_hdr_fr as (cid & pos & _ & Hh1 & Hh2 & Hh3 & Hh4).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in D4, S4.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros HL.
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc body blen fb_HARc Tbody ltac:(lia)) as (_ & _ & _ & B4 & B5 & _).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in B4.
  destruct Hbody0 as [Hb | Hb]; [split; lia | lia].
Qed.

Lemma fb_out_pos : 0 < out.
Proof. pose proof fb_out_bnd as (Ob1 & _). lia. Qed.

(* A range the function reads, outside out's range and the call's stack window. *)
Lemma fb_off_kept : forall q n, decode_off_win regs FRAME_FB_STK q n -> (out + cap <= q \/ q + n <= out) -> 0 <= q ->
  q + n <= 2 ^ 47 -> forall a, q <= a < q + n ->
  0 <= a < 2 ^ 64 /\ ~ (out <= a < out + cap) /\ ~ (spZ regs - FRAME_FB_STK <= a < spZ regs).
Proof. intros q n HO HD H0 H1 a Ha. unfold decode_off_win in HO. clear - HO HD H0 H1 Ha. lia. Qed.

(* ... and outside diginet_body_check's window below the frame. *)
Lemma fb_off_bc : forall q n, decode_off_win regs FRAME_FB_STK q n ->
  q + n <= spZ regs - 96 - PBC.TRANS_BC_STK \/ spZ regs - 96 <= q.
Proof. intros q n HO. pose proof fb_stk as (_ & St2 & _). unfold decode_off_win in HO. clear - HO St2. lia. Qed.


(* body is a 64-bit value even when the body is empty (a block, or decode_rd_ok's bounds). *)
Lemma fb_body_rng : 0 <= body < 2 ^ 64.
Proof.
  pose proof fb_ceil as CEIL.
  destruct Tbody as [(bA & nA & Hin & H1 & H2) | (_ & (_ & _ & _ & _ & R5 & R6))]; [|fb_lia].
  destruct (al_blocks segs B LAWS lyc Sc W memc mdc bA nA fb_HARc Hin) as (_ & H4 & Hc & _ & _ & _ & Hn0).
  pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq]. fb_lia.
Qed.

Lemma fb_hdr_bytes_eq :
  frame_fb_hdr_bytes send ack retry cmd ncmds = map bz (FBI.fb_hdr_in send ack retry cmd ncmds).
Proof. reflexivity. Qed.

(* ---- the caller's journal across the function's own runs ---- *)

Lemma fb_aj_md : forall ly1 S1 W1 m1 md1 md2, AJ ly1 S1 W1 m1 md1 -> same_but_materialized md1 md2 ->
  AJ ly1 S1 W1 m1 md2.
Proof.
  intros ly1 S1 W1 m1 md1 md2 HJ1 Hs.
  apply (ajournal_gx_exec segs B LAWS decode_segs_low G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k m1 md2
           (fun _ => False) fb_GOK HJ1).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

(* A run that writes [lo, hi): each byte visible and one the caller's journal may change (an awr_byte or a byte
   of G). *)
Lemma fb_aj_write : forall ly1 S1 W1 m1 md1 m2 md2 lo hi,
  AJ ly1 S1 W1 m1 md1 -> LFrame.munch [(lo, hi)] m1 m2 -> YK1b.mem_grows m1 m2 ->
  (forall a, lo <= a < hi -> w_H W1 (Z_to_bv 64 a) = false /\
     ((awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly1 S1) ly1 own a /\ ~ (sp0 <= a < sp0 + 0)) \/ inG G a)) ->
  same_but_materialized md1 md2 -> AJ ly1 S1 W1 m2 md2.
Proof.
  intros ly1 S1 W1 m1 md1 m2 md2 lo hi HJ1 MU MG HW Hs.
  apply (ajournal_gx_exec segs B LAWS decode_segs_low G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k m2 md2
           (fun a => lo <= a < hi) fb_GOK HJ1).
  - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [LFrame.outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold mrestrict in *. destruct (w_H W1 x); [exact Hx|]. exact (MG x Hx).
  - intros x Hx. apply MU. cbn [LFrame.outside]. split; [|exact I]. intros Hr.
    destruct (HW _ Hr) as [Hh _]. rewrite MState.Z_to_bv_bv_unsigned in Hh. congruence.
  - exact Hs.
  - intros a Ha. destruct (proj2 (HW a Ha)) as [Hw | Hg]; [left; exact Hw | right; left; exact Hg].
Qed.

(* The write right on out, at a state of the caller's journal: the premise's awr_byte at the call state is one at
   the state (the blocks are a permutation, the frame addresses the same), or a byte of G. *)
Lemma fb_awr_tr : forall ly1 S1 a, Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) ->
  (forall cid pos, frame_addr ly1 cid pos = frame_addr lyc cid pos) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly1 S1) ly1 own a.
Proof.
  intros ly1 S1 a HP HF Hw.
  destruct Hw as [Hw | [(Hfp & b & n & Hin & Hb) | [(b & n & Hin & Hn & Hb) | (cid & pos & Hin & Hr)]]].
  - left. exact Hw.
  - right. left. split; [exact Hfp|]. exists b, n. split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | exact Hb].
  - right. right. left. exists b, n. split; [exact (Permutation_in _ (Permutation_sym HP) Hin)|].
    split; [exact Hn | exact Hb].
  - right. right. right. exists cid, pos. split; [exact Hin|]. rewrite !HF. exact Hr.
Qed.

Lemma fb_out_wr : forall ly1 S1 W1 m1 md1, AJ ly1 S1 W1 m1 md1 -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) ->
  forall a, out <= a < out + cap ->
  (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly1 S1) ly1 own a /\
   ~ (spZ regs - 96 - ESTACK <= a < spZ regs - 96)) \/ inG G a.
Proof.
  intros ly1 S1 W1 m1 md1 HJ1 HP a Ha. destruct (fb_ly ly1 S1 W1 m1 md1 HJ1) as (HF & _ & _).
  destruct (Htwr a Ha) as [(Hw & _ & _ & Hs) | Hg]; [left | right; exact Hg].
  split; [exact (fb_awr_tr ly1 S1 a HP HF Hw) | unfold FRAME_FB_FRAME in Hs; exact Hs].
Qed.

(* Each byte of out is visible and writable in the footprint view: a present awr_byte, or a byte of G. *)
Lemma fb_out_vis : forall ly1 S1 W1 m1 md1, AJ ly1 S1 W1 m1 md1 -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) ->
  forall a, out <= a < out + cap ->
  w_H W1 (Z_to_bv 64 a) = false /\ wview AImg0.rsegs m1 (LMem.wa a) <> None.
Proof.
  intros ly1 S1 W1 m1 md1 HJ1 HP a Ha.
  destruct (fb_out_wr ly1 S1 W1 m1 md1 HJ1 HP a Ha) as [(Hw & _) | Hg].
  - destruct (gx_open segs B G STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k HJ1) as (memS & J & _ & _).
    destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a J Hw) as [(Hh & b & Hb) _].
    split; [exact Hh|]. unfold LMem.wa. exact (decode_wview_some m1 _ b Hb).
  - pose proof (inG_low segs B decode_segs_low G a fb_GOK Hg) as Hl. unfold kLowMemEnd in Hl.
    split.
    + apply hidden_not_img. rewrite fbk_u64 by fb_lia. exact (trans_g_img a Hg).
    + pose proof (gx_rw_writable segs G a G_HARNESS_rw Hg m1) as Hwr. unfold writable_at in Hwr.
      rewrite decode_segs_eq in Hwr. exact Hwr.
Qed.

(* ---- the post's two keep facts across a step ---- *)

(* A step that changes only bytes of out or of the call's stack window keeps acall_kept_g (DgnTransportCg.v
   dk_kept_step_g, at the current world). *)
Lemma fb_kp_step : forall W1 m1 m2 (Zs : Z -> Prop),
  KP W1 m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) m2 a = aview segs (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
  (forall a, Zs a -> out <= a < out + cap \/ spZ regs - FRAME_FB_STK <= a < spZ regs) ->
  KP W1 m2.
Proof.
  intros W1 m1 m2 Zs (K1 & K2 & K3 & K4 & K5 & K6) Hk Hp HZ.
  pose proof fb_sp as (Hsp1 & Hsp2 & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HE : forall a, out <= a < out + cap -> 4096 <= a < alloc_ceiling).
  { intros a Ha. destruct (fb_out_far ltac:(fb_lia)) as (O1 & O2 & _). fb_lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hk; [exact (K1 a Ha Hw) | fb_lia |].
    intros HZa. destruct (HZ a HZa) as [He | He]; [pose proof (HE a He); fb_lia | fb_lia].
  - intros b m i Hb Hi Hn.
    destruct (al_blocks segs B LAWS lyc Sc W memc mdc b m fb_HARc Hb) as (_ & H4 & Hc & _).
    rewrite Hk; [exact (K2 b m i Hb Hi Hn) | fb_lia |].
    intros HZa. destruct (HZ _ HZa) as [He | He]; [exact (Hn He) | fb_lia].
  - intros a Hi HnG Hno Her. pose proof (decode_segs_low a Hi) as Hl.
    rewrite Hk; [exact (K3 a Hi HnG Hno Her) | fb_lia |].
    intros HZa. destruct (HZ _ HZa) as [He | He]; [|fb_lia].
    destruct fb_out_place as [(cid & pos & Hin & F1 & F2) | HGo].
    + exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a fb_HARc Hin ltac:(fb_lia) Hi).
    + exact (HnG (HGo a He)).
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos fb_HARc Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [fb_lia|].
      unfold shadow_addr, SHADOW_OFF in Hr. pose proof C1 as C1'. clear - Hr F1 F2 Fn C1'. revert Hr.
      Z.div_mod_to_equations. lia. }
    rewrite Hk; [exact (K4 cid pos a Hin Hr Hn) | fb_lia |].
    intros HZa. destruct (HZ _ HZa) as [He | He]; [exact (Hn He) | fb_lia].
  - intros a Ha Hw Hpm. apply Hp. exact (K5 a Ha Hw Hpm).
  - intros a Ha. apply Hp. exact (K6 a Ha).
Qed.

Lemma fb_kx_step : forall W1 m1 m2 (Zs : Z -> Prop),
  KX W1 m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) m2 a = aview segs (w_H W1) m1 a) ->
  (forall a, Zs a -> out <= a < out + cap \/ spZ regs - FRAME_FB_STK <= a < spZ regs) ->
  KX W1 m2.
Proof.
  intros W1 m1 m2 Zs KX1 Hk HZ a Ha Hn.
  pose proof fb_sp as (Hsp1 & Hsp2 & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof fb_ceil as CEIL.
  pose proof (inG_low segs B decode_segs_low G a fb_GOK Ha) as Hl.
  rewrite Hk; [exact (KX1 a Ha Hn) | fb_lia |].
  intros HZa. destruct (HZ _ HZa) as [He | He]; [exact (Hn He) | fb_lia].
Qed.

(* ---- the bytes the function reads, across a step ---- *)

Lemma fb_sv_step : forall ly1 S1 W1 m1 m2 q l,
  fb_sv ly1 S1 W1 m1 q l ->
  (forall a, q <= a < q + Z.of_nat (length l) -> aview segs (w_H W1) m2 a = aview segs (w_H W1) m1 a) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W1) m2 s = aview segs (w_H W1) m1 s) ->
  fb_sv ly1 S1 W1 m2 q l.
Proof.
  intros ly1 S1 W1 m1 m2 q l (Ht & Hv) K1 K2. split.
  - exact (trans_src_ok_view B ly1 S1 W1 W1 m1 m2 q _ Ht K1 K2).
  - intros j Hj. rewrite K1 by fb_lia. exact (Hv j Hj).
Qed.

(* A step that changes only bytes of out or of the call's stack window keeps what the function reads. *)
Lemma fb_rd_step : forall ly1 S1 W1 m1 m2, fb_rd ly1 S1 W1 m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + cap) -> ~ (spZ regs - FRAME_FB_STK <= a < spZ regs) ->
     aview segs (w_H W1) m2 a = aview segs (w_H W1) m1 a) ->
  fb_rd ly1 S1 W1 m2.
Proof.
  intros ly1 S1 W1 m1 m2 (Rd & Rs & Rb & Rh & Ora & Oh) K.
  pose proof fb_sp as (Hsp1 & Hsp2 & _). pose proof fb_ceil as CEIL.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof fb_bnd as (Bd1 & Bd2 & Bs1 & Bs2 & Bh1 & Bh2 & Bb).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3).
  assert (Kr : forall q n, decode_off_win regs FRAME_FB_STK q n -> (out + cap <= q \/ q + n <= out) -> 0 <= q ->
            q + n <= 2 ^ 47 -> forall a, q <= a < q + n -> aview segs (w_H W1) m2 a = aview segs (w_H W1) m1 a).
  { intros q n HO HD H0 H1 a Ha. destruct (fb_off_kept q n HO HD H0 H1 a Ha) as (A1 & A2 & A3). exact (K a A1 A2 A3). }
  assert (Kb : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W1) m2 s = aview segs (w_H W1) m1 s).
  { intros s Hs. apply K; [fb_lia | | fb_lia].
    intros Ho. assert (Hc : 0 < cap) by fb_lia. destruct (fb_out_far Hc) as (_ & _ & Hlh).
    unfold kLowShadowBeg in Hlh. fb_lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - apply (fb_sv_step ly1 S1 W1 m1 m2 dst dmac Rd); [|exact Kb]. rewrite Ldmac.
    exact (Kr dst 6 Odst Ddst ltac:(fb_lia) ltac:(fb_lia)).
  - apply (fb_sv_step ly1 S1 W1 m1 m2 src smac Rs); [|exact Kb]. rewrite Lsmac.
    exact (Kr src 6 Osrc Dsrc ltac:(fb_lia) ltac:(fb_lia)).
  - intros HL. apply (fb_sv_step ly1 S1 W1 m1 m2 body bb (Rb HL)); [|exact Kb].
    destruct (Bb HL) as (Bb1 & Bb2). exact (Kr body blen Obody Dbody ltac:(fb_lia) ltac:(fb_lia)).
  - apply (fb_sv_step ly1 S1 W1 m1 m2 (hp + 4) _ Rh); [|exact Kb]. rewrite FBI.fb_hdr_in_length.
    exact (Kr (hp + 4) 12 Ohdr ltac:(clear - Dhdr; lia) ltac:(fb_lia) ltac:(fb_lia)).
  - exact (fb_ra_band W1 W1 m1 m2 out cap Ob3 Ob1 Ora Kb).
  - intros Hc. exact (fb_hull_band W1 W1 m1 m2 out cap Ob3 Ob1 (Oh Hc) Kb).
Qed.

(* The prologue's frame keeps its cells when its bytes keep their views. *)
Lemma fb_frame_kept : forall W1 W2 m1 m2 ly1 S1 md1 ly2 S2 md2,
  fb_frame m1 -> AJ ly1 S1 W1 m1 md1 -> AJ ly2 S2 W2 m2 md2 ->
  (forall a, spZ regs - 96 <= a < spZ regs -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  fb_frame m2.
Proof.
  intros W1 W2 m1 m2 ly1 S1 md1 ly2 S2 md2 HF J1 J2 E.
  pose proof fb_stk as (St1 & St2 & St3).
  unfold fb_frame in *. apply (decode_rw_cells_eq m1 m2 _ _ HF). intros i Hi.
  rewrite FBI.fb_fr_size in Hi. unfold FBI.FB_FRAME in Hi. unfold LMem.wa.
  apply (decode_byte_eq (w_H W1) (w_H W2) m1 m2).
  - apply (fb_win _ _ _ _ _ J1). fb_lia.
  - apply (fb_win _ _ _ _ _ J2). fb_lia.
  - apply E. fb_lia.
Qed.

(* A step of the function's own (a run, or an intrinsic below its frame) at the current state. *)
Lemma fb_stR_step : forall ly1 S1 W1 m1 md1 m2 md2 (Zs : Z -> Prop),
  fb_stR ly1 S1 W1 m1 md1 -> AJ ly1 S1 W1 m2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) m2 a = aview segs (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
  (forall a, Zs a -> out <= a < out + cap \/ spZ regs - FRAME_FB_STK <= a < spZ regs - 96) ->
  fb_stR ly1 S1 W1 m2 md2.
Proof.
  intros ly1 S1 W1 m1 md1 m2 md2 Zs ((J1 & Hfr & HP & Hmo & HF & KP1 & KX1) & RD) J2 Hk Hpr HZ.
  pose proof fb_sp as (Hsp1 & Hsp2 & _). pose proof fb_stk as (St1 & St2 & St3). pose proof fb_ceil as CEIL.
  assert (HE : forall a, out <= a < out + cap -> a < alloc_ceiling).
  { intros a Ha. destruct (fb_out_far ltac:(fb_lia)) as (_ & O2 & _). fb_lia. }
  assert (HZ' : forall a, Zs a -> out <= a < out + cap \/ spZ regs - FRAME_FB_STK <= a < spZ regs).
  { intros a Ha. destruct (HZ a Ha) as [H | H]; [left; exact H | right; fb_lia]. }
  split; [split|].
  - exact J2.
  - split; [exact Hfr|]. split; [exact HP|]. split; [exact Hmo|].
    split; [|split; [exact (fb_kp_step W1 m1 m2 Zs KP1 Hk Hpr HZ') | exact (fb_kx_step W1 m1 m2 Zs KX1 Hk HZ')]].
    apply (fb_frame_kept W1 W1 m1 m2 _ _ _ _ _ _ HF J1 J2). intros a Ha. apply Hk; [fb_lia|].
    intros HZa. destruct (HZ a HZa) as [H | H]; [pose proof (HE a H); fb_lia | fb_lia].
  - apply (fb_rd_step ly1 S1 W1 m1 m2 RD). intros a Ha H1 H2. apply Hk; [exact Ha|].
    intros HZa. destruct (HZ a HZa) as [H | H]; [exact (H1 H) | fb_lia].
Qed.

Lemma fb_stR_md : forall ly1 S1 W1 m1 md1 md2, fb_stR ly1 S1 W1 m1 md1 -> same_but_materialized md1 md2 ->
  fb_stR ly1 S1 W1 m1 md2.
Proof.
  intros ly1 S1 W1 m1 md1 md2 ((J & H1 & H2 & H3 & H4 & H5 & H6) & RD) Hs.
  split; [|exact RD]. split; [exact (fb_aj_md _ _ _ _ _ _ J Hs)|].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

(* A run that writes a range of out keeps the state. *)
Lemma fb_st_write : forall ly1 S1 W1 m1 md1 m2 md2 lo hi,
  fb_stR ly1 S1 W1 m1 md1 -> LFrame.munch [(lo, hi)] m1 m2 -> YK1b.mem_grows m1 m2 ->
  out <= lo -> hi <= out + cap -> same_but_materialized md1 md2 -> fb_stR ly1 S1 W1 m2 md2.
Proof.
  intros ly1 S1 W1 m1 md1 m2 md2 lo hi HS MU MG Hlo Hhi Hs.
  pose proof HS as ((J1 & _ & HP & _ & _ & _ & _) & _).
  assert (J2 : AJ ly1 S1 W1 m2 md2).
  { apply (fb_aj_write ly1 S1 W1 m1 md1 m2 md2 lo hi J1 MU MG); [|exact Hs].
    intros a Ha. split; [exact (proj1 (fb_out_vis ly1 S1 W1 m1 md1 J1 HP a ltac:(fb_lia)))|].
    destruct (fb_out_wr ly1 S1 W1 m1 md1 J1 HP a ltac:(fb_lia)) as [(Hw & _) | Hg]; [left; split; [exact Hw | fb_lia] | right; exact Hg]. }
  apply (fb_stR_step ly1 S1 W1 m1 md1 m2 md2 (fun a => lo <= a < hi) HS J2).
  - intros a Ha Hn. exact (fbk_aview_munch _ m1 m2 lo hi a MU Ha Hn).
  - intros a Hp. exact (fb_pres_grow _ m1 m2 a MG Hp).
  - intros a Ha. left. fb_lia.
Qed.

(* ---- facts of a state the pieces ask ---- *)

(* A range the function reads, at a state. *)
Lemma fb_src_run : forall ly1 S1 W1 m1 md1 q l, fb_stR ly1 S1 W1 m1 md1 -> fb_sv ly1 S1 W1 m1 q l ->
  (0 < length l)%nat ->
  LMem.bytes_at AImg0.rsegs m1 q l /\ FC.addressable m1 q (Z.of_nat (length l)) /\
  ExecF.rng (RNGW W1) q (Z.of_nat (length l)) /\
  ExecF.rng (RNGW W1) (FC.shadow_addr q)
    (FC.shadow_addr (q + Z.of_nat (length l) - 1) - FC.shadow_addr q + 1) /\
  0 <= q /\ q + Z.of_nat (length l) <= 2 ^ 47.
Proof.
  intros ly1 S1 W1 m1 md1 q l ((J1 & _) & _) (Ht & Hv) Hl.
  pose proof (ajournal_gx_AR segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k J1) as HAR1.
  destruct (trans_src_ok_rd B LAWS ly1 S1 W1 m1 md1 q _ HAR1 Ht ltac:(fb_lia)) as (R1 & R2 & R3 & R4 & R5 & R6).
  assert (Hq : q + Z.of_nat (length l) <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in R4; fb_lia).
  destruct (decode_addressable_of (w_H W1) m1 q _ R2 R4 R5 ltac:(fb_lia)) as (Ad & Sv).
  split; [exact (fbk_bytes_of_aview W1 m1 q l R5 ltac:(fb_lia) Hv)|].
  split; [exact Ad|].
  split; [apply decode_rng_vis; [fb_lia | fb_lia |]; intros i Hi;
          replace (q + i) with (q + Z.of_nat (Z.to_nat i)) by fb_lia;
          exact (fbk_aview_vis W1 m1 _ _ (Hv (Z.to_nat i) ltac:(fb_lia)))|].
  split; [apply fbk_rng_shadow; [fb_lia | fb_lia | fb_lia | exact Sv]|].
  split; fb_lia.
Qed.

(* A range of out, at a state: addressable, and in the footprint with its shadow bytes. *)
Lemma fb_out_run : forall ly1 S1 W1 m1 md1 q n, fb_stR ly1 S1 W1 m1 md1 -> out <= q -> q + n <= out + cap -> 0 < n ->
  FC.addressable m1 q n /\ ExecF.rng (RNGW W1) q n /\
  ExecF.rng (RNGW W1) (FC.shadow_addr q) (FC.shadow_addr (q + n - 1) - FC.shadow_addr q + 1).
Proof.
  intros ly1 S1 W1 m1 md1 q n ((J1 & _ & HP & _) & (_ & _ & _ & _ & Ora & _)) H1 H2 Hn.
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3).
  assert (Ra : range_addressable (aview segs (w_H W1) m1) SHADOW_OFF q n)
    by exact (range_addressable_sub _ _ out cap q n Ora H1 H2).
  assert (Am : amem_range q n) by (unfold amem_range in *; fb_lia).
  destruct (decode_addressable_of (w_H W1) m1 q n Ra Am ltac:(fb_lia) ltac:(fb_lia)) as (Ad & Sv).
  split; [exact Ad|]. split.
  - apply decode_rng_vis; [fb_lia | fb_lia |]. intros i Hi.
    exact (proj1 (fb_out_vis ly1 S1 W1 m1 md1 J1 HP (q + i) ltac:(fb_lia))).
  - apply fbk_rng_shadow; [fb_lia | fb_lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Am; fb_lia | exact Sv].
Qed.

(* ---- the bytes at out ---- *)

Lemma fb_outv0 : fb_outv W memc oj.
Proof.
  pose proof fb_out_bnd as (Ob1 & Ob2 & _). destruct Hout as (_ & (R1 & _)).
  split; [reflexivity|].
  apply (fbk_garr8_aview (w_H W) memc out oj); [fb_lia | fb_lia | | exact Goj].
  intros j Hj. apply (fb_vis_h W memc). apply R1. fb_lia.
Qed.

Lemma fb_outv_kept : forall W1 m1 W2 m2 l, fb_outv W1 m1 l ->
  (forall j, (j < length oj)%nat -> aview segs (w_H W2) m2 (out + Z.of_nat j) = aview segs (w_H W1) m1 (out + Z.of_nat j)) ->
  fb_outv W2 m2 l.
Proof.
  intros W1 m1 W2 m2 l (Hl & HV) E. split; [exact Hl|]. intros j Hj. rewrite E by fb_lia. exact (HV j Hj).
Qed.

Lemma fb_outv_put : forall W1 m1 m2 l kk w, fb_outv W1 m1 l -> (kk + length w <= length oj)%nat ->
  (forall i, (i < length w)%nat ->
     aview segs (w_H W1) m2 (out + Z.of_nat kk + Z.of_nat i) = Some (bz (nth i w (b8 0)))) ->
  (forall j, (j < length oj)%nat -> ~ (kk <= j < kk + length w)%nat ->
     aview segs (w_H W1) m2 (out + Z.of_nat j) = aview segs (w_H W1) m1 (out + Z.of_nat j)) ->
  fb_outv W1 m2 (FBI.fb_put l kk w).
Proof.
  intros W1 m1 m2 l kk w (Hl & HV) Hk HW HK.
  split; [rewrite FBI.fb_put_length by fb_lia; exact Hl|].
  intros j Hj. rewrite FBI.fb_put_length in Hj by fb_lia. rewrite fbk_put_nth by fb_lia.
  destruct (Nat.ltb_spec j kk).
  - rewrite HK by fb_lia. apply HV; fb_lia.
  - destruct (Nat.ltb_spec j (kk + length w)).
    + replace (out + Z.of_nat j) with (out + Z.of_nat kk + Z.of_nat (j - kk)) by fb_lia. apply HW. fb_lia.
    + rewrite HK by fb_lia. apply HV; fb_lia.
Qed.

Lemma fb_outv_rw : forall ly1 S1 W1 m1 md1 l, fb_stR ly1 S1 W1 m1 md1 -> fb_outv W1 m1 l ->
  LStep.rw_cells AImg0.rsegs m1 out [LCells.CB (length l) l].
Proof.
  intros ly1 S1 W1 m1 md1 l ((J1 & _ & HP & _) & _) (Hl & HV). pose proof fb_out_bnd as (Ob1 & Ob2 & _).
  apply (fb_rw_of_garr8 (w_H W1)).
  - cbn [LCells.cells_wf LCells.cell_wf]. split; [reflexivity | exact I].
  - fb_lia.
  - cbn [LCells.cells_size LCells.csize]. rewrite Nat.add_0_r, Hl. fb_lia.
  - intros i Hi. cbn [LCells.cells_size LCells.csize] in Hi. rewrite Nat.add_0_r, Hl in Hi.
    exact (fb_out_vis ly1 S1 W1 m1 md1 J1 HP (out + i) ltac:(fb_lia)).
  - cbn [LCells.cells_bytes LCells.cbytes]. rewrite app_nil_r.
    apply (fbk_aview_garr8 W1 m1 out l); [fb_lia | rewrite Hl; fb_lia | exact HV].
Qed.

Lemma fb_outv_of_rw : forall ly1 S1 W1 m1 md1 (l l' : list byte), fb_stR ly1 S1 W1 m1 md1 ->
  LStep.rw_cells AImg0.rsegs m1 out [LCells.CB (length l) l'] -> length l' = length oj -> fb_outv W1 m1 l'.
Proof.
  intros ly1 S1 W1 m1 md1 l l' ((J1 & _ & HP & _) & _) [[_ HB] _] Hl. cbn [LCells.cells_bytes LCells.cbytes] in HB.
  rewrite app_nil_r in HB.
  split; [exact Hl|]. apply (fbk_aview_of_bytes _ m1 out l' HB). intros j Hj.
  exact (proj1 (fb_out_vis ly1 S1 W1 m1 md1 J1 HP (out + Z.of_nat j) ltac:(fb_lia))).
Qed.

(* The ranges the function reads, at the entry. *)
Lemma fb_sv0 : forall q (l : list byte), (0 < length l)%nat -> trans_src_ok B lyc Sc W memc q (Z.of_nat (length l)) ->
  garr8 segs (mrestrict (w_H W) memc) q (map bz l) -> fb_sv lyc Sc W memc q l.
Proof.
  intros q l Hl Ht Hg. split; [exact Ht|].
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc q _ fb_HARc Ht ltac:(fb_lia)) as (R1 & _ & _ & _ & R5 & R6).
  apply (fbk_garr8_aview (w_H W) memc q l); [fb_lia | fb_lia | | exact Hg].
  intros j Hj. apply (fb_vis_h W memc). apply R1. fb_lia.
Qed.

Lemma fb_rd0 : fb_rd lyc Sc W memc.
Proof.
  split; [apply fb_sv0; [rewrite Ldmac; fb_lia | rewrite Ldmac; exact Tdst | exact Gdmac]|].
  split; [apply fb_sv0; [rewrite Lsmac; fb_lia | rewrite Lsmac; exact Tsrc | exact Gsmac]|].
  split; [intros HL; apply fb_sv0; [exact HL | exact Tbody | exact Gbb]|].
  split.
  - apply fb_sv0; [rewrite FBI.fb_hdr_in_length; fb_lia | | rewrite <- fb_hdr_bytes_eq; exact Ghdr].
    rewrite FBI.fb_hdr_in_length. right. split; [left; exact Fhdr | exact Rhdr].
  - destruct Hout as (_ & (_ & R2 & R3 & _)). split; [exact R2 | intros _; exact R3].
Qed.

(* ---- the calls of __asan_memcpy and __asan_memset ---- *)

Lemma fb_o16 : (spZ regs - 96 - sp0) mod 16 = 0.
Proof. pose proof fb_sp as (_ & _ & H0). Z.div_mod_to_equations. fb_lia. Qed.

(* __asan_memcpy(out + kk, x, n), x a range the function reads, apart from out's range: TransportGCg.v gx_intrin_at
   from the caller's G journal, the destination's write right from the premise (fb_out_wr). *)
Lemma fb_memcpy : forall ly1 S1 W1 rg m1 md1 (l : list byte) kk (w : list byte) x raw Q,
  fb_stR ly1 S1 W1 m1 md1 -> fb_k4 rg ->
  GR rg 1 = Z_to_bv 64 raw -> 0 <= raw < 2 ^ 64 -> raw mod 2 = 0 ->
  GR rg 10 = Z_to_bv 64 (out + Z.of_nat kk) -> GR rg 11 = Z_to_bv 64 x ->
  GR rg 12 = Z_to_bv 64 (Z.of_nat (length w)) ->
  fb_outv W1 m1 l -> (kk + length w <= length oj)%nat -> (0 < length w)%nat -> (length w <= 1484)%nat ->
  fb_sv ly1 S1 W1 m1 x w -> decode_off_win regs FRAME_FB_STK x (Z.of_nat (length w)) ->
  (out + cap <= x \/ x + Z.of_nat (length w) <= out) ->
  (forall regs2 m2 md2, fb_stR ly1 S1 W1 m2 md2 -> aregs_preserved rg regs2 ->
     fb_outv W1 m2 (FBI.fb_put l kk w) -> SRr segs W1 (@cfg_at fx segs raw regs2 m2 md2) Q) ->
  SRr segs W1 (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 FBI.FB_CPY) m1 (YK11.seg_rom segs)) md1) Q.
Proof.
  intros ly1 S1 W1 rg m1 md1 l kk w x raw Q HS (K2 & K3 & K4 & K27) G1 Hraw Hev G10 G11 G12 HO Hk Hw0 Hw Hxs Hxo
    Hxd KONT.
  pose proof HS as ((J1 & _ & HP & _ & _ & _ & _) & (_ & _ & _ & _ & Ora & Ohull)).
  pose proof fb_sp as (Hsp1 & Hsp2 & Hs016). pose proof fb_stk as (St1 & St2 & St3). pose proof fb_ceil as CEIL.
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3).
  assert (Hcap0 : 0 < cap) by fb_lia.
  pose proof (fb_out_far Hcap0) as (Of1 & Of2 & Of3).
  pose proof (ajournal_gx_AR segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k J1) as HAR1.
  destruct (trans_src_ok_rd B LAWS ly1 S1 W1 m1 md1 x _ HAR1 (proj1 Hxs) ltac:(fb_lia)) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (SPR : spZ rg = spZ regs + -96).
  { change (spZ rg) with (bv_unsigned (GR rg 2)). rewrite K2. rewrite fbk_u64 by fb_lia. fb_lia. }
  unfold decode_off_win in Hxo.
  unfold FBI.FB_CPY.
  eapply SRr_bind.
  { apply (gx_intrin_at segs B LAWS decode_segs_low OCpy (transport_sigma TS___asan_memcpy) (AMEMCPY fx) G W1 rg m1
             STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md1 k (out + Z.of_nat kk) x (Z.of_nat (length w))
             (spZ regs - 96 - sp0) (Z_to_bv 64 raw) fb_GOK G_HARNESS_rw J1 G10 G11 G12).
    - fb_lia.
    - fb_lia.
    - fb_lia.
    - rewrite SPR. fb_lia.
    - exact fb_o16.
    - fb_lia.
    - fb_lia.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - exact G1.
    - apply YK0s.ret_ok_even. rewrite fbk_u64 by fb_lia. exact Hev.
    - apply (@transport_twr_ok_g_intro rc AE2k.tfib_sink_head segs B LAWS G STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1
               md1 k). exact J1.
      intros a Ha. destruct (fb_out_wr ly1 S1 W1 m1 md1 J1 HP a ltac:(fb_lia)) as [(Hw' & Hs') | Hg].
      + left. split; [exact Hw' | rewrite SPR; fb_lia].
      + right. exact Hg.
    - unfold amem_range in *. fb_lia.
    - exact (range_addressable_sub _ _ out cap (out + Z.of_nat kk) (Z.of_nat (length w)) Ora ltac:(fb_lia) ltac:(fb_lia)).
    - intros _. exact (trans_hull_sub _ out cap (out + Z.of_nat kk) (Z.of_nat (length w)) (Ohull Hcap0) ltac:(fb_lia)
                         ltac:(fb_lia)).
    - split; [fb_lia|]. split; [fb_lia|]. split.
      { intros a Ha. split; [apply X1; fb_lia | rewrite SPR; fb_lia]. }
      split; [fb_lia|]. split; [exact X4|]. split; [exact X2 | intros _; exact X3]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & J2 & HPR & HA0 & HCOPY & HVIEW & HPRES).
  apply (KONT regs2 m2 md2).
  - apply (fb_stR_step ly1 S1 W1 m1 md1 m2 md2
             (fun a => (out + Z.of_nat kk <= a < out + Z.of_nat kk + Z.of_nat (length w)) \/
                       (spZ regs - 96 - ESTACK <= a < spZ regs - 96)) HS J2).
    + intros a Ha Hn. apply HVIEW; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; fb_lia].
    + exact HPRES.
    + intros a [Ha | Ha]; [left; fb_lia | right; fb_lia].
  - exact HPR.
  - apply (fb_outv_put W1 m1 m2 l kk w HO Hk).
    + intros i Hi. rewrite (HCOPY (Z.of_nat i) ltac:(fb_lia)). exact (proj2 Hxs i Hi).
    + intros j Hj Hn. apply HVIEW; fb_lia.
Qed.

(* __asan_memset(out + kk, 0, n). *)
Lemma fb_memset : forall ly1 S1 W1 rg m1 md1 (l : list byte) kk n raw Q,
  fb_stR ly1 S1 W1 m1 md1 -> fb_k4 rg ->
  GR rg 1 = Z_to_bv 64 raw -> 0 <= raw < 2 ^ 64 -> raw mod 2 = 0 ->
  GR rg 10 = Z_to_bv 64 (out + Z.of_nat kk) -> GR rg 11 = Z_to_bv 64 0 -> GR rg 12 = Z_to_bv 64 (Z.of_nat n) ->
  fb_outv W1 m1 l -> (kk + n <= length oj)%nat -> (0 < n)%nat -> (n <= 1484)%nat ->
  (forall regs2 m2 md2, fb_stR ly1 S1 W1 m2 md2 -> aregs_preserved rg regs2 ->
     fb_outv W1 m2 (FBI.fb_put l kk (repeat (b8 0) n)) -> SRr segs W1 (@cfg_at fx segs raw regs2 m2 md2) Q) ->
  SRr segs W1 (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 FBI.FB_SET) m1 (YK11.seg_rom segs)) md1) Q.
Proof.
  intros ly1 S1 W1 rg m1 md1 l kk n raw Q HS (K2 & K3 & K4 & K27) G1 Hraw Hev G10 G11 G12 HO Hk Hn0 Hnb KONT.
  pose proof HS as ((J1 & _ & HP & _ & _ & _ & _) & (_ & _ & _ & _ & Ora & Ohull)).
  pose proof fb_sp as (Hsp1 & Hsp2 & Hs016). pose proof fb_stk as (St1 & St2 & St3). pose proof fb_ceil as CEIL.
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3).
  assert (Hcap0 : 0 < cap) by fb_lia.
  pose proof (fb_out_far Hcap0) as (Of1 & Of2 & Of3).
  assert (SPR : spZ rg = spZ regs + -96).
  { change (spZ rg) with (bv_unsigned (GR rg 2)). rewrite K2. rewrite fbk_u64 by fb_lia. fb_lia. }
  unfold FBI.FB_SET.
  eapply SRr_bind.
  { apply (gx_intrin_at segs B LAWS decode_segs_low OSet (transport_sigma TS___asan_memset) (AMEMSET fx) G W1 rg m1
             STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md1 k (out + Z.of_nat kk) 0 (Z.of_nat n)
             (spZ regs - 96 - sp0) (Z_to_bv 64 raw) fb_GOK G_HARNESS_rw J1 G10 G11 G12).
    - fb_lia.
    - fb_lia.
    - fb_lia.
    - rewrite SPR. fb_lia.
    - exact fb_o16.
    - fb_lia.
    - fb_lia.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - exact G1.
    - apply YK0s.ret_ok_even. rewrite fbk_u64 by fb_lia. exact Hev.
    - apply (@transport_twr_ok_g_intro rc AE2k.tfib_sink_head segs B LAWS G STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1
               md1 k). exact J1.
      intros a Ha. destruct (fb_out_wr ly1 S1 W1 m1 md1 J1 HP a ltac:(fb_lia)) as [(Hw' & Hs') | Hg].
      + left. split; [exact Hw' | rewrite SPR; fb_lia].
      + right. exact Hg.
    - unfold amem_range in *. fb_lia.
    - exact (range_addressable_sub _ _ out cap (out + Z.of_nat kk) (Z.of_nat n) Ora ltac:(fb_lia) ltac:(fb_lia)).
    - intros _. exact (trans_hull_sub _ out cap (out + Z.of_nat kk) (Z.of_nat n) (Ohull Hcap0) ltac:(fb_lia)
                         ltac:(fb_lia)).
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & J2 & HPR & HA0 & HSET & HVIEW & HPRES).
  apply (KONT regs2 m2 md2).
  - apply (fb_stR_step ly1 S1 W1 m1 md1 m2 md2
             (fun a => (out + Z.of_nat kk <= a < out + Z.of_nat kk + Z.of_nat n) \/
                       (spZ regs - 96 - ESTACK <= a < spZ regs - 96)) HS J2).
    + intros a Ha Hn. apply HVIEW; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; fb_lia].
    + exact HPRES.
    + intros a [Ha | Ha]; [left; fb_lia | right; fb_lia].
  - exact HPR.
  - apply (fb_outv_put W1 m1 m2 l kk (repeat (b8 0) n) HO); [rewrite repeat_length; exact Hk | |].
    + intros i Hi. rewrite repeat_length in Hi. rewrite (HSET (Z.of_nat i) ltac:(fb_lia)), nth_repeat. reflexivity.
    + intros j Hj Hn. rewrite repeat_length in Hn. apply HVIEW; fb_lia.
Qed.

(* ---- the return ---- *)

(* At FB_EPI with s8 = v = build_code_w bb cap mode and the cap bytes at out = build_out_w: fb_epi, the return,
   the post (TransportGCg.v transport_cg_post, with the state's keep facts). *)
Lemma fb_at_epi : forall ly2 S2 W2 rg m2 md2 v,
  fb_st ly2 S2 W2 m2 md2 -> fb_k4 rg -> GR rg 24 = Z_to_bv 64 v -> v = PBuildW.build_code_w bb cap mode ->
  fb_outv W2 m2 (PBuildW.build_out_w dmac smac send ack retry cmd ncmds bb mode oj) ->
  SRr segs W2 (@cfg_at fx segs FBI.FB_EPI rg m2 md2) POST.
Proof.
  intros ly2 S2 W2 rg m2 md2 v (J2 & Hfr & Hperm & Hmo & HF & KP2 & KX2) (K2 & K3 & K4 & K27) G24 Hv HO.
  pose proof fb_sp as (Hsp1 & Hsp2 & _). pose proof fb_stk as (St1 & St2 & St3). pose proof fb_ceil as CEIL.
  pose proof fb_out_bnd as (Ob1 & Ob2 & _).
  assert (SP2 : bv_unsigned (GR rg 2) = spZ regs - 96) by (rewrite K2; apply fbk_u64; fb_lia).
  assert (Hvr : - 2 ^ 31 <= v < 2 ^ 31) by (rewrite Hv; apply fb_code_w_range).
  pose proof EPI as EP. unfold FBI.fb_epi_stmt in EP.
  eapply (decode_run W2 rg m2 md2 FBI.FB_EPI).
  { unfold LCK.ms_of_regs. rewrite G24. eapply EP.
    - rewrite SP2. exact HF.
    - rewrite SP2. fb_lia.
    - rewrite SP2. apply decode_rng_vis; [fb_lia | fb_lia |]. intros i Hi.
      exact (proj1 (fb_win _ _ _ _ _ J2 (spZ regs - 96 + i) ltac:(fb_lia))).
    - exact Hvr. }
  intros ms1 ms2 md' -> HE _ Hs.
  destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
  destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
    E24 & E25 & E26 & E27).
  assert (Hret : MState.ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret.
  pose proof (fb_aj_md _ _ _ _ _ _ J2 Hs) as J2'.
  apply SRr_ret. unfold frame_fb_post, transport_cg_post.
  exists ly2, S2, R', m2, md', 0.
  split; [reflexivity|].
  split; [unfold FRAME_FB_EV; fb_lia|].
  split; [rewrite Z.add_0_r; exact J2'|].
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by fb_lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - rewrite E2, SP2. replace (spZ regs - 96 + 96) with (spZ regs) by fb_lia. unfold spZ.
      apply MState.Z_to_bv_bv_unsigned.
    - rewrite E3. exact K3.
    - rewrite E4. exact K4.
    - exact E8.
    - exact E9.
    - exact E18.
    - exact E19.
    - exact E20.
    - exact E21.
    - exact E22.
    - exact E23.
    - exact E24.
    - exact E25.
    - exact E26.
    - rewrite E27. exact K27. }
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [exact KP2|].
  split; [exact Hmo|].
  split; [change (GR R' 10 = w64 (PBuildW.build_code_w bb cap mode)); rewrite E10, Hv; reflexivity|].
  split; [destruct HO as (HOl & HOv); apply (fbk_aview_garr8 W2 m2 out); [fb_lia | rewrite HOl; fb_lia | exact HOv]|].
  exact KX2.
Qed.

(* ---- mode 0 or 1: the body_check call and the rest ---- *)

Lemma fb_out_neg : build_code bb cap < 0 -> PBuild.build_out dmac smac send ack retry cmd ncmds bb mode oj = oj.
Proof.
  intros H. unfold PBuild.build_out. cbv zeta.
  destruct (Z.leb_spec 0 (build_code bb cap)); [fb_lia | reflexivity].
Qed.


Section M01.
Hypothesis Hm01 : mode = 0 \/ mode = 1.

Lemma fb_at_epi01 : forall ly2 S2 W2 rg m2 md2 v,
  fb_st ly2 S2 W2 m2 md2 -> fb_k4 rg -> GR rg 24 = Z_to_bv 64 v -> v = build_code bb cap ->
  fb_outv W2 m2 (PBuild.build_out dmac smac send ack retry cmd ncmds bb mode oj) ->
  SRr segs W2 (@cfg_at fx segs FBI.FB_EPI rg m2 md2) POST.
Proof.
  intros ly2 S2 W2 rg m2 md2 v HS HK G24 Hv HO.
  destruct (fb_w01 dmac smac send ack retry cmd ncmds bb mode oj Hm01) as (E1 & E2).
  apply (fb_at_epi ly2 S2 W2 rg m2 md2 v HS HK G24); [rewrite E1; exact Hv | rewrite E2; exact HO].
Qed.

(* ---- the success path: body_len <= 1484, no refused message in the body, cap >= len ---- *)

Section Succ.
Hypothesis Hbl : blen <= 1484.
Hypothesis Hcapok : FBI.fb_len blen <= cap.
Hypothesis Hsys : system_at bb = false.

Lemma fb_code_ok : build_code bb cap = FBI.fb_len blen.
Proof.
  unfold build_code. rewrite (proj2 (Z.ltb_ge 1484 blen) Hbl), Hsys.
  pose proof Hcapok as Hc. rewrite FBI.fb_len_frame_len in Hc.
  rewrite (proj2 (Z.ltb_ge cap (frame_len (length bb))) Hc).
  symmetry. apply FBI.fb_len_frame_len.
Qed.

Lemma fb_L7_out : fb_L7 = PBuild.build_out dmac smac send ack retry cmd ncmds bb mode oj.
Proof.
  unfold PBuild.build_out. cbv zeta. rewrite fb_code_ok.
  assert (E0 : (0 <=? FBI.fb_len blen) = true) by (apply Z.leb_le; unfold FBI.fb_len; fb_lia). rewrite E0. cbv iota.
  unfold fb_L7, fb_L6, fb_L5, fb_L4, fb_L3, fb_L2, fb_L1.
  rewrite fbk_frame_bytes by (first [exact Ldmac | exact Lsmac | exact Hm01 | rewrite <- FBI.fb_len_frame_len; exact Hcapok]).
  f_equal. f_equal.
  pose proof (length_build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1) Ldmac Lsmac) as L.
  rewrite <- FBI.fb_len_frame_len in L. fb_lia.
Qed.

Lemma fb_succ_bounds : 60 <= cap /\ 30 + blen <= cap /\ (30 <= length oj)%nat.
Proof. pose proof Hcapok as H. unfold FBI.fb_len in H. fb_lia. Qed.

(* At FB_RET_C3: fb_seg5Z, or fb_seg5 and __asan_memset(out + 30 + body_len, 0, 30 - body_len), then fb_at_epi. *)
Lemma fb_at_retc3 : forall ly1 S1 W1 rg m1 md1, fb_stR ly1 S1 W1 m1 md1 -> fb_sregs rg -> fb_outv W1 m1 fb_L6 ->
  SRr segs W1 (@cfg_at fx segs FBI.FB_RET_C3 rg m1 md1) POST.
Proof.
  pose proof fb_out_pos as Opos.
  intros ly1 S1 W1 rg m1 md1 HS HR HO.
  pose proof HR as ((HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) & K24 & K25).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3). pose proof fb_ceil as CEIL. pose proof fb_succ_bounds as (Sb1 & Sb2 & Sb3).
  destruct (Z_lt_le_dec blen 30) as [Hlt | Hge].
  - assert (Elen : FBI.fb_len blen = 60) by (unfold FBI.fb_len; fb_lia).
    pose proof SEG5 as SG. unfold FBI.fb_seg5_stmt in SG.
    eapply (decode_run W1 rg m1 md1 FBI.FB_RET_C3).
    { unfold LCK.ms_of_regs. rewrite K8, K24, K25, Elen. eapply SG; fb_lia. }
    intros ms1 ms2 md' -> HE _ Hs.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    pose proof (fb_ra 0x3d0 ltac:(fb_in)) as (RA1 & RA2).
    apply (fb_memset ly1 S1 W1 R' m1 md' fb_L6 (30 + length bb) (30 - length bb) FBI.FB_EPI POST).
    + exact (fb_stR_md _ _ _ _ _ _ HS Hs).
    + unfold fb_k4. fb_regs.
    + exact E1.
    + unfold FBI.FB_EPI. fb_lia.
    + exact RA2.
    + rewrite E10. f_equal; fb_lia.
    + exact E11.
    + rewrite E12. f_equal; fb_lia.
    + exact HO.
    + fb_lia.
    + fb_lia.
    + fb_lia.
    + intros regs2 m2 md2 HS2 HP2 HO2.
      apply (fb_at_epi01 ly1 S1 W1 regs2 m2 md2 60 (proj1 HS2)).
      * apply (fb_k4_pres R' regs2); [unfold fb_k4; fb_regs | exact HP2].
      * fb_kp HP2.
      * rewrite fb_code_ok. exact (eq_sym Elen).
      * rewrite <- fb_L7_out. exact HO2.
  - pose proof SEG5Z as SG. unfold FBI.fb_seg5Z_stmt in SG.
    eapply (decode_run W1 rg m1 md1 FBI.FB_RET_C3).
    { unfold LCK.ms_of_regs. rewrite K24, K25. eapply SG. fb_lia. }
    intros ms1 ms2 md' -> HE _ Hs.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    apply (fb_at_epi01 ly1 S1 W1 R' m1 md' (FBI.fb_len blen)).
    + exact (proj1 (fb_stR_md _ _ _ _ _ _ HS Hs)).
    + unfold fb_k4. fb_regs.
    + exact E24.
    + symmetry. exact fb_code_ok.
    + rewrite <- fb_L7_out. unfold fb_L7. replace (30 - length bb)%nat with 0%nat by fb_lia. cbn [repeat].
      rewrite fbk_put_nil; [exact HO|]. destruct HO as (HOl & _). rewrite HOl. fb_lia.
Qed.

(* At FB_TAIL: fb_seg4Z (empty body), or fb_seg4 and __asan_memcpy(out + 30, body, body_len). *)
Lemma fb_at_tail : forall ly1 S1 W1 rg m1 md1, fb_stR ly1 S1 W1 m1 md1 -> fb_sregs rg -> fb_outv W1 m1 fb_L5 ->
  SRr segs W1 (@cfg_at fx segs FBI.FB_TAIL rg m1 md1) POST.
Proof.
  pose proof fb_out_pos as Opos.
  intros ly1 S1 W1 rg m1 md1 HS HR HO.
  pose proof HR as ((HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) & K24 & K25).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3). pose proof fb_ceil as CEIL. pose proof fb_succ_bounds as (Sb1 & Sb2 & Sb3).
  pose proof fb_bnd as (_ & _ & _ & _ & _ & _ & Bb).
  destruct (Nat.eq_dec (length bb) 0) as [H0 | H0].
  - pose proof SEG4Z as SG. unfold FBI.fb_seg4Z_stmt in SG.
    eapply (decode_run W1 rg m1 md1 FBI.FB_TAIL).
    { unfold LCK.ms_of_regs. rewrite K9, H0. eapply SG. }
    intros ms1 ms2 md' -> HE _ Hs.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    apply (fb_at_retc3 ly1 S1 W1 R' m1 md').
    + exact (fb_stR_md _ _ _ _ _ _ HS Hs).
    + assert (E9' : GR R' 9 = Z_to_bv 64 blen) by (rewrite E9, H0; reflexivity). clear E9.
      unfold fb_sregs, fb_s9, fb_k4. fb_regs.
    + apply length_zero_iff_nil in H0. unfold fb_L6. rewrite H0, fbk_put_nil; [exact HO|].
      destruct HO as (HOl & _). rewrite HOl. fb_lia.
  - destruct (Bb ltac:(fb_lia)) as (Bb1 & Bb2).
    pose proof HS as (_ & (_ & _ & Rb & _)).
    pose proof SEG4 as SG. unfold FBI.fb_seg4_stmt in SG.
    eapply (decode_run W1 rg m1 md1 FBI.FB_TAIL).
    { unfold LCK.ms_of_regs. rewrite K8, K9, K18. eapply SG; fb_lia. }
    intros ms1 ms2 md' -> HE _ Hs.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    pose proof (fb_ra 0x3bc ltac:(fb_in)) as (RA1 & RA2).
    assert (HR' : fb_sregs R') by (unfold fb_sregs, fb_s9, fb_k4; fb_regs).
    apply (fb_memcpy ly1 S1 W1 R' m1 md' fb_L5 30 bb body FBI.FB_RET_C3 POST).
    + exact (fb_stR_md _ _ _ _ _ _ HS Hs).
    + exact (proj1 (proj1 HR')).
    + exact E1.
    + unfold FBI.FB_RET_C3. fb_lia.
    + exact RA2.
    + rewrite E10. f_equal; fb_lia.
    + exact E11.
    + exact E12.
    + exact HO.
    + fb_lia.
    + fb_lia.
    + fb_lia.
    + exact (Rb ltac:(fb_lia)).
    + exact Obody.
    + exact Dbody.
    + intros regs2 m2 md2 HS2 HP2 HO2.
      exact (fb_at_retc3 ly1 S1 W1 regs2 m2 md2 HS2 (fb_sregs_pres R' regs2 HR' HP2) HO2).
Qed.

(* The 12 header bytes, at a state: what fb_h2a and fb_h2b ask. *)
Lemma fb_hdr_run : forall ly1 S1 W1 m1 md1, fb_stR ly1 S1 W1 m1 md1 ->
  LMem.bytes_at AImg0.rsegs m1 (hp + 4) (FBI.fb_hdr_in send ack retry cmd ncmds) /\
  FC.addressable m1 (hp + 4) 12 /\ ExecF.rng (RNGW W1) (hp + 4) 12 /\
  ExecF.rng (RNGW W1) (FC.shadow_addr (hp + 4)) (FC.shadow_addr (hp + 15) - FC.shadow_addr (hp + 4) + 1).
Proof.
  intros ly1 S1 W1 m1 md1 HS. pose proof HS as (_ & (_ & _ & _ & Rh & _)).
  destruct (fb_src_run ly1 S1 W1 m1 md1 (hp + 4) _ HS Rh ltac:(rewrite FBI.fb_hdr_in_length; fb_lia))
    as (Hb & Had & Hrg & Hrs & _).
  rewrite FBI.fb_hdr_in_length in Had, Hrg, Hrs.
  replace (hp + 15) with (hp + 4 + Z.of_nat 12 - 1) by fb_lia.
  split; [exact Hb|]. split; [exact Had|]. split; [exact Hrg | exact Hrs].
Qed.

(* At FB_H2B: fb_h2b, the stores out+22 .. out+29. *)
Lemma fb_at_h2b : forall ly1 S1 W1 rg m1 md1, fb_stR ly1 S1 W1 m1 md1 -> fb_sregs rg -> fb_outv W1 m1 fb_L4 ->
  SRr segs W1 (@cfg_at fx segs FBI.FB_H2B rg m1 md1) POST.
Proof.
  pose proof fb_out_pos as Opos.
  intros ly1 S1 W1 rg m1 md1 HS HR HO.
  pose proof HR as ((HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) & K24 & K25).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3). pose proof fb_ceil as CEIL. pose proof fb_succ_bounds as (Sb1 & Sb2 & Sb3).
  pose proof fb_bnd as (_ & _ & _ & _ & Bh1 & Bh2 & _).
  destruct (fb_hdr_run _ _ _ _ _ HS) as (Hb & Had & Hrg & Hrs).
  destruct (fb_out_run _ _ _ _ _ (out + 12) 18 HS ltac:(fb_lia) ltac:(fb_lia) ltac:(fb_lia)) as (Oad & Org & Ors).
  pose proof HO as (HOl & _).
  pose proof H2BS as SG. unfold FBI.fb_h2b_stmt in SG.
  eapply (decode_run W1 rg m1 md1 FBI.FB_H2B).
  { unfold LCK.ms_of_regs. rewrite K8, K19, K26.
    eapply SG with (l := fb_L4) (send := send) (ack := ack) (retry := retry) (cmd := cmd) (ncmds := ncmds).
    - fb_lia.
    - rewrite HOl. fb_lia.
    - rewrite HOl. exact Sb3.
    - fb_lia.
    - fb_lia.
    - exact Hsend.
    - exact Hack.
    - exact Hretry.
    - exact Hcmd.
    - exact Hncmds.
    - rewrite HOl. exact Dhdr.
    - exact (fb_outv_rw _ _ _ _ _ fb_L4 HS HO).
    - exact Hb.
    - exact Oad.
    - exact Had.
    - exact Org.
    - exact Hrg.
    - replace (out + 29) with (out + 12 + 18 - 1) by fb_lia. exact Ors.
    - exact Hrs. }
  intros ms1 ms2 md' (a0' & a1' & a2' & a3' & m2 & -> & MU & WM & RW) HE HG Hs.
  destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
  destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  pose proof (fb_st_write ly1 S1 W1 m1 md1 m2 md' (out + 22) (out + 30) HS MU HG ltac:(fb_lia) ltac:(fb_lia) Hs) as HS2.
  apply (fb_at_tail ly1 S1 W1 R' m2 md' HS2).
  - unfold fb_sregs, fb_s9, fb_k4. fb_regs.
  - apply (fb_outv_of_rw _ _ _ _ _ fb_L4 _ HS2 RW).
    rewrite FBI.fb_put_length; [exact HOl|]. cbn [length app put16 put32]. rewrite HOl. fb_lia.
Qed.

(* At FB_H2: fb_h2a, the stores out+16 .. out+21. *)
Lemma fb_at_h2 : forall ly1 S1 W1 rg m1 md1, fb_stR ly1 S1 W1 m1 md1 -> fb_sregs rg ->
  GR rg 11 = Z_to_bv 64 (FBI.fb_sum bb mode) -> GR rg 12 = Z_to_bv 64 (FBI.fb_sum bb mode / 2 ^ 8) ->
  fb_outv W1 m1 fb_L3 -> SRr segs W1 (@cfg_at fx segs FBI.FB_H2 rg m1 md1) POST.
Proof.
  pose proof fb_out_pos as Opos.
  intros ly1 S1 W1 rg m1 md1 HS HR G11 G12 HO.
  pose proof HR as ((HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) & K24 & K25).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3). pose proof fb_ceil as CEIL. pose proof fb_succ_bounds as (Sb1 & Sb2 & Sb3).
  pose proof fb_bnd as (_ & _ & _ & _ & Bh1 & Bh2 & _).
  destruct (fb_hdr_run _ _ _ _ _ HS) as (Hb & Had & Hrg & Hrs).
  destruct (fb_out_run _ _ _ _ _ (out + 12) 18 HS ltac:(fb_lia) ltac:(fb_lia) ltac:(fb_lia)) as (Oad & Org & Ors).
  pose proof HO as (HOl & _).
  pose proof (FBI.fb_sum_nonneg bb mode) as Sm0.
  assert (Sm1 : FBI.fb_sum bb mode < 2 ^ 32).
  { unfold FBI.fb_sum. destruct (mode =? 0); [|fb_lia]. pose proof (FBI.sum_bytes_le bb). fb_lia. }
  pose proof H2AS as SG. unfold FBI.fb_h2a_stmt in SG.
  eapply (decode_run W1 rg m1 md1 FBI.FB_H2).
  { unfold LCK.ms_of_regs. rewrite K8, G11, G12, K19, K26.
    eapply SG with (l := fb_L3) (send := send) (ack := ack) (retry := retry) (cmd := cmd) (ncmds := ncmds).
    - fb_lia.
    - rewrite HOl. fb_lia.
    - rewrite HOl. exact Sb3.
    - fb_lia.
    - fb_lia.
    - exact Hsend.
    - exact Hack.
    - exact Hretry.
    - exact Hcmd.
    - exact Hncmds.
    - fb_lia.
    - rewrite HOl. exact Dhdr.
    - exact (fb_outv_rw _ _ _ _ _ fb_L3 HS HO).
    - exact Hb.
    - exact Oad.
    - exact Had.
    - exact Org.
    - exact Hrg.
    - replace (out + 29) with (out + 12 + 18 - 1) by fb_lia. exact Ors.
    - exact Hrs. }
  intros ms1 ms2 md' (a0' & a1' & a2' & a3' & m2 & -> & MU & WM & RW) HE HG Hs.
  destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
  destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  pose proof (fb_st_write ly1 S1 W1 m1 md1 m2 md' (out + 16) (out + 22) HS MU HG ltac:(fb_lia) ltac:(fb_lia) Hs) as HS2.
  apply (fb_at_h2b ly1 S1 W1 R' m2 md' HS2).
  - unfold fb_sregs, fb_s9, fb_k4. fb_regs.
  - apply (fb_outv_of_rw _ _ _ _ _ fb_L3 _ HS2 RW).
    rewrite FBI.fb_put_length; [exact HOl|]. cbn [length app put16 put32]. rewrite HOl. fb_lia.
Qed.

(* At FB_SUM: fb_loop, the sum of the body; no byte written. *)
Lemma fb_at_sum : forall ly1 S1 W1 rg m1 md1, fb_stR ly1 S1 W1 m1 md1 -> fb_sregs rg ->
  GR rg 11 = Z_to_bv 64 0 -> GR rg 12 = Z_to_bv 64 0 ->
  fb_outv W1 m1 fb_L3 -> SRr segs W1 (@cfg_at fx segs FBI.FB_SUM rg m1 md1) POST.
Proof.
  intros ly1 S1 W1 rg m1 md1 HS HR G11 G12 HO.
  pose proof HR as ((HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) & K24 & K25).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_ceil as CEIL.
  pose proof HS as (_ & (_ & _ & Rb & _)).
  pose proof fb_bnd as (_ & _ & _ & _ & _ & _ & Bb).
  pose proof LOOPS as SG. unfold FBI.fb_loop_stmt in SG.
  eapply (decode_run W1 rg m1 md1 FBI.FB_SUM).
  { unfold LCK.ms_of_regs. rewrite K8, K9, G11, G12, K18, K20, K26.
    eapply SG.
    - fb_lia.
    - exact Hm01.
    - intros HL. destruct (Bb HL) as (Bb1 & Bb2).
      destruct (fb_src_run _ _ _ _ _ body bb HS (Rb HL) HL) as (Hb & Had & Hrg & Hrs & _).
      split; [fb_lia|]. split; [fb_lia|]. split; [exact Hb|]. split; [exact Had|]. split; [exact Hrg | exact Hrs]. }
  intros ms1 ms2 md' (a0' & a3' & a4' & a5' & ->) HE _ Hs.
  destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
  destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  apply (fb_at_h2 ly1 S1 W1 R' m1 md').
  - exact (fb_stR_md _ _ _ _ _ _ HS Hs).
  - unfold fb_sregs, fb_s9, fb_k4. fb_regs.
  - exact E11.
  - exact E12.
  - exact HO.
Qed.

(* At FB_RET_C2: fb_h1, the stores out+12 .. out+15. *)
Lemma fb_at_retc2 : forall ly1 S1 W1 rg m1 md1, fb_stR ly1 S1 W1 m1 md1 -> fb_sregs rg -> fb_outv W1 m1 fb_L2 ->
  SRr segs W1 (@cfg_at fx segs FBI.FB_RET_C2 rg m1 md1) POST.
Proof.
  pose proof fb_out_pos as Opos.
  intros ly1 S1 W1 rg m1 md1 HS HR HO.
  pose proof HR as ((HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) & K24 & K25).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3). pose proof fb_ceil as CEIL. pose proof fb_succ_bounds as (Sb1 & Sb2 & Sb3).
  destruct (fb_out_run _ _ _ _ _ (out + 12) 4 HS ltac:(fb_lia) ltac:(fb_lia) ltac:(fb_lia)) as (Oad & Org & Ors).
  pose proof HO as (HOl & _).
  pose proof H1S as SG. unfold FBI.fb_h1_stmt in SG.
  eapply (decode_run W1 rg m1 md1 FBI.FB_RET_C2).
  { unfold LCK.ms_of_regs. rewrite K8, K9, K26.
    eapply SG with (l := fb_L2).
    - fb_lia.
    - rewrite HOl. fb_lia.
    - rewrite HOl. exact Sb3.
    - fb_lia.
    - exact (fb_outv_rw _ _ _ _ _ fb_L2 HS HO).
    - exact Oad.
    - exact Org.
    - replace (out + 15) with (out + 12 + 4 - 1) by fb_lia. exact Ors. }
  intros ms1 ms2 md' (a3' & m2 & -> & MU & WM & RW) HE HG Hs.
  destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
  destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  pose proof (fb_st_write ly1 S1 W1 m1 md1 m2 md' (out + 12) (out + 16) HS MU HG ltac:(fb_lia) ltac:(fb_lia) Hs) as HS2.
  apply (fb_at_sum ly1 S1 W1 R' m2 md' HS2).
  - unfold fb_sregs, fb_s9, fb_k4. fb_regs.
  - exact E11.
  - exact E12.
  - apply (fb_outv_of_rw _ _ _ _ _ fb_L2 _ HS2 RW).
    rewrite FBI.fb_put_length; [exact HOl|]. cbn [length app put16 put32]. rewrite HOl. fb_lia.
Qed.

(* At FB_RET_C1: fb_seg3 and __asan_memcpy(out + 6, src, 6). *)
Lemma fb_at_retc1 : forall ly1 S1 W1 rg m1 md1, fb_stR ly1 S1 W1 m1 md1 -> fb_sregs rg -> fb_outv W1 m1 fb_L1 ->
  SRr segs W1 (@cfg_at fx segs FBI.FB_RET_C1 rg m1 md1) POST.
Proof.
  pose proof fb_out_pos as Opos.
  intros ly1 S1 W1 rg m1 md1 HS HR HO.
  pose proof HR as ((HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26) & K24 & K25).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3). pose proof fb_ceil as CEIL. pose proof fb_succ_bounds as (Sb1 & Sb2 & Sb3).
  pose proof fb_bnd as (_ & _ & Bs1 & Bs2 & _).
  pose proof HS as (_ & (_ & Rs & _)).
  pose proof SEG3 as SG. unfold FBI.fb_seg3_stmt in SG.
  eapply (decode_run W1 rg m1 md1 FBI.FB_RET_C1).
  { unfold LCK.ms_of_regs. rewrite K8, K21. eapply SG; fb_lia. }
  intros ms1 ms2 md' -> HE _ Hs.
  destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
  destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  pose proof (fb_ra 0xf4 ltac:(fb_in)) as (RA1 & RA2).
  assert (HR' : fb_sregs R') by (unfold fb_sregs, fb_s9, fb_k4; fb_regs).
  apply (fb_memcpy ly1 S1 W1 R' m1 md' fb_L1 6 smac src FBI.FB_RET_C2 POST).
  - exact (fb_stR_md _ _ _ _ _ _ HS Hs).
  - exact (proj1 (proj1 HR')).
  - exact E1.
  - unfold FBI.FB_RET_C2. fb_lia.
  - exact RA2.
  - rewrite E10. f_equal; fb_lia.
  - exact E11.
  - rewrite E12, Lsmac. reflexivity.
  - exact HO.
  - rewrite Lsmac. fb_lia.
  - rewrite Lsmac. fb_lia.
  - rewrite Lsmac. fb_lia.
  - exact Rs.
  - rewrite Lsmac. exact Osrc.
  - rewrite Lsmac. exact Dsrc.
  - intros regs2 m2 md2 HS2 HP2 HO2.
    exact (fb_at_retc2 ly1 S1 W1 regs2 m2 md2 HS2 (fb_sregs_pres R' regs2 HR' HP2) HO2).
Qed.
End Succ.

(* At FB_RET_BC: a0 = body_check bb. -10: fb_seg2R; cap < len: fb_seg2S (-5); else fb_seg2C and
   __asan_memcpy(out, dst, 6). *)
Lemma fb_at_retbc : forall ly2 S2 W2 rg m2 md2, fb_stR ly2 S2 W2 m2 md2 -> fb_s9 rg ->
  GR rg 10 = Z_to_bv 64 (body_check bb) -> blen <= 1484 -> fb_outv W2 m2 oj ->
  SRr segs W2 (@cfg_at fx segs FBI.FB_RET_BC rg m2 md2) POST.
Proof.
  pose proof fb_out_pos as Opos.
  intros ly2 S2 W2 rg m2 md2 HS HR G10 Hbl HO.
  pose proof HR as (HK & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K26).
  pose proof HK as (K2 & K3 & K4 & K27).
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3). pose proof fb_ceil as CEIL.
  pose proof fb_bnd as (Bd1 & Bd2 & _).
  pose proof HS as (_ & (Rd & _)).
  destruct (system_at bb) eqn:Hsys.
  - assert (G10' : GR rg 10 = Z_to_bv 64 (-10)) by (rewrite G10, body_check_spec, Hsys; reflexivity).
    pose proof SEG2R as SG. unfold FBI.fb_seg2R_stmt in SG.
    eapply (decode_run W2 rg m2 md2 FBI.FB_RET_BC).
    { unfold LCK.ms_of_regs. rewrite G10'. eapply SG. intros E. vm_compute in E. discriminate E. }
    intros ms1 ms2 md' -> HE _ Hs.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    assert (Hcode : build_code bb cap = -10) by (unfold build_code; rewrite (proj2 (Z.ltb_ge 1484 blen) Hbl), Hsys; reflexivity).
    apply (fb_at_epi01 ly2 S2 W2 R' m2 md' (-10)).
    + exact (proj1 (fb_stR_md _ _ _ _ _ _ HS Hs)).
    + unfold fb_k4. fb_regs.
    + exact E24.
    + symmetry. exact Hcode.
    + rewrite fb_out_neg by fb_lia. exact HO.
  - assert (G10' : GR rg 10 = Z_to_bv 64 0) by (rewrite G10, body_check_spec, Hsys; reflexivity).
    destruct (Z_lt_le_dec cap (FBI.fb_len blen)) as [Hlt | Hge].
    + pose proof SEG2S as SG. unfold FBI.fb_seg2S_stmt in SG.
      eapply (decode_run W2 rg m2 md2 FBI.FB_RET_BC).
      { unfold LCK.ms_of_regs. rewrite G10', K9, K23. eapply SG; [reflexivity | fb_lia | fb_lia | exact Hlt]. }
      intros ms1 ms2 md' -> HE _ Hs.
      destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
      destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
        E23 & E24 & E25 & E26 & E27).
      assert (Hcode : build_code bb cap = -5).
      { unfold build_code. rewrite (proj2 (Z.ltb_ge 1484 blen) Hbl), Hsys.
        rewrite FBI.fb_len_frame_len in Hlt. rewrite (proj2 (Z.ltb_lt cap (frame_len (length bb))) Hlt). reflexivity. }
      apply (fb_at_epi01 ly2 S2 W2 R' m2 md' (-5)).
      * exact (proj1 (fb_stR_md _ _ _ _ _ _ HS Hs)).
      * unfold fb_k4. fb_regs.
      * exact E24.
      * symmetry. exact Hcode.
      * rewrite fb_out_neg by fb_lia. exact HO.
    + pose proof SEG2C as SG. unfold FBI.fb_seg2C_stmt in SG.
      eapply (decode_run W2 rg m2 md2 FBI.FB_RET_BC).
      { unfold LCK.ms_of_regs. rewrite G10', K8, K9, K22, K23. eapply SG; [reflexivity | fb_lia | fb_lia | exact Hge | fb_lia | fb_lia]. }
      intros ms1 ms2 md' -> HE _ Hs.
      destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
      destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
        E23 & E24 & E25 & E26 & E27).
      pose proof (fb_ra 0xe4 ltac:(fb_in)) as (RA1 & RA2).
      assert (HR' : fb_sregs R') by (unfold fb_sregs, fb_s9, fb_k4; fb_regs).
      pose proof Hge as Hge'. unfold FBI.fb_len in Hge'.
      apply (fb_memcpy ly2 S2 W2 R' m2 md' oj 0 dmac dst FBI.FB_RET_C1 POST).
      * exact (fb_stR_md _ _ _ _ _ _ HS Hs).
      * exact (proj1 (proj1 HR')).
      * exact E1.
      * unfold FBI.FB_RET_C1. fb_lia.
      * exact RA2.
      * rewrite E10. f_equal; fb_lia.
      * exact E11.
      * rewrite E12, Ldmac. reflexivity.
      * exact HO.
      * rewrite Ldmac. fb_lia.
      * rewrite Ldmac. fb_lia.
      * rewrite Ldmac. fb_lia.
      * exact Rd.
      * rewrite Ldmac. exact Odst.
      * rewrite Ldmac. exact Ddst.
      * intros regs2 m2' md2' HS2 HP2 HO2.
        exact (fb_at_retc1 Hbl Hge Hsys ly2 S2 W2 regs2 m2' md2' HS2 (fb_sregs_pres R' regs2 HR' HP2) HO2).
Qed.

(* The call of diginet_body_check (body, body_len) at FB_BC, from the state after the prologue: a donor-form callee,
   lifted into the caller's G journal by TransportGCg.v gx_call_cg. Its post keeps every byte at or above
   alloc_ceiling outside its window, the caller's blocks, the image outside the owned statics and errno, the frames
   of the call state and their shadow bytes, and every byte of G: the keep facts compose (dk_kept_trans_g,
   gx_kept_ex_trans), and each range the function reads keeps its placement and bytes (trans_src_ok_acall_g). *)
Lemma fb_bc_call : forall m1 md1 rgB, fb_stR lyc Sc W m1 md1 -> fb_outv W m1 oj ->
  trans_src_ok B lyc Sc W m1 out cap -> blen <= 1484 ->
  fb_k4 rgB -> GR rgB 1 = Z_to_bv 64 FBI.FB_RET_BC -> GR rgB 8 = Z_to_bv 64 out -> GR rgB 9 = Z_to_bv 64 blen ->
  GR rgB 10 = Z_to_bv 64 body -> GR rgB 11 = Z_to_bv 64 blen -> GR rgB 18 = Z_to_bv 64 body ->
  GR rgB 19 = Z_to_bv 64 hp -> GR rgB 20 = Z_to_bv 64 mode -> GR rgB 21 = Z_to_bv 64 src ->
  GR rgB 22 = Z_to_bv 64 dst -> GR rgB 23 = Z_to_bv 64 cap -> GR rgB 26 = Z_to_bv 64 FC.ASAN_K ->
  SRr segs W (mkCfg (@YK11.mkst fx rgB (Z_to_bv 64 FBI.FB_BC) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros m1 md1 rgB ((J1 & Hfr & HP & Hmo & HF & KP1 & KX1) & RD) HO Hos Hbl (K2 & K3 & K4 & K27) G1 G8 G9 G10 G11
    G18 G19 G20 G21 G22 G23 G26.
  pose proof fb_sp as (Hsp1 & Hsp2 & Hs016). pose proof fb_stk as (St1 & St2 & St3). pose proof fb_ceil as CEIL.
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3).
  pose proof fb_bnd as (Bd1 & Bd2 & Bs1 & Bs2 & Bh1 & Bh2 & Bb).
  pose proof fb_body_rng as Br.
  pose proof (fb_ra 0xa8 ltac:(fb_in)) as (RA1 & RA2).
  assert (SPB : spZ rgB = spZ regs - 96).
  { change (spZ rgB) with (bv_unsigned (GR rgB 2)). rewrite K2. rewrite fbk_u64 by fb_lia. reflexivity. }
  pose proof RD as (Rd & Rs & Rb & Rh & _).
  pose proof (ajournal_gx_AR segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k J1) as HAR1.
  unfold FBI.FB_BC.
  eapply SRr_bind.
  { apply (@gx_call_cg fx rc AE2k.tfib_sink_head segs B MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k _ rgB
             PBC.TRANS_BC_STK
             PBC.TRANS_BC_EV 0 (fun _ => False) (fun regs2 _ _ => YK11.getr regs2 10 = w64 (body_check bb))
             fb_GOK fb_GNE J1).
    intros memS HJS. eapply SRr_mono.
    { apply (ABC fx STK sp0 FP ly S W0 memS md0 own lyc Sc W m1 md1 k rgB body bb HJS).
      - change (YK11.getr rgB 1) with (GR rgB 1). rewrite G1. apply YK0s.ret_ok_even.
        rewrite fbk_u64 by (unfold FBI.FB_RET_BC; fb_lia). exact RA2.
      - change (raZ rgB) with (bv_unsigned (GR rgB 1)). rewrite G1, fbk_u64 by (unfold FBI.FB_RET_BC; fb_lia).
        unfold FBI.FB_RET_BC. fb_lia.
      - exact (eq_trans K3 Hgp).
      - exact (eq_trans K4 Htp).
      - exact G10.
      - exact G11.
      - rewrite SPB. rewrite Zminus_mod, Hal. reflexivity.
      - rewrite SPB. fb_lia.
      - rewrite SPB. fb_lia.
      - exact Hbody0.
      - intros HL. exact (proj1 (Rb HL)).
      - intros HL. unfold decode_off_win. rewrite SPB. exact (fb_off_bc _ _ Obody).
      - destruct (Nat.eq_dec (length bb) 0) as [H0 | H0].
        + apply (fbk_aview_garr8 W m1 body bb); [fb_lia | fb_lia |]. intros j Hj. exfalso. fb_lia.
        + destruct (Bb ltac:(fb_lia)) as (Bb1 & Bb2).
          apply (fbk_aview_garr8 W m1 body bb); [fb_lia | fb_lia |]. exact (proj2 (Rb ltac:(fb_lia))).
      - exact Hcid.
      - unfold PBC.TRANS_BC_EV. unfold FRAME_FB_EV in Hnev. fb_lia. }
    intros W' c' _ Hp.
    exact (decode_cg_post_dcg B MT STK sp0 FP ly S W0 memS md0 own lyc Sc W m1 k rgB _ _ _ _ _ W' c' Hp). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & e & -> & He & J2 & HPR & Hfr2 & Hperm2 & HK & Hmo2 &
    (H10' & HGK)).
  assert (Ee : e = 0) by (unfold PBC.TRANS_BC_EV in He; fb_lia). subst e. rewrite Z.add_0_r in J2.
  change (YK11.getr rgB 1) with (GR rgB 1). rewrite G1.
  pose proof (ajournal_gx_AR segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m2 md2 k J2) as HAR2.
  destruct (fb_ly ly2 S2 W2 m2 md2 J2) as (HF2 & HL2 & HH2).
  assert (AC : forall q n, q + n <= spZ rgB - PBC.TRANS_BC_STK \/ spZ rgB <= q -> trans_src_ok B lyc Sc W m1 q n -> 0 < n ->
            trans_src_ok B ly2 S2 W2 m2 q n /\
            (forall a, q <= a < q + n -> aview segs (w_H W2) m2 a = aview segs (w_H W) m1 a)).
  { intros q n Hw Ht Hn.
    exact (trans_src_ok_acall_g B LAWS HROU HROE lyc Sc W m1 md1 ly2 S2 W2 m2 md2 _ _ (fun _ => False) q n HAR1 HAR2
             Hperm2 Hfr2 HF2 HL2 HH2 HK HGK (fun _ _ H => H) (fun _ _ H => H) Hw Ht Hn). }
  assert (SVt : forall q (l : list byte), (0 < length l)%nat ->
            q + Z.of_nat (length l) <= spZ rgB - PBC.TRANS_BC_STK \/ spZ rgB <= q ->
            fb_sv lyc Sc W m1 q l -> fb_sv ly2 S2 W2 m2 q l).
  { intros q l Hl Hw (Ht & Hv). destruct (AC q _ Hw Ht ltac:(fb_lia)) as (Ht2 & Hk2). split; [exact Ht2|].
    intros j Hj. rewrite Hk2 by fb_lia. exact (Hv j Hj). }
  assert (Hcap : forall a, out <= a < out + cap -> a < alloc_ceiling).
  { intros a Ha. destruct (fb_out_far ltac:(fb_lia)) as (_ & O2 & _). fb_lia. }
  assert (OUT2 : fb_outv W2 m2 oj /\ range_addressable (aview segs (w_H W2) m2) SHADOW_OFF out cap /\
                 (0 < cap -> shadow_hull_vis (aview segs (w_H W2) m2) out cap)).
  { destruct (Z_lt_le_dec 0 cap) as [Hc | Hc].
    - destruct (fb_out_far Hc) as (O1 & O2 & _).
      destruct (AC out cap ltac:(rewrite SPB; fb_lia) Hos Hc) as (Ht2 & Hk2).
      destruct (trans_src_ok_rd B LAWS ly2 S2 W2 m2 md2 out cap HAR2 Ht2 Hc) as (_ & R2 & R3 & _).
      split; [|split; [exact R2 | intros _; exact R3]].
      apply (fb_outv_kept W m1 W2 m2 oj HO). intros j Hj. apply Hk2. fb_lia.
    - split; [|split; [intros x Hx; exfalso; fb_lia | intros H; exfalso; fb_lia]].
      split; [reflexivity|]. intros j Hj. exfalso. fb_lia. }
  destruct OUT2 as (HO2 & Ora2 & Oh2).
  apply (fb_at_retbc ly2 S2 W2 regs2 m2 md2).
  - split; [split|].
    + exact J2.
    + split; [exact Hfr2|]. split; [exact Hperm2|]. split; [exact Hmo2|].
      split.
      { apply (fb_frame_kept W W2 m1 m2 lyc Sc md1 ly2 S2 md2 HF J1 J2). intros a Ha.
        apply (proj1 HK); [fb_lia | rewrite SPB; fb_lia]. }
      split.
      { apply (dk_kept_trans_g segs B G lyc Sc W memc W m1 W2 m2 (spZ regs - FRAME_FB_STK) (spZ regs)
                 (spZ rgB - PBC.TRANS_BC_STK) (spZ rgB) _ (fun _ => False)); [fb_lia | fb_lia | exact KP1 | exact HK | | |].
        - rewrite SPB. fb_lia.
        - rewrite SPB. fb_lia.
        - intros a []. }
      exact (gx_kept_ex_trans segs G _ W memc W m1 W2 m2 KX1 (gx_kept_ex_of_kept segs G _ W m1 W2 m2 HGK)).
    + split; [apply (SVt dst dmac); [rewrite Ldmac; fb_lia | rewrite Ldmac, SPB; exact (fb_off_bc _ _ Odst) | exact Rd]|].
      split; [apply (SVt src smac); [rewrite Lsmac; fb_lia | rewrite Lsmac, SPB; exact (fb_off_bc _ _ Osrc) | exact Rs]|].
      split; [intros HL; apply (SVt body bb); [exact HL | rewrite SPB; exact (fb_off_bc _ _ Obody) | exact (Rb HL)]|].
      split; [apply (SVt (hp + 4) _); [rewrite FBI.fb_hdr_in_length; fb_lia |
                rewrite FBI.fb_hdr_in_length, SPB; exact (fb_off_bc _ _ Ohdr) | exact Rh]|].
      split; [exact Ora2 | exact Oh2].
  - apply (fb_s9_pres rgB regs2); [|exact HPR]. unfold fb_s9, fb_k4.
    repeat match goal with |- _ /\ _ => split end; assumption.
  - exact H10'.
  - exact Hbl.
  - exact HO2.
Qed.
End M01.

(* The prologue (fb_seg1, fb_seg1L, fb_seg1M) writes only the frame [spZ regs - 96, spZ regs): the state after it. *)
Lemma fb_pro : forall m1 md', LFrame.munch [(spZ regs - 96, spZ regs)] memc m1 -> YK1b.mem_grows memc m1 ->
  same_but_materialized mdc md' -> fb_frame m1 ->
  fb_stR lyc Sc W m1 md' /\ fb_outv W m1 oj /\ trans_src_ok B lyc Sc W m1 out cap.
Proof.
  intros m1 md' MU MG Hs RW.
  pose proof fb_sp as (Hsp1 & Hsp2 & Hs016). pose proof fb_stk as (St1 & St2 & St3). pose proof fb_ceil as CEIL.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (fb_win _ _ _ _ _ HJ) as Hpres0.
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3).
  assert (Kv : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
                aview segs (w_H W) m1 a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; exact (fbk_aview_munch _ memc m1 _ _ a MU Ha Hn)).
  assert (HZ : forall a, spZ regs - 96 <= a < spZ regs -> out <= a < out + cap \/ spZ regs - FRAME_FB_STK <= a < spZ regs)
    by (intros a Ha; right; fb_lia).
  assert (J1 : AJ lyc Sc W m1 md').
  { apply (fb_aj_write lyc Sc W memc mdc m1 md' (spZ regs - 96) (spZ regs) HJ MU MG); [|exact Hs].
    intros a Ha. split; [exact (proj1 (Hpres0 a ltac:(fb_lia)))|]. left. split; [left; fb_lia | fb_lia]. }
  assert (Hout_lo : forall a, out <= a < out + cap -> a < spZ regs - 96).
  { intros a Ha. destruct (fb_out_far ltac:(fb_lia)) as (_ & O2 & _). fb_lia. }
  split; [split; [split|] |].
  - exact J1.
  - split; [reflexivity|]. split; [apply Permutation_refl|]. split; [exact (mle_start MT Sc MTL)|].
    split; [exact RW|]. split.
    + apply (fb_kp_step W memc m1 (fun a => spZ regs - 96 <= a < spZ regs)).
      * apply dk_kept_refl_g. exact Hpres0.
      * exact Kv.
      * intros a Hp. exact (fb_pres_grow _ memc m1 a MG Hp).
      * exact HZ.
    + apply (fb_kx_step W memc m1 (fun a => spZ regs - 96 <= a < spZ regs)).
      * apply gx_kept_ex_refl.
      * exact Kv.
      * exact HZ.
  - apply (fb_rd_step lyc Sc W memc m1 fb_rd0). intros a Ha H1 H2. apply Kv; [exact Ha | fb_lia].
  - split.
    + apply (fb_outv_kept W memc W m1 oj fb_outv0). intros j Hj. apply Kv; [fb_lia|]. pose proof (Hout_lo (out + Z.of_nat j) ltac:(fb_lia)). fb_lia.
    + apply (trans_src_ok_view B lyc Sc W W memc m1 out cap fb_out_src).
      * intros a Ha. apply Kv; [fb_lia|]. pose proof (Hout_lo a Ha). fb_lia.
      * intros s Hs'. apply Kv; fb_lia.
Qed.

(* At the entry: fb_seg1M (mode not 0 or 1), fb_seg1L (body_len > 1484) to fb_at_epi, or fb_seg1 to
   diginet_body_check. *)
Lemma fb_entry : SRr segs W (@cfg_at fx segs (transport_sigma TS_diginet_frame_build) regs memc mdc) POST.
Proof.
  pose proof fb_out_pos as Opos.
  pose proof fb_sp as (Hsp1 & Hsp2 & Hs016). pose proof fb_stk as (St1 & St2 & St3). pose proof fb_ceil as CEIL.
  pose proof (fb_win _ _ _ _ _ HJ) as Hpres0.
  pose proof fb_bnd as (Bd1 & Bd2 & Bs1 & Bs2 & Bh1 & Bh2 & Bb).
  pose proof fb_body_rng as Br.
  pose proof fb_out_bnd as (Ob1 & Ob2 & Ob3).
  destruct (decode_cells_asan B HCELLS lyc Sc W memc mdc fb_HARc) as (CK & GCK & _).
  assert (E10 : GR regs 10 = Z_to_bv 64 out) by exact H10.
  assert (E11 : GR regs 11 = Z_to_bv 64 cap) by exact H11.
  assert (E12 : GR regs 12 = Z_to_bv 64 dst) by exact H12.
  assert (E13 : GR regs 13 = Z_to_bv 64 src) by exact H13.
  assert (E14 : GR regs 14 = Z_to_bv 64 hp) by exact H14.
  assert (E15 : GR regs 15 = Z_to_bv 64 body) by exact H15.
  assert (E16 : GR regs 16 = Z_to_bv 64 blen) by exact H16.
  assert (E17 : GR regs 17 = Z_to_bv 64 mode) by exact H17.
  assert (Hbz : 0 < body \/ blen = 0) by (destruct Hbody0 as [H | H]; [left; fb_lia | right; rewrite H; reflexivity]).
  assert (Hbl47 : blen <= 2 ^ 47)
    by (destruct (Nat.eq_dec (length bb) 0) as [E | E]; [rewrite E; fb_lia | destruct (Bb ltac:(fb_lia)); fb_lia]).
  assert (Hmd : (mode = 0 \/ mode = 1) \/ (mode <> 0 /\ mode <> 1)) by fb_lia.
  destruct Hmd as [Hm01 | (Hm0 & Hm1)].
  2: { pose proof SEG1M as SG. unfold FBI.fb_seg1M_stmt in SG.
    eapply (decode_run W regs memc mdc (transport_sigma TS_diginet_frame_build)).
    { unfold LCK.ms_of_regs. rewrite E10, E11, E12, E13, E14, E15, E16, E17.
      eapply SG with (lo := spZ regs - FRAME_FB_STK).
      all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
      - apply (decode_stk_present (w_H W)); [fb_lia | fb_lia | exact Hpres0].
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - exact Br.
      - exact Hbz.
      - fb_lia.
      - fb_lia.
      - exact Hmode.
      - exact Hm0.
      - exact Hm1.
      - apply decode_rng_vis; [fb_lia | fb_lia |]. intros i Hi. exact (proj1 (Hpres0 (spZ regs - 96 + i) ltac:(fb_lia))). }
    intros ms1 ms2 md' (a1' & m1 & -> & MU & WM & RW) HE HG Hs.
    change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, RW.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    destruct (fb_pro m1 md' MU HG Hs RW) as ((HS1 & _) & HO1 & _).
    destruct (fb_wM dmac smac send ack retry cmd ncmds bb mode oj Hm0 Hm1) as (Ec & Eo).
    apply (fb_at_epi lyc Sc W R' m1 md' (-1) HS1).
    + unfold fb_k4. fb_regs.
    + exact E24.
    + symmetry. exact Ec.
    + rewrite Eo. exact HO1. }
  destruct (Z_le_gt_dec blen 1484) as [Hbl | Hbl].
  - pose proof SEG1 as SG. unfold FBI.fb_seg1_stmt in SG.
    eapply (decode_run W regs memc mdc (transport_sigma TS_diginet_frame_build)).
    { unfold LCK.ms_of_regs. rewrite E10, E11, E12, E13, E14, E15, E16, E17.
      eapply SG with (lo := spZ regs - FRAME_FB_STK).
      all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
      - apply (decode_stk_present (w_H W)); [fb_lia | fb_lia | exact Hpres0].
      - fb_lia.
      - exact GCK.
      - exact CK.
      - unfold FC.CELL_K. fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - exact Br.
      - exact Hbz.
      - fb_lia.
      - fb_lia.
      - exact Hm01.
      - apply decode_rng_vis; [fb_lia | fb_lia |]. intros i Hi. exact (proj1 (Hpres0 (spZ regs - 96 + i) ltac:(fb_lia))).
      - apply decode_rng_vis; [unfold FC.GOT_CELL_K; fb_lia | unfold FC.GOT_CELL_K; fb_lia |]. intros i Hi.
        apply (decode_cell_visible W FC.GOT_CELL_K 8 i); [unfold decode_asan_cell_ranges; right; left; reflexivity | exact Hi].
      - apply decode_rng_vis; [unfold FC.CELL_K; fb_lia | unfold FC.CELL_K; fb_lia |]. intros i Hi.
        apply (decode_cell_visible W FC.CELL_K 8 i); [unfold decode_asan_cell_ranges; left; reflexivity | exact Hi]. }
    intros ms1 ms2 md' (m1 & -> & MU & WM & RW) HE HG Hs.
    change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, RW.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    destruct (fb_pro m1 md' MU HG Hs RW) as (HS1 & HO1 & Hos1).
    apply (fb_bc_call Hm01 m1 md' R' HS1 HO1 Hos1 Hbl).
    + unfold fb_k4. fb_regs.
    + exact E1.
    + exact E8.
    + exact E9.
    + exact E10'.
    + exact E11'.
    + exact E18.
    + exact E19.
    + exact E20.
    + exact E21.
    + exact E22.
    + exact E23.
    + exact E26.
  - assert (Hb1 : 0 < body) by (destruct Hbz; fb_lia).
    pose proof SEG1L as SG. unfold FBI.fb_seg1L_stmt in SG.
    eapply (decode_run W regs memc mdc (transport_sigma TS_diginet_frame_build)).
    { unfold LCK.ms_of_regs. rewrite E10, E11, E12, E13, E14, E15, E16, E17.
      eapply SG with (lo := spZ regs - FRAME_FB_STK).
      all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
      - apply (decode_stk_present (w_H W)); [fb_lia | fb_lia | exact Hpres0].
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - fb_lia.
      - exact Hm01.
      - apply decode_rng_vis; [fb_lia | fb_lia |]. intros i Hi. exact (proj1 (Hpres0 (spZ regs - 96 + i) ltac:(fb_lia))). }
    intros ms1 ms2 md' (m1 & -> & MU & WM & RW) HE HG Hs.
    change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, RW.
    destruct (decode_eqv_mkst _ _ _ _ HE) as (R' & -> & HX).
    destruct (fbk_regs_of HX) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    destruct (fb_pro m1 md' MU HG Hs RW) as ((HS1 & _) & HO1 & _).
    assert (Hcode : build_code bb cap = -4)
      by (unfold build_code; rewrite (proj2 (Z.ltb_lt 1484 blen) ltac:(fb_lia)); reflexivity).
    apply (fb_at_epi01 Hm01 lyc Sc W R' m1 md' (-4) HS1).
    + unfold fb_k4. fb_regs.
    + exact E24.
    + symmetry. exact Hcode.
    + rewrite fb_out_neg by fb_lia. exact HO1.
Qed.
End Entry.

Theorem fb_walk : transport_diginet_frame_build_cg B MT (transport_sigma TS_diginet_frame_build).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs out dst src hp body mode send ack retry cmd ncmds
    dmac smac bb oj.
  intros HJ Hra Hra4 Hgp Htp H10 H11 H12 H13 H14 H15 H16 H17 Hal Hwlo Hwhi Hout0 Hdst0 Hsrc0 Hhp0 Hbody0 Hmode
    Hsend Hack Hretry Hcmd Hncmds Hout Htwr Goj Ldmac Tdst Odst Gdmac Lsmac Tsrc Osrc Gsmac Tbody Obody Gbb
    Fhdr Rhdr Ohdr Ghdr Ddst Dsrc Dhdr Dbody Hcid Hnev.
  eapply fb_entry; eassumption.
Qed.
End Walk.

Theorem fb_cg_holds_of_segs : @transport_diginet_frame_build_cg_holds_stmt fx rc B MT.
Proof.
  intros HC HROU HROE LAWS MTL HGU HGE AMC AMS ABC. exact (fb_walk HC HROU HROE LAWS MTL HGU HGE AMC AMS ABC).
Qed.
End Segs.

(* The statement: fb_cg_holds_of_segs at the sixteen footprint runs. *)
Theorem transport_diginet_frame_build_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_frame_build_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@fb_cg_holds_of_segs
           diginet_frame_build_seg_a.fb_seg1_F diginet_frame_build_seg_a.fb_seg1L_F
           diginet_frame_build_seg_a.fb_seg1M_F
           diginet_frame_build_seg_a.fb_seg2R_F diginet_frame_build_seg_a.fb_seg2S_F
           diginet_frame_build_seg_a.fb_seg2C_F diginet_frame_build_seg_a.fb_seg3_F
           diginet_frame_build_seg_h1.fb_h1_F diginet_frame_build_seg_loop.fb_loop_F
           diginet_frame_build_seg_h2a.fb_h2a_F diginet_frame_build_seg_h2b.fb_h2b_F
           diginet_frame_build_seg_a.fb_seg4Z_F diginet_frame_build_seg_a.fb_seg4_F
           diginet_frame_build_seg_a.fb_seg5Z_F diginet_frame_build_seg_a.fb_seg5_F
           diginet_frame_build_seg_a.fb_epi_F fx rc B MT).
Qed.
