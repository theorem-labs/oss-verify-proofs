(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecF6M.v (commit 237eb205ab7b, H4 srrm M walk (image-specific files); file sha256 7b0e151fa43c) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcSecF6M.v at commit c83cc72b041, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: srrm-walk bookkeeping; the walk of __asan::QuarantineCallback::Recycle (0x33e88) is already
   proved by H4; this file composes its prefix pieces on the materialized-page (M) engine).

   WHAT.  [to_XG_M] is DMrcSecF6.to_XG composed from the M pieces YFf5M.segGA_M (zone YFf5M.ZGA: the stack and the
   image window) and YFfbM.gloop_M (zone YFfbM.ZGL lim Q: the scanned cells [Q, Q + 8 * nA) of the pointer array);
   its post adds DMrcSecMat.mat_win (DMrcSecMat.RDW ly MAP LEN lst) mat: every page materialized at 0x341a4 was
   materialized at the entry or is the page of a read-zone address.  ZGA is RDW's first two zones; [Q, Q + 8 * nA)
   lies in RDW's pointer-array zone [Q, Q + kPtrArrayResv) since nA <= 16384 (sec_cut's sc_ARRF).  The prelude and
   the Section header are DMrcSecF6.v's, verbatim, with v / hs / lim taken from DMrcSecF6 by notation; the lemmas
   are DMrcSecF6's, by their qualified names. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFex YFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb DMrcSecGx DMrcSecGxWalk DMrcSecGv YFg8 YFfc YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIF DMrcSecFc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMrcSecF6 YFf5M YFfbM DMrcSecMat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, YFgu.GFRAME, DMrcSecGx.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Section c.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable inst : Z.
Hypothesis PRE : rcc_pre_x B ARXr inst ly X k cbp W regs mem md.
Hypothesis SC : DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Hypothesis HN : ck_n k < NMAXD.
Hypothesis HE : ck_extent k <= LMAXD.
Local Notation fc_LO := (DMrcSecFc.sc_LO B ly X k W regs mem r o sm i SC).
Local Notation fc_IMG := (DMrcSecFc.sc_IMG B ly X k W regs mem r o sm i SC).
Local Notation fc_Hk := (DMrcSecFc.sc_Hk B ly X k W regs mem r o sm i SC).
Local Notation fc_HSP := (DMrcSecFc.sc_HSP B ly X k W regs mem r o sm i SC).
Local Notation fc_HI := (DMrcSecFc.sc_HI B ly X k W regs mem r o sm i SC).
Local Notation fc_ARRF := (DMrcSecFc.sc_ARRF B ly X k W regs mem r o sm i SC).
Local Notation fc_slot_geom := (DMrcSecFc.sc_slot_geom B ly X k W regs mem r o sm i SC).
Local Notation fc_slot_val := (DMrcSecFc.sc_slot_val B ly X k W regs mem r o sm i SC).
Local Notation fc_ELEN := (DMrcSecFc.sc_ELEN B ly X k W regs mem r o sm i SC).
Local Notation fc_const_vals := (DMrcSecFc.sc_const_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_inst_vals := (DMrcSecFc.sc_inst_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_junkD_vals := (DMrcSecFc.sc_junkD_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_last_facts := (DMrcSecFc.sc_last_facts B ly X k W regs mem r o sm i SC).
Local Notation fc_maph_vals := (DMrcSecFc.sc_maph_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_qi_val := (DMrcSecFc.sc_qi_val B ly X k W regs mem r o sm i SC).
Local Notation fc_shadow_present := (DMrcSecFc.sc_shadow_present B ly X k W regs mem r o sm i SC).
Local Notation fc_thread_present := (DMrcSecFc.sc_thread_present B ly X k W regs mem r o sm i SC).
Local Notation fc_tls_vals := (DMrcSecFc.sc_tls_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_hw_val := (DMrcSecFc.sc_hw_val B ly X k W regs mem r o sm i SC).
Local Notation fc_junk_vals := (DMrcSecFc.sc_junk_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_MAPX := (DMrcSecFc.sc_MAPX B ly X k W regs mem r o sm i SC).
Local Notation fc_SX := (DMrcSecFc.sc_SX B ly X k W regs mem r o sm i SC).
Local Notation fc_SECX := (DMrcSecFc.sc_SECX B ly X k W regs mem r o sm i SC).
Local Notation fc_LST := (DMrcSecFc.sc_LST B ly X k W regs mem r o sm i SC).
Local Notation fc_FH_A := (DMrcSecFc.sc_FH_A B ly X k W regs mem r o sm i SC).
Local Notation fc_GEOM := (DMrcSecFc.GEOMw B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE).
Local Notation fc_hdr_facts := (DMrcSecFc.hdr_factsw B ly X k W regs mem r o sm i SC NMAXD NOK HN).
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation Q := (ly_Q ly).
Local Notation arr := (st_sec_arr X).
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation nA := (YFg8.nA X).
Local Notation hdr := (YFfc.hdr B ly k).
Local Notation HWv := (YFfc.HWv B ly k W mem).
Local Notation j1 := (YFfc.j1 ly W mem).
Local Notation j2 := (YFfc.j2 ly W mem).
Local Notation IMG := (fc_IMG).
Local Notation v := (DMrcSecF6.v regs).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
Local Notation vs3 := (DMrcSecF6.v regs 19%bv).
Local Notation vs4 := (DMrcSecF6.v regs 20%bv).
Local Notation hs := (DMrcSecF6.hs ly X).
Local Notation lim := (DMrcSecF6.lim ly X).
Let LO : layout_ok ly := fc_LO.
(* The read zones of the walk (DMrcSecMat.RDW at this Section's map, length and last map). *)
Local Notation RDWs := (DMrcSecMat.RDW ly MAP LEN (YFg8.lst ly X r)).
Lemma ZGA_RDW : forall a, YFf5M.ZGA ly a -> RDWs a.
Proof. intros a Ha. unfold YFf5M.ZGA in Ha. unfold DMrcSecMat.RDW. tauto. Qed.
Lemma ZGL_RDW : forall a, YFfbM.ZGL lim Q a -> RDWs a.
Proof.
intros a Ha. pose proof (fc_ARRF) as (_ & _ & _ & A4 & _).
unfold YFfbM.ZGL, DMrcSecF6.lim in Ha. unfold DMrcSecMat.RDW. right; right; right; right; left.
clear - Ha A4. unfold kPtrArrayResv. lia.
Qed.
Theorem to_XG_M : forall mat, SRr tfibsegs W (mkCfg (mkst regs (w64 A_RChunk) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => DMrcSecF6.ATX B ly X k cbp W regs mem md r W' c' /\ DMrcSecMat.mat_win (DMrcSecMat.RDW ly MAP LEN (YFg8.lst ly X r)) mat (m_vm_materialized (cfg_model c'))).
Proof.
intros mat. pose proof (fc_FH_A) as FHA.
eapply SRr_bind; [exact (YFf5M.segGA_M W ly regs mem md hdr nA Q mat FHA)|].
intros W1 c1 _ [HL0 MWA].
destruct (DMrcSecF6.L0_STL B ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi W1 c1 HL0) as (-> & regsL & memL & matL & -> & STL & PX).
cbn [cfg_model] in MWA. rewrite m_vm_materialized_wvb in MWA.
pose proof (DMrcSecF6.hs_facts B ly X k W regs mem r o sm i SC Hi) as (L1 & L2 & _).
eapply SRr_mono; [exact (YFfbM.gloop_M W ly md hdr lim LO IMG (DMrcSecF6.HP B ly X k W regs mem r o sm i SC NMAXD LMAXD NOK LOK HN HE)
  (DMrcSecF6.HLIM B ly X k W regs mem r o sm i SC) hs Q 0 regsL memL matL L2 STL)|].
intros W2 c2 _ [HX MWL].
split.
- destruct HX as (-> & regsX & memX & matX & -> & SR & A12 & A13 & MQ).
split; [reflexivity|]. exists regsX, memX, matX. split; [reflexivity|].
assert (EM : memX = memL) by (apply functional_extensionality; exact MQ). rewrite EM.
exists regsL. split; [exact PX|]. split; [exact SR|].
rewrite A13, (DMrcSecF6.scan_is_MAP B ly X k W regs mem r o sm i SC NMAXD LMAXD NOK LOK HN HE Hi). reflexivity.
- exact (YFfbM.mat_win_trans _ _ _ _ (YFfbM.mat_win_mono _ _ _ _ ZGA_RDW MWA) (YFfbM.mat_win_mono _ _ _ _ ZGL_RDW MWL)).
Qed.
End c.
End b.
