(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecF6M.v (commit 5ad50e61fc6a, file sha256 7b0e151fa43c) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; #102 pin 1be0f53d96cb); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: srrm-walk bookkeeping; the walk of __asan::QuarantineCallback::Recycle (0x34810) is already
   proved by H4; this file composes its prefix pieces on the materialized-page (M) engine).

   WHAT.  [to_XG_M] is DMrcSecF6A.to_XG composed from the M pieces AFf5M.segGA_M (zone AFf5M.ZGA: the stack and the
   image window) and AFfbM.gloop_M (zone AFfbM.ZGL lim Q: the scanned cells [Q, Q + 8 * nA) of the pointer array);
   its post adds DMrcSecMatA.mat_win (DMrcSecMatA.RDW ly MAP LEN lst) mat: every page materialized at 0x34b2c was
   materialized at the entry or is the page of a read-zone address.  ZGA is RDW's first two zones; [Q, Q + 8 * nA)
   lies in RDW's pointer-array zone [Q, Q + kPtrArrayResv) since nA <= 16384 (sec_cut's sc_ARRF).  The prelude and
   the Section header are DMrcSecF6A.v's, verbatim, with v / hs / lim taken from DMrcSecF6 by notation; the lemmas
   are DMrcSecF6's, by their qualified names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFex AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb DMrcSecGxA DMrcSecGxWalkA DMrcSecGvA AFg8 AFfc AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrcSecFcA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcSecF6A AFf5M AFfbM DMrcSecMatA.
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
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, AFgu.GFRAME, DMrcSecGxA.GFRAME, GDEPTH in *.
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
Hypothesis SC : DMrcSecFcA.sec_cut B ly X k W regs mem r o sm i.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIFA.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIFA.lmaxd_ok NMAXD LMAXD.
Hypothesis HN : ck_n k < NMAXD.
Hypothesis HE : ck_extent k <= LMAXD.
Local Notation fc_LO := (DMrcSecFcA.sc_LO B ly X k W regs mem r o sm i SC).
Local Notation fc_IMG := (DMrcSecFcA.sc_IMG B ly X k W regs mem r o sm i SC).
Local Notation fc_Hk := (DMrcSecFcA.sc_Hk B ly X k W regs mem r o sm i SC).
Local Notation fc_HSP := (DMrcSecFcA.sc_HSP B ly X k W regs mem r o sm i SC).
Local Notation fc_HI := (DMrcSecFcA.sc_HI B ly X k W regs mem r o sm i SC).
Local Notation fc_ARRF := (DMrcSecFcA.sc_ARRF B ly X k W regs mem r o sm i SC).
Local Notation fc_slot_geom := (DMrcSecFcA.sc_slot_geom B ly X k W regs mem r o sm i SC).
Local Notation fc_slot_val := (DMrcSecFcA.sc_slot_val B ly X k W regs mem r o sm i SC).
Local Notation fc_ELEN := (DMrcSecFcA.sc_ELEN B ly X k W regs mem r o sm i SC).
Local Notation fc_const_vals := (DMrcSecFcA.sc_const_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_inst_vals := (DMrcSecFcA.sc_inst_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_junkD_vals := (DMrcSecFcA.sc_junkD_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_last_facts := (DMrcSecFcA.sc_last_facts B ly X k W regs mem r o sm i SC).
Local Notation fc_maph_vals := (DMrcSecFcA.sc_maph_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_qi_val := (DMrcSecFcA.sc_qi_val B ly X k W regs mem r o sm i SC).
Local Notation fc_shadow_present := (DMrcSecFcA.sc_shadow_present B ly X k W regs mem r o sm i SC).
Local Notation fc_thread_present := (DMrcSecFcA.sc_thread_present B ly X k W regs mem r o sm i SC).
Local Notation fc_tls_vals := (DMrcSecFcA.sc_tls_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_hw_val := (DMrcSecFcA.sc_hw_val B ly X k W regs mem r o sm i SC).
Local Notation fc_junk_vals := (DMrcSecFcA.sc_junk_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_MAPX := (DMrcSecFcA.sc_MAPX B ly X k W regs mem r o sm i SC).
Local Notation fc_SX := (DMrcSecFcA.sc_SX B ly X k W regs mem r o sm i SC).
Local Notation fc_SECX := (DMrcSecFcA.sc_SECX B ly X k W regs mem r o sm i SC).
Local Notation fc_LST := (DMrcSecFcA.sc_LST B ly X k W regs mem r o sm i SC).
Local Notation fc_FH_A := (DMrcSecFcA.sc_FH_A B ly X k W regs mem r o sm i SC).
Local Notation fc_GEOM := (DMrcSecFcA.GEOMw B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE).
Local Notation fc_hdr_facts := (DMrcSecFcA.hdr_factsw B ly X k W regs mem r o sm i SC NMAXD NOK HN).
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
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation hdr := (AFfc.hdr B ly k).
Local Notation HWv := (AFfc.HWv B ly k W mem).
Local Notation j1 := (AFfc.j1 ly W mem).
Local Notation j2 := (AFfc.j2 ly W mem).
Local Notation IMG := (fc_IMG).
Local Notation v := (DMrcSecF6A.v regs).
Local Notation vra := (DMrcSecF6A.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6A.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6A.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6A.v regs 18%bv).
Local Notation vs3 := (DMrcSecF6A.v regs 19%bv).
Local Notation vs4 := (DMrcSecF6A.v regs 20%bv).
Local Notation hs := (DMrcSecF6A.hs ly X).
Local Notation lim := (DMrcSecF6A.lim ly X).
Let LO : layout_ok ly := fc_LO.
(* The read zones of the walk (DMrcSecMatA.RDW at this Section's map, length and last map). *)
Local Notation RDWs := (DMrcSecMatA.RDW ly MAP LEN (AFg8.lst ly X r)).
Lemma ZGA_RDW : forall a, AFf5M.ZGA ly a -> RDWs a.
Proof. intros a Ha. unfold AFf5M.ZGA in Ha. unfold DMrcSecMatA.RDW. tauto. Qed.
Lemma ZGL_RDW : forall a, AFfbM.ZGL lim Q a -> RDWs a.
Proof.
intros a Ha. pose proof (fc_ARRF) as (_ & _ & _ & A4 & _).
unfold AFfbM.ZGL, DMrcSecF6A.lim in Ha. unfold DMrcSecMatA.RDW. right; right; right; right; left.
clear - Ha A4. unfold kPtrArrayResv. lia.
Qed.
Theorem to_XG_M : forall mat, SRr tfibsegs W (mkCfg (mkst regs (w64 A_RChunk) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => DMrcSecF6A.ATX B ly X k cbp W regs mem md r W' c' /\ DMrcSecMatA.mat_win (DMrcSecMatA.RDW ly MAP LEN (AFg8.lst ly X r)) mat (m_vm_materialized (cfg_model c'))).
Proof.
intros mat. pose proof (fc_FH_A) as FHA.
eapply SRr_bind; [exact (AFf5M.segGA_M W ly regs mem md hdr nA Q mat FHA)|].
intros W1 c1 _ [HL0 MWA].
destruct (DMrcSecF6A.L0_STL B ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi W1 c1 HL0) as (-> & regsL & memL & matL & -> & STL & PX).
cbn [cfg_model] in MWA. rewrite m_vm_materialized_wvb in MWA.
pose proof (DMrcSecF6A.hs_facts B ly X k W regs mem r o sm i SC Hi) as (L1 & L2 & _).
eapply SRr_mono; [exact (AFfbM.gloop_M W ly md hdr lim LO IMG (DMrcSecF6A.HP B ly X k W regs mem r o sm i SC NMAXD LMAXD NOK LOK HN HE)
  (DMrcSecF6A.HLIM B ly X k W regs mem r o sm i SC) hs Q 0 regsL memL matL L2 STL)|].
intros W2 c2 _ [HX MWL].
split.
- destruct HX as (-> & regsX & memX & matX & -> & SR & A12 & A13 & MQ).
split; [reflexivity|]. exists regsX, memX, matX. split; [reflexivity|].
assert (EM : memX = memL) by (apply functional_extensionality; exact MQ). rewrite EM.
exists regsL. split; [exact PX|]. split; [exact SR|].
rewrite A13, (DMrcSecF6A.scan_is_MAP B ly X k W regs mem r o sm i SC NMAXD LMAXD NOK LOK HN HE Hi). reflexivity.
- exact (AFfbM.mat_win_trans _ _ _ _ (AFfbM.mat_win_mono _ _ _ _ ZGA_RDW MWA) (AFfbM.mat_win_mono _ _ _ _ ZGL_RDW MWL)).
Qed.
End c.
End b.
