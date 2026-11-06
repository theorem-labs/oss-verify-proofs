(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecM.v (commit 3d8ad2aeb77e, H4 stage B (slack-indexed post relation; DMrcDefs / DGif1Geo split; re-hide head); file sha256 8584481cac42) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: srrm-walk bookkeeping over the already proved walk of __asan::QuarantineCallback::Recycle
   (0x33e30)).

   WHAT.  [rchunk_sec_mach_M] is DMrcSec.rchunk_sec_mach (the secondary arm of the RChunk recycle: the walk to the
   munmap ecall, the munmap and the walk to the return) on the materialized-page (M) engine: the walk is
   DMrcSecMunM.WALK_M, the munmap step is rchunk_sec_mach's, and the return config gets DMrcSec.FINx through
   DMrcSecMat.at_RET_M's plain part.  Its post adds, at the return config c' (the config of rc_mach_sec, whose model
   carries the final materialized pages), the form F2: DMrcSecMat.mat_rec relative to the materialized pages of the
   ENTRY model md (F2a) and DMrcSecMat.mat_gone (F2b).  The prelude and the Section header are DMrcSec.v's,
   verbatim, with its lemmas CUT / MAPR and the notation SC.  As in DMrcSec, Section e is the walk over
   DMrcSecReads.rc_sec_step_g with the post relation [ARXp] a parameter indexed by the slack ([rchunk_sec_mach_M_g],
   through DMrcSec.FINx_g, at ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP)), and Section i states
   rchunk_sec_mach_M, its ARXp := fun _ => ARXr instance. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFex AFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFg8 AFfc AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMwalkIF DMrcSecFc DMrcSecGv DMrcSecWalk DMrcSecF6 DMrcSecF7 DMrcSecF9 DMrcSecMun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG MemnormT MemnormLocG MemnormSafereply DMrcReads DMrcSecReads DMrcConst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DIfaceR DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YFfn YA05 YG0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrcSec DMrcSecMat DMrcSecMunM YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, AFgu.GFRAME, DMrcSecGv.GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac numconst_hi := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kLowMemEnd, kPage, t_stats, A_ALLOCATOR, TFIB_INST, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXp : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Hypothesis RCs : DMrcSecReads.rc_sec_cut_t B ARXr.
Hypothesis RMs : DMrcSecReads.rc_sec_mapr_t B ARXr.
Hypothesis RSs : DMrcSecReads.rc_sec_step_g B ARXr ARXp AOX.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre_x B ARXr inst ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HN : ck_n k < NMAXD.
Hypothesis HE : ck_extent k <= LMAXD.
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis Hkin : In k (st_chunks X).
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation idx := (AFg8.idx i).
Local Notation qi := (AFg8.qi ly i).
Local Notation lst := (AFg8.lst ly X r).
Local Notation own := (AFg8.own X i).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
Local Notation X2v := (AFg8.X2v X k r sm i).
Local Notation W2 := (AFg8.W2 ly W r sm).
Lemma CUT : inst = as_inst B /\ ly_tsd ly = as_tsd B /\ Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) /\
DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Proof. exact (RCs inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hkin Hst). Qed.
Lemma MAPR : index_of (st_sec_arr X) r 0%nat = Some i /\
In (MAP, MAP + LEN) (w_A W) /\ In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md)) /\ amwf md /\
(forall PB kk, 0 < kk -> DMrcSecGv.SHAv MAP <= PB -> PB + kk <= DMrcSecGv.SHEv MAP LEN ->
 madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
Proof. exact (RMs inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi). Qed.
Local Notation SC := (proj2 (proj2 (proj2 CUT))).
(* rc_mach_sec_g at the return config, its post relation at the recycled slot's slack, with the materialized-page facts
   of that config's model (form F2). *)
Theorem rchunk_sec_mach_M_g : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
  (fun (r0 : unit * astate) (W' : world tfibsegs) (c' : config) =>
   DMrcSec.rc_mach_sec_g B (ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP)) AOX inst ly X k W regs mem md r0 W' c' /\
   DMrcSecMat.mat_rec ly MAP LEN lst (m_vm_materialized md) (m_vm_materialized (cfg_model c')) /\
   DMrcSecMat.mat_gone MAP LEN (m_vm_materialized (cfg_model c'))).
Proof.
pose proof MAPR as (Hidx & INA & INV & MW & GATE).
pose proof (DMrcSecFc.GEOMw _ _ _ _ _ _ _ _ _ _ _ SC NMAXD LMAXD LOK HE) as (P1 & P2 & P3 & [L1 L1'] & L2 & _).
pose proof (DMrcSecFc.sc_Hk _ _ _ _ _ _ _ _ _ _ _ SC) as Hk.
pose proof (DMrcSecMun.SMALL B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) as SMALL.
pose proof (DMrcSecMunM.WALK_M B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi GATE) as WALK.
rewrite (AFg8.recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hk) Hb Hsm Hidx SMALL). cbn [amreal].
eapply SRr_bind; [exact WALK|]. intros W1 c1 _ (regsD & memD & LNK & HM).
destruct HM as (-> & regs1 & mem1 & mat1 & -> & H17 & H10 & H11 & _ & _ & INNER). cbv zeta in INNER.
apply SRr_use_AI. cbn [cfg_model]. intros HAI. apply SRr_ret.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (c2 := mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 0x65a18) (unfill (w64 MAP) (w64 LEN) mem1) (seg_rom tfibsegs))
  (munmap_model (w64 MAP) (w64 LEN) md1)).
assert (UM : bv_unsigned (w64 MAP) = MAP) by (unfold w64; apply unsigned_lit_small; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (UL : bv_unsigned (w64 LEN) = LEN) by (unfold w64; apply unsigned_lit_small; lia).
assert (MW1 : amwf md1) by (apply (amwf_same md md1); [subst md1; apply m_vmmaps_wvb | subst md1; apply m_vm_lazy_wvb | exact MW]).
assert (INV1 : In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1))) by (subst md1; rewrite m_vmmaps_wvb; exact INV).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
exists unit, (fun _ => c2), (fun _ => 1), (fun _ => false), tt.
split.
{ pose proof (munmap_node tfibsegs regs1 (w64 0x65a14) mem1 (seg_rom tfibsegs) md1 (w64 MAP) LEN (AI_halted _ _ _ _ HAI) H17 H10
    ltac:(rewrite UM; unfold page_size; exact P3) H11 ltac:(lia)
    ltac:(rewrite UM, (AFg8.page_round_up_Z_aligned LEN) by lia; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, two_pow_64, TASK_SIZE, kHighMemBeg, ASAN_CEIL in *; lia)
    ltac:(rewrite (AFg8.page_round_up_Z_aligned LEN) by lia; exact (map_has_In _ _ _ INV1))) as ND.
  cbv zeta in ND. rewrite (AFg8.page_round_up_Z_aligned LEN) in ND by lia. exact ND. }
split. { intros [] _. cbn [cfg_model]. exact (munmap_AI tfibsegs (w_H W) (w_A W) md1 (w64 MAP, w64 LEN) l1 l2 HAI MW1 EVM
    ltac:(cbn [fst]; rewrite UM; unfold page_size; exact P3)
    ltac:(cbn [fst snd]; rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)). }
split. { intros []. cbn [aok]. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros [] _; reflexivity|]. split; [intros [] XX; discriminate XX|].
intros [] _. cbn [amreal].
eapply SRr_bind; [exact INNER|]. intros W3 c3 _ HR. pose proof HR as ((-> & regs' & mem' & mat' & Ec3 & _) & _).
apply SRr_use_AI. intros HAI3. rewrite Ec3 in HAI3 |- *. cbn [cfg_model] in HAI3.
apply (SRr_world_le tfibsegs W W2).
{ apply wrefund_wle. }
{ intros _. cbn [cfg_model]. apply AI_refund_gen; [exact HAI3|]. intros p Hp. rewrite m_vm_lazy_wvb in Hp. unfold AFg8.iv. cbn [fst snd].
  pose proof (munmap_lazy_out (w64 MAP) (w64 LEN) md1 p ltac:(destruct MW1 as [(_ & _ & W3l & _) _]; intros q Hq; exact (W3l q Hq))
    ltac:(rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) Hp) as NL. rewrite UM, UL in NL. exact NL. }
apply SRr_ret. rewrite <- Ec3. destruct HR as (HRp & MR & MG). cbv beta.
split; [exact (DMrcSec.FINx_g B TB ARXr ARXp AOX RCs RSs NMAXD LMAXD LOK inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HE Hst Hni Hkin
  regsD memD mat1 c3 LNK HRp)|].
split; [exact MR | exact MG].
Qed.
End e.

(* The walk at ARXp := fun _ => ARXr. *)
Section i.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Hypothesis RCs : DMrcSecReads.rc_sec_cut_t B ARXr.
Hypothesis RMs : DMrcSecReads.rc_sec_mapr_t B ARXr.
Hypothesis RSs : DMrcSecReads.rc_sec_step_t B ARXr AOX.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre_x B ARXr inst ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HN : ck_n k < NMAXD.
Hypothesis HE : ck_extent k <= LMAXD.
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis Hkin : In k (st_chunks X).
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation lst := (AFg8.lst ly X r).
(* rc_mach_sec at the return config, with the materialized-page facts of that config's model (form F2). *)
Theorem rchunk_sec_mach_M : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
  (fun (r0 : unit * astate) (W' : world tfibsegs) (c' : config) =>
   DMrcSec.rc_mach_sec B ARXr AOX inst ly X k W regs mem md r0 W' c' /\
   DMrcSecMat.mat_rec ly MAP LEN lst (m_vm_materialized md) (m_vm_materialized (cfg_model c')) /\
   DMrcSecMat.mat_gone MAP LEN (m_vm_materialized (cfg_model c'))).
Proof.
exact (rchunk_sec_mach_M_g B TB ARXr (fun _ => ARXr) AOX RCs RMs RSs NMAXD LMAXD NOK LOK inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HN HE
  Hst Hni Hkin).
Qed.
End i.
End d.
