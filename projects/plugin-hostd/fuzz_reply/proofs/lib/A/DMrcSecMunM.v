(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecMunM.v (commit 237eb205ab7b, H4 srrm M walk (image-specific files); file sha256 352b4c408917) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: srrm-walk bookkeeping over the already proved walk of __asan::QuarantineCallback::Recycle
   (0x33e30)).

   WHAT.  [WALK_M] is DMrcSecMun.WALK (the machine walk from 0x33e30 to the munmap ecall, and its continuation to the
   return) on the materialized-page (M) engine: the prefix DMrcSecF7M.to_LMD_M (mat := the entry's materialized
   pages, as WALK takes them through DMrcSecF6.wvb_self), the seed DMrcSecF9.DSEED and the walk
   DMrcSecWalkM.segGD_M (q := ly_Q ly).  Its post [POSTMUN_M] is DMrcSecMun.POSTMUN with DMrcSecMat.at_MUN_M in
   place of DMrcSecGv.at_MUN, and at_MUN_M's start list is the materialized-page list of the ENTRY model md: the
   prefix's DMrcSecMat.mat_win (RDW ...) is folded into each mat_rec of at_MUN_M by [mat_rec_of_win]
   ([at_MUN_M_win]).  So the munmap ecall and the return carry DMrcSecMat.mat_rec relative to (m_vm_materialized md).
   The prelude and the Section header are DMrcSecMun.v's, verbatim (WPRE / LINKD are DMrcSecMun's, by name). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMwalkIF DMrcSecFc DMrcSecGv DMrcSecWalk DMrcSecF6 DMrcSecF7 DMrcSecF9.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrcSecMun DMrcSecMat DMrcSecF7M DMrcSecWalkM.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
(* A page list within the read zones of the start list moves each mat_rec relative to it back to the start list. *)
Lemma mat_rec_of_win : forall (ly : alayout) (map len lst : Z) (m0 m1 m2 : list word),
DMrcSecMat.mat_win (DMrcSecMat.RDW ly map len lst) m0 m1 -> DMrcSecMat.mat_rec ly map len lst m1 m2 ->
DMrcSecMat.mat_rec ly map len lst m0 m2.
Proof.
intros ly map len lst m0 m1 m2 H1 H2 p Hp. destruct (H2 p Hp) as [Hin|[Hr|Hw]].
- destruct (H1 p Hin) as [H0|(a & Ha & ->)]; [left; exact H0 | right; left; exists a; split; [exact Ha | reflexivity]].
- right; left; exact Hr.
- right; right; exact Hw.
Qed.
(* The same for the post at the munmap ecall, and through it for the post at the return. *)
Lemma at_MUN_M_win : forall (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
(map len idx n qi lst vra vs0 vs1 vs2 : Z) (own : bool) (m0 m1 : list word) (W' : world tfibsegs) (c' : config),
DMrcSecMat.mat_win (DMrcSecMat.RDW ly map len lst) m0 m1 ->
DMrcSecMat.at_MUN_M W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own m1 W' c' ->
DMrcSecMat.at_MUN_M W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own m0 W' c'.
Proof.
intros W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own m0 m1 W' c' MW HM.
destruct HM as (EW & regs1 & mem1 & mat1 & Ec & H17 & H10 & H11 & MR & MM & INNER).
split; [exact EW|]. exists regs1, mem1, mat1.
split; [exact Ec|]. split; [exact H17|]. split; [exact H10|]. split; [exact H11|].
split; [exact (mat_rec_of_win _ _ _ _ _ _ _ MW MR)|]. split; [exact MM|].
cbv zeta in INNER |- *. eapply SRr_mono; [exact INNER|].
intros W3 c3 _ (HR & MR3 & MG3). split; [exact HR|]. split; [exact (mat_rec_of_win _ _ _ _ _ _ _ MW MR3) | exact MG3].
Qed.
Section e.
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
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
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
Local Notation ql := (DMrcSecF9.ql ly X).
Local Notation ji1 := (AFfc.ji1 W mem).
Local Notation ji2 := (AFfc.ji2 W mem).
Local Notation ji3 := (AFfc.ji3 W mem).
Local Notation ji4 := (AFfc.ji4 W mem).
Local Notation j5 := (AFfc.j5 ly W mem).
Local Notation j6 := (AFfc.j6 ly W mem).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
(* The madvise gate over the map's shadow: a READ of the model (cgif: YFg9.WALK's GATE, from the ledger by madvise_gate_L). *)
Hypothesis GATE : forall PB kk, 0 < kk -> DMrcSecGv.SHAv MAP <= PB -> PB + kk <= DMrcSecGv.SHEv MAP LEN ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true.
(* DMrcSecMun.POSTMUN with the M post; at_MUN_M's start list is the entry's materialized pages. *)
Definition POSTMUN_M (W' : world tfibsegs) (c' : config) : Prop :=
exists regsD memD, DMrcSecMun.LINKD ly W regs mem regsD memD /\
DMrcSecMat.at_MUN_M W ly regsD memD md MAP LEN idx nA qi lst vra vs0 vs1 vs2 own (m_vm_materialized md) W' c'.
Theorem WALK_M : SRr tfibsegs W (cfg_at tfibsegs A_RChunk regs mem md) POSTMUN_M.
Proof.
unfold cfg_at. rewrite <- (DMrcSecF6.wvb_self md) at 1.
eapply SRr_bind; [exact (DMrcSecF7M.to_LMD_M B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi (m_vm_materialized md))|].
intros W1 c1 _ [HD MW]. destruct HD as (-> & regsD & memD & matD & -> & PD).
cbn [cfg_model] in MW. rewrite m_vm_materialized_wvb in MW.
pose proof (DMrcSecF9.DSEED B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD LOK HE true
  (DMrcSecMun.SMALL B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) regsD memD PD) as FHD.
eapply SRr_mono; [exact (DMrcSecWalkM.segGD_M W ly regsD memD md MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own true matD
  FHD GATE eq_refl eq_refl)|].
intros W2 c2 _ HM. unfold POSTMUN_M. exists regsD, memD. split; [|exact (at_MUN_M_win _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MW HM)].
destruct PD as (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
unfold DMrcSecMun.LINKD. split; [exact D2|]. split; [exact DSR|]. split; [|exact DTJ].
intros x Hx. apply MQD. intros HW. apply Hx. unfold DMrcSecMun.WPRE. unfold DMrcSecF7.WIND, DMrcSecF6.WINA in HW. cbv zeta in HW |- *. fold sp0 in HW |- *.
unfold DMrcSecGv.GDEPTH. clear - HW. lia.
Qed.
End e.
End d.
