(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecMun.v (commit 5ad50e61fc6a, file sha256 5131aab3ec3e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; #102 pin 1be0f53d96cb); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (head H4 of the interface DMwalkIF.v at dc3949af11c): the SECONDARY arm of
   __asan::QuarantineCallback::Recycle (0x34810), i.e. LargeMmapAllocator::Deallocate, over the opaque cut relation ARXr.
   rule 24: proves function __asan::QuarantineCallback::Recycle (secondary arm), at omx-clap-core/fuzz_preset's asan
   image A' (relocated from the donor's proof at cgif_file_fuzzer's asan-ubsan image); reuse search at fuzz_preset
   (2026-10-31, by name and by word over the released corpus, both with and without the meaning ranking, and an exact
   theorem-name grep over origin/ossv/recipes; a by-address search cannot see this unit, whose released builds carry no
   symbol table): no released file is named for the function.  PRIOR ART: tfib_rchunk_sec (in the released file lib/A/AFg9.v, deleted in this series; at 87c4b944683b of
   origin/ossv/recipes) proves the secondary arm over the concrete amreal / rcc_pre form; this file restates the machine
   walk of that arm over the opaque cut relation ARXr of DMwalkIF head H4, and takes the map definitions of the released
   lib/A/AFg8.v, which this tree carries at the released blob.
   This file: the machine walk from 0x34810 to the munmap ecall (YFg9.WALK's composition over the twins), generic in the cut
   relation: it reads only rcc_pre_x, the cut-read record DMrcSecFcA.sec_cut, the size premises of DMwalkIF and the madvise
   gate of the map's shadow (a model read).  It takes no recycle invariant, so a direct non-quarantine caller can use it. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFg8 AFfc AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrcSecFcA DMrcSecGvA DMrcSecWalkA DMrcSecF6A DMrcSecF7A DMrcSecF9A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, AFgu.GFRAME, DMrcSecGvA.GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section e.
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
Local Notation ql := (DMrcSecF9A.ql ly X).
Local Notation ji1 := (AFfc.ji1 W mem).
Local Notation ji2 := (AFfc.ji2 W mem).
Local Notation ji3 := (AFfc.ji3 W mem).
Local Notation ji4 := (AFfc.ji4 W mem).
Local Notation j5 := (AFfc.j5 ly W mem).
Local Notation j6 := (AFfc.j6 ly W mem).
Local Notation vra := (DMrcSecF6A.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6A.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6A.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6A.v regs 18%bv).
(* The madvise gate over the map's shadow: a READ of the model (cgif: YFg9.WALK's GATE, from the ledger by madvise_gate_L). *)
Hypothesis GATE : forall PB kk, 0 < kk -> DMrcSecGvA.SHAv MAP <= PB -> PB + kk <= DMrcSecGvA.SHEv MAP LEN ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true.
Definition WPRE (a : Z) : Prop :=
(sp0 - DMrcSecGvA.GDEPTH <= a < sp0) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition LINKD (regsD : bvmap 5 word) (memD : word -> option byte) : Prop :=
getr regsD 2 = getr regs 2 /\ (forall r' : bv 5, In r' DMrcSecGvA.SREGS -> getr regsD r' = getr regs r') /\
(forall x : word, ~ WPRE (bv_unsigned x) -> memD x = mem x) /\
(forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent (w_H W) memD a).
Definition POSTMUN (W' : world tfibsegs) (c' : config) : Prop :=
exists regsD memD, LINKD regsD memD /\ DMrcSecGvA.at_MUN W ly regsD memD md MAP LEN idx nA qi lst vra vs0 vs1 vs2 own W' c'.
(* At this image, as at the donor's, the shadow is cleared in place: kClearShadowMmapThreshold = 2 ^ 64 - 1 (YG00.v:32),
   and LEN < 2 ^ 31. *)
Lemma SMALL : needs_remap (sm_len sm) = false.
Proof.
pose proof (DMrcSecFcA.GEOMw B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) as (_ & _ & _ & [L1 L2] & _).
unfold AFg8.LEN in L1, L2. unfold needs_remap, kClearShadowMmapThreshold. apply Z.leb_gt.
apply (Z.le_lt_trans _ (sm_len sm)); [apply Z.div_le_upper_bound; lia | lia].
Qed.
Theorem WALK : SRr tfibsegs W (cfg_at tfibsegs A_RChunk regs mem md) POSTMUN.
Proof.
unfold cfg_at. rewrite <- (DMrcSecF6A.wvb_self md) at 1.
eapply SRr_bind; [exact (DMrcSecF7A.to_LMD B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi (m_vm_materialized md))|].
intros W1 c1 _ HD. destruct HD as (-> & regsD & memD & matD & -> & PD).
pose proof (DMrcSecF9A.DSEED B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD LOK HE true SMALL regsD memD PD) as FHD.
eapply SRr_mono; [exact (DMrcSecWalkA.segGD W ly regsD memD md MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own true matD FHD GATE eq_refl)|].
intros W2 c2 _ HM. unfold POSTMUN. exists regsD, memD. split; [|exact HM].
destruct PD as (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
unfold LINKD. split; [exact D2|]. split; [exact DSR|]. split; [|exact DTJ].
intros x Hx. apply MQD. intros HW. apply Hx. unfold WPRE. unfold DMrcSecF7A.WIND, DMrcSecF6A.WINA in HW. fold sp0 in HW |- *.
unfold DMrcSecGvA.GDEPTH. clear - HW. lia.
Qed.
End e.
End d.
