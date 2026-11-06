(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecMun.v (commit 6fdbdd538bcf, H4 flag-free secondary Recycle walk set; file sha256 5131aab3ec3e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcSecMun.v at commit edc7f827e38, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; interface DMwalkIF.v at dc3949af11c): the SECONDARY arm of
   __asan::QuarantineCallback::Recycle (0x33e88), i.e. LargeMmapAllocator::Deallocate, over the opaque cut relation ARXr.
   rule 24: proves function __asan::QuarantineCallback::Recycle (secondary arm), at cgif_file_fuzzer's asan-ubsan image;
   reuse search LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record) (2026-10-29T23:07:48Z exit 0), rule-24 check B1LookupCheck CONFIRM.
   This file: the machine walk from 0x33e88 to the munmap ecall (YFg9.WALK's composition over the twins), generic in the cut
   relation: it reads only rcc_pre_x, the cut-read record DMrcSecFc.sec_cut, the size premises of DMwalkIF and the madvise
   gate of the map's shadow (a model read).  It takes no recycle invariant, so a direct non-quarantine caller can use it. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb YFg8 YFfc YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIF DMrcSecFc DMrcSecGv DMrcSecWalk DMrcSecF6 DMrcSecF7 DMrcSecF9.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, YFgu.GFRAME, DMrcSecGv.GDEPTH in *.
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
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation nA := (YFg8.nA X).
Local Notation idx := (YFg8.idx i).
Local Notation qi := (YFg8.qi ly i).
Local Notation lst := (YFg8.lst ly X r).
Local Notation own := (YFg8.own X i).
Local Notation ql := (DMrcSecF9.ql ly X).
Local Notation ji1 := (YFfc.ji1 W mem).
Local Notation ji2 := (YFfc.ji2 W mem).
Local Notation ji3 := (YFfc.ji3 W mem).
Local Notation ji4 := (YFfc.ji4 W mem).
Local Notation j5 := (YFfc.j5 ly W mem).
Local Notation j6 := (YFfc.j6 ly W mem).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
(* The madvise gate over the map's shadow: a READ of the model (cgif: YFg9.WALK's GATE, from the ledger by madvise_gate_L). *)
Hypothesis GATE : forall PB kk, 0 < kk -> DMrcSecGv.SHAv MAP <= PB -> PB + kk <= DMrcSecGv.SHEv MAP LEN ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true.
Definition WPRE (a : Z) : Prop :=
(sp0 - DMrcSecGv.GDEPTH <= a < sp0) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition LINKD (regsD : bvmap 5 word) (memD : word -> option byte) : Prop :=
getr regsD 2 = getr regs 2 /\ (forall r' : bv 5, In r' DMrcSecGv.SREGS -> getr regsD r' = getr regs r') /\
(forall x : word, ~ WPRE (bv_unsigned x) -> memD x = mem x) /\
(forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent (w_H W) memD a).
Definition POSTMUN (W' : world tfibsegs) (c' : config) : Prop :=
exists regsD memD, LINKD regsD memD /\ DMrcSecGv.at_MUN W ly regsD memD md MAP LEN idx nA qi lst vra vs0 vs1 vs2 own W' c'.
(* At cgif's image the shadow is cleared in place: kClearShadowMmapThreshold = 2 ^ 64 - 1, and LEN < 2 ^ 31. *)
Lemma SMALL : needs_remap (sm_len sm) = false.
Proof.
pose proof (DMrcSecFc.GEOMw B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) as (_ & _ & _ & [L1 L2] & _).
unfold YFg8.LEN in L1, L2. unfold needs_remap, kClearShadowMmapThreshold. apply Z.leb_gt.
apply (Z.le_lt_trans _ (sm_len sm)); [apply Z.div_le_upper_bound; lia | lia].
Qed.
Theorem WALK : SRr tfibsegs W (cfg_at tfibsegs A_RChunk regs mem md) POSTMUN.
Proof.
unfold cfg_at. rewrite <- (DMrcSecF6.wvb_self md) at 1.
eapply SRr_bind; [exact (DMrcSecF7.to_LMD B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi (m_vm_materialized md))|].
intros W1 c1 _ HD. destruct HD as (-> & regsD & memD & matD & -> & PD).
pose proof (DMrcSecF9.DSEED B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD LOK HE true SMALL regsD memD PD) as FHD.
eapply SRr_mono; [exact (DMrcSecWalk.segGD W ly regsD memD md MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own true matD FHD GATE eq_refl)|].
intros W2 c2 _ HM. unfold POSTMUN. exists regsD, memD. split; [|exact HM].
destruct PD as (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
unfold LINKD. split; [exact D2|]. split; [exact DSR|]. split; [|exact DTJ].
intros x Hx. apply MQD. intros HW. apply Hx. unfold WPRE. unfold DMrcSecF7.WIND, DMrcSecF6.WINA in HW. fold sp0 in HW |- *.
unfold DMrcSecGv.GDEPTH. clear - HW. lia.
Qed.
End e.
End d.
