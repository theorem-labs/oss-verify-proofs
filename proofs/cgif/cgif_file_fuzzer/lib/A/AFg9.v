(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFgx AFfd AFgv AFg8 AFfc AFf6 AFfe AFf7 AFf8 AFf9 AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG08 YG0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, AFgu.GFRAME, AFgx.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hidx : index_of (st_sec_arr X) r 0%nat = Some i.
Hypothesis SMALL : needs_remap (sm_len sm) = false.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
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
Local Notation ql := (AFf9.ql ly X).
Local Notation ji1 := (AFfc.ji1 W mem).
Local Notation ji2 := (AFfc.ji2 W mem).
Local Notation ji3 := (AFfc.ji3 W mem).
Local Notation ji4 := (AFfc.ji4 W mem).
Local Notation j5 := (AFfc.j5 ly W mem).
Local Notation j6 := (AFfc.j6 ly W mem).
Local Notation vra := (AFf6.v regs 1%bv).
Local Notation vs0 := (AFf6.v regs 8%bv).
Local Notation vs1 := (AFf6.v regs 9%bv).
Local Notation vs2 := (AFf6.v regs 18%bv).
Theorem WALK : SRr tfibsegs W (cfg_at tfibsegs A_RChunk regs mem md) (AFg8.POSTMUN ly X W regs mem md r sm i).
Proof.
unfold cfg_at. rewrite <- (AFf6.wvb_self md) at 1.
eapply SRr_bind; [exact (AFf7.to_LMD B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HTSD (m_vm_materialized md))|].
intros W1 c1 _ HD. destruct HD as (-> & regsD & memD & matD & -> & PD).
pose proof (AFf9.DSEED B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi true SMALL HTSD regsD memD PD) as FHD.
assert (GATE : forall PB kk, 0 < kk -> SHAv MAP <= PB -> PB + kk <= SHEv MAP LEN ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
{ intros PB kk Hkk H1 H2.
pose proof (AFgv.fh_Hmap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FHD) as (Z3 & ZC & _ & ZL & _).
pose proof (AFgv.fh_LY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FHD) as LO.
pose proof PRE as ((_ & LG & _) & _).
apply (madvise_gate_L tfibsegs ly X md PB kk LO LG Hkk).
unfold SHAv, SHEv, CNTv, SHAv in H1, H2. clear - Z3 ZC ZL H1 H2 Hkk. ceil.
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *.
Z.div_mod_to_equations. lia. }
eapply SRr_mono; [exact (AFf8.segGD W ly regsD memD md MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own true matD FHD GATE eq_refl)|].
intros W2 c2 _ HM. unfold AFg8.POSTMUN. exists regsD, memD. split; [|exact HM].
destruct PD as (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
unfold AFg8.LINKD. split; [exact D2|]. split; [exact DSR|]. split; [|exact DTJ].
intros x Hx. apply MQD. intros HW. apply Hx. unfold AFg8.WPRE. unfold AFf7.WIND, AFf6.WINA in HW. fold sp0 in HW |- *.
unfold GDEPTH. clear - HW. lia.
Qed.
Theorem tfib_rchunk_sec_small_arm : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof. exact (AFg8.plumbing B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hidx SMALL HTSD WALK). Qed.
End b.
Theorem tfib_rchunk_sec_small : forall B, TfibSyms B -> forall ly X k cbp W regs mem md r o,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o -> needs_remap (sec_map_size (ck_req k)) = false ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
intros B TB ly X k cbp W regs mem md r o PRE Hb SMALL. pose proof PRE as ((M & _) & _ & Hk & _).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly X _ M); apply (ts_tsd _ TB)).
pose proof (am_wf B ly X _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK]. rewrite Hb in CK. destruct CK as (_ & _ & sm & Hsm & Hlive & Hsz & Hlen).
destruct (wf_secondary _ _ _ _ _ WF) as [_ Sac _ _ _].
assert (Hr : In r (st_sec_arr X)).
{ apply (proj2 (Sac r)). exists k. split; [exact Hk|]. rewrite Hb.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK']. rewrite Hb in CK'. destruct CK' as (_ & -> & _). reflexivity. }
destruct (index_of_spec (st_sec_arr X) r 0%nat Hr) as (i & Hidx & Hi). rewrite Nat.add_0_l in Hidx.
assert (SM : needs_remap (sm_len sm) = false) by (rewrite Hlen; exact SMALL).
exact (tfib_rchunk_sec_small_arm B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hidx SM HTSD).
Qed.
Theorem tfib_rchunk_sec : forall B, TfibSyms B -> forall ly X k cbp W regs mem md r o,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
intros B TB ly X k cbp W regs mem md r o PRE Hb.
apply (tfib_rchunk_sec_small B TB ly X k cbp W regs mem md r o PRE Hb). apply needs_remap_false.
pose proof PRE as ((M & _) & _ & Hk & _). pose proof (am_wf B ly X _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [CKr _].
pose proof (YG08.sec_map_size_bound (ck_req k) (proj1 CKr)) as SB. unfold req_size, MALLOC_MAX in *.
destruct (ck_req k =? 0); lia.
Qed.
End a.
