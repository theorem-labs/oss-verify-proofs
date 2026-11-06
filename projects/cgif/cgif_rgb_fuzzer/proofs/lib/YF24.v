(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0r YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1g YF0x YF0y YF19 YF2p YF0z YF2r YF15 YF2s YF17 YF2q YF23 YF16 YF10 YF18 YF11 YF12 YF13 YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG08 YG0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFX_IMG_END, kBatchBytes, SHADOW_OFF, TFX_TP, TFX_TSD, TFX_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, YF2p.GFRAME, YF2s.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; img_refl | right]).
Section b. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hidx : index_of (st_sec_arr X) r 0%nat = Some i.
Hypothesis SMALL : needs_remap (sm_len sm) = false.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (YF23.MAP ly r).
Local Notation LEN := (YF23.LEN sm).
Local Notation nA := (YF23.nA X).
Local Notation idx := (YF23.idx i).
Local Notation qi := (YF23.qi ly i).
Local Notation lst := (YF23.lst ly X r).
Local Notation own := (YF23.own X i).
Local Notation ql := (YF13.ql ly X).
Local Notation ji1 := (YF16.ji1 W mem).
Local Notation ji2 := (YF16.ji2 W mem).
Local Notation ji3 := (YF16.ji3 W mem).
Local Notation ji4 := (YF16.ji4 W mem).
Local Notation j5 := (YF16.j5 ly W mem).
Local Notation j6 := (YF16.j6 ly W mem).
Local Notation vra := (YF10.v regs 1%bv).
Local Notation vs0 := (YF10.v regs 8%bv).
Local Notation vs1 := (YF10.v regs 9%bv).
Local Notation vs2 := (YF10.v regs 18%bv).
Theorem WALK : SRr tfxsegs W (cfg_at tfxsegs A_RChunk regs mem md) (YF23.POSTMUN ly X W regs mem md r sm i).
Proof.
unfold cfg_at. rewrite <- (YF10.wvb_self md) at 1.
eapply SRr_bind; [img_try (img_exact (YF11.to_LMD B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HTSD (m_vm_materialized md)))|].
intros W1 c1 _ HD. destruct HD as (-> & regsD & memD & matD & -> & PD).
pose proof (YF13.DSEED B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi true SMALL HTSD regsD memD PD) as FHD.
assert (GATE : forall PB kk, 0 < kk -> SHAv MAP <= PB -> PB + kk <= SHEv MAP LEN ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
{ intros PB kk Hkk H1 H2.
pose proof (YF2q.fh_Hmap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FHD) as (Z3 & ZC & _ & ZL & _).
pose proof (YF2q.fh_LY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FHD) as LO.
pose proof PRE as ((_ & LG & _) & _).
img_apply (madvise_gate_L tfxsegs ly X md PB kk LO LG Hkk).
unfold SHAv, SHEv, CNTv, SHAv in H1, H2. clear - Z3 ZC ZL H1 H2 Hkk. ceil.
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *.
Z.div_mod_to_equations. img_lia. }
eapply SRr_mono; [img_try (img_exact (YF12.segGD W ly regsD memD md MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own true matD FHD GATE eq_refl))|].
intros W2 c2 _ HM. unfold YF23.POSTMUN. exists regsD, memD. split; [|img_try (img_exact HM)].
destruct PD as (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
unfold YF23.LINKD. split; [img_try (img_exact D2)|]. split; [img_try (img_exact DSR)|]. split; [|img_try (img_exact DTJ)].
intros x Hx. img_apply MQD. intros HW. img_apply Hx. unfold YF23.WPRE. unfold YF11.WIND, YF10.WINA in HW. fold sp0 in HW |- *.
unfold GDEPTH. clear - HW. img_lia.
Qed.
Theorem tfx_rchunk_sec_small_arm : amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof. img_exact (YF23.plumbing B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hidx SMALL HTSD WALK). Qed.
End b.
Theorem tfx_rchunk_sec_small {imgk : img} : forall B, TfxSyms B -> forall ly X k cbp W regs mem md r o,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o -> needs_remap (sec_map_size (ck_req k)) = false ->
amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
intros B TB ly X k cbp W regs mem md r o PRE Hb SMALL. pose proof PRE as ((M & _) & _ & Hk & _).
assert (HTSD : ly_tsd ly = TFX_TSD) by (img_try (rewrite (am_tsd B ly X _ M); img_apply (ts_tsd _ TB))).
pose proof (am_wf B ly X _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK]. rewrite Hb in CK. destruct CK as (_ & _ & sm & Hsm & Hlive & Hsz & Hlen).
destruct (wf_secondary _ _ _ _ _ WF) as [_ Sac _ _ _].
assert (Hr : In r (st_sec_arr X)).
{ img_apply (proj2 (Sac r)). exists k. split; [img_try (img_exact Hk)|]. rewrite Hb.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK']. rewrite Hb in CK'. destruct CK' as (_ & -> & _). img_refl. }
destruct (index_of_spec (st_sec_arr X) r 0%nat Hr) as (i & Hidx & Hi). rewrite Nat.add_0_l in Hidx.
assert (SM : needs_remap (sm_len sm) = false) by (img_try (rewrite Hlen; img_exact SMALL)).
img_exact (tfx_rchunk_sec_small_arm B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hidx SM HTSD).
Qed.
Theorem tfx_rchunk_sec {imgk : img} : forall B, TfxSyms B -> forall ly X k cbp W regs mem md r o,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o ->
amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
intros B TB ly X k cbp W regs mem md r o PRE Hb.
img_apply (tfx_rchunk_sec_small B TB ly X k cbp W regs mem md r o PRE Hb). img_apply needs_remap_false.
pose proof PRE as ((M & _) & _ & Hk & _). pose proof (am_wf B ly X _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [CKr _].
pose proof (YG08.sec_map_size_bound (ck_req k) (proj1 CKr)) as SB. unfold req_size, MALLOC_MAX in *.
destruct (ck_req k =? 0); img_lia.
Qed.
End a.
