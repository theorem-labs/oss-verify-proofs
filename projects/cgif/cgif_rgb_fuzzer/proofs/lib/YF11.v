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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1g YF0x YF0y YF19 YF2p YF0z YF2r YF15 YF2s YF17 YF2q YF23 YF16 YF10 YF18 YF07.
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
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFX_IMG_END, kBatchBytes, SHADOW_OFF, TFX_TP, TFX_TSD, TFX_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, YF2p.GFRAME, YF2s.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; img_refl | right]).
Section c. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (YF23.MAP ly r).
Local Notation LEN := (YF23.LEN sm).
Local Notation nA := (YF23.nA X).
Local Notation hdr := (YF16.hdr B ly k).
Local Notation HWv := (YF16.HWv B ly k W mem).
Local Notation j1 := (YF16.j1 ly W mem).
Local Notation j2 := (YF16.j2 ly W mem).
Local Notation v := (YF10.v regs).
Local Notation vra := (YF10.v regs 1%bv).
Local Notation vs0 := (YF10.v regs 8%bv).
Local Notation vs1 := (YF10.v regs 9%bv).
Local Notation vs2 := (YF10.v regs 18%bv).
Local Notation vs3 := (YF10.v regs 19%bv).
Local Notation vs4 := (YF10.v regs 20%bv).
Local Notation WINA := (YF10.WINA regs).
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Definition WIND (a : Z) : Prop := WINA a \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition MEQD (mm : word -> option byte) : Prop := forall x : word, ~ WIND (bv_unsigned x) -> mm x = mem x.
Definition PRED (regsD : bvmap 5 word) (memD : word -> option byte) : Prop :=
(forall r' : bv 5, In r' YF2q.SREGS -> getr regsD r' = getr regs r') /\
getr regsD 2 = getr regs 2 /\ getr regsD 1 = w64 vra /\ getr regsD 8 = w64 vs0 /\ getr regsD 9 = w64 vs1 /\ getr regsD 18 = w64 vs2 /\
getr regsD 10 = w64 (A_ALLOCATOR + 64) /\ getr regsD 11 = w64 (A_ALLOCATOR + 688) /\ getr regsD 12 = w64 (MAP + 4096) /\
MEQD memD /\
(forall a, sp0 - 80 <= a < sp0 -> apresent H0 memD a) /\
(forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent H0 memD a) /\
val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 680) 4 0.
Definition ATD (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regsD memD matD, c' = mkCfg (mkst regsD (w64 (0x34140 + D_150)) memD (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) matD md) /\ PRED regsD memD.
Theorem to_LMD : forall mat, SRr tfxsegs W (mkCfg (mkst regs (w64 A_RChunk) mem (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md)) ATD.
Proof.
intros mat.
pose proof (YF16.HI B TB ly X k cbp W regs mem md PRE) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _).
pose proof (YF16.HSP B ly X k cbp W regs mem md PRE) as [S1 S2].
eapply SRr_bind; [img_try (img_exact (YF10.to_XG B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi mat))|].
intros W1 c1 _ HX. destruct HX as (-> & regsX & memX & matX & -> & SX).
pose proof (YF18.XSEED B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HTSD regsX memX SX) as FHX.
destruct SX as (regsL & PX & SR & R13).
destruct PX as (SRL & L2 & L1r & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & MQA & PRS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VM).
assert (X2 : getr regsX 2 = w64 (sp0 - 80)) by (img_try (rewrite (SR 2%bv ltac:(inS)); img_exact L2)).
assert (USX : bv_unsigned (getr regsX 2) = sp0 - 80) by (img_try (rewrite X2; unfold w64; img_apply unsigned_lit_small; pose proof (u64_range (getr regs 2)); clear - S1 S2 hS1 hS2 H; numconst; (subst sp0; cbv beta); img_lia)).
eapply SRr_mono; [img_try (img_exact (YF17.segGX W ly regsX memX md hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 matX FHX))|].
intros W2 c2 _ HD. destruct HD as (-> & regsD & memD & matD & -> & DSR & D2 & D1 & D8 & D9 & D18 & D19 & D20 & D10 & D11 & D12 & MQX & DPRS & DMUT & DJ1 & DJ2).
rewrite USX in D2, DPRS. unfold YF2s.MEQ, YF2s.WIN in MQX. rewrite USX in MQX.
split; [img_refl|]. exists regsD, memD, matD. split; [img_refl|].
unfold PRED. splits.
- intros r' Hr'. unfold YF2q.SREGS in Hr'. cbn [In] in Hr'.
assert (CASE : r' = 19%bv \/ r' = 20%bv \/ In r' YF2s.SREGS).
{ unfold YF2s.SREGS. cbn [In]. clear - Hr'. intuition ((subst; cbv beta); auto 20). }
destruct CASE as [-> | [-> | C]].
+ rewrite D19. unfold YF10.v, w64. img_apply Z_to_bv_bv_unsigned.
+ rewrite D20. unfold YF10.v, w64. img_apply Z_to_bv_bv_unsigned.
+ rewrite (DSR r' C). assert (C2 : In r' YF2r.SREGS /\ In r' YF2p.SREGS).
{ unfold YF2s.SREGS in C. unfold YF2r.SREGS, YF2p.SREGS. cbn [In] in C |- *. clear - C. intuition ((subst; cbv beta); auto 40). }
destruct C2 as [C2 C3]. rewrite (SR r' C2). img_exact (SRL r' C3).
- rewrite D2. replace (sp0 - 80 + YF2s.GFRAME) with sp0 by (img_try (numconst; img_lia)). unfold sp0, w64. img_apply Z_to_bv_bv_unsigned.
- img_exact D1.
- img_exact D8.
- img_exact D9.
- img_exact D18.
- img_exact D10.
- img_exact D11.
- img_exact D12.
- intros x Hx. unfold WIND, YF10.WINA in Hx. fold sp0 in Hx. rewrite MQX by (img_try (clear - Hx; numconst; img_lia)). img_apply MQA. unfold YF10.WINA. fold sp0. clear - Hx. img_lia.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - 48)) as [LOW|HI'].
+ img_apply DPRS. img_lia.
+ img_apply (apresent_same (w_H W) memX); [|img_try (img_apply PRS; img_lia)]. img_apply MQX. rewrite unsigned_lit_small by (img_try (clear - Ha S1 S2 hS1 hS2; numconst; img_lia)).
clear - Ha HI' S1 S2 hS1 hCE hT1 hT2. numconst. img_lia.
- intros a Ha. assert (Ha' : off_img a) by (img_try (img_apply (zone3_off_img _ _ _ hT1); clear - Ha; unfold t_stats, kThreadObjSize in *; img_lia)).
destruct (Z_lt_le_dec a (T + t_stats + 48)) as [LOW|HI'].
+ pose proof (DJ1 (Z.to_nat (a - (T + t_stats + 40))) ltac:(img_lia)) as Hb'. rewrite Z2Nat.id in Hb' by img_lia. replace (T + t_stats + 40 + (a - (T + t_stats + 40))) with a in Hb' by img_lia.
img_exact (mbyte_off_apresent (w_H W) memD a _ Ha' Hb').
+ pose proof (DJ2 (Z.to_nat (a - (T + t_stats + 48))) ltac:(img_lia)) as Hb'. rewrite Z2Nat.id in Hb' by img_lia. replace (T + t_stats + 48 + (a - (T + t_stats + 48))) with a in Hb' by img_lia.
img_exact (mbyte_off_apresent (w_H W) memD a _ Ha' Hb').
-
intros kk Hkk. destruct kk as [|kk'].
+ pose proof (DMUT 0%nat ltac:(img_lia)) as E0. cbn [Z.of_nat] in E0 |- *. rewrite le_byte_zero in *. img_exact E0.
+ rewrite (mbyte_mrestrict_same (w_H W) memX memD).
* pose proof (VM (S kk') Hkk) as E1. rewrite E1. f_equal. f_equal. rewrite le_byte_zero.
unfold YP0g.le_byte. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. rewrite Z.mod_small by img_lia.
rewrite Z.div_small; [img_refl|]. split; [img_lia|]. eapply Z.lt_le_trans with (2 ^ 8); [img_lia|]. img_apply Z.pow_le_mono_r; img_lia.
* img_apply MQX. unfold A_ALLOCATOR. rewrite unsigned_lit_small by img_lia. clear - Hkk S1 hS1 hT1. numconst. img_lia.
Qed.
End c.
End b.
