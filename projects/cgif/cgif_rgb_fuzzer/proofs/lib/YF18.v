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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1g YF0x YF0y YF19 YF2p YF0z YF2r YF15 YF2s YF17 YF2q YF23 YF16 YF10 YF07.
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
Local Notation E0x := (YF2s.E0 ly).
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Uv : forall r', 0 <= v r' < 2 ^ 64. Proof. intros r'. unfold YF10.v. img_apply u64_range. Qed.
Lemma chunk_litx : forall regsX mm a (w : BinNums.N) x, val_mem tfxsegs mm a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) mm 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros regsX mm a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_litx_at : forall regsX mm base a (w : BinNums.N) x, val_mem tfxsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) mm base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros regsX mm base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
Lemma chunk_atomx : forall regsX mm base a (w : BinNums.N) k0 d x, ew (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) mm base (YQ0b.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros regsX mm base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac r4 := img_change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); img_lia.
Theorem XSEED : forall regsX memX, YF10.STX B ly X k cbp W regs mem r regsX memX ->
YF2s.free_hyps W ly regsX memX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4.
Proof.
intros regsX memX (regsL & PX & SR & R13).
destruct PX as (SRL & L2 & L1r & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & MQA & PRS & V1 & V8 & V9 & V18 & V19 & V20 & V56 & V10 & V72 & V80 & VM).
pose proof PRE as PRE'. destruct PRE' as (_ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hcb1 & Hcb2 & _ & HPRES & _ & _ & _ & Htp & _ & _).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof (YF16.HI B TB ly X k cbp W regs mem md PRE) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & hTAL & hCAL & _).
pose proof hT1 as ZT3. pose proof hC1 as ZC3.
pose proof (YF16.hdr_facts B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (D1 & D2 & D3 & D4 & _).
pose proof (YF16.GEOM B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (M1 & M2 & M3 & M4 & M5 & _).
pose proof (YF16.hw_val B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (W1 & W2 & WP & WR).
pose proof (YF16.maph_vals B ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as (H1v & H2v & _ & _ & HPm).
pose proof (YF16.tls_vals B TB ly X k cbp W regs mem md PRE HTSD) as (T1 & T2 & T3 & T4 & T5 & T6).
pose proof (YF16.inst_vals B TB ly X k cbp W regs mem md PRE) as (I1 & I2 & _ & _).
pose proof (YF16.junk_vals B ly X k cbp W regs mem md PRE) as ([J1R J1] & [J2R J2]).
pose proof (YF10.CBP B TB ly X k cbp W regs mem md PRE) as (C10 & C1 & C2 & C3 & CR).
pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 0%nat _ eq_refl) as DP.
pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 2%nat _ eq_refl) as DT.
pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 6%nat _ eq_refl) as DC.
cbn [fst snd] in DP, DT, DC. pose proof (YF16.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _).
unfold YF0y.MAP, YF0y.LEN in DP, DT, DC. rewrite <- E in DP, DT, DC. fold (YF23.MAP ly r) in DP, DT, DC. clear E.
pose proof (YF16.thread_present B TB ly X k cbp W regs mem md PRE) as TPRES.
clear LO.
assert (XFER : forall a (w : nat) x, val_mem tfxsegs m0 a w x -> (forall kk, (kk < w)%nat -> ~ WINA (a + Z.of_nat kk) /\ 0 <= a + Z.of_nat kk < 2 ^ 64) ->
val_mem tfxsegs (mrestrict H0 memX) a w x).
{ intros a w x Hv Hout. img_apply (val_mem_frame (w_H W) mem memX); [|img_try (img_exact Hv)]. intros kk Hkk. img_apply MQA. destruct (Hout kk Hkk) as [O1 O2]. rewrite unsigned_lit_small by img_exact O2. img_exact O1. }
assert (PXFER : forall a, apresent H0 mem a -> ~ WINA a -> 0 <= a < 2 ^ 64 -> apresent H0 memX a).
{ intros a Hp Ho Ha. img_apply (apresent_same (w_H W) mem); [img_try (img_apply MQA; rewrite unsigned_lit_small by img_exact Ha; img_exact Ho) | img_try (img_exact Hp)]. }
assert (X2 : getr regsX 2 = w64 (sp0 - 80)) by (img_try (rewrite (SR 2%bv ltac:(inS)); img_exact L2)).
assert (USX : bv_unsigned (getr regsX 2) = sp0 - 80) by (img_try (rewrite X2; unfold w64; img_apply unsigned_lit_small; clear - Hlo hS1 Hcb1 Hcb2 hS2; numconst; img_lia)).
assert (HREGS : getr regsX 10 = w64 (A_ALLOCATOR + 64) /\ getr regsX 11 = w64 hdr /\ getr regsX 13 = w64 MAP /\ getr regsX 8 = w64 (A_ALLOCATOR + 680) /\
getr regsX 9 = w64 hdr /\ getr regsX 18 = w64 vs2 /\ getr regsX 19 = w64 A_ALLOCATOR /\ getr regsX 20 = w64 (2 ^ 37)).
{ splits.
- rewrite (SR 10%bv ltac:(img_try (inS))). img_exact L10.
- rewrite (SR 11%bv ltac:(img_try (inS))). img_exact L11.
- img_exact R13.
- rewrite (SR 8%bv ltac:(img_try (inS))). img_exact L8.
- rewrite (SR 9%bv ltac:(img_try (inS))). img_exact L9.
- rewrite (SR 18%bv ltac:(img_try (inS))), (SRL 18%bv ltac:(img_try (inS))). unfold YF10.v, w64. symmetry. img_apply Z_to_bv_bv_unsigned.
- rewrite (SR 19%bv ltac:(img_try (inS))). img_exact L19.
- rewrite (SR 20%bv ltac:(img_try (inS))). img_exact L20. }
assert (XTP : getr regsX 4 = w64 TFX_TP) by (img_try (rewrite (SR 4%bv ltac:(inS)), (SRL 4%bv ltac:(inS)), Htp, (ts_tp _ TB); img_refl)).
clear SR SRL L2 L1r L8 L9 L10 L11 L12 L13 L14 L19 L20 R13 Htp.
assert (OUT_img : forall a, 0 <= a < TFX_IMG_END -> ~ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) -> ~ WINA a /\ 0 <= a < 2 ^ 64).
{ intros a Ha Hm. unfold YF10.WINA. fold sp0. clear - Ha Hm Hlo hS1. numconst. img_lia. }
assert (OUT_z : forall x sz a, zone3 x sz -> x <= a < x + sz -> ~ WINA a /\ 0 <= a < 2 ^ 64).
{ intros x sz a Z3 Ha. unfold YF10.WINA. fold sp0. clear - Z3 Ha Hlo hS1 hCE. numconst. img_lia. }
pose proof M1 as ZM3.
pose proof (Uv 1%bv) as U1. pose proof (Uv 8%bv) as U8. pose proof (Uv 9%bv) as U9. pose proof (Uv 18%bv) as U18. pose proof (Uv 19%bv) as U19. pose proof (Uv 20%bv) as U20.
constructor.
- img_exact (am_layout B ly X rd0 M).
- img_exact (YF16.IMG B ly X k cbp W regs mem md PRE).
- img_exact XTP.
- img_exact HREGS.
- rewrite USX. replace (sp0 - 80 + YF2s.GFRAME) with sp0 by (img_try (numconst; img_lia)). split; [img_try (img_exact Hlo) | img_try (clear - Hcb1 Hcb2; img_lia)].
- rewrite USX. clear - Hal. apply Z.mod_divide in Hal as [q Hq]; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q - 5). img_lia.
- rewrite USX. replace (sp0 - 80 + YF2s.GFRAME) with sp0 by (img_try (numconst; img_lia)). intros a Ha.
destruct (Z_lt_le_dec a (sp0 - 80)) as [LOW|HI'].
+ img_apply PXFER; [img_try (img_apply HPRES; img_lia) | img_try (unfold YF10.WINA; fold sp0; clear - Ha LOW Hlo hS1; numconst; img_lia) | img_try (clear - Ha LOW Hlo hS1 hS2 Hcb1 Hcb2; numconst; img_lia)].
+ img_apply PRS. img_lia.
- rewrite USX. splits.
+ img_exact V80.
+ replace (sp0 - 80 + 8) with (sp0 - 72) by img_lia. img_exact V72.
+ replace (sp0 - 80 + 16) with (sp0 - 64) by img_lia. img_exact V10.
+ replace (sp0 - 80 + 24) with (sp0 - 56) by img_lia. img_exact V56.
+ replace (sp0 - 80 + 32) with (sp0 - 48) by img_lia. img_exact V20.
+ replace (sp0 - 80 + 40) with (sp0 - 40) by img_lia. img_exact V19.
+ replace (sp0 - 80 + 48) with (sp0 - 32) by img_lia. img_exact V18.
+ replace (sp0 - 80 + 56) with (sp0 - 24) by img_lia. img_exact V9.
+ replace (sp0 - 80 + 64) with (sp0 - 16) by img_lia. img_exact V8.
+ replace (sp0 - 80 + 72) with (sp0 - 8) by img_lia. img_exact V1.
- clear - U1 U8 U9 U18 U19 U20 C1 C2 C3 CR. unfold YF10.v in *. splits; img_lia.
- split; [img_try (img_exact M1)|]. clear - M1 M2 M3 M4 M5 D1 D2 D3 D4 DP hSP1 hSP2 hP1 hP2. unfold zdisjoint in DP. cbn [fst snd] in DP. numconst. splits; try assumption; img_lia.
- splits.
+ img_apply XFER; [img_try (img_exact H1v) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk M4; img_lia)].
+ img_apply XFER; [img_try (img_exact H2v) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk M4; img_lia)].
+ intros a Ha. img_apply PXFER; [img_try (img_apply HPm; img_lia) | |]; destruct (OUT_z _ _ a ZM3 ltac:(img_try (clear - Ha M4; img_lia))) as [O1 O2]; assumption.
- split; [img_try (img_exact WR) | img_try (img_exact D2)].
- splits.
+ img_apply XFER; [img_try (img_exact W1) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; img_lia)].
+ img_apply XFER; [img_try (img_exact W2) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; img_lia)].
+ intros a Ha. img_apply PXFER; [img_try (img_apply WP; img_lia) | |]; destruct (OUT_z _ _ a ZM3 ltac:(img_try (clear - Ha D1 D2 D3 M4; img_lia))) as [O1 O2]; assumption.
-   intros kk Hkk. destruct kk; [|img_lia]. img_exact (VM 0%nat ltac:(img_lia)).
- img_apply XFER; [img_try (img_exact I1) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)].
- splits.
+ img_apply XFER; [img_try (img_exact T4) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)].
+ img_apply XFER; [img_try (img_exact T5) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZC3); clear - Hkk; img_lia)].
+ img_apply XFER; [img_try (img_exact T6) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZC3); clear - Hkk; img_lia)].
- split; [|img_try (split; [|split; [img_exact J1R | split; [img_exact J2R |]]])].
+ img_apply XFER; [img_try (img_exact J1) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; img_lia)].
+ img_apply XFER; [img_try (img_exact J2) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; img_lia)].
+ intros a Ha. img_apply PXFER; [img_try (img_apply TPRES; clear - Ha; numconst; img_lia) | |]; destruct (OUT_z _ _ a ZT3 ltac:(img_try (clear - Ha; unfold t_stats, kThreadObjSize in *; img_lia))) as [O1 O2]; assumption.
-
assert (VX : val_mem tfxsegs (mrestrict H0 memX) MAP 8 MAP /\ val_mem tfxsegs (mrestrict H0 memX) (MAP + 8) 8 LEN /\
val_mem tfxsegs (mrestrict H0 memX) hdr 4 HWv /\ val_mem tfxsegs (mrestrict H0 memX) (hdr + 4) 4 (ck_n k) /\
val_mem tfxsegs (mrestrict H0 memX) (ly_C ly + 8) 4 0 /\ val_mem tfxsegs (mrestrict H0 memX) (ly_C ly + 152) 8 T /\
val_mem tfxsegs (mrestrict H0 memX) (T + t_stats + 40) 8 j1 /\ val_mem tfxsegs (mrestrict H0 memX) (T + t_stats + 48) 8 j2 /\
val_mem tfxsegs (mrestrict H0 memX) (A_ALLOCATOR + 64) 8 4096 /\ val_mem tfxsegs (mrestrict H0 memX) (A_ALLOCATOR + 32) 8 SB /\
val_mem tfxsegs (mrestrict H0 memX) (0xa9a20 + D_10c0) 1 1 /\ val_mem tfxsegs (mrestrict H0 memX) (0xa9a24 + D_10c0) 4 0 /\
val_mem tfxsegs (mrestrict H0 memX) (TFX_TP - 88) 8 TFX_TSD /\ val_mem tfxsegs (mrestrict H0 memX) TFX_TSD 8 (ly_C ly)).
{ splits.
- img_apply XFER; [img_try (img_exact H1v) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk M4; img_lia)].
- img_apply XFER; [img_try (img_exact H2v) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk M4; img_lia)].
- img_apply XFER; [img_try (img_exact W1) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; img_lia)].
- img_apply XFER; [img_try (img_exact W2) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; img_lia)].
- img_apply XFER; [img_try (img_exact T5) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZC3); clear - Hkk; img_lia)].
- img_apply XFER; [img_try (img_exact T6) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZC3); clear - Hkk; img_lia)].
- img_apply XFER; [img_try (img_exact J1) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; img_lia)].
- img_apply XFER; [img_try (img_exact J2) | img_try (intros kk Hkk; img_apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; img_lia)].
- img_apply XFER; [img_try (img_exact I2) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)].
- img_apply XFER; [img_try (img_exact I1) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)].
- img_apply XFER; [img_try (img_exact T1) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)].
- img_apply XFER; [img_try (img_exact T2) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)].
- img_apply XFER; [img_try (img_exact T3) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)].
- img_apply XFER; [img_try (img_exact T4) | img_try (intros kk Hkk; img_apply OUT_img; clear - Hkk; numconst; img_lia)]. }
destruct VX as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14).
assert (TJP : forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent H0 memX a).
{ intros a Ha. img_apply PXFER; [img_try (img_apply TPRES; clear - Ha; numconst; img_lia) | |]; destruct (OUT_z _ _ a ZT3 ltac:(img_try (clear - Ha; unfold t_stats, kThreadObjSize in *; img_lia))) as [O1 O2]; assumption. }
pose proof hI1 as J1'. pose proof hI2 as J2'. rewrite hIE in J1', J2'.
clear XFER PXFER HPRES MQA H1v H2v W1 W2 WP HPm T1 T2 T3 T4 T5 T6 I1 I2 J1 J2 TPRES OUT_img OUT_z hI1 hI2 hIE hQ1 hQ2 hQAL C10.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, KSTACK, kLowMemEnd, TFX_INST in hP1, hP2, hT1, hT2, hC1, hC2, hS1, hS2, hCE, hSP1, hSP2, Hlo, J1', J2', M1, M2, M4, D1, D3, C1, C2.
rewrite restrict_mkst_fx. unfold YF2s.SS0, YF2s.SR0, sr_set. cbn [bv_eqb]. unfold YF2s.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ destruct HREGS as (R10 & R11 & R13' & R8 & R9 & R18 & R19 & R20).
img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin;
[img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact XTP]
| intros XX; discriminate | cbn [sv_denot]; img_exact R10]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite YF2s.EqM, R11; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite YF2s.EqMAP, R13'; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]
| intros XX; discriminate | cbn [sv_denot]; img_exact R8]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite YF2s.EqM, R9; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite YF2s.EqS2, R18; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]
| intros XX; discriminate | cbn [sv_denot]; img_exact R19])
| img_try (intros XX; discriminate) | img_try (cbn [sv_denot]; img_exact R20)].
+ img_case; vm_compute. all: img_refl.
+
cbn [ms_mem mkst]. fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
unfold YF2s.REG0, YF2s.R_STK, YF2s.R_MAPH, YF2s.R_HDR, YF2s.R_MUT1, YF2s.R_CTX, YF2s.R_JST, flit1, flit4, flit8, fatom8.
img_apply Forall_cons.
{   reg_intro. rewrite (YF2s.E2 ly regsX), X2. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o' Ho'. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; img_lia) | img_try (img_apply PRS; img_lia)]. }
repeat (img_apply Forall_cons); [..|img_try (img_apply Forall_nil)].
- img_apply (chunk_atomx _ _ _ _ 8 46%nat 0 vs2); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact V80) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 35%nat 0 hdr); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 8) with (sp0 - 72) by img_lia; img_exact V72) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 42%nat 0 cbp); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 16) with (sp0 - 64) by img_lia; img_exact V10) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply chunk_litx_at; [img_try (replace (sp0 - 80 + 24) with (sp0 - 56) by img_lia; img_exact V56) | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 48%nat 0 vs4); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 32) with (sp0 - 48) by img_lia; img_exact V20) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 47%nat 0 vs3); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 40) with (sp0 - 40) by img_lia; img_exact V19) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 46%nat 0 vs2); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 48) with (sp0 - 32) by img_lia; img_exact V18) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 45%nat 0 vs1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 56) with (sp0 - 24) by img_lia; img_exact V9) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 44%nat 0 vs0); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 64) with (sp0 - 16) by img_lia; img_exact V8) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 43%nat 0 vra); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (sp0 - 80 + 72) with (sp0 - 8) by img_lia; img_exact V1) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2s.EqMAP. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atomx _ _ _ _ 8 36%nat 0 MAP); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact Y1) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 37%nat 0 LEN); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact Y2) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2s.EqM. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atomx _ _ _ _ 4 38%nat 0 HWv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact Y3) | img_try (r4) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 4 39%nat 0 (ck_n k)); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact Y4) | img_try (r4) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split.
{ intros o' Ho'. img_apply rw_writable. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_litx; [| img_try (cbn; img_lia) | img_try (cbn; img_lia)]. intros kk Hkk. destruct kk; [|img_lia]. img_exact (VM 0%nat ltac:(img_lia)). }
img_apply Forall_cons.
{   reg_intro. rewrite YF2s.EqC. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_litx_at; [img_try (img_exact Y5) | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 32%nat 0 T); [img_try (rewrite YF2s.EqT; unfold w64; f_equal; img_lia) | img_lia | img_try (img_exact Y6) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2s.EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_stats in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o' Ho'. img_apply apresent_writable_off; [img_try (img_apply (zone3_off_img _ _ _ ZT3); unfold kThreadObjSize; img_lia)|]. img_apply TJP. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atomx _ _ _ _ 8 40%nat 0 j1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact Y7 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomx _ _ _ _ 8 41%nat 0 j2); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact Y8 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_litx; [img_try (img_exact Y9) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomx _ _ _ _ 8 34%nat 0 SB); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y10) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_litx; [img_try (img_exact Y11) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_litx; [img_try (img_exact Y12) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold TFX_TP. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_litx; [img_try (img_exact Y13) | img_try (unfold TFX_TSD; cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{   reg_intro. unfold TFX_TSD. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomx _ _ _ _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite YF2s.EqC; unfold w64; f_equal; img_lia) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y14) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
+
fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4). img_apply pairwise_disjoint_of_extents.
unfold YF2s.REG0, YF2s.R_STK, YF2s.R_MAPH, YF2s.R_HDR, YF2s.R_MUT1, YF2s.R_CTX, YF2s.R_JST, flit1, flit4, flit8, fatom8, extent_of_region.
cbn [map fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite (YF2s.E2 ly regsX), X2, YF2s.EqMAP, YF2s.EqM, YF2s.EqC, YF2s.EqT. unfold w64.
pose proof (YF16.HI B TB ly X k cbp W regs mem md PRE) as HIF.
destruct HIF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hTC & _ & _).
clear - Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2 hC1 hC2 hTC M1 M2 M4 D1 D3 DT DC J1' J2'. unfold zdisjoint in DT, DC. cbn [fst snd] in DT, DC. numconst. rewrite !unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; img_lia.
+
fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4). split; [|img_try (split; img_exact I)].
assert (AF : forall k0 Xv lo hi al, ew (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (E2' : ew (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) 2 = w64 (sp0 - 80)) by (img_try (rewrite (YF2s.E2 ly regsX); img_exact X2)).
cbn [YF2s.FFX f_atoms atoms_ok]. numconst.
split. { img_apply (AF 2%nat (sp0 - 80)); [img_try (img_exact E2')| | | |]. all: clear - CR0 Hlo Hcb1 Hcb2 hS1 hS2 hCE Hal; first [img_lia | apply Z.mod_divide in Hal as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists (q - 5); img_change (2 ^ 4) with 16; img_lia]. }
split. { img_apply (AF 32%nat T); [img_refl| | | |]. all: clear - CR0 hT1 hT2 hTAL; first [img_lia | img_change (2 ^ 12) with 4096; img_exact hTAL]. }
split. { img_apply (AF 33%nat (ly_C ly)); [img_refl| | | |]. all: clear - CR0 hC1 hC2 hCAL; first [img_lia | img_change (2 ^ 3) with 8; img_exact hCAL]. }
split. { img_apply (AF 34%nat SB); [img_refl| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 hSAL; first [img_lia | apply Z.mod_divide in hSAL as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists q; img_change (2 ^ 16) with 65536; img_lia]. }
split. { img_apply (AF 35%nat hdr); [img_refl| | | |]. all: clear - CR0 D1 D3 D2 D4 M1 M2 M4; first [img_lia | img_change (2 ^ 4) with 16; img_exact D4]. }
split. { img_apply (AF 36%nat MAP); [img_refl| | | |]. all: clear - CR0 M1 M2 M3 M4; first [img_lia | img_change (2 ^ 12) with 4096; img_exact M3]. }
split. { img_apply (AF 37%nat LEN); [img_refl| | | |]. all: clear - M4 M5; first [img_lia | img_change (2 ^ 12) with 4096; img_exact M5]. }
split. { img_apply (AF 38%nat HWv); [img_refl| | | |]. all: clear - WR; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 39%nat (ck_n k)); [img_refl| | | |]. all: clear - D2; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat j1); [img_refl| | | |]. all: clear - J1R; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 41%nat j2); [img_refl| | | |]. all: clear - J2R; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 42%nat cbp); [img_refl| | | |]. all: clear - CR0 C1 C2 C3 CR; first [img_lia | img_change (2 ^ 3) with 8; img_exact C3]. }
split. { img_apply (AF 43%nat vra); [img_refl| | | |]. all: clear - U1; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 44%nat vs0); [img_refl| | | |]. all: clear - U8; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 45%nat vs1); [img_refl| | | |]. all: clear - U9; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 46%nat vs2); [img_refl| | | |]. all: clear - U18; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 47%nat vs3); [img_refl| | | |]. all: clear - U19; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 48%nat vs4); [img_refl| | | |]. all: clear - U20; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
Qed.
End c.
End b.
