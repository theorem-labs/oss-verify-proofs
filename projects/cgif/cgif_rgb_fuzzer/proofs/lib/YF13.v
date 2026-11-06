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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1g YF0x YF0y YF19 YF2p YF0z YF2r YF15 YF2s YF17 YF2q YF23 YF16 YF10 YF18 YF11 YF07.
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
Variable small : bool.
Hypothesis HSM : needs_remap (sm_len sm) = negb small.
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
Local Notation idx := (YF23.idx i).
Local Notation qi := (YF23.qi ly i).
Local Notation lst := (YF23.lst ly X r).
Local Notation own := (YF23.own X i).
Definition ql : Z := Q + 8 * (nA - 1).
Local Notation ji1 := (YF16.ji1 W mem).
Local Notation ji2 := (YF16.ji2 W mem).
Local Notation ji3 := (YF16.ji3 W mem).
Local Notation ji4 := (YF16.ji4 W mem).
Local Notation j5 := (YF16.j5 ly W mem).
Local Notation j6 := (YF16.j6 ly W mem).
Local Notation v := (YF10.v regs).
Local Notation vra := (YF10.v regs 1%bv).
Local Notation vs0 := (YF10.v regs 8%bv).
Local Notation vs1 := (YF10.v regs 9%bv).
Local Notation vs2 := (YF10.v regs 18%bv).
Local Notation WIND := (YF11.WIND ly regs).
Local Notation E0d := (YF2q.E0 ly).
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Lemma Uv : forall r', 0 <= v r' < 2 ^ 64. Proof. intros r'. unfold YF10.v. img_apply u64_range. Qed.
Lemma SM19 : if small then True else 2 ^ 19 <= LEN.
Proof.
pose proof HSM as SM. unfold needs_remap, kClearShadowMmapThreshold in SM. unfold YF23.LEN. clear - SM.
destruct small; cbn [negb] in SM; [img_try (img_exact I) | img_try (apply Z.leb_le in SM; Z.div_mod_to_equations; img_lia)].
Qed.
Lemma chunk_litd : forall E mm a (w : BinNums.N) x, val_mem tfxsegs mm a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E mm 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros E mm a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_litd_at : forall E mm base a (w : BinNums.N) x, val_mem tfxsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E mm base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros E mm base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
Lemma chunk_atomd : forall E mm base a (w : BinNums.N) k0 d x, ew E k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E mm base (YQ0b.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros E mm base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac lit_region V := reg_intro; unfold A_ALLOCATOR, TFX_TP, TFX_TSD; split; [img_try (clear; img_lia)|]; split; [img_try (clear; img_lia)|]; split; [img_try (intros ? ?; img_lia)|]; img_apply Forall_cons; [img_try (img_apply chunk_litd; [img_exact V | clear; cbn; img_lia | clear; cbn; img_lia]) | img_try (img_apply Forall_nil)].
Theorem DSEED : forall regsD memD, YF11.PRED ly W regs mem r regsD memD ->
YF2q.free_hyps W ly regsD memD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own small.
Proof.
intros regsD memD (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
pose proof PRE as PRE'. destruct PRE' as (_ & _ & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & _ & HPRES & _ & _ & _ & Htp & _ & _).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof (YF16.HI B TB ly X k cbp W regs mem md PRE) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & hTAL & hCAL & _).
pose proof (YF16.GEOM B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (M1 & M2 & M3 & M4 & M5 & _).
pose proof (YF16.ARRF B ly X k cbp W regs mem md r i PRE Hi) as (_ & _ & _ & A4 & A5).
pose proof (YF16.maph_vals B ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as (H1v & H2v & _ & H4v & HPm).
pose proof (YF16.tls_vals B TB ly X k cbp W regs mem md PRE HTSD) as (T1 & T2 & T3 & T4 & T5 & T6).
pose proof (YF16.inst_vals B TB ly X k cbp W regs mem md PRE) as (I1 & I2 & I3 & I4).
pose proof (YF16.junkD_vals B TB ly X k cbp W regs mem md PRE) as ([JR1 JV1] & [JR2 JV2] & [JR3 JV3] & [JR4 JV4] & [JR5 JV5] & [JR6 JV6]).
pose proof (YF16.last_facts B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as (_ & QLV & QLP & L24 & L24P & LL1 & LL2 & LL3 & LOWN).
pose proof (YF16.qi_val B TB ly X k cbp W regs mem md r i PRE Hi) as [QIV QIP].
pose proof M1 as ZM3. pose proof hT1 as ZT3. pose proof hQ1 as ZQ3. pose proof LL1 as ZL3.
pose proof (YF16.const_vals B TB ly X k cbp W regs mem md PRE) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (YF16.shadow_present B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as SHP.
pose proof (YF16.thread_present B TB ly X k cbp W regs mem md PRE) as TPRES.
pose proof SM19 as L19.
assert (MT : forall a, MAP <= a < MAP + LEN -> a < T \/ T + kThreadObjSize <= a).
{ pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 2%nat _ eq_refl) as DT.
unfold zdisjoint in DT. cbn [fst snd] in DT. unfold YF0y.MAP, YF0y.LEN in DT.
pose proof (YF16.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _). rewrite <- E in DT. unfold YF23.MAP. clear - DT. intros a Ha. img_lia. }
assert (MC : forall a, MAP <= a < MAP + LEN -> a < ly_C ly \/ ly_C ly + 256 <= a).
{ pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 6%nat _ eq_refl) as DC.
unfold zdisjoint in DC. cbn [fst snd] in DC. unfold YF0y.MAP, YF0y.LEN in DC.
pose proof (YF16.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _). rewrite <- E in DC. unfold YF23.MAP. clear - DC. intros a Ha. img_lia. }
assert (MQ : forall a, MAP <= a < MAP + LEN -> a < Q \/ Q + kPtrArrayResv <= a).
{ pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 1%nat _ eq_refl) as DQ.
unfold zdisjoint in DQ. cbn [fst snd] in DQ. unfold YF0y.MAP, YF0y.LEN in DQ.
pose proof (YF16.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _). rewrite <- E in DQ. unfold YF23.MAP. clear - DQ. intros a Ha. img_lia. }
assert (QT : forall a, Q <= a < Q + kPtrArrayResv -> a < T \/ T + kThreadObjSize <= a).
{ pose proof (YF0y.SX B ly X rd0 M 1%nat 2%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D. intros a Ha. img_lia. }
assert (CT : forall a, ly_C ly <= a < ly_C ly + 256 -> a < T \/ T + kThreadObjSize <= a).
{ pose proof (YF0y.SX B ly X rd0 M 6%nat 2%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D. intros a Ha. img_lia. }
assert (LT : (lst + 8192 <= T \/ T + kThreadObjSize <= lst) /\ (lst + 8192 <= Q \/ Q + kPtrArrayResv <= lst) /\ (lst + 8192 <= ly_C ly \/ ly_C ly + 256 <= lst)).
{ destruct (YF0y.LST B ly X rd0 M k r o sm i (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm Hi (YF16.IMG B ly X k cbp W regs mem md PRE)) as (y2 & Hy2 & Ey2 & CI2 & _ & _ & _ & SZ2 & _).
pose proof (YF0y.SECX B ly X rd0 M _ 2%nat _ CI2 eq_refl) as D2'. pose proof (YF0y.SECX B ly X rd0 M _ 1%nat _ CI2 eq_refl) as D1'.
pose proof (YF0y.SECX B ly X rd0 M _ 6%nat _ CI2 eq_refl) as D6'. unfold zdisjoint in D1', D2', D6'. cbn [fst snd] in D1', D2', D6'.
unfold YF0y.lst, YF0y.lastr, YF0y.arr in *. unfold YF23.lst. clear - D1' D2' D6' SZ2. splits; img_lia. }
assert (OUTD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0) -> ~ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) -> ~ (T + t_stats + 40 <= a < T + t_stats + 56) -> ~ WIND a /\ 0 <= a < 2 ^ 64).
{ intros a Ha N1 N2 N3. unfold YF11.WIND, YF10.WINA. fold sp0. split; [img_try (tauto) | img_try (img_exact Ha)]. }
assert (XFER : forall a (w : nat) x, val_mem tfxsegs m0 a w x -> (forall kk, (kk < w)%nat -> ~ WIND (a + Z.of_nat kk) /\ 0 <= a + Z.of_nat kk < 2 ^ 64) ->
val_mem tfxsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv Hout. img_apply (val_mem_frame (w_H W) mem memD); [|img_try (img_exact Hv)]. intros kk Hkk. img_apply MQD. destruct (Hout kk Hkk) as [O1 O2]. rewrite unsigned_lit_small by img_exact O2. img_exact O1. }
assert (PXFER : forall a, apresent H0 mem a -> ~ WIND a /\ 0 <= a < 2 ^ 64 -> apresent H0 memD a).
{ intros a Hp [Ho Ha]. img_apply (apresent_same (w_H W) mem); [img_try (img_apply MQD; rewrite unsigned_lit_small by img_exact Ha; img_exact Ho) | img_try (img_exact Hp)]. }
assert (XI : forall a (w : nat) x, val_mem tfxsegs m0 a w x -> TFX_IMG_LO <= a -> a + Z.of_nat w <= TFX_IMG_END -> (a + Z.of_nat w <= A_ALLOCATOR + 680 \/ A_ALLOCATOR + 684 <= a) -> val_mem tfxsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2 H3. img_apply XFER; [img_try (img_exact Hv)|]. intros kk Hkk. img_apply OUTD; clear - Hkk H1 H2 H3 Hlo hS1 hT1; numconst; img_lia. }
assert (XM : forall a (w : nat) x, val_mem tfxsegs m0 a w x -> MAP <= a -> a + Z.of_nat w <= MAP + LEN -> val_mem tfxsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. img_apply XFER; [img_try (img_exact Hv)|]. intros kk Hkk. destruct (MT (a + Z.of_nat kk) ltac:(img_lia)); (img_apply OUTD; clear - Hkk H1 H2 H Hlo hS1 hCE M1 M2; numconst; img_lia). }
assert (PM : forall a, MAP <= a < MAP + 32 -> apresent H0 memD a).
{ intros a Ha. img_apply PXFER; [img_try (img_apply HPm; img_exact Ha)|]. destruct (MT a ltac:(img_lia)); (img_apply OUTD; clear - Ha H Hlo hS1 hCE M1 M2 M4; numconst; img_lia). }
assert (XQ : forall a (w : nat) x, val_mem tfxsegs m0 a w x -> Q <= a -> a + Z.of_nat w <= Q + kPtrArrayResv -> val_mem tfxsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. img_apply XFER; [img_try (img_exact Hv)|]. intros kk Hkk. destruct (QT (a + Z.of_nat kk) ltac:(img_lia)); (img_apply OUTD; clear - Hkk H1 H2 H Hlo hS1 hCE hQ1 hQ2; numconst; img_lia). }
assert (PQ : forall a, Q <= a < Q + kPtrArrayResv -> apresent H0 mem a -> apresent H0 memD a).
{ intros a Ha Hp. img_apply PXFER; [img_try (img_exact Hp)|]. destruct (QT a Ha); (img_apply OUTD; clear - Ha H Hlo hS1 hCE hQ1 hQ2; numconst; img_lia). }
assert (XL : own = false -> val_mem tfxsegs (mrestrict H0 memD) (lst + 24) 8 (nA - 1) /\ (forall a, lst + 24 <= a < lst + 32 -> apresent H0 memD a)).
{ intros Ho. split.
- img_apply XFER; [img_try (img_exact L24)|]. intros kk Hkk. destruct LT as [D' _]. img_apply OUTD; clear - Hkk D' Hlo hS1 hCE LL1 LL2; numconst; img_lia.
- intros a Ha. img_apply PXFER; [img_try (img_apply L24P; img_exact Ha)|]. destruct LT as [D' _]. img_apply OUTD; clear - Ha D' Hlo hS1 hCE LL1 LL2; numconst; img_lia. }
assert (XTI : forall a (w : nat) x, val_mem tfxsegs m0 a w x -> T + t_stats + 56 <= a -> a + Z.of_nat w <= T + kThreadObjSize -> val_mem tfxsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. img_apply XFER; [img_try (img_exact Hv)|]. intros kk Hkk. img_apply OUTD; clear - Hkk H1 H2 Hlo hS1 hCE hT1 hT2; numconst; img_lia. }
assert (XC : forall a (w : nat) x, val_mem tfxsegs m0 a w x -> ly_C ly <= a -> a + Z.of_nat w <= ly_C ly + 256 -> val_mem tfxsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. img_apply XFER; [img_try (img_exact Hv)|]. intros kk Hkk. destruct (CT (a + Z.of_nat kk) ltac:(img_lia)); (img_apply OUTD; clear - Hkk H1 H2 H Hlo hS1 hCE hC1 hC2; numconst; img_lia). }
assert (USD : bv_unsigned (getr regsD 2) = sp0) by (img_try (rewrite D2; img_refl)).
assert (XTP : getr regsD 4 = w64 TFX_TP) by (img_try (rewrite (DSR 4%bv ltac:(inS)), Htp, (ts_tp _ TB); img_refl)).
pose proof (Uv 1%bv) as U1. pose proof (Uv 8%bv) as U8. pose proof (Uv 9%bv) as U9. pose proof (Uv 18%bv) as U18.
assert (Y1 : val_mem tfxsegs (mrestrict H0 memD) MAP 8 MAP) by (img_try (img_apply XM; [img_try (img_exact H1v) | img_lia | img_try (cbn; img_lia)])).
assert (Y2 : val_mem tfxsegs (mrestrict H0 memD) (MAP + 8) 8 LEN) by (img_try (img_apply XM; [img_try (img_exact H2v) | img_lia | img_try (cbn; img_lia)])).
assert (Y3 : val_mem tfxsegs (mrestrict H0 memD) (MAP + 24) 8 idx) by (img_try (img_apply XM; [img_try (img_exact H4v) | img_lia | img_try (cbn; img_lia)])).
assert (Y4 : val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 72) 8 Q) by (img_try (img_apply XI; [img_try (img_exact I3) | img_try (clear; numconst; img_lia) | img_try (clear; cbn; numconst; img_lia) | img_try (clear; cbn; img_lia)])).
assert (Y5 : val_mem tfxsegs (mrestrict H0 memD) qi 8 MAP) by (img_try (unfold YF23.qi, YF23.idx; img_apply XQ; [img_try (img_exact QIV) | img_lia | img_try (cbn; clear - A4 A5; numconst; img_lia)])).
assert (Y6 : val_mem tfxsegs (mrestrict H0 memD) ql 8 lst) by (img_try (unfold ql; img_apply XQ; [img_try (img_exact QLV) | img_lia | img_try (cbn; clear - A4 A5; numconst; img_lia)])).
assert (Y7 : val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 120) 8 nA) by (img_try (img_apply XI; [img_try (img_exact I4) | img_try (clear; numconst; img_lia) | img_try (clear; cbn; numconst; img_lia) | img_try (clear; cbn; img_lia)])).
assert (Y8 : val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 144) 8 ji1 /\ val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 152) 8 ji2 /\
val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 704) 8 ji3 /\ val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 712) 8 ji4).
{
splits; [ img_try (img_apply XI; [img_exact JV1 | clear; numconst; img_lia | clear; cbn; numconst; img_lia | clear; cbn; img_lia])
| img_try (img_apply XI; [img_exact JV2 | clear; numconst; img_lia | clear; cbn; numconst; img_lia | clear; cbn; img_lia])
| img_try (img_apply XI; [img_exact JV3 | clear; numconst; img_lia | clear; cbn; numconst; img_lia | clear; cbn; img_lia])
| img_try (img_apply XI; [img_exact JV4 | clear; numconst; img_lia | clear; cbn; numconst; img_lia | clear; cbn; img_lia]) ]. }
destruct Y8 as (Y8a & Y8b & Y8c & Y8d).
assert (Y9 : val_mem tfxsegs (mrestrict H0 memD) TFX_TSD 8 (ly_C ly) /\ val_mem tfxsegs (mrestrict H0 memD) (ly_C ly + 8) 4 0 /\ val_mem tfxsegs (mrestrict H0 memD) (ly_C ly + 152) 8 T).
{ splits; [img_try (img_apply XI; [img_exact T4 | clear; numconst; img_lia | clear; cbn; numconst; img_lia | clear; cbn; numconst; img_lia]) | img_try (img_apply XC; [img_exact T5 | img_lia | cbn; img_lia]) | img_try (img_apply XC; [img_exact T6 | img_lia | cbn; img_lia])]. }
destruct Y9 as (Y9a & Y9b & Y9c).
assert (Y10 : val_mem tfxsegs (mrestrict H0 memD) (T + t_stats + 88) 8 j5 /\ val_mem tfxsegs (mrestrict H0 memD) (T + t_stats + 96) 8 j6).
{ split; [ img_try (img_apply XTI; [img_exact JV5 | clear; numconst; img_lia | clear; cbn; numconst; img_lia]) | img_try (img_apply XTI; [img_exact JV6 | clear; numconst; img_lia | clear; cbn; numconst; img_lia]) ]. }
destruct Y10 as [Y10a Y10b].
assert (TJP : forall a, T + t_stats + 88 <= a < T + t_stats + 104 -> apresent H0 memD a).
{ intros a Ha. img_apply PXFER; [img_try (img_apply TPRES; clear - Ha; numconst; img_lia)|]. img_apply OUTD; clear - Ha Hlo hS1 hCE hT1 hT2; numconst; img_lia. }
assert (YK : val_mem tfxsegs (mrestrict H0 memD) (A_ALLOCATOR + 64) 8 4096 /\ val_mem tfxsegs (mrestrict H0 memD) (0xa9a20 + D_10c0) 1 1 /\ val_mem tfxsegs (mrestrict H0 memD) (0xa9a24 + D_10c0) 4 0 /\
val_mem tfxsegs (mrestrict H0 memD) (TFX_TP - 88) 8 TFX_TSD /\
val_mem tfxsegs (mrestrict H0 memD) (0xa2150 + D_10f0) 8 (0x13bce8 + D_10c0) /\ val_mem tfxsegs (mrestrict H0 memD) (0x13bd60 + D_10c0) 8 0xffffffffffffffff /\ val_mem tfxsegs (mrestrict H0 memD) (0x13bd78 + D_10c0) 8 0 /\
val_mem tfxsegs (mrestrict H0 memD) (0xa2160 + D_10f0) 8 (0xaa1b8 + D_10c0) /\ val_mem tfxsegs (mrestrict H0 memD) (0xaa1b8 + D_10c0) 8 0x7fff8000 /\
val_mem tfxsegs (mrestrict H0 memD) (0xa2168 + D_10f0) 8 (0xaaea8 + D_10c0) /\ val_mem tfxsegs (mrestrict H0 memD) (0xa2170 + D_10f0) 8 (0xaaeb0 + D_10c0) /\ val_mem tfxsegs (mrestrict H0 memD) (0xa2178 + D_10f0) 8 (0xaaea0 + D_10c0) /\
val_mem tfxsegs (mrestrict H0 memD) (0xaaea0 + D_10c0) 8 0x7fffffffffff /\ val_mem tfxsegs (mrestrict H0 memD) (0xaaea8 + D_10c0) 8 0 /\ val_mem tfxsegs (mrestrict H0 memD) (0xaaeb0 + D_10c0) 8 0 /\
val_mem tfxsegs (mrestrict H0 memD) (0xa2180 + D_10f0) 8 (0xa4000 + D_10f0) /\ val_mem tfxsegs (mrestrict H0 memD) (0xa4000 + D_10f0) 8 (0x9b894 + D_10ec) /\
val_mem tfxsegs (mrestrict H0 memD) (0xa2140 + D_10f0) 8 (0x139c60 + D_10c0) /\ val_mem tfxsegs (mrestrict H0 memD) (0x139c60 + D_10c0) 8 4096 /\ val_mem tfxsegs (mrestrict H0 memD) (0xa21a0 + D_10f0) 8 1).
{ splits; (img_apply XI; [ img_try (first [img_exact I1 | img_exact I2 | img_exact I3 | img_exact I4 | img_exact T1 | img_exact T2 | img_exact T3 | img_exact T4 | img_exact K1 | img_exact K2 | img_exact K3 | img_exact K4 | img_exact K5 | img_exact K6 | img_exact K7 | img_exact K8
| img_exact K9 | img_exact K10 | img_exact K11 | img_exact K12 | img_exact K13 | img_exact K14 | img_exact K15 | img_exact K16])
| img_try (clear; numconst; img_lia) | img_try (clear; cbn; numconst; img_lia) | img_try (clear; cbn; numconst; img_lia)]). }
destruct YK as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18 & Z19 & Z20).
constructor.
- img_exact (am_layout B ly X rd0 M).
- img_exact (YF16.IMG B ly X k cbp W regs mem md PRE).
- img_exact XTP.
- unfold YF10.v, w64. rewrite Z_to_bv_bv_unsigned. img_exact Hra.
- splits; [img_try (img_exact D10) | img_try (img_exact D11) | img_try (img_exact D12) | img_try (img_exact D1) | img_try (img_exact D8) | img_try (img_exact D9) | img_try (img_exact D18)].
- rewrite USD. split; [img_try (img_exact Hlo) | img_try (clear - Hcb1 Hcb2; img_lia)].
- rewrite USD. img_exact Hal.
- rewrite USD. intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [LOW|HI'].
+ img_apply PXFER; [img_try (img_apply HPRES; img_lia)|]. img_apply OUTD; clear - Ha LOW Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2; numconst; img_lia.
+ img_apply DPRS. img_lia.
- clear - U1 U8 U9 U18. unfold YF10.v in *. splits; img_lia.
- split; [img_try (img_exact M1)|]. cbn. clear - M2 M3 M4 M5 L19. destruct small; (splits; try assumption; img_lia).
- pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 2%nat _ eq_refl) as DT.
pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 6%nat _ eq_refl) as DC.
pose proof (YF16.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _).
unfold zdisjoint in DT, DC. cbn [fst snd] in DT, DC. unfold YF0y.MAP, YF0y.LEN in DT, DC. rewrite <- E in DT, DC.
unfold YF23.MAP. clear - DT DC. unfold kThreadObjSize in *. split; img_lia.
- splits; [img_try (img_exact Y1) | img_try (img_exact Y2) | img_try (img_exact Y3) | img_try (img_exact PM)].
- unfold YF23.qi, ql. splits; try img_refl; try assumption.
+ clear - A5. unfold YF23.idx. img_lia.
+ clear - A5. unfold YF23.idx. img_lia.
+ clear - A4. img_lia.
+ pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 1%nat _ eq_refl) as DQ.
pose proof (YF16.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _).
unfold zdisjoint in DQ. cbn [fst snd] in DQ. unfold YF0y.MAP, YF0y.LEN in DQ. rewrite <- E in DQ.
unfold YF23.MAP. clear - DQ. img_lia.
- img_exact Y4.
- split; [img_try (img_exact Y5)|]. intros a Ha. unfold YF23.qi, YF23.idx in Ha. img_apply PQ; [img_try (clear - Ha A4 A5; numconst; img_lia) | img_try (img_apply QIP; img_exact Ha)].
- intros Ho. split; [img_try (img_exact Y6)|]. intros a Ha. unfold ql in Ha. img_apply PQ; [img_try (clear - Ha A4 A5; numconst; img_lia) | img_try (img_apply QLP; img_exact Ha)].
- splits; assumption.
- img_exact LOWN.
- intros Ho. img_exact (proj2 (XL Ho)).
- img_exact Y7.
- splits; first [assumption | clear - JR1 JR2 JR3 JR4; img_lia].
- img_exact DMUT.
- splits; assumption.
- splits; [img_try (img_exact Y10a) | img_try (img_exact Y10b) | | | | | img_try (img_exact TJP)]; clear - JR5 JR6; img_lia.
- intros a Ha. img_apply PXFER; [img_try (img_apply SHP; img_exact Ha)|]. img_apply OUTD; unfold SHAv, CNTv in Ha; clear - Ha Hlo hS1 hCE hT1 M1 M2 M4; numconst;
pose proof (Z.div_pos MAP 8 ltac:(img_lia) ltac:(img_lia)); pose proof (Z.div_le_mono _ _ 8 ltac:(img_lia) M2); Z.div_mod_to_equations; img_lia.
-
pose proof hI1 as J1'. pose proof hI2 as J2'. rewrite hIE in J1', J2'.
pose proof HPRES as HPRES'. clear XFER XI XM XQ XTI XC HPRES MQD H1v H2v H4v HPm T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 JV1 JV2 JV3 JV4 JV5 JV6 QLV QLP L24 L24P QIV
K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 SHP TPRES hI1 hI2 hIE MT MC CT.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, KSTACK, kLowMemEnd, TFX_INST in hP1, hP2, hQ1, hQ2, hT1, hT2, hC1, hC2, hS1, hS2, hCE, hSP1, hSP2, Hlo, J1', J2', M1, M2, M4, LL1, LL2, L19, QT, LT, MQ.
rewrite restrict_mkst_fx. unfold YF2q.SS0, YF2q.SR0, sr_set. cbn [bv_eqb]. unfold YF2q.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin;
[img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact XTP]
| intros XX; discriminate | cbn [sv_denot]; img_exact D10]
| intros XX; discriminate | cbn [sv_denot]; img_exact D11]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite YF2q.EqMAP, D12; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite YF2q.EqRA, D1; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite YF2q.EqS0, D8; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite YF2q.EqS1, D9; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia])
| img_try (intros XX; discriminate) | img_try (cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite YF2q.EqS2, D18; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia)].
+ destruct own; (img_case; vm_compute); img_refl.
+
cbn [ms_mem mkst]. fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2).
assert (SHB : 2147450880 = SHADOW_OFF) by img_refl.
unfold YF2q.REG0, YF2q.COMMON. img_apply Forall_cons; [|img_try (img_apply Forall_app; split)].
{   unfold YF2q.R_MAPH. reg_intro. rewrite YF2q.EqMAP. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (destruct own; img_lia)|]. split.
{ intros o' Ho'. img_apply apresent_writable_off; [img_try (img_apply (zone3_off_img _ _ _ ZM3); destruct own; img_lia)|]. img_apply PM. destruct own; img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- img_apply (chunk_atomd _ _ _ _ 8 34%nat 0 MAP); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact Y1) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomd _ _ _ _ 8 35%nat 0 LEN); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact Y2) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomd _ _ _ _ 8 36%nat 0 idx); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (unfold YF23.idx in *; img_lia) | img_try (img_exact Y3) | img_try (unfold YF23.idx in *; r8) | img_try (cbn; img_lia)]. }
{ unfold YF2q.R_STK, YF2q.R_MW0, YF2q.R_NS, YF2q.R_J12, YF2q.R_J34, YF2q.R_QI, YF2q.R_CTX, YF2q.R_JST, flit1, flit4, flit8, fatom8.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs _ _ 2 sp0 (- GDEPTH)); [img_try (rewrite YF2q.E2; img_exact USD) | img_try (unfold GDEPTH; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, GDEPTH in *; img_lia)|]. destruct (Z_lt_le_dec a (sp0 - 80)) as [LOW|HI'].
- img_apply PXFER; [img_try (img_apply HPRES'; unfold GDEPTH, KSTACK in *; img_lia)|]. img_apply OUTD; clear - Ha LOW Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2; numconst; img_lia.
- img_apply DPRS. img_lia. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_apply rw_writable; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero_mb. intros z Hz. cbn [YQ0b.c_off] in Hz |- *.
pose proof (DMUT (Z.to_nat z) ltac:(img_lia)) as E0. rewrite Z2Nat.id in E0 by img_lia. rewrite le_byte_zero in E0. unfold A_ALLOCATOR in E0. rewrite Z.add_0_l. img_exact E0. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_apply rw_writable; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atomd _ _ 0 _ 8 37%nat 0 nA); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y7) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_apply rw_writable; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atomd _ _ 0 _ 8 42%nat 0 ji1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y8a) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomd _ _ 0 _ 8 43%nat 0 ji2); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y8b) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_apply rw_writable; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atomd _ _ 0 _ 8 44%nat 0 ji3); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y8c) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomd _ _ 0 _ 8 45%nat 0 ji4); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y8d) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2q.EqQI. unfold w64. rewrite unsigned_lit_small by (img_try (unfold YF23.qi, YF23.idx; img_lia)).
unfold YF23.qi, YF23.idx in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o' Ho'. img_apply apresent_writable_off; [img_try (img_apply (zone3_off_img _ _ _ ZQ3); unfold kPtrArrayResv; clear - Ho' A4 A5; img_lia)|]. img_apply PQ; [img_try (unfold kPtrArrayResv; clear - Ho' A4 A5; img_lia)|]. img_apply QIP. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atomd _ _ _ _ 8 34%nat 0 MAP); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact Y5) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2q.EqC. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_litd_at; [img_try (img_exact Y9b) | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
- img_apply (chunk_atomd _ _ _ _ 8 32%nat 0 T); [img_try (rewrite YF2q.EqT; unfold w64; f_equal; img_lia) | img_lia | img_try (img_exact Y9c) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2q.EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_stats in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o' Ho'. img_apply apresent_writable_off; [img_try (img_apply (zone3_off_img _ _ _ ZT3); unfold t_stats, kThreadObjSize in *; img_lia)|]. img_apply TJP. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atomd _ _ _ _ 8 46%nat 0 j5); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact Y10a | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atomd _ _ _ _ 8 47%nat 0 j6); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact Y10b | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [img_try (lit_region Z1)|].
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomd _ _ 0 _ 8 38%nat 0 Q); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y4) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [img_try (lit_region Z5)|]. img_apply Forall_cons; [img_try (lit_region Z6)|]. img_apply Forall_cons; [img_try (lit_region Z7)|]. img_apply Forall_cons; [img_try (lit_region Z8)|].
img_apply Forall_cons.
{   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomd _ _ 0 _ 8 48%nat 0 SHADOW_OFF); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (clear; numconst; img_lia) | img_try (rewrite Z.add_0_l, <- SHB; img_exact Z9) | img_try (clear; numconst; cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [img_try (lit_region Z10)|]. img_apply Forall_cons; [img_try (lit_region Z11)|]. img_apply Forall_cons; [img_try (lit_region Z12)|]. img_apply Forall_cons; [img_try (lit_region Z13)|].
img_apply Forall_cons; [img_try (lit_region Z14)|]. img_apply Forall_cons; [img_try (lit_region Z15)|]. img_apply Forall_cons; [img_try (lit_region Z16)|]. img_apply Forall_cons; [img_try (lit_region Z17)|].
img_apply Forall_cons; [img_try (lit_region Z18)|]. img_apply Forall_cons; [img_try (lit_region Z19)|]. img_apply Forall_cons; [img_try (lit_region Z20)|].
img_apply Forall_cons; [img_try (lit_region Z2)|]. img_apply Forall_cons; [img_try (lit_region Z3)|].
img_apply Forall_cons. {   unfold TFX_TP. lit_region Z4. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{   reg_intro. unfold TFX_TSD. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomd _ _ 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite YF2q.EqC; unfold w64; f_equal; img_lia) | img_lia | img_try (rewrite Z.add_0_l; img_exact Y9a) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. } }
{
destruct own eqn:EO; [img_try (img_apply Forall_nil)|]. destruct (XL eq_refl) as [XL1 XL2].
unfold YF2q.R_LASTH, YF2q.R_QL. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- reg_intro. rewrite YF2q.EqLAST. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [|img_try (img_apply Forall_nil)]. intros o' Ho'. img_apply apresent_writable_off; [img_try (img_apply (zone3_off_img _ _ _ ZL3); img_lia)|]. img_apply XL2. img_lia.
- reg_intro. rewrite YF2q.EqQL. unfold w64. unfold ql in *. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomd _ _ _ _ 8 41%nat 0 lst); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact Y6) | img_try (r8) | img_try (cbn; img_lia)]. }
+
fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2).
pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 2%nat _ eq_refl) as DT.
pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 6%nat _ eq_refl) as DC.
pose proof (YF0y.MAPX B ly X rd0 M k r o sm (YF16.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 1%nat _ eq_refl) as DQ.
pose proof (YF16.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _).
unfold zdisjoint in DT, DC, DQ. cbn [fst snd] in DT, DC, DQ. unfold YF0y.MAP, YF0y.LEN in DT, DC, DQ. rewrite <- E in DT, DC, DQ. fold (YF23.MAP ly r) in DT, DC, DQ. clear E.
pose proof (YF0y.SX B ly X rd0 M 6%nat 2%nat _ _ eq_refl eq_refl ltac:(img_lia)) as CT0. pose proof (YF0y.SX B ly X rd0 M 1%nat 2%nat _ _ eq_refl eq_refl ltac:(img_lia)) as QT0.
pose proof (YF0y.SX B ly X rd0 M 1%nat 6%nat _ _ eq_refl eq_refl ltac:(img_lia)) as QC0. unfold zdisjoint in CT0, QT0, QC0. cbn [fst snd] in CT0, QT0, QC0.
destruct LT as (LT1 & LT2 & LT3).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, KSTACK, kLowMemEnd, TFX_INST in DT, DC, DQ, CT0, QT0, QC0, LT1, LT2, LT3, LOWN.
destruct own eqn:EO.
* img_apply pairwise_disjoint_of_extents.
unfold YF2q.REG0, YF2q.COMMON, YF2q.R_MAPH, YF2q.R_STK, YF2q.R_MW0, YF2q.R_NS, YF2q.R_J12, YF2q.R_J34, YF2q.R_QI, YF2q.R_CTX, YF2q.R_JST, flit1, flit4, flit8, fatom8, extent_of_region.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite YF2q.E2, USD, YF2q.EqMAP, YF2q.EqQI, YF2q.EqC, YF2q.EqT. unfold w64. unfold YF23.qi, YF23.idx in *.
clear - Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2 hC1 hC2 hQ1 hQ2 M1 M2 M4 A4 A5 J1' J2' DT DC DQ CT0 QT0 QC0. numconst. rewrite !unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [clear DT DC DQ CT0 QT0 QC0; img_lia | clear DC DQ CT0 QT0 QC0; img_lia | clear DT DQ CT0 QT0 QC0; img_lia | clear DT DC CT0 QT0 QC0; img_lia | clear DT DC DQ QT0 QC0; img_lia | clear DT DC DQ CT0 QC0; img_lia | clear DT DC DQ CT0 QT0; img_lia | img_lia].
* pose proof LOWN as LOWN'. img_apply pairwise_disjoint_of_extents.
unfold YF2q.REG0, YF2q.COMMON, YF2q.R_MAPH, YF2q.R_STK, YF2q.R_MW0, YF2q.R_NS, YF2q.R_J12, YF2q.R_J34, YF2q.R_QI, YF2q.R_CTX, YF2q.R_JST,
YF2q.R_LASTH, YF2q.R_QL, flit1, flit4, flit8, fatom8, extent_of_region.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite YF2q.E2, USD, YF2q.EqMAP, YF2q.EqQI, YF2q.EqC, YF2q.EqT, YF2q.EqLAST, YF2q.EqQL. unfold w64. unfold YF23.qi, YF23.idx, ql in *.
assert (NEI : Z.of_nat i <> nA - 1) by (img_try (unfold YF23.own, YF23.idx in EO; apply Z.eqb_neq in EO; img_exact EO)).
clear - Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2 hC1 hC2 hQ1 hQ2 M1 M2 M4 A4 A5 J1' J2' LL1 LL2 NEI DT DC DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'. numconst. rewrite !unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [clear DT DC DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; img_lia | clear DC DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; img_lia | clear DT DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; img_lia
| clear DT DC CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; img_lia | clear DT DC DQ QT0 QC0 LT1 LT2 LT3 LOWN'; img_lia | clear DT DC DQ CT0 QC0 LT1 LT2 LT3 LOWN'; img_lia
| clear DT DC DQ CT0 QT0 LT1 LT2 LT3 LOWN'; img_lia | clear DT DC DQ CT0 QT0 QC0 LT2 LT3 LOWN'; img_lia | clear DT DC DQ CT0 QT0 QC0 LT1 LT3 LOWN'; img_lia
| clear DT DC DQ CT0 QT0 QC0 LT1 LT2 LOWN'; img_lia | clear DT DC DQ CT0 QT0 QC0 LT1 LT2 LT3; img_lia | img_lia].
+
fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2). split; [|img_try (split; img_exact I)].
assert (AF : forall k0 Xv lo hi al, ew (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (E2' : ew (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2) 2 = w64 sp0) by (img_try (rewrite YF2q.E2, D2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (HSA : 2147451392 <= SHAv MAP /\ SHAv MAP + CNTv LEN <= 17594332446720 /\ SHAv MAP mod 2 ^ 9 = 0 /\ CNTv LEN mod 2 ^ 9 = 0 /\ 1024 <= CNTv LEN < 2 ^ 26 /\ (SHEv MAP LEN) mod 2 ^ 9 = 0 /\
(if small then CNTv LEN <= 2 ^ 26 - 512 else 65536 <= CNTv LEN)).
{ unfold SHAv, CNTv, SHEv, SHAv, CNTv. clear - M1 M2 M3 M4 M5 L19. numconst. img_change (2 ^ 9) with 512.
apply Z.mod_divide in M3 as [q Hq]; [|img_lia]. apply Z.mod_divide in M5 as [q' Hq']; [|img_lia]. rewrite Hq, Hq' in *.
replace (q * 4096 / 8) with (q * 512) by (img_try (Z.div_mod_to_equations; img_lia)). replace (q' * 4096 / 8) with (q' * 512) by (img_try (Z.div_mod_to_equations; img_lia)).
splits; try (Z.div_mod_to_equations; img_lia);
try ((img_apply Z.mod_divide; [img_lia|]); first [exists (4194240 + q); img_lia | exists q'; img_lia | exists (4194240 + q + q'); img_lia]).
destruct small; Z.div_mod_to_equations; img_lia. }
destruct HSA as (SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7).
cbn [YF2q.FFD f_atoms atoms_ok]. unfold YF23.qi, YF23.idx, ql in *. numconst.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Hlo Hcb1 Hcb2 hS1 hS2 hCE Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_refl| | | |]. all: clear - CR0 hT1 hT2 hTAL; first [img_lia | img_change (2 ^ 12) with 4096; img_exact hTAL]. }
split. { img_apply (AF 33%nat (ly_C ly)); [img_refl| | | |]. all: clear - CR0 hC1 hC2 hCAL; first [img_lia | img_change (2 ^ 3) with 8; img_exact hCAL]. }
split. { img_apply (AF 34%nat MAP); [img_refl| | | |]. all: clear - CR0 M1 M2 M3 M4; first [img_lia | img_change (2 ^ 12) with 4096; img_exact M3]. }
split. { clear - AF M4 M5 L19. destruct small; (img_apply (AF 35%nat LEN); [img_refl| | | |]); first [Z.div_mod_to_equations; img_lia | img_change (2 ^ 12) with 4096; img_exact M5]. }
split. { img_apply (AF 36%nat (Z.of_nat i)); [img_refl| | | |]. all: clear - A4 A5; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat nA); [img_refl| | | |]. all: clear - A4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat Q); [img_refl| | | |]. all: clear - CR0 hQ1 hQ2 hQAL; first [img_lia | img_change (2 ^ 12) with 4096; img_exact hQAL]. }
split. { img_apply (AF 39%nat (Q + 8 * Z.of_nat i)); [img_refl| | | |]. all: clear - CR0 hQ1 hQ2 hQAL A4 A5; first [img_lia | apply Z.mod_divide in hQAL as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists (q * 512 + Z.of_nat i); img_change (2 ^ 3) with 8; img_lia]. }
split. { img_apply (AF 40%nat (Q + 8 * (nA - 1))); [img_refl| | | |]. all: clear - CR0 hQ1 hQ2 hQAL A4 A5; first [img_lia | apply Z.mod_divide in hQAL as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists (q * 512 + (nA - 1)); img_change (2 ^ 3) with 8; img_lia]. }
split. { img_apply (AF 41%nat lst); [img_refl| | | |]. all: clear - CR0 LL1 LL2 LL3; first [img_lia | img_change (2 ^ 12) with 4096; img_exact LL3]. }
split. { img_apply (AF 42%nat ji1); [img_refl| | | |]. all: clear - JR1; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 43%nat ji2); [img_refl| | | |]. all: clear - JR2; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 44%nat ji3); [img_refl| | | |]. all: clear - JR3; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 45%nat ji4); [img_refl| | | |]. all: clear - JR4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 46%nat j5); [img_refl| | | |]. all: clear - JR5; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 47%nat j6); [img_refl| | | |]. all: clear - JR6; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 48%nat SHADOW_OFF); [img_refl| | | |]. all: clear; unfold SHADOW_OFF; first [img_lia | img_refl]. }
split. { img_apply (AF 49%nat (SHAv MAP)); [img_refl| | | |]. all: clear - SA1 SA2 SA3 SA5; first [img_lia | img_exact SA3]. }
split. { clear - AF SA4 SA5 SA7. destruct small; (img_apply (AF 50%nat (CNTv LEN)); [img_refl| | | |]); first [img_lia | img_exact SA4]. }
split. { img_apply (AF 51%nat vra); [img_refl| | | |]. all: clear - U1; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 52%nat vs0); [img_refl| | | |]. all: clear - U8; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 53%nat vs1); [img_refl| | | |]. all: clear - U9; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 54%nat vs2); [img_refl| | | |]. all: clear - U18; unfold YF10.v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 55%nat (SHEv MAP LEN)); [img_refl| | | |]. all: unfold SHEv in *; clear - SA1 SA2 SA5 SA6; first [img_lia | img_exact SA6]. }
Qed.
End c.
End b.
