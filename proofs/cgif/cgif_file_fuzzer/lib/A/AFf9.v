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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFgx AFfd AFgv AFg8 AFfc AFf6 AFfe AFf7 AB13.
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, AFgu.GFRAME, AFgx.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Section c.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Variable small : bool.
Hypothesis HSM : needs_remap (sm_len sm) = negb small.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation idx := (AFg8.idx i).
Local Notation qi := (AFg8.qi ly i).
Local Notation lst := (AFg8.lst ly X r).
Local Notation own := (AFg8.own X i).
Definition ql : Z := Q + 8 * (nA - 1).
Local Notation ji1 := (AFfc.ji1 W mem).
Local Notation ji2 := (AFfc.ji2 W mem).
Local Notation ji3 := (AFfc.ji3 W mem).
Local Notation ji4 := (AFfc.ji4 W mem).
Local Notation j5 := (AFfc.j5 ly W mem).
Local Notation j6 := (AFfc.j6 ly W mem).
Local Notation v := (AFf6.v regs).
Local Notation vra := (AFf6.v regs 1%bv).
Local Notation vs0 := (AFf6.v regs 8%bv).
Local Notation vs1 := (AFf6.v regs 9%bv).
Local Notation vs2 := (AFf6.v regs 18%bv).
Local Notation WIND := (AFf7.WIND ly regs).
Local Notation E0d := (AFgv.E0 ly).
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Lemma Uv : forall r', 0 <= v r' < 2 ^ 64. Proof. intros r'. unfold AFf6.v. apply u64_range. Qed.
Lemma SM19 : if small then True else 2 ^ 19 <= LEN.
Proof.
pose proof HSM as SM. unfold needs_remap, kClearShadowMmapThreshold in SM. unfold AFg8.LEN. clear - SM.
destruct small; cbn [negb] in SM; [exact I | apply Z.leb_le in SM; Z.div_mod_to_equations; lia].
Qed.
Lemma chunk_litd : forall E mm a (w : BinNums.N) x, val_mem tfibsegs mm a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E mm 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros E mm a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_litd_at : forall E mm base a (w : BinNums.N) x, val_mem tfibsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E mm base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros E mm base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atomd : forall E mm base a (w : BinNums.N) k0 d x, ew E k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E mm base (YP09.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros E mm base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac lit_region V := reg_intro; unfold A_ALLOCATOR, TFIB_TP, TFIB_TSD; split; [clear; lia|]; split; [clear; lia|]; split; [intros ? ?; lia|]; apply Forall_cons; [apply chunk_litd; [exact V | clear; cbn; lia | clear; cbn; lia] | apply Forall_nil].
Theorem DSEED : forall regsD memD, AFf7.PRED ly W regs mem r regsD memD ->
AFgv.free_hyps W ly regsD memD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2 own small.
Proof.
intros regsD memD (DSR & D2 & D1 & D8 & D9 & D18 & D10 & D11 & D12 & MQD & DPRS & DTJ & DMUT).
pose proof PRE as PRE'. destruct PRE' as (_ & _ & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & _ & HPRES & _ & _ & _ & Htp & _ & _).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof (AFfc.HI B TB ly X k cbp W regs mem md PRE) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & hTAL & hCAL & _).
pose proof (AFfc.GEOM B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (M1 & M2 & M3 & M4 & M5 & _).
pose proof (AFfc.ARRF B ly X k cbp W regs mem md r i PRE Hi) as (_ & _ & _ & A4 & A5).
pose proof (AFfc.maph_vals B ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as (H1v & H2v & _ & H4v & HPm).
pose proof (AFfc.tls_vals B TB ly X k cbp W regs mem md PRE HTSD) as (T1 & T2 & T3 & T4 & T5 & T6).
pose proof (AFfc.inst_vals B TB ly X k cbp W regs mem md PRE) as (I1 & I2 & I3 & I4).
pose proof (AFfc.junkD_vals B TB ly X k cbp W regs mem md PRE) as ([JR1 JV1] & [JR2 JV2] & [JR3 JV3] & [JR4 JV4] & [JR5 JV5] & [JR6 JV6]).
pose proof (AFfc.last_facts B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as (_ & QLV & QLP & L24 & L24P & LL1 & LL2 & LL3 & LOWN).
pose proof (AFfc.qi_val B TB ly X k cbp W regs mem md r i PRE Hi) as [QIV QIP].
pose proof M1 as ZM3. pose proof hT1 as ZT3. pose proof hQ1 as ZQ3. pose proof LL1 as ZL3.
pose proof (AFfc.const_vals B TB ly X k cbp W regs mem md PRE) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (AFfc.shadow_present B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as SHP.
pose proof (AFfc.thread_present B TB ly X k cbp W regs mem md PRE) as TPRES.
pose proof SM19 as L19.
assert (MT : forall a, MAP <= a < MAP + LEN -> a < T \/ T + kThreadObjSize <= a).
{ pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 2%nat _ eq_refl) as DT.
unfold zdisjoint in DT. cbn [fst snd] in DT. unfold AFf4.MAP, AFf4.LEN in DT.
pose proof (AFfc.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _). rewrite <- E in DT. unfold AFg8.MAP. clear - DT. intros a Ha. lia. }
assert (MC : forall a, MAP <= a < MAP + LEN -> a < ly_C ly \/ ly_C ly + 256 <= a).
{ pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 6%nat _ eq_refl) as DC.
unfold zdisjoint in DC. cbn [fst snd] in DC. unfold AFf4.MAP, AFf4.LEN in DC.
pose proof (AFfc.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _). rewrite <- E in DC. unfold AFg8.MAP. clear - DC. intros a Ha. lia. }
assert (MQ : forall a, MAP <= a < MAP + LEN -> a < Q \/ Q + kPtrArrayResv <= a).
{ pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 1%nat _ eq_refl) as DQ.
unfold zdisjoint in DQ. cbn [fst snd] in DQ. unfold AFf4.MAP, AFf4.LEN in DQ.
pose proof (AFfc.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _). rewrite <- E in DQ. unfold AFg8.MAP. clear - DQ. intros a Ha. lia. }
assert (QT : forall a, Q <= a < Q + kPtrArrayResv -> a < T \/ T + kThreadObjSize <= a).
{ pose proof (AFf4.SX B ly X rd0 M 1%nat 2%nat _ _ eq_refl eq_refl ltac:(lia)) as D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D. intros a Ha. lia. }
assert (CT : forall a, ly_C ly <= a < ly_C ly + 256 -> a < T \/ T + kThreadObjSize <= a).
{ pose proof (AFf4.SX B ly X rd0 M 6%nat 2%nat _ _ eq_refl eq_refl ltac:(lia)) as D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D. intros a Ha. lia. }
assert (LT : (lst + 8192 <= T \/ T + kThreadObjSize <= lst) /\ (lst + 8192 <= Q \/ Q + kPtrArrayResv <= lst) /\ (lst + 8192 <= ly_C ly \/ ly_C ly + 256 <= lst)).
{ destruct (AFf4.LST B ly X rd0 M k r o sm i (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm Hi (AFfc.IMG B ly X k cbp W regs mem md PRE)) as (y2 & Hy2 & Ey2 & CI2 & _ & _ & _ & SZ2 & _).
pose proof (AFf4.SECX B ly X rd0 M _ 2%nat _ CI2 eq_refl) as D2'. pose proof (AFf4.SECX B ly X rd0 M _ 1%nat _ CI2 eq_refl) as D1'.
pose proof (AFf4.SECX B ly X rd0 M _ 6%nat _ CI2 eq_refl) as D6'. unfold zdisjoint in D1', D2', D6'. cbn [fst snd] in D1', D2', D6'.
unfold AFf4.lst, AFf4.lastr, AFf4.arr in *. unfold AFg8.lst. clear - D1' D2' D6' SZ2. splits; lia. }
assert (OUTD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0) -> ~ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) -> ~ (T + t_stats + 40 <= a < T + t_stats + 56) -> ~ WIND a /\ 0 <= a < 2 ^ 64).
{ intros a Ha N1 N2 N3. unfold AFf7.WIND, AFf6.WINA. fold sp0. split; [tauto | exact Ha]. }
assert (XFER : forall a (w : nat) x, val_mem tfibsegs m0 a w x -> (forall kk, (kk < w)%nat -> ~ WIND (a + Z.of_nat kk) /\ 0 <= a + Z.of_nat kk < 2 ^ 64) ->
val_mem tfibsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv Hout. apply (val_mem_frame (w_H W) mem memD); [|exact Hv]. intros kk Hkk. apply MQD. destruct (Hout kk Hkk) as [O1 O2]. rewrite unsigned_lit_small by exact O2. exact O1. }
assert (PXFER : forall a, apresent H0 mem a -> ~ WIND a /\ 0 <= a < 2 ^ 64 -> apresent H0 memD a).
{ intros a Hp [Ho Ha]. apply (apresent_same (w_H W) mem); [apply MQD; rewrite unsigned_lit_small by exact Ha; exact Ho | exact Hp]. }
assert (XI : forall a (w : nat) x, val_mem tfibsegs m0 a w x -> TFIB_IMG_LO <= a -> a + Z.of_nat w <= TFIB_IMG_END -> (a + Z.of_nat w <= A_ALLOCATOR + 680 \/ A_ALLOCATOR + 684 <= a) -> val_mem tfibsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2 H3. apply XFER; [exact Hv|]. intros kk Hkk. apply OUTD; clear - Hkk H1 H2 H3 Hlo hS1 hT1; numconst; lia. }
assert (XM : forall a (w : nat) x, val_mem tfibsegs m0 a w x -> MAP <= a -> a + Z.of_nat w <= MAP + LEN -> val_mem tfibsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. apply XFER; [exact Hv|]. intros kk Hkk. destruct (MT (a + Z.of_nat kk) ltac:(lia)); (apply OUTD; clear - Hkk H1 H2 H Hlo hS1 hCE M1 M2; numconst; lia). }
assert (PM : forall a, MAP <= a < MAP + 32 -> apresent H0 memD a).
{ intros a Ha. apply PXFER; [apply HPm; exact Ha|]. destruct (MT a ltac:(lia)); (apply OUTD; clear - Ha H Hlo hS1 hCE M1 M2 M4; numconst; lia). }
assert (XQ : forall a (w : nat) x, val_mem tfibsegs m0 a w x -> Q <= a -> a + Z.of_nat w <= Q + kPtrArrayResv -> val_mem tfibsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. apply XFER; [exact Hv|]. intros kk Hkk. destruct (QT (a + Z.of_nat kk) ltac:(lia)); (apply OUTD; clear - Hkk H1 H2 H Hlo hS1 hCE hQ1 hQ2; numconst; lia). }
assert (PQ : forall a, Q <= a < Q + kPtrArrayResv -> apresent H0 mem a -> apresent H0 memD a).
{ intros a Ha Hp. apply PXFER; [exact Hp|]. destruct (QT a Ha); (apply OUTD; clear - Ha H Hlo hS1 hCE hQ1 hQ2; numconst; lia). }
assert (XL : own = false -> val_mem tfibsegs (mrestrict H0 memD) (lst + 24) 8 (nA - 1) /\ (forall a, lst + 24 <= a < lst + 32 -> apresent H0 memD a)).
{ intros Ho. split.
- apply XFER; [exact L24|]. intros kk Hkk. destruct LT as [D' _]. apply OUTD; clear - Hkk D' Hlo hS1 hCE LL1 LL2; numconst; lia.
- intros a Ha. apply PXFER; [apply L24P; exact Ha|]. destruct LT as [D' _]. apply OUTD; clear - Ha D' Hlo hS1 hCE LL1 LL2; numconst; lia. }
assert (XTI : forall a (w : nat) x, val_mem tfibsegs m0 a w x -> T + t_stats + 56 <= a -> a + Z.of_nat w <= T + kThreadObjSize -> val_mem tfibsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. apply XFER; [exact Hv|]. intros kk Hkk. apply OUTD; clear - Hkk H1 H2 Hlo hS1 hCE hT1 hT2; numconst; lia. }
assert (XC : forall a (w : nat) x, val_mem tfibsegs m0 a w x -> ly_C ly <= a -> a + Z.of_nat w <= ly_C ly + 256 -> val_mem tfibsegs (mrestrict H0 memD) a w x).
{ intros a w x Hv H1 H2. apply XFER; [exact Hv|]. intros kk Hkk. destruct (CT (a + Z.of_nat kk) ltac:(lia)); (apply OUTD; clear - Hkk H1 H2 H Hlo hS1 hCE hC1 hC2; numconst; lia). }
assert (USD : bv_unsigned (getr regsD 2) = sp0) by (rewrite D2; reflexivity).
assert (XTP : getr regsD 4 = w64 TFIB_TP) by (rewrite (DSR 4%bv ltac:(inS)), Htp, (ts_tp _ TB); reflexivity).
pose proof (Uv 1%bv) as U1. pose proof (Uv 8%bv) as U8. pose proof (Uv 9%bv) as U9. pose proof (Uv 18%bv) as U18.
assert (Y1 : val_mem tfibsegs (mrestrict H0 memD) MAP 8 MAP) by (apply XM; [exact H1v | lia | cbn; lia]).
assert (Y2 : val_mem tfibsegs (mrestrict H0 memD) (MAP + 8) 8 LEN) by (apply XM; [exact H2v | lia | cbn; lia]).
assert (Y3 : val_mem tfibsegs (mrestrict H0 memD) (MAP + 24) 8 idx) by (apply XM; [exact H4v | lia | cbn; lia]).
assert (Y4 : val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 72) 8 Q) by (apply XI; [exact I3 | clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; lia]).
assert (Y5 : val_mem tfibsegs (mrestrict H0 memD) qi 8 MAP) by (unfold AFg8.qi, AFg8.idx; apply XQ; [exact QIV | lia | cbn; clear - A4 A5; numconst; lia]).
assert (Y6 : val_mem tfibsegs (mrestrict H0 memD) ql 8 lst) by (unfold ql; apply XQ; [exact QLV | lia | cbn; clear - A4 A5; numconst; lia]).
assert (Y7 : val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 120) 8 nA) by (apply XI; [exact I4 | clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; lia]).
assert (Y8 : val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 144) 8 ji1 /\ val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 152) 8 ji2 /\
val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 704) 8 ji3 /\ val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 712) 8 ji4).
{
splits; [ apply XI; [exact JV1 | clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; lia]
| apply XI; [exact JV2 | clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; lia]
| apply XI; [exact JV3 | clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; lia]
| apply XI; [exact JV4 | clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; lia] ]. }
destruct Y8 as (Y8a & Y8b & Y8c & Y8d).
assert (Y9 : val_mem tfibsegs (mrestrict H0 memD) TFIB_TSD 8 (ly_C ly) /\ val_mem tfibsegs (mrestrict H0 memD) (ly_C ly + 8) 4 0 /\ val_mem tfibsegs (mrestrict H0 memD) (ly_C ly + 152) 8 T).
{ splits; [apply XI; [exact T4 | clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; numconst; lia] | apply XC; [exact T5 | lia | cbn; lia] | apply XC; [exact T6 | lia | cbn; lia]]. }
destruct Y9 as (Y9a & Y9b & Y9c).
assert (Y10 : val_mem tfibsegs (mrestrict H0 memD) (T + t_stats + 88) 8 j5 /\ val_mem tfibsegs (mrestrict H0 memD) (T + t_stats + 96) 8 j6).
{ split; [ apply XTI; [exact JV5 | clear; numconst; lia | clear; cbn; numconst; lia] | apply XTI; [exact JV6 | clear; numconst; lia | clear; cbn; numconst; lia] ]. }
destruct Y10 as [Y10a Y10b].
assert (TJP : forall a, T + t_stats + 88 <= a < T + t_stats + 104 -> apresent H0 memD a).
{ intros a Ha. apply PXFER; [apply TPRES; clear - Ha; numconst; lia|]. apply OUTD; clear - Ha Hlo hS1 hCE hT1 hT2; numconst; lia. }
assert (YK : val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 64) 8 4096 /\ val_mem tfibsegs (mrestrict H0 memD) 0xa5860 1 1 /\ val_mem tfibsegs (mrestrict H0 memD) 0xa5864 4 0 /\
val_mem tfibsegs (mrestrict H0 memD) (TFIB_TP - 88) 8 TFIB_TSD /\
val_mem tfibsegs (mrestrict H0 memD) 0x9df88 8 0x137b28 /\ val_mem tfibsegs (mrestrict H0 memD) 0x137ba0 8 0xffffffffffffffff /\ val_mem tfibsegs (mrestrict H0 memD) 0x137bb8 8 0 /\
val_mem tfibsegs (mrestrict H0 memD) 0x9df98 8 0xa5ff8 /\ val_mem tfibsegs (mrestrict H0 memD) 0xa5ff8 8 0x7fff8000 /\
val_mem tfibsegs (mrestrict H0 memD) 0x9dfa0 8 0xa6ce8 /\ val_mem tfibsegs (mrestrict H0 memD) 0x9dfa8 8 0xa6cf0 /\ val_mem tfibsegs (mrestrict H0 memD) 0x9dfb0 8 0xa6ce0 /\
val_mem tfibsegs (mrestrict H0 memD) 0xa6ce0 8 0x7fffffffffff /\ val_mem tfibsegs (mrestrict H0 memD) 0xa6ce8 8 0 /\ val_mem tfibsegs (mrestrict H0 memD) 0xa6cf0 8 0 /\
val_mem tfibsegs (mrestrict H0 memD) 0x9dfb8 8 0x9fe28 /\ val_mem tfibsegs (mrestrict H0 memD) 0x9fe28 8 0x97698 /\
val_mem tfibsegs (mrestrict H0 memD) 0x9df78 8 0x135aa0 /\ val_mem tfibsegs (mrestrict H0 memD) 0x135aa0 8 4096 /\ val_mem tfibsegs (mrestrict H0 memD) 0x9dfd8 8 1).
{ splits; (apply XI; [ first [exact I1 | exact I2 | exact I3 | exact I4 | exact T1 | exact T2 | exact T3 | exact T4 | exact K1 | exact K2 | exact K3 | exact K4 | exact K5 | exact K6 | exact K7 | exact K8
| exact K9 | exact K10 | exact K11 | exact K12 | exact K13 | exact K14 | exact K15 | exact K16]
| clear; numconst; lia | clear; cbn; numconst; lia | clear; cbn; numconst; lia]). }
destruct YK as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18 & Z19 & Z20).
constructor.
- exact (am_layout B ly X rd0 M).
- exact (AFfc.IMG B ly X k cbp W regs mem md PRE).
- exact XTP.
- unfold AFf6.v, w64. rewrite Z_to_bv_bv_unsigned. exact Hra.
- splits; [exact D10 | exact D11 | exact D12 | exact D1 | exact D8 | exact D9 | exact D18].
- rewrite USD. split; [exact Hlo | clear - Hcb1 Hcb2; lia].
- rewrite USD. exact Hal.
- rewrite USD. intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [LOW|HI'].
+ apply PXFER; [apply HPRES; lia|]. apply OUTD; clear - Ha LOW Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2; numconst; lia.
+ apply DPRS. lia.
- clear - U1 U8 U9 U18. unfold AFf6.v in *. splits; lia.
- split; [exact M1|]. cbn. clear - M2 M3 M4 M5 L19. destruct small; (splits; try assumption; lia).
- pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 2%nat _ eq_refl) as DT.
pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 6%nat _ eq_refl) as DC.
pose proof (AFfc.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _).
unfold zdisjoint in DT, DC. cbn [fst snd] in DT, DC. unfold AFf4.MAP, AFf4.LEN in DT, DC. rewrite <- E in DT, DC.
unfold AFg8.MAP. clear - DT DC. unfold kThreadObjSize in *. split; lia.
- splits; [exact Y1 | exact Y2 | exact Y3 | exact PM].
- unfold AFg8.qi, ql. splits; try reflexivity; try assumption.
+ clear - A5. unfold AFg8.idx. lia.
+ clear - A5. unfold AFg8.idx. lia.
+ clear - A4. lia.
+ pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 1%nat _ eq_refl) as DQ.
pose proof (AFfc.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _).
unfold zdisjoint in DQ. cbn [fst snd] in DQ. unfold AFf4.MAP, AFf4.LEN in DQ. rewrite <- E in DQ.
unfold AFg8.MAP. clear - DQ. lia.
- exact Y4.
- split; [exact Y5|]. intros a Ha. unfold AFg8.qi, AFg8.idx in Ha. apply PQ; [clear - Ha A4 A5; numconst; lia | apply QIP; exact Ha].
- intros Ho. split; [exact Y6|]. intros a Ha. unfold ql in Ha. apply PQ; [clear - Ha A4 A5; numconst; lia | apply QLP; exact Ha].
- splits; assumption.
- exact LOWN.
- intros Ho. exact (proj2 (XL Ho)).
- exact Y7.
- splits; first [assumption | clear - JR1 JR2 JR3 JR4; lia].
- exact DMUT.
- splits; assumption.
- splits; [exact Y10a | exact Y10b | | | | | exact TJP]; clear - JR5 JR6; lia.
- intros a Ha. apply PXFER; [apply SHP; exact Ha|]. apply OUTD; unfold SHAv, CNTv in Ha; clear - Ha Hlo hS1 hCE hT1 M1 M2 M4; numconst;
pose proof (Z.div_pos MAP 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_mono _ _ 8 ltac:(lia) M2); Z.div_mod_to_equations; lia.
-
pose proof hI1 as J1'. pose proof hI2 as J2'. rewrite hIE in J1', J2'.
pose proof HPRES as HPRES'. clear XFER XI XM XQ XTI XC HPRES MQD H1v H2v H4v HPm T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 JV1 JV2 JV3 JV4 JV5 JV6 QLV QLP L24 L24P QIV
K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 SHP TPRES hI1 hI2 hIE MT MC CT.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, KSTACK, kLowMemEnd, TFIB_INST in hP1, hP2, hQ1, hQ2, hT1, hT2, hC1, hC2, hS1, hS2, hCE, hSP1, hSP2, Hlo, J1', J2', M1, M2, M4, LL1, LL2, L19, QT, LT, MQ.
rewrite restrict_mkst_fx. unfold AFgv.SS0, AFgv.SR0, sr_set. cbn [bv_eqb]. unfold AFgv.E0, w64. apply (entry_st_ok_full tfibsegs).
+ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact XTP]
| intros XX; discriminate | cbn [sv_denot]; exact D10]
| intros XX; discriminate | cbn [sv_denot]; exact D11]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite AFgv.EqMAP, D12; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite AFgv.EqRA, D1; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite AFgv.EqS0, D8; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite AFgv.EqS1, D9; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2); rewrite AFgv.EqS2, D18; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia].
+ destruct own; vm_compute; reflexivity.
+
cbn [ms_mem mkst]. fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2).
assert (SHB : 2147450880 = SHADOW_OFF) by reflexivity.
unfold AFgv.REG0, AFgv.COMMON. apply Forall_cons; [|apply Forall_app; split].
{   unfold AFgv.R_MAPH. reg_intro. rewrite AFgv.EqMAP. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [destruct own; lia|]. split.
{ intros o' Ho'. apply apresent_writable_off; [apply (zone3_off_img _ _ _ ZM3); destruct own; lia|]. apply PM. destruct own; lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atomd _ _ _ _ 8 34%nat 0 MAP); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact Y1 | r8 | cbn; lia].
- apply (chunk_atomd _ _ _ _ 8 35%nat 0 LEN); [rewrite Z.sub_0_r; reflexivity | lia | exact Y2 | r8 | cbn; lia].
- apply (chunk_atomd _ _ _ _ 8 36%nat 0 idx); [rewrite Z.sub_0_r; reflexivity | unfold AFg8.idx in *; lia | exact Y3 | unfold AFg8.idx in *; r8 | cbn; lia]. }
{ unfold AFgv.R_STK, AFgv.R_MW0, AFgv.R_NS, AFgv.R_J12, AFgv.R_J34, AFgv.R_QI, AFgv.R_CTX, AFgv.R_JST, flit1, flit4, flit8, fatom8.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs _ _ 2 sp0 (- GDEPTH)); [rewrite AFgv.E2; exact USD | unfold GDEPTH; lia | lia |].
intros a Ha. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, GDEPTH in *; lia|]. destruct (Z_lt_le_dec a (sp0 - 80)) as [LOW|HI'].
- apply PXFER; [apply HPRES'; unfold GDEPTH, KSTACK in *; lia|]. apply OUTD; clear - Ha LOW Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2; numconst; lia.
- apply DPRS. lia. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; apply rw_writable; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero_mb. intros z Hz. cbn [YP09.c_off] in Hz |- *.
pose proof (DMUT (Z.to_nat z) ltac:(lia)) as E0. rewrite Z2Nat.id in E0 by lia. rewrite le_byte_zero in E0. unfold A_ALLOCATOR in E0. rewrite Z.add_0_l. exact E0. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; apply rw_writable; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atomd _ _ 0 _ 8 37%nat 0 nA); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact Y7 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; apply rw_writable; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atomd _ _ 0 _ 8 42%nat 0 ji1); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact Y8a | r8 | cbn; lia].
- apply (chunk_atomd _ _ 0 _ 8 43%nat 0 ji2); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact Y8b | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; apply rw_writable; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atomd _ _ 0 _ 8 44%nat 0 ji3); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact Y8c | r8 | cbn; lia].
- apply (chunk_atomd _ _ 0 _ 8 45%nat 0 ji4); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact Y8d | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. rewrite AFgv.EqQI. unfold w64. rewrite unsigned_lit_small by (unfold AFg8.qi, AFg8.idx; lia).
unfold AFg8.qi, AFg8.idx in *.
split; [lia|]. split; [lia|]. split.
{ intros o' Ho'. apply apresent_writable_off; [apply (zone3_off_img _ _ _ ZQ3); unfold kPtrArrayResv; clear - Ho' A4 A5; lia|]. apply PQ; [unfold kPtrArrayResv; clear - Ho' A4 A5; lia|]. apply QIP. lia. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atomd _ _ _ _ 8 34%nat 0 MAP); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact Y5 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. rewrite AFgv.EqC. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_litd_at; [exact Y9b | cbn; lia | cbn; lia].
- apply (chunk_atomd _ _ _ _ 8 32%nat 0 T); [rewrite AFgv.EqT; unfold w64; f_equal; lia | lia | exact Y9c | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. rewrite AFgv.EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o' Ho'. apply apresent_writable_off; [apply (zone3_off_img _ _ _ ZT3); unfold t_stats, kThreadObjSize in *; lia|]. apply TJP. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atomd _ _ _ _ 8 46%nat 0 j5); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact Y10a | lia] | r8 | cbn; lia].
- apply (chunk_atomd _ _ _ _ 8 47%nat 0 j6); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact Y10b | lia] | r8 | cbn; lia]. }
apply Forall_cons; [lit_region Z1|].
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomd _ _ 0 _ 8 38%nat 0 Q); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact Y4 | r8 | cbn; lia]. }
apply Forall_cons; [lit_region Z5|]. apply Forall_cons; [lit_region Z6|]. apply Forall_cons; [lit_region Z7|]. apply Forall_cons; [lit_region Z8|].
apply Forall_cons.
{   reg_intro. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomd _ _ 0 _ 8 48%nat 0 SHADOW_OFF); [rewrite Z.sub_0_r; reflexivity | clear; numconst; lia | rewrite Z.add_0_l, <- SHB; exact Z9 | clear; numconst; cbn; lia | cbn; lia]. }
apply Forall_cons; [lit_region Z10|]. apply Forall_cons; [lit_region Z11|]. apply Forall_cons; [lit_region Z12|]. apply Forall_cons; [lit_region Z13|].
apply Forall_cons; [lit_region Z14|]. apply Forall_cons; [lit_region Z15|]. apply Forall_cons; [lit_region Z16|]. apply Forall_cons; [lit_region Z17|].
apply Forall_cons; [lit_region Z18|]. apply Forall_cons; [lit_region Z19|]. apply Forall_cons; [lit_region Z20|].
apply Forall_cons; [lit_region Z2|]. apply Forall_cons; [lit_region Z3|].
apply Forall_cons. {   unfold TFIB_TP. lit_region Z4. }
apply Forall_cons; [|apply Forall_nil].
{   reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomd _ _ 0 _ 8 33%nat 0 (ly_C ly)); [rewrite AFgv.EqC; unfold w64; f_equal; lia | lia | rewrite Z.add_0_l; exact Y9a | cbn; lia | cbn; lia]. } }
{
destruct own eqn:EO; [apply Forall_nil|]. destruct (XL eq_refl) as [XL1 XL2].
unfold AFgv.R_LASTH, AFgv.R_QL. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- reg_intro. rewrite AFgv.EqLAST. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o' Ho'. apply apresent_writable_off; [apply (zone3_off_img _ _ _ ZL3); lia|]. apply XL2. lia.
- reg_intro. rewrite AFgv.EqQL. unfold w64. unfold ql in *. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomd _ _ _ _ 8 41%nat 0 lst); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact Y6 | r8 | cbn; lia]. }
+
fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2).
pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 2%nat _ eq_refl) as DT.
pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 6%nat _ eq_refl) as DC.
pose proof (AFf4.MAPX B ly X rd0 M k r o sm (AFfc.Hk B ly X k cbp W regs mem md PRE) Hb Hsm 1%nat _ eq_refl) as DQ.
pose proof (AFfc.ELEN B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (E & _).
unfold zdisjoint in DT, DC, DQ. cbn [fst snd] in DT, DC, DQ. unfold AFf4.MAP, AFf4.LEN in DT, DC, DQ. rewrite <- E in DT, DC, DQ. fold (AFg8.MAP ly r) in DT, DC, DQ. clear E.
pose proof (AFf4.SX B ly X rd0 M 6%nat 2%nat _ _ eq_refl eq_refl ltac:(lia)) as CT0. pose proof (AFf4.SX B ly X rd0 M 1%nat 2%nat _ _ eq_refl eq_refl ltac:(lia)) as QT0.
pose proof (AFf4.SX B ly X rd0 M 1%nat 6%nat _ _ eq_refl eq_refl ltac:(lia)) as QC0. unfold zdisjoint in CT0, QT0, QC0. cbn [fst snd] in CT0, QT0, QC0.
destruct LT as (LT1 & LT2 & LT3).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, KSTACK, kLowMemEnd, TFIB_INST in DT, DC, DQ, CT0, QT0, QC0, LT1, LT2, LT3, LOWN.
destruct own eqn:EO.
* apply pairwise_disjoint_of_extents.
unfold AFgv.REG0, AFgv.COMMON, AFgv.R_MAPH, AFgv.R_STK, AFgv.R_MW0, AFgv.R_NS, AFgv.R_J12, AFgv.R_J34, AFgv.R_QI, AFgv.R_CTX, AFgv.R_JST, flit1, flit4, flit8, fatom8, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite AFgv.E2, USD, AFgv.EqMAP, AFgv.EqQI, AFgv.EqC, AFgv.EqT. unfold w64. unfold AFg8.qi, AFg8.idx in *.
clear - Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2 hC1 hC2 hQ1 hQ2 M1 M2 M4 A4 A5 J1' J2' DT DC DQ CT0 QT0 QC0. numconst. rewrite !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [clear DT DC DQ CT0 QT0 QC0; lia | clear DC DQ CT0 QT0 QC0; lia | clear DT DQ CT0 QT0 QC0; lia | clear DT DC CT0 QT0 QC0; lia | clear DT DC DQ QT0 QC0; lia | clear DT DC DQ CT0 QC0; lia | clear DT DC DQ CT0 QT0; lia | lia].
* pose proof LOWN as LOWN'. apply pairwise_disjoint_of_extents.
unfold AFgv.REG0, AFgv.COMMON, AFgv.R_MAPH, AFgv.R_STK, AFgv.R_MW0, AFgv.R_NS, AFgv.R_J12, AFgv.R_J34, AFgv.R_QI, AFgv.R_CTX, AFgv.R_JST,
AFgv.R_LASTH, AFgv.R_QL, flit1, flit4, flit8, fatom8, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite AFgv.E2, USD, AFgv.EqMAP, AFgv.EqQI, AFgv.EqC, AFgv.EqT, AFgv.EqLAST, AFgv.EqQL. unfold w64. unfold AFg8.qi, AFg8.idx, ql in *.
assert (NEI : Z.of_nat i <> nA - 1) by (unfold AFg8.own, AFg8.idx in EO; apply Z.eqb_neq in EO; exact EO).
clear - Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2 hC1 hC2 hQ1 hQ2 M1 M2 M4 A4 A5 J1' J2' LL1 LL2 NEI DT DC DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'. numconst. rewrite !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [clear DT DC DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; lia | clear DC DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; lia | clear DT DQ CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; lia
| clear DT DC CT0 QT0 QC0 LT1 LT2 LT3 LOWN'; lia | clear DT DC DQ QT0 QC0 LT1 LT2 LT3 LOWN'; lia | clear DT DC DQ CT0 QC0 LT1 LT2 LT3 LOWN'; lia
| clear DT DC DQ CT0 QT0 LT1 LT2 LT3 LOWN'; lia | clear DT DC DQ CT0 QT0 QC0 LT2 LT3 LOWN'; lia | clear DT DC DQ CT0 QT0 QC0 LT1 LT3 LOWN'; lia
| clear DT DC DQ CT0 QT0 QC0 LT1 LT2 LOWN'; lia | clear DT DC DQ CT0 QT0 QC0 LT1 LT2 LT3; lia | lia].
+
fold (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2). split; [|split; exact I].
assert (AF : forall k0 Xv lo hi al, ew (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew (E0d regsD MAP LEN idx nA Q qi ql lst ji1 ji2 ji3 ji4 j5 j6 vra vs0 vs1 vs2) 2 = w64 sp0) by (rewrite AFgv.E2, D2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (HSA : 2147451392 <= SHAv MAP /\ SHAv MAP + CNTv LEN <= 17594332446720 /\ SHAv MAP mod 2 ^ 9 = 0 /\ CNTv LEN mod 2 ^ 9 = 0 /\ 1024 <= CNTv LEN < 2 ^ 26 /\ (SHEv MAP LEN) mod 2 ^ 9 = 0 /\
(if small then CNTv LEN <= 2 ^ 26 - 512 else 65536 <= CNTv LEN)).
{ unfold SHAv, CNTv, SHEv, SHAv, CNTv. clear - M1 M2 M3 M4 M5 L19. numconst. change (2 ^ 9) with 512.
apply Z.mod_divide in M3 as [q Hq]; [|lia]. apply Z.mod_divide in M5 as [q' Hq']; [|lia]. rewrite Hq, Hq' in *.
replace (q * 4096 / 8) with (q * 512) by (Z.div_mod_to_equations; lia). replace (q' * 4096 / 8) with (q' * 512) by (Z.div_mod_to_equations; lia).
splits; try (Z.div_mod_to_equations; lia);
try ((apply Z.mod_divide; [lia|]); first [exists (4194240 + q); lia | exists q'; lia | exists (4194240 + q + q'); lia]).
destruct small; Z.div_mod_to_equations; lia. }
destruct HSA as (SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7).
cbn [AFgv.FFD f_atoms atoms_ok]. unfold AFg8.qi, AFg8.idx, ql in *. numconst.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Hlo Hcb1 Hcb2 hS1 hS2 hCE Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [reflexivity| | | |]. all: clear - CR0 hT1 hT2 hTAL; first [lia | change (2 ^ 12) with 4096; exact hTAL]. }
split. { apply (AF 33%nat (ly_C ly)); [reflexivity| | | |]. all: clear - CR0 hC1 hC2 hCAL; first [lia | change (2 ^ 3) with 8; exact hCAL]. }
split. { apply (AF 34%nat MAP); [reflexivity| | | |]. all: clear - CR0 M1 M2 M3 M4; first [lia | change (2 ^ 12) with 4096; exact M3]. }
split. { clear - AF M4 M5 L19. destruct small; (apply (AF 35%nat LEN); [reflexivity| | | |]); first [Z.div_mod_to_equations; lia | change (2 ^ 12) with 4096; exact M5]. }
split. { apply (AF 36%nat (Z.of_nat i)); [reflexivity| | | |]. all: clear - A4 A5; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat nA); [reflexivity| | | |]. all: clear - A4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat Q); [reflexivity| | | |]. all: clear - CR0 hQ1 hQ2 hQAL; first [lia | change (2 ^ 12) with 4096; exact hQAL]. }
split. { apply (AF 39%nat (Q + 8 * Z.of_nat i)); [reflexivity| | | |]. all: clear - CR0 hQ1 hQ2 hQAL A4 A5; first [lia | apply Z.mod_divide in hQAL as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (q * 512 + Z.of_nat i); change (2 ^ 3) with 8; lia]. }
split. { apply (AF 40%nat (Q + 8 * (nA - 1))); [reflexivity| | | |]. all: clear - CR0 hQ1 hQ2 hQAL A4 A5; first [lia | apply Z.mod_divide in hQAL as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (q * 512 + (nA - 1)); change (2 ^ 3) with 8; lia]. }
split. { apply (AF 41%nat lst); [reflexivity| | | |]. all: clear - CR0 LL1 LL2 LL3; first [lia | change (2 ^ 12) with 4096; exact LL3]. }
split. { apply (AF 42%nat ji1); [reflexivity| | | |]. all: clear - JR1; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 43%nat ji2); [reflexivity| | | |]. all: clear - JR2; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 44%nat ji3); [reflexivity| | | |]. all: clear - JR3; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 45%nat ji4); [reflexivity| | | |]. all: clear - JR4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 46%nat j5); [reflexivity| | | |]. all: clear - JR5; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 47%nat j6); [reflexivity| | | |]. all: clear - JR6; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 48%nat SHADOW_OFF); [reflexivity| | | |]. all: clear; unfold SHADOW_OFF; first [lia | reflexivity]. }
split. { apply (AF 49%nat (SHAv MAP)); [reflexivity| | | |]. all: clear - SA1 SA2 SA3 SA5; first [lia | exact SA3]. }
split. { clear - AF SA4 SA5 SA7. destruct small; (apply (AF 50%nat (CNTv LEN)); [reflexivity| | | |]); first [lia | exact SA4]. }
split. { apply (AF 51%nat vra); [reflexivity| | | |]. all: clear - U1; unfold AFf6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 52%nat vs0); [reflexivity| | | |]. all: clear - U8; unfold AFf6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 53%nat vs1); [reflexivity| | | |]. all: clear - U9; unfold AFf6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 54%nat vs2); [reflexivity| | | |]. all: clear - U18; unfold AFf6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 55%nat (SHEv MAP LEN)); [reflexivity| | | |]. all: unfold SHEv in *; clear - SA1 SA2 SA5 SA6; first [lia | exact SA6]. }
Qed.
End c.
End b.
