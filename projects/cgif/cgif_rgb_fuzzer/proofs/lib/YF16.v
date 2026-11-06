(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1g YF0x YF0y YF19 YF2p YF2s YF2q YF23 YF07.
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
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFX_IMG_END, kBatchBytes, SHADOW_OFF, TFX_TP, TFX_TSD, TFX_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, YF2p.GFRAME, YF2s.GFRAME, GDEPTH in *.
Section f. Context {imgk : img}.
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
Local Notation arr := (st_sec_arr X).
Local Notation MAP := (YF23.MAP ly r).
Local Notation LEN := (YF23.LEN sm).
Local Notation nA := (YF23.nA X).
Definition hdr : Z := ck_base B ly k + ck_rz k - kChunkHeaderSize.
Definition hb1 : Z := match rd0 (hdr + 1) with Some b => b | None => 0 end.
Definition HWv : Z := 3 + 256 * hb1.
Definition jw (a : Z) : Z := match rdword rd0 a with Some w => w | None => 0 end.
Definition j1 : Z := jw (T + t_stats + 40).
Definition j2 : Z := jw (T + t_stats + 48).
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Lemma IMG : img_cover ly.
Proof. img_exact (img_cover_of_ledger ly X md (proj1 (proj2 (proj1 PRE)))). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hci : st_cache_inited X = true. Proof. img_exact (proj1 (proj2 PRE)). Qed.
Lemma Hk : In k (st_chunks X). Proof. img_exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. img_exact (proj1 (proj2 (proj2 (proj2 PRE)))). Qed.
Lemma Hni : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. img_exact (proj1 (proj2 (proj2 (proj2 (proj2 PRE))))). Qed.
Lemma KF : cfacts B ly X k. Proof. img_exact (chunk_facts B ly X rd0 k M Hk). Qed.
Lemma AINST : as_inst B = A_ALLOCATOR. Proof. rewrite (ts_inst _ TB). img_refl. Qed.
Lemma HSP : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma Hci' : st_cache_inited X = true. Proof. img_exact Hci. Qed.
Lemma ELEN : LEN = sec_map_size (ck_req k) /\ o = kPage /\ sm_live sm = true.
Proof.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [Hn CK].
rewrite Hb in CK. destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
unfold YF23.LEN. repeat split; assumption.
Qed.
Lemma GEOM : zone3 MAP LEN /\ MAP + LEN <= ASAN_CEIL /\ MAP mod 4096 = 0 /\ 8192 <= LEN < 2 ^ 29 /\ LEN mod 4096 = 0 /\
ck_base B ly k = MAP + kPage /\ ck_extent k = LEN - kPage.
Proof.
pose proof ELEN as (E & _). rewrite E. img_exact (YF0y.geom B ly X rd0 M k r o Hk Hb IMG).
Qed.
Lemma RZ : ck_rz k = 2048.
Proof.
pose proof KF as (_ & _ & _ & _ & _ & _ & RQ & _ & CK). rewrite Hb in CK. destruct CK as (_ & FP & _).
unfold ck_rz. unfold from_primary, needed_primary, rounded_size, round_up, kMaxSize in FP. apply Z.leb_gt in FP.
unfold rz_size, rz_log in *.
destruct (ck_req k <=? 48) eqn:C0. { exfalso. apply Z.leb_le in C0. img_change (Z.shiftl 16 0) with 16 in FP. clear - FP C0 RQ. img_lia. }
destruct (ck_req k <=? 96) eqn:C1. { exfalso. apply Z.leb_le in C1. img_change (Z.shiftl 16 1) with 32 in FP. clear - FP C1 RQ. img_lia. }
destruct (ck_req k <=? 448) eqn:C2. { exfalso. apply Z.leb_le in C2. img_change (Z.shiftl 16 2) with 64 in FP. clear - FP C2 RQ. img_lia. }
destruct (ck_req k <=? 3968) eqn:C3. { exfalso. apply Z.leb_le in C3. img_change (Z.shiftl 16 3) with 128 in FP. clear - FP C3 RQ. img_lia. }
destruct (ck_req k <=? 16128) eqn:C4. { exfalso. apply Z.leb_le in C4. img_change (Z.shiftl 16 4) with 256 in FP. clear - FP C4 RQ. img_lia. }
destruct (ck_req k <=? 32256) eqn:C5. { exfalso. apply Z.leb_le in C5. img_change (Z.shiftl 16 5) with 512 in FP. clear - FP C5 RQ. img_lia. }
destruct (ck_req k <=? 64512) eqn:C6. { exfalso. apply Z.leb_le in C6. img_change (Z.shiftl 16 6) with 1024 in FP. clear - FP C6 RQ. img_lia. }
img_refl.
Qed.
Lemma hdr_facts : hdr = MAP + 6128 /\ 1 <= ck_n k < 2 ^ 28 /\ hdr + 16 + ck_n k <= MAP + LEN /\ hdr mod 16 = 0 /\ 0 <= ck_req k < MALLOC_MAX.
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & M6 & M7). pose proof RZ as R.
unfold hdr, ck_n, req_size. rewrite M6, R. unfold req_size in G8. rewrite R, M7 in G8.
split; [img_try (unfold kPage, kChunkHeaderSize; img_lia)|]. split; [img_try (destruct (Z.eqb_spec (ck_req k) 0); unfold MALLOC_MAX in *; img_lia)|].
split; [img_try (unfold kPage, kChunkHeaderSize in *; destruct (Z.eqb_spec (ck_req k) 0); img_lia)|].
split; [| img_try (img_exact G7)]. apply Z.mod_divide in M3 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (q * 256 + 383). unfold kPage, kChunkHeaderSize. img_lia.
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 Q kPtrArrayResv /\ Q + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ ASAN_CEIL <= ly_stk_lo ly /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ SB mod 65536 = 0 /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\ as_inst B = TFX_INST /\
Q mod 4096 = 0 /\ T mod 4096 = 0 /\ ly_C ly mod 8 = 0 /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\ (ly_C ly + 256 <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= ly_C ly) /\
(Q + kPtrArrayResv <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= Q) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\ (T + kThreadObjSize <= Q \/ Q + kPtrArrayResv <= T) /\ (ly_C ly + 256 <= Q \/ Q + kPtrArrayResv <= ly_C ly).
Proof.
pose proof (YF0y.HIGH B TB ly X rd0 M IMG) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hN1 & hN2 & hB1 & hB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hI1 & hI2 & hCE & hIE).
pose proof hQ1 as (hQa & hQb & _). pose proof hT1 as (hTa & hTb & _). pose proof hC1 as (hCa & hCb & _).
pose proof (lo_Q_al ly LO) as QAL. pose proof (lo_T_al ly LO) as TAL. pose proof (lo_C_al ly LO) as CAL. pose proof (lo_space_al ly LO) as SAL. unfold page_aligned in QAL, TAL.
pose proof (YF0y.SX B ly X rd0 M) as SX.
pose proof (SX 2%nat 0%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D20. pose proof (SX 6%nat 0%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D60. pose proof (SX 1%nat 0%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D10.
pose proof (SX 2%nat 6%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D26. pose proof (SX 2%nat 1%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D21. pose proof (SX 6%nat 1%nat _ _ eq_refl eq_refl ltac:(img_lia)) as D61.
unfold zdisjoint in *. cbn [fst snd] in *.
repeat match goal with |- _ /\ _ => split end; first [img_exact hQ1 | img_exact hT1 | img_exact hC1 | assumption | img_lia].
Qed.
Lemma ARRF : In r arr /\ (i < length arr)%nat /\ List.NoDup arr /\ 1 <= nA <= 16384 /\ 0 <= Z.of_nat i < nA.
Proof.
pose proof (YF0y.ARR B ly X rd0 M r i Hi) as (A1 & A2 & A3 & A4 & A5 & _).
unfold YF23.nA. unfold YF0y.nA, YF0y.arr, YF0y.idx in A1, A2, A3, A4, A5. splits; first [img_exact A1 | img_exact A2 | img_exact A3 | img_lia].
Qed.
Lemma slot_geom : forall j rj, nth_error arr j = Some rj ->
exists y, In y (st_chunks X) /\ ck_beg y = PSec rj kPage /\ In (ly_sec ly rj, sec_map_size (ck_req y)) (sec_extents ly X) /\
zone3 (ly_sec ly rj) (sec_map_size (ck_req y)) /\ ly_sec ly rj + sec_map_size (ck_req y) <= ASAN_CEIL /\ ly_sec ly rj mod 4096 = 0 /\ 8192 <= sec_map_size (ck_req y) /\
(ly_sec ly rj <> MAP -> ly_sec ly rj + sec_map_size (ck_req y) <= MAP \/ MAP + LEN <= ly_sec ly rj).
Proof.
intros j rj Hj. pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
destruct (proj1 (Sac rj) (nth_error_In _ _ Hj)) as (y & Hy & Ey). exists y.
pose proof (chunk_facts B ly X rd0 y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Ey in CK. destruct CK as (_ & FP & CB & CE & CI & PA & _).
pose proof (YF0y.ZSEC B ly X rd0 M IMG _ CI) as (I1 & _ & I2). cbn [fst snd] in I1, I2. unfold page_aligned in PA.
assert (SZ : 8192 <= sec_map_size (ck_req y)).
{ unfold sec_map_size, needed_size. rewrite FP. unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req y) + rz_size (ck_req y)) kPage ltac:(img_try (unfold kPage; img_lia))) as [R1 _].
pose proof (rz_size_bounds (ck_req y)) as [RZ' _]. unfold kMaxSize, kPage in *. img_lia. }
splits; try assumption.
intros Hne. assert (Hne' : ck_beg y <> ck_beg k).
{ rewrite Ey, Hb. pose proof ELEN as (_ & -> & _). intros E. injection E as E. img_apply Hne. unfold YF23.MAP. rewrite E. img_refl. }
pose proof (secmaps_disjoint B ly X rd0 y k rj kPage r o M Hy Hk Ey Hb Hne') as DJ. pose proof ELEN as (E & _). unfold YF23.MAP. rewrite E.
unfold zdisjoint in DJ. cbn [fst snd] in DJ. img_exact DJ.
Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfxsegs m0 a w x.
Proof. intros a w x E. img_exact (tfx_const_lookup B TB ly X H0 mem a w x M E). Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfx_const ly) e = Some (ACell e w (AV e')) -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. img_exact (tfx_const_lookup_sym B TB ly X H0 mem e w e' M E). Qed.
Lemma cell_state : forall cc e (w : nat) e', In cc (acells B ly X) -> cc = ACell e w (AV e') -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros cc e w e' Hin ->. img_apply (cell_holds_val_mem B ly H0 mem e w e'). img_exact (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M) _ Hin).
Qed.
Lemma cell_stateZ : forall cc e (w : nat) x, In cc (acells B ly X) -> cc = ACell e w (AV (ANum x)) -> val_mem tfxsegs m0 (aeval B ly e) w x.
Proof. intros cc e w x Hin E. img_exact (cell_state cc e w (ANum x) Hin E). Qed.
Lemma vis_range : forall e len i', In (e, len) (ajunk B ly X) \/ In (e, len) (aareas X) \/ In (e, len) (aclient X) ->
0 <= i' < len -> rd0 (aeval B ly e + i') <> None.
Proof.
intros e len i' Hin Hi'. destruct Hin as [Hin|[Hin|Hin]].
- img_exact (proj1 (Forall_forall _ _) (am_junk B ly X rd0 M) _ Hin i' Hi').
- img_exact (proj1 (Forall_forall _ _) (am_areas B ly X rd0 M) _ Hin i' Hi').
- img_exact (proj1 (Forall_forall _ _) (am_client B ly X rd0 M) _ Hin i' Hi').
Qed.
Lemma sec_In : forall cc, In cc (sec_cells X) -> In cc (acells B ly X).
Proof. intros cc Hcc. unfold acells. rewrite !in_app_iff. do 3 right. left. img_exact Hcc. Qed.
Lemma hdr_In : forall cc, In cc (chunk_cells k) -> In cc (acells B ly X).
Proof. intros cc Hcc. unfold acells. rewrite !in_app_iff. do 2 right. left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk) | img_try (img_exact Hcc)]. Qed.
Lemma EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d.
Proof. intros d. unfold ck_base, sptr_addr. rewrite Hb. cbn. img_lia. Qed.
Lemma EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d'.
Proof. intros d d'. unfold ck_base, sptr_addr. rewrite Hb. cbn. img_lia. Qed.
Lemma inst_vals : val_mem tfxsegs m0 (A_ALLOCATOR + 32) 8 SB /\ val_mem tfxsegs m0 (A_ALLOCATOR + 64) 8 4096 /\
val_mem tfxsegs m0 (A_ALLOCATOR + 72) 8 Q /\ val_mem tfxsegs m0 (A_ALLOCATOR + 120) 8 nA.
Proof.
pose proof AINST as AI. splits.
- replace (A_ALLOCATOR + 32) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite AI; img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply cell_lit. img_case; vm_compute. all: img_refl.
- replace (A_ALLOCATOR + 72) with (aeval B ly (AInst o_sec_chunks)) by (img_try (cbn; rewrite AI; img_refl)).
replace Q with (aeval B ly (AQ 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- replace (A_ALLOCATOR + 120) with (aeval B ly (AInst o_sec_n)) by (img_try (cbn; rewrite AI; img_refl)). unfold YF23.nA.
eapply cell_stateZ; [img_try (img_apply sec_In; unfold sec_cells; right; left; img_refl) | img_refl].
Qed.
Lemma mutex_bytes : forall a, A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684 -> mbyte tfxsegs m0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof AINST as AI.
assert (C1 : val_mem tfxsegs m0 (as_inst B + o_sec_mutex) 1 0).
{ img_apply (cell_stateZ (z1 (AInst o_sec_mutex) 0) (AInst o_sec_mutex) 1 0); [|img_refl]. img_apply sec_In. unfold sec_cells. do 2 right; left. img_refl. }
assert (C2 : val_mem tfxsegs m0 (0xa6e01 + D_10c0) 1 0) by (img_try (img_apply cell_lit; (img_case; vm_compute); img_refl)).
assert (C3 : val_mem tfxsegs m0 (0xa6e02 + D_10c0) 2 0) by (img_try (img_apply cell_lit; (img_case; vm_compute); img_refl)).
rewrite AI in C1. unfold o_sec_mutex, A_ALLOCATOR, TFX_INST in *.
assert (CASES : a = (682840 + D_10c0) + 680 \/ a = (683521 + D_10c0) + Z.of_nat 0 \/ a = (683522 + D_10c0) + Z.of_nat 0 \/ a = (683522 + D_10c0) + Z.of_nat 1) by img_lia.
destruct CASES as [-> |[-> |[-> | ->]]].
- pose proof (C1 0%nat ltac:(img_lia)) as E. rewrite Z.add_0_r in E. img_exact E.
- img_exact (C2 0%nat ltac:(img_lia)).
- img_exact (C3 0%nat ltac:(img_lia)).
- img_exact (C3 1%nat ltac:(img_lia)).
Qed.
Lemma mutex_val : val_mem tfxsegs m0 (A_ALLOCATOR + 680) 4 0.
Proof. intros kk Hkk. rewrite le_byte_zero. img_apply mutex_bytes. img_lia. Qed.
Lemma slot_val : forall j rj, nth_error arr j = Some rj ->
val_mem tfxsegs m0 (Q + 8 * Z.of_nat j) 8 (ly_sec ly rj) /\ (forall a, Q + 8 * Z.of_nat j <= a < Q + 8 * Z.of_nat j + 8 -> apresent H0 mem a).
Proof.
intros j rj Hj. pose proof HI as (_ & _ & hQ1 & hQ2 & _). pose proof ARRF as (_ & _ & _ & A4 & _). pose proof (nth_error_lt _ _ _ Hj) as JL.
assert (V : val_mem tfxsegs m0 (Q + 8 * Z.of_nat j) 8 (ly_sec ly rj)).
{ replace (Q + 8 * Z.of_nat j) with (aeval B ly (AQ (8 * Z.of_nat j))) by img_refl.
replace (ly_sec ly rj) with (aeval B ly (ASec rj 0)) by (img_try (cbn; img_lia)).
eapply cell_state; [|img_refl]. img_apply sec_In. unfold sec_cells. do 3 right. img_apply in_app_iff. left.
img_apply in_map_iff. exists (j, rj). split; [img_refl|]. img_apply YF0y.in_combine_seq0. img_exact Hj. }
split; [img_try (img_exact V)|]. intros a Ha.
assert (JB : Z.of_nat j < nA) by (img_try (unfold YF23.nA; clear - JL; img_lia)).
img_apply vis_apresent_off; [img_try (img_apply (zone3_off_img _ _ _ hQ1); clear - Ha A4 JB; unfold kPtrArrayResv; img_lia)|]. eapply val_mem_vis; [img_try (img_exact V) | img_lia].
Qed.
Lemma maph_vals : val_mem tfxsegs m0 MAP 8 MAP /\ val_mem tfxsegs m0 (MAP + 8) 8 LEN /\ val_mem tfxsegs m0 (MAP + 16) 8 (needed_size (ck_req k)) /\
val_mem tfxsegs m0 (MAP + 24) 8 (Z.of_nat i) /\ (forall a, MAP <= a < MAP + 32 -> apresent H0 mem a).
Proof.
pose proof ELEN as (E & _). pose proof GEOM as (M1 & M2 & M3 & M4 & _). pose proof ARRF as (_ & _ & ND & _).
assert (IN : forall cc, In cc [ c8 (ASec r 0) (ASec r 0); z8 (ASec r 8) (sec_map_size (ck_req k)); z8 (ASec r 16) (needed_size (ck_req k)); z8 (ASec r 24) (index_ofZ (st_sec_arr X) r) ] ->
In cc (acells B ly X)).
{ intros cc Hcc. img_apply sec_In. unfold sec_cells. do 3 right. img_apply in_app_iff. right. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk)|]. rewrite Hb. img_exact Hcc. }
assert (V0 : val_mem tfxsegs m0 MAP 8 MAP).
{ unfold YF23.MAP. replace (ly_sec ly r) with (aeval B ly (ASec r 0)) by (img_try (cbn; img_lia)). eapply cell_state; [img_try (img_apply IN; left; img_refl) | img_refl]. }
assert (V1 : val_mem tfxsegs m0 (MAP + 8) 8 LEN).
{ rewrite E. unfold YF23.MAP. replace (ly_sec ly r + 8) with (aeval B ly (ASec r 8)) by img_refl. eapply cell_stateZ; [img_try (img_apply IN; right; left; img_refl) | img_refl]. }
assert (V2 : val_mem tfxsegs m0 (MAP + 16) 8 (needed_size (ck_req k))).
{ unfold YF23.MAP. replace (ly_sec ly r + 16) with (aeval B ly (ASec r 16)) by img_refl. eapply cell_stateZ; [img_try (img_apply IN; do 2 right; left; img_refl) | img_refl]. }
assert (V3 : val_mem tfxsegs m0 (MAP + 24) 8 (Z.of_nat i)).
{ unfold YF23.MAP. replace (ly_sec ly r + 24) with (aeval B ly (ASec r 24)) by img_refl.
rewrite <- (YF0y.index_ofZ_nth arr i r ND Hi). eapply cell_stateZ; [img_try (img_apply IN; do 3 right; left; img_refl) | img_refl]. }
splits; try assumption.
intros a Ha.
img_apply vis_apresent_off; [img_try (img_apply (zone3_off_img _ _ _ M1); clear - Ha M4; img_lia)|].
destruct (Z_lt_le_dec a (MAP + 8)); [img_try (eapply val_mem_vis; [img_exact V0 | img_lia])|].
destruct (Z_lt_le_dec a (MAP + 16)); [img_try (replace a with (MAP + 8 + (a - (MAP + 8))) by img_lia; eapply val_mem_vis; [img_exact V1 | img_lia])|].
destruct (Z_lt_le_dec a (MAP + 24)); [img_try (replace a with (MAP + 16 + (a - (MAP + 16))) by img_lia; eapply val_mem_vis; [img_exact V2 | img_lia])|].
replace a with (MAP + 24 + (a - (MAP + 24))) by img_lia. eapply val_mem_vis; [img_try (img_exact V3) | img_lia].
Qed.
Lemma hb1_facts : rd0 (hdr + 1) = Some hb1 /\ 0 <= hb1 < 256.
Proof.
assert (C : cell_holds B ly rd0 (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ img_apply (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M)). img_apply hdr_In. unfold chunk_cells. img_apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite EA2 in C.
replace (ck_base B ly k + (ck_rz k - kChunkHeaderSize) + 1) with (hdr + 1) in C by (img_try (unfold hdr; img_lia)).
destruct C as (b & Hb' & Hm). unfold hb1. rewrite Hb'.
destruct (aview_vis_byte H0 mem _ ltac:(img_try (rewrite Hb'; discriminate))) as (b' & E' & R' & _). rewrite Hb' in E'. injection E' as <-. auto.
Qed.
Lemma hw_val : val_mem tfxsegs m0 hdr 4 HWv /\ val_mem tfxsegs m0 (hdr + 4) 4 (ck_n k) /\ (forall a, hdr <= a < hdr + 8 -> apresent H0 mem a) /\ 0 <= HWv < 65536.
Proof.
pose proof hb1_facts as [HB HR]. pose proof hdr_facts as (H1 & _). pose proof GEOM as (M1 & M2 & _ & M4 & _).
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) = hdr) by (img_try (rewrite EA; unfold hdr; img_lia)).
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) d) = hdr + d) by (img_try (intros d; rewrite EA2; unfold hdr; img_lia)).
assert (V0 : val_mem tfxsegs m0 hdr 1 3).
{ rewrite <- EH. eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; left; img_refl)|]. unfold z1, c1, hdr_state. rewrite Hst. img_refl. }
assert (V2 : val_mem tfxsegs m0 (hdr + 2) 2 0).
{ rewrite <- (EH2 2). eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; do 2 right; left; img_refl)|]. img_refl. }
assert (V4 : val_mem tfxsegs m0 (hdr + 4) 4 (ck_n k)).
{ rewrite <- (EH2 4). eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; do 3 right; left; img_refl)|]. img_refl. }
assert (W1 : val_mem tfxsegs m0 hdr 4 HWv).
{ intros i' Hi'. unfold HWv.
assert (LB : forall v (w j : nat), YP0g.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YP0g.le_byte. rewrite Z.shiftr_div_pow2 by img_lia. img_refl. }
destruct i' as [|[|[|[|i']]]]; [| | | |img_lia].
- rewrite (V0 0%nat ltac:(img_lia)). do 2 f_equal. rewrite !LB. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
img_change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- img_change (Z.of_nat 1) with 1. rewrite (aview_byte _ _ _ _ HB). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia.
- replace (hdr + Z.of_nat 2) with (hdr + 2 + Z.of_nat 0) by img_lia. rewrite (V2 0%nat ltac:(img_lia)). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 2)) with 65536. img_change (2 ^ (8 * Z.of_nat 0)) with 1.
rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- replace (hdr + Z.of_nat 3) with (hdr + 2 + Z.of_nat 1) by img_lia. rewrite (V2 1%nat ltac:(img_lia)). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 2)) with 65536.
img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. nia. }
splits; [img_try (img_exact W1) | img_try (img_exact V4) | | img_try (unfold HWv; img_lia) | img_try (unfold HWv; img_lia)].
intros a Ha. img_apply vis_apresent_off; [img_try (img_apply (zone3_off_img _ _ _ M1); pose proof hdr_facts as (_ & D2 & D3 & _); clear - Ha H1 M4 D2 D3; img_lia)|].
destruct (Z_lt_le_dec a (hdr + 4)); [img_try (replace a with (hdr + (a - hdr)) by img_lia; eapply val_mem_vis; [img_exact W1 | img_lia]) | img_try (replace a with (hdr + 4 + (a - (hdr + 4))) by img_lia; eapply val_mem_vis; [img_exact V4 | img_lia])].
Qed.
Lemma tls_vals : val_mem tfxsegs m0 (0xa9a20 + D_10c0) 1 1 /\ val_mem tfxsegs m0 (0xa9a24 + D_10c0) 4 0 /\ val_mem tfxsegs m0 (TFX_TP - 88) 8 TFX_TSD /\
val_mem tfxsegs m0 TFX_TSD 8 (ly_C ly) /\ val_mem tfxsegs m0 (ly_C ly + 8) 4 0 /\ val_mem tfxsegs m0 (ly_C ly + 152) 8 T.
Proof.
splits.
- img_apply cell_lit. img_case; vm_compute. all: img_refl.
- img_apply cell_lit. img_case; vm_compute. all: img_refl.
- replace (TFX_TP - 88) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TB); img_lia)).
replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_lia)). replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- replace (ly_C ly + 8) with (aeval B ly (AC 8)) by img_refl. img_apply (cell_sym (AC 8) 4 (ANum 0)). img_case; vm_compute. all: img_refl.
- replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
Qed.
Lemma const_vals :
val_mem tfxsegs m0 (0xa2150 + D_10f0) 8 (0x13bce8 + D_10c0) /\ val_mem tfxsegs m0 (0x13bd60 + D_10c0) 8 0xffffffffffffffff /\ val_mem tfxsegs m0 (0x13bd78 + D_10c0) 8 0 /\
val_mem tfxsegs m0 (0xa2160 + D_10f0) 8 (0xaa1b8 + D_10c0) /\ val_mem tfxsegs m0 (0xaa1b8 + D_10c0) 8 0x7fff8000 /\
val_mem tfxsegs m0 (0xa2168 + D_10f0) 8 (0xaaea8 + D_10c0) /\ val_mem tfxsegs m0 (0xa2170 + D_10f0) 8 (0xaaeb0 + D_10c0) /\ val_mem tfxsegs m0 (0xa2178 + D_10f0) 8 (0xaaea0 + D_10c0) /\
val_mem tfxsegs m0 (0xaaea0 + D_10c0) 8 0x7fffffffffff /\ val_mem tfxsegs m0 (0xaaea8 + D_10c0) 8 0 /\ val_mem tfxsegs m0 (0xaaeb0 + D_10c0) 8 0 /\
val_mem tfxsegs m0 (0xa2180 + D_10f0) 8 (0xa4000 + D_10f0) /\ val_mem tfxsegs m0 (0xa4000 + D_10f0) 8 (0x9b894 + D_10ec) /\
val_mem tfxsegs m0 (0xa2140 + D_10f0) 8 (0x139c60 + D_10c0) /\ val_mem tfxsegs m0 (0x139c60 + D_10c0) 8 4096 /\ val_mem tfxsegs m0 (0xa21a0 + D_10f0) 8 1.
Proof. splits; (img_apply cell_lit; (img_case; vm_compute); img_refl). Qed.
Lemma vis_present : forall e len a, In (e, len) (ajunk B ly X) \/ In (e, len) (aareas X) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent H0 mem a.
Proof.
intros e len a Hin Ha Hhi.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [img_try (img_exact (proj1 (Forall_forall _ _) (am_junk B ly X rd0 M) _ Hin)) | img_try (img_exact (proj1 (Forall_forall _ _) (am_areas B ly X rd0 M) _ Hin))]. }
destruct (range_vis_mbyte B ly H0 mem e len (a - aeval B ly e) RV ltac:(img_lia)) as [b Hb'].
replace (aeval B ly e + (a - aeval B ly e)) with a in Hb' by img_lia. img_exact (mbyte_off_apresent H0 mem a b Hhi Hb').
Qed.
Lemma thread_present : forall a, T <= a < T + kThreadObjSize -> apresent H0 mem a.
Proof.
intros a Ha. pose proof HI as (_ & _ & _ & _ & F1 & F2 & _).
img_apply (vis_present (AT 0) kThreadObjSize).
- right. unfold aareas. do 3 (img_apply in_or_app; right). do 3 right. left. img_refl.
- cbn [aeval]. img_lia.
- img_exact (zone3_off_img _ _ a F1 Ha).
Qed.
Lemma stack_present : forall a, sp0 - KSTACK <= a < sp0 -> apresent H0 mem a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). unfold spZ in HP. img_exact HP. Qed.
Lemma shadow_vis : forall t, 0 <= t < LEN / 8 -> exists v, rd0 (SHAv MAP + t) = Some v.
Proof.
intros t Ht. pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). pose proof ELEN as (E & _).
set (g := MAP + 8 * t).
assert (Hg : g mod 8 = 0). { (subst g; cbv beta). apply Z.mod_divide in M3 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (q * 512 + t). img_lia. }
assert (ESA : shadow_addr g = SHAv MAP + t).
{ unfold shadow_addr, SHAv. (subst g; cbv beta). apply Z.mod_divide in M3 as [q Hq]; [|img_lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by img_lia.
replace (q * 512 * 8 + 8 * t) with ((q * 512 + t) * 8) by img_lia. rewrite !Z_div_mult by img_lia. img_lia. }
assert (SH : exists v, ashadow B ly X g = Some v).
{ unfold ashadow. destruct (find_chunk_at B ly (st_chunks X) g) as [y|]; [img_try (eexists; img_refl)|].
rewrite (in_rangesb_In g (fa_poison_ranges ly X) MAP (sec_map_size (ck_req k))); [img_try (eexists; img_refl)| |].
- unfold fa_poison_ranges. img_apply in_app_iff. right. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk)|]. rewrite Hb. left. img_refl.
- rewrite <- E. (subst g; cbv beta). pose proof (Z.mul_div_le LEN 8 ltac:(img_lia)). img_lia. }
destruct SH as [v Hv]. exists v. rewrite <- ESA. img_exact (am_shadow B ly X rd0 M g v Hg Hv).
Qed.
Lemma shadow_present : forall a, SHAv MAP <= a < SHAv MAP + CNTv LEN -> apresent H0 mem a.
Proof.
intros a Ha. pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). unfold CNTv in Ha.
destruct (shadow_vis (a - SHAv MAP) ltac:(img_lia)) as [v Hv]. replace (SHAv MAP + (a - SHAv MAP)) with a in Hv by img_lia.
img_apply vis_apresent; [| img_try (rewrite Hv; discriminate)]. unfold SHAv in *. clear - Ha M1 M2 M4. numconst.
pose proof (Z.div_pos MAP 8 ltac:(img_lia) ltac:(img_lia)). pose proof (Z.div_le_upper_bound LEN 8). Z.div_mod_to_equations. img_lia.
Qed.
Lemma tjunk_vals : forall a, (T + t_stats + 40 <= a /\ a + 8 <= T + t_stats + 56) \/ (T + t_stats + 88 <= a /\ a + 8 <= T + t_stats + 104) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfxsegs m0 a 8 w /\ rdword rd0 a = Some w.
Proof.
intros a Ha. img_apply vis_word. intros i' Hi'.
replace (a + i') with (aeval B ly (AT t_stats) + (a + i' - (T + t_stats))) by (img_try (cbn; img_lia)).
img_apply (vis_range _ (t_unwinding - t_stats)); [|img_try (clear - Ha Hi'; numconst; img_lia)]. left. unfold ajunk. right. right. rewrite !in_app_iff. do 5 right. left.
unfold thread_junk. right; right; left; img_refl.
Qed.

Lemma junk_vals : (0 <= j1 < 2 ^ 64 /\ val_mem tfxsegs m0 (T + t_stats + 40) 8 j1) /\ (0 <= j2 < 2 ^ 64 /\ val_mem tfxsegs m0 (T + t_stats + 48) 8 j2).
Proof.
destruct (tjunk_vals (T + t_stats + 40) ltac:(img_lia)) as (w1 & R1 & V1 & E1). destruct (tjunk_vals (T + t_stats + 48) ltac:(img_lia)) as (w2 & R2 & V2 & E2).
unfold j1, j2, jw. rewrite E1, E2. repeat split; assumption || img_lia.
Qed.
Lemma ijunk_vals : forall a, a = A_ALLOCATOR + 144 \/ a = A_ALLOCATOR + 152 \/ a = A_ALLOCATOR + 704 \/ a = A_ALLOCATOR + 712 ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfxsegs m0 a 8 w /\ rdword rd0 a = Some w.
Proof.
intros a Ha. pose proof AINST as AI. img_apply vis_word. intros i' Hi'.
assert (SJ : forall d, 0 <= d < o_sec_mutex - o_sec_stats -> rd0 (aeval B ly (AInst o_sec_stats) + d) <> None).
{ intros d Hd. img_apply (vis_range _ (o_sec_mutex - o_sec_stats)); [|img_try (img_exact Hd)]. left. unfold ajunk. right. right. rewrite !in_app_iff. do 3 right. left.
unfold sec_junk. right; left; img_refl. }
assert (CJ : forall d, 0 <= d < 40 -> rd0 (aeval B ly (ANum (TFX_INST + o_comb_stats)) + d) <> None).
{ intros d Hd. img_apply (vis_range _ 40); [|img_try (img_exact Hd)]. left. unfold ajunk. right. right. rewrite !in_app_iff. do 7 right. img_apply (ts_junk_comb _ TB ly). }
cbn [aeval] in SJ, CJ. rewrite AI in SJ. unfold o_sec_stats, o_sec_mutex, o_comb_stats in *.
destruct Ha as [-> |[-> |[-> | ->]]].
- replace (A_ALLOCATOR + 144 + i') with (A_ALLOCATOR + 136 + (8 + i')) by img_lia. img_apply SJ. img_lia.
- replace (A_ALLOCATOR + 152 + i') with (A_ALLOCATOR + 136 + (16 + i')) by img_lia. img_apply SJ. img_lia.
- replace (A_ALLOCATOR + 704 + i') with (TFX_INST + 688 + (16 + i')) by (img_try (numconst; img_lia)). img_apply CJ. img_lia.
- replace (A_ALLOCATOR + 712 + i') with (TFX_INST + 688 + (24 + i')) by (img_try (numconst; img_lia)). img_apply CJ. img_lia.
Qed.
Local Notation lastr := (last (st_sec_arr X) r).
Local Notation lst := (YF23.lst ly X r).
Local Notation own := (YF23.own X i).
Lemma last_facts : nth_error arr (length arr - 1) = Some lastr /\
val_mem tfxsegs m0 (Q + 8 * (nA - 1)) 8 lst /\ (forall a, Q + 8 * (nA - 1) <= a < Q + 8 * (nA - 1) + 8 -> apresent H0 mem a) /\
val_mem tfxsegs m0 (lst + 24) 8 (nA - 1) /\ (forall a, lst + 24 <= a < lst + 32 -> apresent H0 mem a) /\
zone3 lst 8192 /\ lst + 8192 <= ASAN_CEIL /\ lst mod 4096 = 0 /\
(if own then Z.of_nat i = nA - 1 /\ lst = MAP else lst + 4096 <= MAP \/ MAP + LEN <= lst).
Proof.
pose proof ARRF as (A1 & A2 & A3 & A4 & A5). pose proof ELEN as (E & _).
assert (NE : st_sec_arr X <> []) by (img_try (destruct (st_sec_arr X); [img_try (cbn in A2; img_lia) | img_try (discriminate)])).
pose proof (YF0y.last_nth_error (st_sec_arr X) r NE) as HL.
assert (EL : Z.of_nat (length (st_sec_arr X) - 1) = nA - 1) by (img_try (unfold YF23.nA; img_lia)).
destruct (slot_val _ _ HL) as [SV SP]. rewrite EL in SV, SP.
destruct (YF0y.LST B ly X rd0 M k r o sm i Hk Hb Hsm Hi IMG) as (y2 & Hy2 & Ey2 & CI2 & L1 & L2 & L3 & SZ2 & DJL).
pose proof (YF0y.ARR B ly X rd0 M r i Hi) as (_ & _ & _ & _ & _ & _ & _ & A8).
unfold YF0y.lst, YF0y.lastr, YF0y.arr in *. unfold YF23.lst.
assert (V24 : val_mem tfxsegs m0 (ly_sec ly lastr + 24) 8 (nA - 1)).
{ replace (ly_sec ly lastr + 24) with (aeval B ly (ASec lastr 24)) by img_refl. rewrite <- EL.
rewrite <- (YF0y.index_ofZ_nth (st_sec_arr X) (length (st_sec_arr X) - 1) lastr A3 HL).
eapply cell_stateZ; [|img_refl]. img_apply sec_In. unfold sec_cells. do 3 right. img_apply in_app_iff. right. img_apply in_flat_map. exists y2. split; [img_try (img_exact Hy2)|]. rewrite Ey2.
do 3 right. left. img_refl. }
splits; try assumption.
- intros a Ha. img_apply vis_apresent_off; [img_try (img_apply (zone3_off_img _ _ _ L1); clear - Ha SZ2; img_lia)|]. replace a with (ly_sec ly lastr + 24 + (a - (ly_sec ly lastr + 24))) by img_lia. eapply val_mem_vis; [img_try (img_exact V24) | img_lia].
- clear - L1 SZ2. unfold zone3, zone3cases in *. img_lia.
- img_lia.
- unfold YF23.own, YF23.idx. unfold YF0y.own, YF0y.idx, YF0y.nA in A8, DJL. unfold YF23.nA.
destruct (Z.of_nat i =? Z.of_nat (length (st_sec_arr X)) - 1) eqn:EO.
+ split; [img_try (apply Z.eqb_eq in EO; img_exact EO)|]. unfold YF0y.arr in A8. rewrite (proj1 A8 EO). img_refl.
+ unfold YF0y.arr in DJL. specialize (DJL EO). unfold zdisjoint in DJL. cbn [fst snd] in DJL. unfold YF0y.MAP, YF0y.LEN in DJL. rewrite <- E in DJL.
unfold YF23.MAP. clear - DJL SZ2. img_lia.
Qed.
Lemma qi_val : val_mem tfxsegs m0 (Q + 8 * Z.of_nat i) 8 MAP /\ (forall a, Q + 8 * Z.of_nat i <= a < Q + 8 * Z.of_nat i + 8 -> apresent H0 mem a).
Proof. img_exact (slot_val i r Hi). Qed.
Definition ji1 : Z := jw (A_ALLOCATOR + 144).
Definition ji2 : Z := jw (A_ALLOCATOR + 152).
Definition ji3 : Z := jw (A_ALLOCATOR + 704).
Definition ji4 : Z := jw (A_ALLOCATOR + 712).
Definition j5 : Z := jw (T + t_stats + 88).
Definition j6 : Z := jw (T + t_stats + 96).
Lemma junkD_vals :
(0 <= ji1 < 2 ^ 64 /\ val_mem tfxsegs m0 (A_ALLOCATOR + 144) 8 ji1) /\ (0 <= ji2 < 2 ^ 64 /\ val_mem tfxsegs m0 (A_ALLOCATOR + 152) 8 ji2) /\
(0 <= ji3 < 2 ^ 64 /\ val_mem tfxsegs m0 (A_ALLOCATOR + 704) 8 ji3) /\ (0 <= ji4 < 2 ^ 64 /\ val_mem tfxsegs m0 (A_ALLOCATOR + 712) 8 ji4) /\
(0 <= j5 < 2 ^ 64 /\ val_mem tfxsegs m0 (T + t_stats + 88) 8 j5) /\ (0 <= j6 < 2 ^ 64 /\ val_mem tfxsegs m0 (T + t_stats + 96) 8 j6).
Proof.
destruct (ijunk_vals (A_ALLOCATOR + 144) ltac:(img_lia)) as (w1 & R1 & V1 & E1). destruct (ijunk_vals (A_ALLOCATOR + 152) ltac:(img_lia)) as (w2 & R2 & V2 & E2').
destruct (ijunk_vals (A_ALLOCATOR + 704) ltac:(img_lia)) as (w3 & R3 & V3 & E3). destruct (ijunk_vals (A_ALLOCATOR + 712) ltac:(img_lia)) as (w4 & R4 & V4 & E4).
destruct (tjunk_vals (T + t_stats + 88) ltac:(img_lia)) as (w5 & R5 & V5 & E5). destruct (tjunk_vals (T + t_stats + 96) ltac:(img_lia)) as (w6 & R6 & V6 & E6).
unfold ji1, ji2, ji3, ji4, j5, j6, jw. rewrite E1, E2', E3, E4, E5, E6. repeat split; assumption || img_lia.
Qed.
Local Notation E0 := (YF2p.E0 ly regs hdr nA Q).
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF2p.E2 ly regs hdr nA Q). Qed.
Lemma chunk_lit0 : forall a (w : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) YF2p.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & _).
pose proof HSP as [S1 S2]. pose proof inst_vals as (V1 & V2 & V3 & V4). pose proof mutex_val as VM. pose proof ARRF as (_ & _ & _ & A4 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kSpaceSize, kPrimResvSize, kPtrArrayResv, KSTACK, kLowMemEnd in hP1, hP2, hQ1, hQ2, hS1, hS2, hCE, hSP1, hSP2, S1, S2, hI1, hI2.
unfold YF2p.REG0, YF2p.R_STK, YF2p.R_MUT, fatom8.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- YF2p.GFRAME)); [img_try (rewrite E2; img_refl) | img_try (unfold YF2p.GFRAME; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, YF2p.GFRAME in *; img_lia) | img_try (img_apply stack_present; clear -Ha; unfold YF2p.GFRAME, KSTACK in *; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split.
{ intros o' Ho'. img_apply rw_writable. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit0; [img_try (img_exact VM) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 32%nat 0 SB); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact V1) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 34%nat 0 nA); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact V4) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o' Ho'; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 35%nat 0 Q); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact V3) | img_try (r8) | img_try (cbn; img_lia)]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF2p.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _). pose proof HSP as [S1 S2].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
img_apply pairwise_disjoint_of_extents.
unfold YF2p.REG0, YF2p.R_STK, YF2p.R_MUT, fatom8, extent_of_region.
cbn [map fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E2. fold sp0. clear WF LO. numconst.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [clear; img_lia | clear - S1 hS1 hCE Usp; img_lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF2p.FFA).
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & _).
pose proof HSP as [S1 S2]. pose proof hdr_facts as (D1 & D2 & D3 & D4 & _). pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). pose proof ARRF as (_ & _ & _ & A4 & _).
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
cbn [YF2p.FFA f_atoms atoms_ok]. clear WF LO. numconst.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 hCE Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat SB); [img_refl| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 hSAL; first [img_lia | apply Z.mod_divide in hSAL as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists q; img_change (2 ^ 16) with 65536; img_lia]. }
split. { img_apply (AF 33%nat hdr); [img_refl| | | |]. all: clear - CR0 D1 D2 D3 D4 M1 M2 M4; first [img_lia | img_change (2 ^ 4) with 16; img_exact D4]. }
split. { img_apply (AF 34%nat nA); [img_refl| | | |]. all: clear - A4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 35%nat Q); [img_refl| | | |]. all: clear - CR0 hQ1 hQ2 hQAL; first [img_lia | img_change (2 ^ 12) with 4096; img_exact hQAL]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF2p.SS0 (restrict (w_H W) (mkst regs (w64 A_RChunk) mem (seg_rom tfxsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1).
pose proof hdr_facts as (D1 & _). pose proof GEOM as (M1 & M2 & _ & M4 & _).
rewrite restrict_mkst_fx. unfold YF2p.SS0, YF2p.SR0, sr_set. cbn [bv_eqb]. unfold YF2p.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros XX; discriminate) |].
cbn [sv_denot]. fold (YF2p.E0 ly regs hdr nA Q). rewrite YF2p.EqM, Ha1. unfold w64, hdr. rewrite Zbv_add_unsigned. f_equal. img_lia.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FH_A : YF2p.free_hyps W ly regs mem hdr nA Q.
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & _).
pose proof hdr_facts as (D1 & D2 & D3 & D4 & _). pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). pose proof ARRF as (_ & _ & _ & A4 & _).
pose proof inst_vals as (V1 & V2 & V3 & V4).
pose proof (YF0y.MAPX B ly X rd0 M k r o sm Hk Hb Hsm 0 _ eq_refl) as DP. unfold zdisjoint in DP. cbn [fst snd] in DP.
pose proof ELEN as (E & _). unfold YF0y.MAP, YF0y.LEN in DP. rewrite <- E in DP. fold (YF23.MAP ly r) in DP.
constructor.
- img_exact LO.
- img_exact IMG.
- rewrite Ha1. unfold hdr. img_refl.
- split; [img_try (img_exact Hlo) | img_try (clear - Hcb1 Hcb2; img_lia)].
- img_exact Hal.
- img_exact HPRES.
- pose proof M1 as M1'. unfold zone3 in M1'. split; [img_try (clear - D1 M1'; img_lia)|]. split; [img_try (clear - D1 D2 D3 M2; img_lia)|]. split; [img_try (img_exact D4)|].
unfold YF23.MAP in *. clear - DP M1' M2 M4 D1 D3 D2 hSP1 hSP2 hP1 hP2. numconst. img_lia.
- img_exact V1.
- split; [img_try (img_exact V4) | img_try (img_exact A4)].
- split; [img_try (img_exact V3)|]. split; [img_try (clear - hQ1; unfold zone3 in hQ1; img_lia)|]. split; [img_try (clear - hQ1 hQ2 A4; numconst; img_lia) | img_try (img_exact hQAL)].
- img_exact mutex_val.
- img_exact SEED_ok.
Qed.
End f.
End c.
