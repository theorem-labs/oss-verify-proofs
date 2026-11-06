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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1g YF2n YF07.
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
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFX_IMG_END, kBatchBytes, SHADOW_OFF, TFX_TP, TFX_TSD, TFX_INST,
A_QUAR, A_ALLOCATOR, o_quar, o_space, o_rinfo, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize, kLowMemEnd, EV_MAX,
kChunkHeaderSize, MALLOC_MAX in *.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variable off : Z.
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PPrim off.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Definition rcl : Z := prim_class off.
Definition rbase : Z := ck_base B ly k.
Definition rrz : Z := ck_rz k.
Definition rnn : Z := ck_n k.
Definition rmuc : Z := rg_mapped_user (reg X rcl).
Definition hb1 : Z := match rd0 (rbase + rrz - kChunkHeaderSize + 1) with Some b => b | None => 0 end.
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
Lemma KF : cfacts B ly X k. Proof. img_exact (chunk_facts B ly X rd0 k M Hk). Qed.
Lemma AINST : as_inst B = A_ALLOCATOR. Proof. rewrite (ts_inst _ TB). img_refl. Qed.
Lemma Hc : 1 <= rcl <= 30. Proof. pose proof KF as (_ & _ & _ & _ & _ & _ & _ & _ & CK). rewrite Hb in CK. img_exact (proj1 CK). Qed.
Lemma HSP : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma CLS : cls_ok rcl (reg X rcl) (cache X rcl) true (chunk_offs X rcl) (batch_offs X rcl).
Proof. pose proof (wf_classes _ _ _ _ _ WF rcl ltac:(img_try (pose proof Hc; img_lia))) as C. unfold wf_class in C. rewrite Hci in C. img_exact C. Qed.
Local Notation Mv := (YF2n.Mv rbase rrz).
Local Notation Uv := (YF2n.Uv rbase rrz).
Local Notation HWv := (YF2n.HWv hb1).
Local Notation SPv := (YF2n.SPv rbase rrz).
Local Notation N8v := (YF2n.N8v rnn).
Local Notation CNT8v := (YF2n.CNT8v rnn).
Local Notation RIv := (YF2n.RIv ly).
Local Notation RGv := (YF2n.RGv ly rcl).
Local Notation SZv := (YF2n.SZv rcl).
Local Notation RELv := (YF2n.RELv ly rcl rbase).
Lemma geom : 1 <= rcl <= 30 /\ rbase = SB + off /\ region_off rcl = rcl * 2 ^ 32 /\ RELv = off - region_off rcl /\
0 <= RELv /\ RELv mod SZv = 0 /\ RELv + SZv <= rg_alloc_user (reg X rcl) /\ rg_alloc_user (reg X rcl) <= rmuc <= 2 ^ 31 /\
rbase mod 16 = 0 /\ 16 <= rrz <= 2048 /\ rrz mod 16 = 0 /\ 1 <= rnn < 2 ^ 28 /\ rrz + rnn <= SZv /\ ck_extent k = SZv /\
32 <= SZv <= kMaxSize /\ SZv mod 32 = 0 /\ kHighMemBeg <= rbase /\ rbase + SZv <= ASAN_CEIL.
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Hb in CK. cbv zeta in CK. destruct CK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3). pose proof (class_ok rcl ltac:(img_try (pose proof Hc; img_lia))) as (K1 & K2 & K3 & _).
assert (K0 : 32 <= class_size rcl) by (img_try (apply Z.mod_divide in K2 as [q Hq]; [|img_lia]; nia)).
unfold rbase, rrz, rnn, rmuc, rcl, YF2n.RELv, YF2n.SZv, ck_n in *. fold (prim_class off) in *.
assert (EB : ck_base B ly k = SB + off) by (img_try (unfold ck_base, sptr_addr; rewrite Hb; img_refl)).
assert (RO : region_off (prim_class off) = prim_class off * 2 ^ 32) by (img_try (unfold region_off; rewrite Z.shiftl_mul_pow2 by img_lia; img_refl)).
pose proof (lo_high ly LO) as IP. unfold in_high in IP. cbn [fst snd] in IP. pose proof (lo_space_in ly LO) as [S1 S2].
unfold region_base in C5. numconst. repeat split; try img_lia.
rewrite EB. replace (SB + off - SB - region_off (prim_class off)) with (off - region_off (prim_class off)) by img_lia. img_exact C7.
Qed.
Lemma Hci' : st_cache_inited X = true. Proof. img_exact Hci. Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ SB mod 65536 = 0 /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\ T mod 4096 = 0 /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ ly_C ly mod 8 = 0 /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\ (ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_C ly).
Proof.
pose proof (lo_high ly LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app ly LO) as HA. pose proof (lo_disj ly LO) as HD0.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear; unfold kThreadObjSize; img_lia)) (Forall_nth_f _ _ 2 _ HA eq_refl) (pairwise_ij_f _ _ 2 6 _ _ HD0 eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear; img_lia)) (Forall_nth_f _ _ 6 _ HA eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD0 eq_refl eq_refl)) as ZC. clear HA.
pose proof (lo_space_in ly LO) as HSPC. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_al ly LO) as SAL.
pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL. pose proof (lo_C_al ly LO) as CAL.
pose proof HD0 as HD. clear HD0. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _ & _ & _ & DC & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [_ DC]. apply Forall_cons_iff in DC as [CSTK _].
pose proof (aso_cells _ (am_syms B ly X rd0 M)) as (I1 & I2 & _).
unfold zdisjoint in PT, PSTK, TSTK, PC, TC, CSTK. cbn [fst snd] in *.
assert (ZT2 : T + kThreadObjSize <= ASAN_CEIL) by (img_try (clear - ZT; unfold zone3 in ZT; img_lia)). assert (ZC2 : ly_C ly + 256 <= ASAN_CEIL) by (img_try (clear - ZC; unfold zone3 in ZC; img_lia)).
clear - IP HSPC T1 T2 T3 T4 T5 T6 T7 SAL TAL CAL PT PSTK TSTK PC TC CSTK I1 I2 ZT ZT2 ZC ZC2. unfold kHighMemBeg, kThreadObjSize, kPrimResvSize in *.
repeat match goal with |- _ /\ _ => split end; first [img_exact ZT | img_exact ZC | img_lia].
Qed.
Lemma derived : RIv = SB + kRegionInfoOff /\ RGv = RIv + 128 * rcl /\ RIv + 128 <= RGv /\ RGv + 128 <= RIv + 4096 /\ kHighMemBeg <= RIv /\ RIv + 4096 <= ASAN_CEIL /\
kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\ SB + 2 ^ 32 <= rbase /\ rbase + SZv <= SB + 31 * 2 ^ 32 /\
Mv = rbase + rrz - 16 /\ Uv = rbase + rrz /\ Mv mod 16 = 0 /\ Uv mod 8 = 0 /\
0x2008fff7000 <= SPv /\ SPv + CNT8v <= kHighMemBeg /\ N8v = 8 * CNT8v /\ rnn <= N8v < rnn + 8 /\ 1 <= CNT8v /\ 0 <= HWv < 65536.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hSAL & _). pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
assert (HB : 0 <= hb1 < 256).
{ unfold hb1. destruct (rd0 _) as [b|] eqn:E; [|img_lia]. apply aview_some in E as (b8 & _ & <-). pose proof (bv_unsigned_in_range 8 b8) as R. img_change (bv_modulus 8) with 256 in R. img_lia. }
unfold YF2n.RGv, YF2n.RIv, YF2n.Mv, YF2n.Uv, YF2n.SPv, YF2n.CNT8v, YF2n.N8v, YF2n.HWv. unfold YF2n.Uv.
assert (U16 : (rbase + rrz) mod 16 = 0).
{ apply Z.mod_divide in G9 as [q Hq]; [|img_lia]. apply Z.mod_divide in G11 as [q' Hq']; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q + q'). img_lia. }
assert (M16 : (rbase + rrz - kChunkHeaderSize) mod 16 = 0).
{ pose proof U16 as U16'. apply Z.mod_divide in U16' as [q Hq]; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q - 1). unfold kChunkHeaderSize. img_lia. }
assert (U8 : (rbase + rrz) mod 8 = 0) by (img_try (img_apply (mod0_factor _ 8 2); [img_lia | img_try (img_exact U16)])).
pose proof (Z.div_mod (rnn + 7) 8 ltac:(img_lia)) as DM. pose proof (Z.mod_pos_bound (rnn + 7) 8 ltac:(img_lia)) as MB.
set (q8 := (rnn + 7) / 8) in *. rewrite (Z_div_mult q8 8) by img_lia.
assert (RELB : rcl * 2 ^ 32 + RELv + SZv <= 31 * 2 ^ 32) by (img_try (clear - G1 G7 G8; nia)).
unfold YF2n.RELv in G4, G5, G7, RELB. rewrite G3 in *.
numconst. unfold kChunkHeaderSize in *.
assert (UB1 : (rbase + rrz + q8 * 8) / 8 <= 140735332483072 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z_div_plus in UB1 by img_lia.
assert (UB3 : 17594333495296 / 8 <= (rbase + rrz) / 8) by (img_try (img_apply Z.div_le_mono; img_lia)).
clear WF LO PRE. repeat split; try assumption; try img_lia.
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
Lemma vis_range : forall e len i, In (e, len) (ajunk B ly X) \/ In (e, len) (aareas X) \/ In (e, len) (aclient X) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- img_exact (proj1 (Forall_forall _ _) (am_junk B ly X rd0 M) _ Hin i Hi).
- img_exact (proj1 (Forall_forall _ _) (am_areas B ly X rd0 M) _ Hin i Hi).
- img_exact (proj1 (Forall_forall _ _) (am_client B ly X rd0 M) _ Hin i Hi).
Qed.
Lemma In_acells_region : forall cc, In cc (region_cells X rcl) -> In cc (acells B ly X).
Proof.
intros cc Hcc. unfold acells. rewrite !in_app_iff. left. img_apply in_flat_map. exists rcl. split; [img_try (img_apply In_zseq; pose proof Hc; img_lia) | img_try (img_exact Hcc)].
Qed.
Lemma hdr_In : forall cc, In cc (chunk_cells k) -> In cc (acells B ly X).
Proof. intros cc Hcc. unfold acells. rewrite !in_app_iff. do 2 right. left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk) | img_try (img_exact Hcc)]. Qed.
Lemma EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = rbase + d.
Proof. intros d. unfold rbase, ck_base, sptr_addr. rewrite Hb. cbn. img_lia. Qed.
Lemma EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = rbase + d + d'.
Proof. intros d d'. unfold rbase, ck_base, sptr_addr. rewrite Hb. cbn. img_lia. Qed.
Lemma EA0 : aeval B ly (sptr_exp (ck_beg k)) = rbase.
Proof. unfold rbase, ck_base, sptr_addr. img_refl. Qed.
Lemma hb1_facts : rd0 (Mv + 1) = Some hb1 /\ 0 <= hb1 < 256.
Proof.
assert (C : cell_holds B ly rd0 (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ img_apply (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M)). img_apply hdr_In. unfold chunk_cells. img_apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite EA2 in C.
replace (rbase + (ck_rz k - kChunkHeaderSize) + 1) with (Mv + 1) in C by (img_try (unfold YF2n.Mv, rrz; img_lia)).
destruct C as (b & Hb' & Hm). unfold hb1. unfold YF2n.Mv in *. unfold rrz in *. rewrite Hb'.
destruct (aview_vis_byte H0 mem _ ltac:(img_try (rewrite Hb'; discriminate))) as (b' & E' & R' & _). rewrite Hb' in E'. injection E' as <-. auto.
Qed.
Lemma hw_val : val_mem tfxsegs m0 Mv 4 HWv /\ val_mem tfxsegs m0 (Mv + 4) 4 rnn.
Proof.
pose proof hb1_facts as [HB HR].
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) = Mv) by (img_try (rewrite EA; unfold YF2n.Mv, rrz; img_lia)).
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) d) = Mv + d) by (img_try (intros d; rewrite EA2; unfold YF2n.Mv, rrz; img_lia)).
assert (V0 : val_mem tfxsegs m0 Mv 1 3).
{ rewrite <- EH. eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; left; img_refl)|]. unfold z1, c1, hdr_state. rewrite Hst. img_refl. }
assert (V2 : val_mem tfxsegs m0 (Mv + 2) 2 0).
{ rewrite <- (EH2 2). eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; do 2 right; left; img_refl)|]. img_refl. }
assert (V4 : val_mem tfxsegs m0 (Mv + 4) 4 (ck_n k)).
{ rewrite <- (EH2 4). eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; do 3 right; left; img_refl)|]. img_refl. }
split; [|img_try (unfold rnn; img_exact V4)].
intros i Hi. unfold YF2n.HWv.
assert (LB : forall v (w j : nat), YP0g.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YP0g.le_byte. rewrite Z.shiftr_div_pow2 by img_lia. img_refl. }
destruct i as [|[|[|[|i]]]]; [| | | |img_lia].
- rewrite (V0 0%nat ltac:(img_lia)). do 2 f_equal. rewrite !LB. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
img_change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- img_change (Z.of_nat 1) with 1. rewrite (aview_byte _ _ _ _ HB). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia.
- replace (Mv + Z.of_nat 2) with (Mv + 2 + Z.of_nat 0) by img_lia. rewrite (V2 0%nat ltac:(img_lia)). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 2)) with 65536. img_change (2 ^ (8 * Z.of_nat 0)) with 1.
rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- replace (Mv + Z.of_nat 3) with (Mv + 2 + Z.of_nat 1) by img_lia. rewrite (V2 1%nat ltac:(img_lia)). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 2)) with 65536.
img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. nia.
Qed.
Lemma mag_val : rrz <> 16 -> val_mem tfxsegs m0 rbase 8 0xCC6E96B9CC6E96B9.
Proof.
intros Hne. rewrite <- EA0. eapply cell_stateZ; [|img_refl]. img_apply hdr_In. unfold chunk_cells. img_apply in_app_iff. right.
unfold rrz in Hne. destruct (Z.eqb_spec (ck_rz k) kChunkHeaderSize) as [E|E]; [img_try (exfalso; img_apply Hne; img_exact E)|]. left. img_refl.
Qed.
Lemma rg_val : val_mem tfxsegs m0 (RGv + 48) 8 rmuc.
Proof.
replace (RGv + 48) with (aeval B ly (aoff (ASp (kRegionInfoOff + 128 * rcl)) 48)) by (img_try (cbn; unfold YF2n.RGv, YF2n.RIv; img_lia)).
unfold rmuc. eapply cell_stateZ; [img_try (img_apply In_acells_region; unfold region_cells; cbv zeta; do 6 right; left; img_refl) | img_refl].
Qed.
Lemma const_vals : val_mem tfxsegs m0 (A_ALLOCATOR + 32) 8 SB /\ val_mem tfxsegs m0 (A_ALLOCATOR + 48) 8 RIv /\ val_mem tfxsegs m0 (0x10328 + D_10) 8 0xCC6E96B9CC6E96B9.
Proof.
pose proof AINST as AI. splits.
- replace (A_ALLOCATOR + 32) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite AI; img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- replace (A_ALLOCATOR + 48) with (aeval B ly (AInst o_rinfo)) by (img_try (cbn; rewrite AI; img_refl)).
replace RIv with (aeval B ly (ASp kRegionInfoOff)) by (img_try (cbn; unfold YF2n.RIv; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply cell_lit. img_case; vm_compute. all: img_refl.
Qed.
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
intros a Ha. pose proof HI as (_ & _ & F1 & F2 & _).
img_apply (vis_present (AT 0) kThreadObjSize).
- right. unfold aareas. do 3 (img_apply in_or_app; right). do 3 right. left. img_refl.
- cbn [aeval]. img_lia.
- img_exact (zone3_off_img _ _ a F1 Ha).
Qed.
Lemma rinfo_present : forall a, RGv <= a < RGv + 128 -> apresent H0 mem a.
Proof.
intros a Ha. pose proof derived as DR. pose proof Hc as Hcx.
img_apply (vis_present (ASp kRegionInfoOff) 4096).
- right. unfold aareas. do 3 (img_apply in_or_app; right). do 4 right. left. img_refl.
- cbn [aeval]. unfold YF2n.RGv, YF2n.RIv in *. clear - Ha Hcx. numconst. img_lia.
- img_apply off_img_high. clear - Ha DR. numconst. img_lia.
Qed.
Lemma extent_present : forall a, rbase <= a < rbase + SZv -> apresent H0 mem a.
Proof.
intros a Ha. pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _ & _ & _ & _ & _ & _ & _ & _ & G17 & G18). pose proof Hc as Hcx.
img_apply (vis_present (ASp (region_off rcl)) (rg_mapped_user (reg X rcl))).
- right. unfold aareas. img_apply in_or_app; left. img_apply in_flat_map. exists rcl. split; [img_try (img_apply In_zseq; img_lia)|]. left; img_refl.
- cbn [aeval]. unfold YF2n.RELv, rmuc in *. clear - Ha G4 G5 G7 G8 G2. img_lia.
- img_apply off_img_high. clear - Ha G17 G18. numconst. img_lia.
Qed.
Lemma stack_present : forall a, sp0 - KSTACK <= a < sp0 -> apresent H0 mem a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). unfold spZ in HP. img_exact HP. Qed.
Lemma cb_facts : sp0 <= cbp /\ cbp + 16 <= ly_stk_hi ly /\ cbp mod 8 = 0 /\ (forall a, cbp <= a < cbp + 16 -> apresent H0 mem a) /\ val_mem tfxsegs m0 cbp 8 (T + t_cache).
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & C3 & _ & C4 & C5 & _). unfold spZ in *. split; [img_try (img_exact C1)|]. split; [img_try (img_exact C2)|]. split; [img_try (img_exact C3)|]. split; [img_try (img_exact C4) | img_try (img_exact C5)]. Qed.
Lemma shadow_vis : forall i, 0 <= i < CNT8v -> exists v, rd0 (SPv + i) = Some v.
Proof.
intros i Hi. pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _). pose proof derived as DR.
destruct DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EU & _ & U8 & _ & _ & EN8 & N8B & C81 & _).
set (g := Uv + 8 * i).
assert (FC : find_chunk_at B ly (st_chunks X) g = Some k).
{ img_apply (find_chunk_at_hit B ly X rd0 (st_chunks X) k g M ltac:(img_try (intros x Hx; img_exact Hx)) (wf_chunks_nodup _ _ _ _ _ WF) Hk). (subst g; cbv beta).
fold rbase. rewrite G14. unfold YF2n.CNT8v, YF2n.N8v in *. clear - Hi EU G10 G12 G13 EN8 N8B. rewrite EU. nia. }
assert (SH : ashadow B ly X g = Some (chunk_granule k ((g - ck_base B ly k) / 8))) by (img_try (unfold ashadow; rewrite FC; img_refl)).
assert (PC : exists c0, Uv = c0 * 8). { apply Z.mod_divide in U8 as [c0 Hc0]; [|img_lia]. exists c0. img_lia. }
destruct PC as [c0 Hc0].
pose proof (am_shadow B ly X rd0 M g _ ltac:(img_try ((subst g; cbv beta); rewrite Hc0; replace (c0 * 8 + 8 * i) with ((c0 + i) * 8) by img_lia; img_apply Z_mod_mult)) SH) as R.
exists (chunk_granule k ((g - ck_base B ly k) / 8)). rewrite <- R. f_equal. unfold shadow_addr, YF2n.SPv. (subst g; cbv beta).
rewrite Hc0. replace (c0 * 8 + 8 * i) with ((c0 + i) * 8) by img_lia. rewrite !Z_div_mult by img_lia. img_lia.
Qed.
Lemma shadow_present : forall a, SPv <= a < SPv + CNT8v -> apresent H0 mem a.
Proof.
intros a Ha. pose proof derived as DR. destruct (shadow_vis (a - SPv) ltac:(img_lia)) as [v Hv]. replace (SPv + (a - SPv)) with a in Hv by img_lia.
img_apply vis_apresent; [img_try (clear - Ha DR; numconst; img_lia) | img_try (rewrite Hv; discriminate)].
Qed.
Lemma junk_vals : (0 <= j1 < 2 ^ 64 /\ val_mem tfxsegs m0 (T + t_stats + 40) 8 j1) /\ (0 <= j2 < 2 ^ 64 /\ val_mem tfxsegs m0 (T + t_stats + 48) 8 j2).
Proof.
assert (VW : forall a, T + t_stats + 40 <= a -> a + 8 <= T + t_stats + 56 -> exists w, 0 <= w < 2 ^ 64 /\ val_mem tfxsegs m0 a 8 w /\ rdword rd0 a = Some w).
{ intros a H1 H2. img_apply vis_word. intros i Hi.
replace (a + i) with (aeval B ly (AT t_stats) + (a + i - (T + t_stats))) by (img_try (cbn; img_lia)).
img_apply (vis_range _ (t_unwinding - t_stats)); [|img_try (clear - H1 H2 Hi; numconst; img_lia)]. left. unfold ajunk. right. right. rewrite !in_app_iff. do 5 right. left.
unfold thread_junk. right; right; left; img_refl. }
destruct (VW (T + t_stats + 40)) as (w1 & R1 & V1 & E1); [img_lia | img_lia |]. destruct (VW (T + t_stats + 48)) as (w2 & R2 & V2 & E2); [img_lia | img_lia |].
unfold j1, j2, jw. rewrite E1, E2. repeat split; assumption || img_lia.
Qed.
Local Notation E0 := (YF2n.E0 ly regs rcl rbase rrz rnn hb1 cbp rmuc j1 j2).
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF2n.E2 ly regs rcl rbase rrz rnn hb1 cbp rmuc j1 j2). Qed.
Lemma chunk_lit0 : forall a (w : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfxsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfxsegs m0 o.
Proof.
intros a w v o Hv Ho Ha. pose proof (Hv (Z.to_nat (o - a)) ltac:(img_lia)) as Hb'. rewrite Z2Nat.id in Hb' by img_lia. replace (a + (o - a)) with o in Hb' by img_lia.
eapply mbyte_off_writable; [img_try (img_exact Ha) | img_try (img_exact Hb')].
Qed.
Ltac offw := first [ img_lia | img_apply off_img_high; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; img_lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); unfold kThreadObjSize, t_stats in *; img_lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac r4 := img_change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); img_lia.
Local Ltac lit_region :=
reg_intro; split; [img_lia|]; split; [img_lia|]; split; [img_try (intros o Ho; img_lia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit0; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; img_lia | cbn; img_lia]) |]); img_apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) YF2n.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hSAL & _ & _ & _ & hI1 & hI2 & hTAL & hC1 & hC2 & hCAL & _).
pose proof HSP as [S1 S2]. pose proof derived as DR. pose proof geom as GE. pose proof cb_facts as (C1 & C2 & C3 & C4 & C5).
pose proof hw_val as [W1 W2]. pose proof rg_val as VRG. pose proof const_vals as (V1 & V2 & V3). pose proof junk_vals as ([J1R J1] & [J2R J2]). pose proof hb1_facts as [_ HBR].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof DR as (dI1 & dG0 & dG1 & dG2 & dI3 & dI4 & dS1 & dS2 & dB1 & dB2 & dM1 & dU1 & dMal & dUal & dSP1 & dSP2 & dN8 & dN8b & dC8 & dHW).
pose proof GE as (gC & gB & gRO & gREL & gX1 & gX2 & gX3 & gMU & gBal & gRZ & gRZal & gNN & gRN & gEXT & gSZ & gSZal & gH1 & gH2).
clear DR GE.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, KSTACK, kMaxSize, kLowMemEnd in
hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hI1, hI2, hC1, hC2, S1, S2, dI3, dI4, dS1, dS2, dSP1, dSP2, gH1, gH2, gSZ.
unfold YF2n.REG0, YF2n.R_STK, YF2n.R_CB, YF2n.R_HDR, YF2n.R_RGMU, YF2n.R_CTX, YF2n.R_JST, flit1, flit4, flit8, flits8, fatom8.
cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
img_apply Forall_cons.
{   reg_intro. rewrite E2. fold sp0. split; [img_lia|]. split; [img_lia|]. split; [|img_try (img_apply Forall_nil)].
intros o Ho. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; img_lia) | img_try (img_apply stack_present; unfold KSTACK; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2n.EqCBP. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 32%nat t_cache (T + t_cache)); [img_try (rewrite YF2n.EqT; unfold w64; f_equal; img_lia) | img_try (unfold t_cache; img_lia) | img_try (rewrite Z.add_0_r; img_exact C5) | img_try (unfold t_cache; r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2n.EqM. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ W1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom _ _ 4 38%nat 0 HWv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact W1) | img_try (r4) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 4 39%nat 0 rnn); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact W2) | img_try (r4) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2n.EqRG. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 45%nat 0 rmuc); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact VRG) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2n.EqC. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_lit_at; [| img_try (cbn; img_lia) | img_try (cbn; img_lia)]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by img_refl. img_apply (cell_sym (AC 8) 4 (ANum 0)). img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 32%nat 0 T); [img_try (rewrite YF2n.EqT; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; img_lia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2n.EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_stats in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 2848); [img_try (img_apply (val_mem_writable _ _ _ _ J1)) | img_try (img_apply (val_mem_writable _ _ _ _ J2))]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom _ _ 8 49%nat 0 j1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact J1 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 50%nat 0 j2); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact J2 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 34%nat 0 SB); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact V1) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 47%nat 0 RIv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact V2) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [img_try (lit_region)|].
do 10 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons; [img_try (lit_region)|].
img_apply Forall_cons. {   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [img_refl | img_try (unfold SHADOW_OFF; img_lia) | | img_try (unfold SHADOW_OFF; cbn; img_lia) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. img_apply cell_lit. img_case; vm_compute. all: img_refl. }
do 8 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. unfold TFX_TP. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit0; [| img_try (unfold TFX_TSD; cbn; img_lia) | img_try (cbn; img_lia)].
replace ((6148432 + D_10c0) - 88) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TB); img_refl)).
replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; unfold TFX_TSD; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{   reg_intro. unfold TFX_TSD. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite YF2n.EqC; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)).
replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF2n.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hSAL & hTP & hTS & hPS & hI1 & hI2 & hTAL & hC1 & hC2 & hCAL & hTC & hPC & hCS).
pose proof HSP as [S1 S2]. pose proof derived as (dI1 & dG0 & dG1 & dG2 & dI3 & dI4 & dS1 & dS2 & dB1 & dB2 & dM1 & dU1 & _).
pose proof geom as (gC & _ & _ & _ & _ & _ & _ & _ & _ & gRZ & _ & _ & gRN & gEXT & gSZ & _ & gH1 & gH2). pose proof cb_facts as (C1 & C2 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
img_apply pairwise_disjoint_of_extents.
unfold YF2n.REG0, YF2n.R_STK, YF2n.R_CB, YF2n.R_HDR, YF2n.R_RGMU, YF2n.R_CTX, YF2n.R_JST, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E2, YF2n.EqCBP, YF2n.EqM, YF2n.EqRG, YF2n.EqC, YF2n.EqT. unfold w64. fold sp0.
clear WF LO PRE. unfold YF2n.RGv, YF2n.RIv, YF2n.Mv in *. numconst. rewrite !unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in hT1, hC1.
repeat split; first [clear; img_lia | clear - S1 hS1 C1 dS1 dB1 dM1 gRZ dI1 dG0 dG1 dI3 hC1 hT1 gC; img_lia | clear hTP hTS hPS hTC hPC hCS; img_lia | img_lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF2n.FFR).
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hSAL & _ & _ & _ & hI1 & hI2 & hTAL & hC1 & hC2 & hCAL & _).
pose proof HSP as [S1 S2]. pose proof derived as DR. pose proof geom as GE. pose proof cb_facts as (C1 & C2 & C3 & _). pose proof junk_vals as ([A1 _] & [A2 _]).
pose proof DR as (dI1 & dG0 & dG1 & dG2 & dI3 & dI4 & dS1 & dS2 & dB1 & dB2 & dM1 & dU1 & dMal & dUal & dSP1 & dSP2 & dN8 & dN8b & dC8 & dHW).
pose proof GE as (gC & gB & gRO & gREL & gX1 & gX2 & gX3 & gMU & gBal & gRZ & gRZal & gNN & gRN & gEXT & gSZ & gSZal & gH1 & gH2).
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (RG7 : RGv mod 2 ^ 7 = 0).
{ unfold YF2n.RGv, YF2n.RIv, kRegionInfoOff. pose proof hSAL as SAL'. apply Z.mod_divide in SAL' as [q Hq]; [|img_lia]. rewrite Hq.
img_apply Z.mod_divide; [img_lia|]. exists (q * 512 + 2 ^ 30 + rcl). img_change (2 ^ 7) with 128. img_lia. }
assert (RI12 : RIv mod 2 ^ 12 = 0).
{ unfold YF2n.RIv, kRegionInfoOff. pose proof hSAL as SAL'. apply Z.mod_divide in SAL' as [q Hq]; [|img_lia]. rewrite Hq.
img_apply Z.mod_divide; [img_lia|]. exists (q * 16 + 2 ^ 25). img_change (2 ^ 12) with 4096. img_lia. }
assert (SP2 : SPv mod 2 ^ 1 = 0).
{ unfold YF2n.SPv, YF2n.Uv.
assert (U16 : (rbase + rrz) mod 16 = 0).
{ pose proof gBal as B16. pose proof gRZal as R16. apply Z.mod_divide in B16 as [q Hq]; [|img_lia]. apply Z.mod_divide in R16 as [q' Hq']; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q + q'). img_lia. }
apply Z.mod_divide in U16 as [q Hq]; [|img_lia]. rewrite Hq. replace (q * 16) with (q * 2 * 8) by img_lia. rewrite Z_div_mult by img_lia.
img_apply Z.mod_divide; [img_lia|]. exists (1073725440 + q). img_change (2 ^ 1) with 2. unfold SHADOW_OFF. img_lia. }
cbn [YF2n.FFR f_atoms atoms_ok]. clear WF LO. numconst.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal C1 C2; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_refl| | | |]. all: clear - CR0 hT1 hT2 hTAL; first [img_lia | img_change (2 ^ 12) with 4096; img_exact hTAL]. }
split. { img_apply (AF 33%nat (ly_C ly)); [img_refl| | | |]. all: clear - CR0 hC1 hC2 hCAL; first [img_lia | img_change (2 ^ 3) with 8; img_exact hCAL]. }
split. { img_apply (AF 34%nat SB); [img_refl| | | |]. all: clear - CR0 dS1 dS2 hSAL; first [img_lia | apply Z.mod_divide in hSAL as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists q; img_change (2 ^ 16) with 65536; img_lia]. }
split. { img_apply (AF 35%nat Mv); [img_refl| | | |]. all: clear - CR0 dS1 dS2 dB1 dB2 dM1 gRZ gSZ dMal; first [img_lia | img_apply (mod0_factor _ 16 1); [img_lia | img_try (img_change (1 * 16) with 16; img_exact dMal)]]. }
split. { img_apply (AF 36%nat rcl); [img_refl| | | |]. all: clear - CR0 gC; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat rbase); [img_refl| | | |]. all: clear - CR0 dS1 dS2 dB1 dB2 gSZ gBal; first [img_lia | img_apply (mod0_factor _ 16 1); [img_lia | img_try (img_change (1 * 16) with 16; img_exact gBal)]]. }
split. { img_apply (AF 38%nat HWv); [img_refl| | | |]. all: clear - CR0 dHW; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 39%nat rnn); [img_refl| | | |]. all: clear - CR0 gNN; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat SHADOW_OFF); [img_refl| | | |]. all: unfold SHADOW_OFF; first [img_lia | img_refl]. }
split. { img_apply (AF 41%nat SPv); [img_refl| | | |]. all: clear - CR0 dSP1 dSP2 dC8 SP2; first [img_lia | img_exact SP2]. }
split. { img_apply (AF 42%nat N8v); [img_refl| | | |]. all: clear - CR0 dN8 dN8b gNN dC8; first [img_lia | rewrite dN8; img_apply Z.mod_divide; [img_lia|]; exists CNT8v; img_change (2 ^ 3) with 8; img_lia]. }
split. { img_apply (AF 43%nat CNT8v); [img_refl| | | |]. all: clear - CR0 dN8 dN8b gNN dC8; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 44%nat cbp); [img_refl| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 C1 C2 C3; first [img_lia | img_change (2 ^ 3) with 8; img_exact C3]. }
split. { img_apply (AF 45%nat rmuc); [img_refl| | | |]. all: clear - CR0 gMU gX1 gX2 gX3 gSZ; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 46%nat RGv); [img_refl| | | |]. all: clear - CR0 dI1 dG0 dG1 dG2 dI3 dI4 RG7; first [img_lia | img_exact RG7]. }
split. { img_apply (AF 47%nat RIv); [img_refl| | | |]. all: clear - CR0 dI1 dI3 dI4 RI12; first [img_lia | img_exact RI12]. }
split. { img_apply (AF 48%nat SZv); [img_refl| | | |]. all: clear - CR0 gSZ gSZal; first [img_lia | apply Z.mod_divide in gSZal as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists q; img_change (2 ^ 5) with 32; img_lia]. }
split. { img_apply (AF 49%nat j1); [img_refl| | | |]. all: clear - CR0 A1; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 50%nat j2); [img_refl| | | |]. all: clear - CR0 A2; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF2n.SS0 (restrict (w_H W) (mkst regs (w64 (0x33b74 + D_150)) mem (seg_rom tfxsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1). rewrite (ts_tp _ TB) in Htp.
pose proof derived as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dM1 & _).
rewrite restrict_mkst_fx. unfold YF2n.SS0, YF2n.SR0, sr_set. cbn [bv_eqb]. unfold YF2n.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact Htp] | intros XX; discriminate |]) | img_try (intros XX; discriminate) |].
+ cbn [sv_denot]. fold (YF2n.E0 ly regs rcl rbase rrz rnn hb1 cbp rmuc j1 j2). rewrite YF2n.EqCBP, Ha0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
+ cbn [sv_denot]. fold (YF2n.E0 ly regs rcl rbase rrz rnn hb1 cbp rmuc j1 j2). rewrite YF2n.EqM, Ha1. unfold w64, YF2n.Mv. rewrite Zbv_add_unsigned. f_equal.
unfold rbase, rrz. img_lia.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FH_ok : YF2n.free_hyps W ly regs mem rcl rbase rrz rnn hb1 cbp rmuc j1 j2.
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof geom as (gC & gB & gRO & gREL & gX1 & gX2 & gX3 & gMU & gBal & gRZ & gRZal & gNN & gRN & gEXT & gSZ & gSZal & gH1 & gH2).
pose proof hb1_facts as [_ HBR]. pose proof hw_val as [W1 W2]. pose proof junk_vals as ([A1 _] & [A2 _]).
constructor.
- img_exact LO.
- img_exact IMG.
- rewrite (ts_tp _ TB) in Htp. img_exact Htp.
- img_exact Hra.
- img_exact Hra4.
- split; [img_try (img_exact Hlo) | img_try (clear - Hcb1 Hcb2; img_lia)].
- img_exact Hal.
- img_exact HPRES.
- img_exact cb_facts.
- img_exact Hc.
- split; [img_try (img_exact gX1)|]. split; [img_try (clear - gX3 gMU; unfold rmuc in *; img_lia)|]. split; [img_try (img_exact gX2)|]. split; [img_try (clear - gMU gX1 gX3 gSZ; unfold rmuc in *; numconst; img_lia) | img_try (img_exact gBal)].
- split; [img_try (img_exact gRZ)|]. split; [img_try (img_exact gRZal) | img_try (img_exact gRN)].
- img_exact gNN.
- img_exact HBR.
- split; [img_try (img_exact W1)|]. split; [img_try (img_exact W2) | img_try (img_exact extent_present)].
- img_exact mag_val.
- img_exact shadow_present.
- split; [img_try (intros a Ha; img_apply rinfo_present; img_lia) | img_try (img_exact rg_val)].
- split; [img_try (img_exact A1) | img_try (img_exact A2)].
- img_exact SEED_ok.
Qed.
End f.
End c.
