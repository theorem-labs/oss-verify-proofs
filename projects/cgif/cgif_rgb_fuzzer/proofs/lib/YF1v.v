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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0r YF0w YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1b YF0j YF0i YF2f YF2t YF2j YF2x YF1i YF2u YF1c YF0t YF07.
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
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFX_IMG_END, kBatchBytes, SHADOW_OFF, TFX_TP, TFX_TSD, TFX_INST, A_QUAR, A_ALLOCATOR, o_quar, o_space, o_rinfo, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize, kLowMemEnd, EV_MAX in *.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. img_refl. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_io. destruct md as [fd [maps lazy mat0] io fs proc lim tm]. cbn. repeat split; img_refl. Qed.
Section d. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (c off : Z) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : cd_pre B ly X c off W regs mem md.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation kcnt := (YF1c.kcnt X c).
Local Notation kold := (YF1c.kold X c).
Local Notation kmf := (YF1c.kmf X c).
Local Notation M := (YF1c.M B ly X c off W regs mem md PRE).
Local Notation LO := (am_layout B ly X rd0 M).
Local Notation HI := (YF1c.HI B ly X c off W regs mem md PRE).
Local Notation IMG := (YF1c.IMG B ly X c off W regs mem md PRE).
Local Notation DRV := (YF1c.derived B ly X c off W regs mem md PRE).
Local Notation HSP := (YF1c.HSP B ly X c off W regs mem md PRE).
Local Notation Hc := (YF1c.Hc B ly X c off W regs mem md PRE).
Local Notation KF := (YF1c.class_facts B ly X c off W regs mem md PRE).
Local Notation RF := (YF1c.reg_facts B ly X c off W regs mem md PRE).
Local Notation PCv := (YF2f.PCv ly c).
Local Notation MAXv := (YF2f.MAXv c).
Local Notation Nv := (YF2f.Nv c).
Local Notation RGv := (YF2f.RGv ly c).
Local Notation DSTv := (YF2f.DSTv ly c kold).
Local Notation SRCv := (YF2f.SRCv ly c kcnt).
Local Notation SLOTv := (YF2f.SLOTv ly c kcnt).
Local Notation WINk := (YF2f.WIN ly regs c kcnt kold).
Local Notation S' := (YF0t.S' X c off).
Lemma GEO :
(ly_prim ly + kPrimResvSize <= T \/ T + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_prim ly) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\
(T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= T) /\
(ly_C ly + 256 <= ly_D ly \/ ly_D ly + 4096 <= ly_C ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_C ly) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly) /\
(4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) /\ (4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL).
Proof.
pose proof (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) as IC. pose proof (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) as ID.
cbn beta in IC, ID. cbn [fst snd] in IC, ID. unfold in_app in IC, ID.
assert (C12 : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by (img_try (clear - IC; ceil; unfold zone3, TFX_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; img_lia)).
assert (D12 : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by (img_try (clear - ID; ceil; unfold zone3, TFX_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; img_lia)). clear IC ID.
pose proof (lo_disj ly LO) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
destruct C12 as [C1 C2]. destruct D12 as [D1 D2].
unfold zdisjoint in *. cbn [fst snd] in *. repeat match goal with G : _ /\ _ |- _ => destruct G as [? ?] end. splits; assumption.
Qed.
Lemma WIN_zone : forall a, WINk a -> (sp0 - 320 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof HI as HIx. pose proof DRV as DR. pose proof RF as RFx. pose proof KF as KFx.
assert (CNTP : 0 <= YF2f.CNTPv c kcnt < MAXv) by (img_try (unfold YF2f.CNTPv; destruct (Z.eqb_spec kcnt MAXv); clear - RFx KFx e || clear - RFx KFx n; img_lia)).
unfold YF2f.WIN, YF2f.WINF, YF2f.WINR, YF2f.WRG in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[Hf Hw]]].
- left. img_exact Hw.
- right; left. unfold YF2f.SLOTv in Hw. clear - Hw DR CNTP KFx. numconst. img_lia.
- right; right. unfold YF2f.DSTv, YF1c.kold, YF1c.kmf, YF2f.Nv, YF2f.MAXv in *. clear - Hw HIx DR RFx KFx Hf. numconst. img_lia.
Qed.
Lemma WIN_dec : forall a, WINk a \/ ~ WINk a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
assert (EF : kcnt = MAXv \/ kcnt <> MAXv) by img_lia.
unfold YF2f.WIN, YF2f.WINF, YF2f.WINR, YF2f.WRG. fold sp0.
destruct (EM (sp0 - 320) sp0) as [C|C0]; [img_try (left; left; img_exact C)|].
destruct (EM PCv (PCv + 4)) as [C|C1]; [img_try (left; right; left; left; img_exact C)|].
destruct (EM SLOTv (SLOTv + 4)) as [C|C2]; [img_try (left; right; left; right; left; img_exact C)|].
destruct (EM (T + t_cache + 2576) (T + t_cache + 2584)) as [C|C3]; [img_try (left; right; left; right; right; img_exact C)|].
destruct EF as [EF|EF].
- destruct (EM RGv (RGv + 8)) as [C|C4]; [img_try (left; do 2 right; split; [img_exact EF | left; left; img_exact C])|].
destruct (EM (RGv + 16) (RGv + 24)) as [C|C5]; [img_try (left; do 2 right; split; [img_exact EF | left; right; left; img_exact C])|].
destruct (EM (RGv + 80) (RGv + 88)) as [C|C6]; [img_try (left; do 2 right; split; [img_exact EF | left; right; right; img_exact C])|].
destruct (EM DSTv (DSTv + 4 * Nv)) as [C|C7]; [img_try (left; do 2 right; split; [img_exact EF | right; img_exact C])|].
right. intros [X0|[[X1|[X2|X3]]|[_ [[X4|[X5|X6]]|X7]]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (C4 X4)) | img_try (img_exact (C5 X5)) | img_try (img_exact (C6 X6)) | img_try (img_exact (C7 X7))].
- right. intros [X0|[[X1|[X2|X3]]|[X4 _]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (EF X4))].
Qed.
Definition low_okq {imgk : img} (a w : Z) : bool :=
((TFX_IMG_LO <=? a) && (a + w <=? TFX_IMG_END)) || ((SHADOW_OFF + TFX_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFX_IMG_END / 8)).
Definition const_loc_okq {imgk : img} (ce : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w ce)) in
match c_at ce with
| ANum a => low_okq a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okq (TFX_TSD + o) w
| ATp o => low_okq (TFX_TP + o) w
| AInst o => low_okq (TFX_INST + o) w
| _ => false
end.
Lemma Tfx_const_locq : forallb const_loc_okq (Tfx_const ly) = true.
Proof. clear. img_case; vm_compute. all: img_refl. Qed.
Lemma CONST_OUT : Forall (fun ce => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w ce)) -> ~ WINk (aeval B ly (c_at ce) + i) /\ 0 <= aeval B ly (c_at ce) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros ce Hce i Hi.
pose proof (proj1 (forallb_forall _ _) Tfx_const_locq ce Hce) as K. unfold const_loc_okq in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 320 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINk a).
{ intros a Hn Hw. img_exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okq a (Z.max 1 (Z.of_nat (c_w ce))) = true -> ~ WINk (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L'. unfold low_okq in L'.
split; [img_try (img_apply ZN)|]; clear - L' Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, KSTACK, kThreadObjSize in *;
img_change (65536 / 8) with 8192 in *; img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in *; img_lia. }
destruct (c_at ce); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; img_lia.
- split; [img_try (img_apply ZN)|]; clear - K Hi C1 C2 S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi D1 D2 S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; img_lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma WIN_D : forall a, WINk a -> YF0t.D ly X c sp0 a.
Proof.
intros a Hw. unfold YF0t.D, YF0t.DT, YF0t.DR, YF0t.DF, YF0t.DS.
unfold YF2f.WIN, YF2f.WINF, YF2f.WINR, YF2f.WRG in Hw. fold sp0 in Hw.
assert (EFULL : kcnt = MAXv -> YF0t.full X c = true) by (img_try (intros E; unfold YF0t.full; img_apply Z.eqb_eq; img_exact E)).
assert (ESLOT : YF0t.SLOTv ly X c = SLOTv).
{ unfold YF0t.SLOTv, YF0t.CNTP, YF0t.PCv, YF0t.full, YF2f.SLOTv, YF2f.CNTPv, YF2f.PCv, YF2f.Nv, YF2f.MAXv, YF1c.kcnt.
destruct (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c); img_refl. }
assert (EPC : YF0t.PCv ly c = PCv) by img_refl.
assert (ERG : YF0t.RGv ly c = RGv) by (img_try (unfold YF0t.RGv, YF2f.RGv, YF2f.RIv; img_lia)).
assert (EDST : YF0t.DSTv ly X c = DSTv) by (img_try (unfold YF0t.DSTv, YF0t.FAv, YF2f.DSTv, YF2f.FAv, YF2f.RBv, YF1c.kold, fa_base; img_lia)).
rewrite ESLOT, EPC, ERG, EDST. img_change (max_cached c / 2) with Nv.
destruct Hw as [Hw|[Hw|[Hf Hw]]].
- do 3 right. clear - Hw. unfold KSTACK. img_lia.
- left. img_exact Hw.
- destruct Hw as [Hw|Hw]; [img_try (right; left) | img_try (right; right; left)]; (split; [img_try (img_exact (EFULL Hf)) | img_try (img_exact Hw)]).
Qed.
Lemma PREF : st_cache_inited X = true /\ 1 <= c <= 30 /\ 0 <= off - region_off c < rg_alloc_user (reg X c) /\ (off - region_off c) mod class_size c = 0 /\
~ In (off - region_off c) (class_elems X c) /\
4 * (Z.of_nat (length (class_elems X c)) + 1 + (0 + bslack c 0 + 2 * (EV_MAX - st_nev X))) <= rg_mapped_fa (reg X c).
Proof. destruct PRE as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _). repeat split; assumption || tauto. Qed.
Lemma FINKH : forall W' c', YF2f.at_RETK W ly regs mem md c off kcnt kold kmf W' c' -> cd_leaf B ly X W regs mem md (tt, S') W' c'.
Proof.
intros W' c' HR.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hci & Hcc & Hx & Hxm & Hxni & HROOM & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & CSP & CS & MEQ' & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & VF).
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof HSP as HSP'. pose proof HI as HIx. pose proof RF as RFx. pose proof KF as KFx. pose proof DRV as DR.
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0t.D ly X c sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by img_exact Ha. intros X'. img_exact (ND (WIN_D a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx'; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem' x); discriminate)|].
destruct (mem' x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
- rewrite (MEQ' x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx'. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. fold x in Hh. rewrite Hx' in Hh. discriminate.
- img_apply (MEQ' x). rewrite Ux. img_exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfxsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0h.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (EFULL : YF0t.full X c = (kcnt =? MAXv)) by img_refl.
assert (ECNTP : YF0t.CNTP X c = YF2f.CNTPv c kcnt).
{ unfold YF0t.CNTP, YF2f.CNTPv. rewrite EFULL. unfold YF1c.kcnt, YF2f.Nv, YF2f.MAXv. destruct (_ =? _); img_refl. }
assert (NEW_cnt : forall i, (i < 4)%nat -> rd' (YF0t.PCv ly c + Z.of_nat i) = Some (YG0h.le_byte (YF0t.CNTP X c + 1) 4 i)).
{ img_apply (VM _ _ 4%nat _ _ V1); [img_refl | img_try (rewrite ECNTP; img_refl)]. }
assert (NEW_slot : forall i, (i < 4)%nat -> rd' (YF0t.SLOTv ly X c + Z.of_nat i) = Some (YG0h.le_byte ((off - region_off c) / 16) 4 i)).
{ img_apply (VM _ _ 4%nat _ _ V2); [| img_refl]. unfold YF0t.SLOTv, YF2f.SLOTv. rewrite ECNTP. img_refl. }
assert (ERG : YF0t.RGv ly c = RGv) by (img_try (unfold YF0t.RGv, YF2f.RGv, YF2f.RIv; img_lia)).
assert (EDST : YF0t.DSTv ly X c = DSTv) by (img_try (unfold YF0t.DSTv, YF0t.FAv, YF2f.DSTv, YF2f.FAv, YF2f.RBv, YF1c.kold, fa_base; img_lia)).
assert (NEW_rg0 : YF0t.full X c = true -> forall i, (i < 8)%nat -> rd' (YF0t.RGv ly c + Z.of_nat i) = Some (YG0h.le_byte 0 8 i)).
{ intros Hf. rewrite EFULL in Hf. apply Z.eqb_eq in Hf. destruct (VF Hf) as (R0 & _). img_apply (VM _ _ 8%nat _ _ R0); [img_try (img_exact (eq_sym ERG)) | img_refl]. }
assert (NEW_rg16 : YF0t.full X c = true -> forall i, (i < 8)%nat ->
rd' (YF0t.RGv ly c + 16 + Z.of_nat i) = Some (YG0h.le_byte (fa_len (rg_free (reg X c)) + max_cached c / 2) 8 i)).
{ intros Hf. rewrite EFULL in Hf. apply Z.eqb_eq in Hf. destruct (VF Hf) as (_ & R16 & _). img_apply (VM _ _ 8%nat _ _ R16); [img_try (rewrite ERG; img_refl) | img_refl]. }
assert (NEW_fa : YF0t.full X c = true -> forall (j : nat) v, Z.of_nat j < max_cached c / 2 ->
nth_error (pc_chunks (cache X c)) (Z.to_nat (Z.of_nat (length (pc_chunks (cache X c))) - max_cached c / 2) + j) = Some v ->
forall i, (i < 4)%nat -> rd' (YF0t.DSTv ly X c + 4 * Z.of_nat j + Z.of_nat i) = Some (YG0h.le_byte (v / 16) 4 i)).
{ intros Hf j v Hj Hv. rewrite EFULL in Hf. apply Z.eqb_eq in Hf. destruct (VF Hf) as (_ & _ & _ & CPY).
pose proof (YF1c.slot_vals B ly X c off W regs mem md PRE _ v Hv) as SV.
assert (ESRC : PCv + 16 + 4 * Z.of_nat (Z.to_nat (Z.of_nat (length (pc_chunks (cache X c))) - max_cached c / 2) + j) = SRCv + 4 * Z.of_nat j).
{ unfold YF2f.SRCv, YF1c.kcnt, YF2f.Nv, YF2f.MAXv. unfold YF1c.kcnt, YF2f.MAXv, YF2f.Nv in Hf, KFx. clear - Hj Hf KFx. rewrite Nat2Z.inj_add, Z2Nat.id by img_lia. img_lia. }
rewrite ESRC in SV. img_apply (VM _ _ 4%nat _ _ (CPY (Z.of_nat j) (v / 16) ltac:(img_try (unfold YF2f.Nv, YF2f.MAXv; img_lia)) SV)); [img_try (rewrite EDST; img_refl) | img_refl]. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros ce Hce. eapply (cell_holds_agree B ly rd); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') ce Hce))|].
intros i Hi. (subst rd rd'; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUT ce Hce i Hi) as [X1 X2]. img_apply aview_same.
img_apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by img_exact X2. img_exact X1. }
pose proof (YF0t.cd_fin_ARm B TB ly X rd rd' M' c off Hci Hcc Hx Hxm Hxni HROOM sp0 HSP' IMG AG VIS NEW_cnt NEW_slot NEW_rg0 NEW_rg16 NEW_fa CONST') as MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split.
2:{ split; [|img_try (img_exact (YF0t.S'_cinit X c off Hci))].
intros a Ha (c' & Hc' & Hr). img_apply AG; [img_try (img_exact Ha)|]. intros HD.
pose proof (wf_classes _ _ _ _ _ (am_wf B ly X rd M') c' Hc') as CL'. pose proof (wr_alloc _ _ _ _ _ _ CL') as A1.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' (am_wf B ly X rd M') Hc') as MB. unfold kUserMapSize, EV_MAX in MB.
pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _).
destruct (YF0t.user_vs_D B ly X rd M' c off Hci Hcc Hx Hxm HROOM IMG c' a Hc' ltac:(img_try (clear - Hr A1 MB; img_lia))) as [N1 N2].
destruct (YF0t.ok_prim B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG a ltac:(img_try (clear - Hr A1 MB R1 R2; img_lia)) N1 N2) as [_ ND]. img_exact (ND HD). }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_apply wle_refl | split; [|split; [|split]]]])].
- split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [img_try (img_exact (YF0t.ALedger_S' B ly X rd M' c off Hcc Hx Hxm sp0 HSP' tfxsegs md LED)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+ destruct BUD as [BUD PIN]. split; [| img_try (img_exact (YF0t.asecA_S' ly X c off _ PIN))].
eapply Z.le_trans; [img_try (img_exact BUD)|]. rewrite <- (YF0t.abudget_S' X c off). img_apply Z.le_refl.
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly X _ (w_H W) mem mem' (al_img_env tfxsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [img_try (img_exact MF) | img_try (img_exact (YF0t.frames' X c off))].
* img_exact (YF0t.sec_extents' ly X c off).
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
intros HD. pose proof HIx as (hP1 & _ & hT1 & _ & hS1 & _).
destruct (YF0t.D_owned B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG (shadow_addr g) ltac:(img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)) HD) as [O|O].
-- pose proof (YF0t.D_cases B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG _ HD) as DC.
clear - DC SBg hP1 hT1 hS1. unfold in_band_rw, zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kThreadObjSize in *. img_lia.
-- unfold YF0t.DS in O. clear - O SBg hS1 HSP'. unfold in_band_rw, zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, KSTACK in *. img_lia.
- intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
destruct R as [->|R]; [img_try (img_exact CSP)|]. img_apply CS. clear - R. unfold YF2f.SREGS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; (subst r; cbv beta); cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]).
- img_apply same_io_wvb.
- intros a Ha NO NO' NS NE. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0t.D_owned B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; unfold ascratch, spZ; left; img_exact O)].
- intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 320)) as [Hb|Hb].
+ img_apply (apresent_same (w_H W) mem); [|img_try (img_apply HPRES; img_exact Ha)]. img_apply MEQ'. pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha Usp HSP' hS1; unfold zone3, TFX_IMG_LO, kLowShadowBeg, KSTACK, kHighMemBeg in *; img_lia)). rewrite unsigned_lit_small by img_exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *. img_lia.
+ img_apply PRESW. unfold YF2f.WIN. left. fold sp0. img_lia.
Qed.
Theorem tfx_cdealloc_arm : amreal tfxsegs (cache_dealloc c off X) W (cfg_at tfxsegs A_CDealloc regs mem md) (cd_leaf B ly X W regs mem md).
Proof.
pose proof PREF as (Hci & Hcc & Hx & Hxm & Hxni & HROOM).
rewrite (YF0t.cache_dealloc_S' B ly X rd0 M c off Hci Hcc Hx Hxm HROOM). cbn [amreal].
destruct (YF1c.junk_vals B ly X c off W regs mem md PRE) as (j80 & j88 & jst & HJ80 & HJ88 & HJST).
pose proof (YF1c.FH_ok B TB ly X c off W regs mem md PRE j80 j88 jst HJ80 HJ88 HJST) as FH.
pose proof RF as RFx.
unfold cfg_at, A_CDealloc. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [| img_try (intros W' c' _ HR; img_exact (FINKH W' c' HR))].
destruct (Z_lt_le_dec kcnt MAXv) as [LT|GE].
- img_exact (YF2t.segK1 W ly regs mem md c off kcnt kold kmf j80 j88 jst (m_vm_materialized md) FH LT).
- img_apply (YF2u.segK2 W ly regs mem md c off kcnt kold kmf j80 j88 jst (m_vm_materialized md) FH). clear - RFx GE. unfold YF2f.MAXv in *. img_lia.
Qed.
End d.
Theorem tfx_cdealloc_ok {imgk : img} : forall B, TfxSyms B -> forall ly X c off W regs mem md,
cd_pre B ly X c off W regs mem md -> ly_tsd ly = TFX_TSD ->
amreal tfxsegs (cache_dealloc c off X) W (cfg_at tfxsegs A_CDealloc regs mem md) (cd_leaf B ly X W regs mem md).
Proof. intros B TB ly X c off W regs mem md PRE HTSD. img_exact (tfx_cdealloc_arm B TB ly X c off W regs mem md PRE HTSD). Qed.
End b.
