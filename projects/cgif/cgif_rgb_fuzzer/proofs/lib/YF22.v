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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF0o YF1g YF2n YF32 YF1l YF0x YF1v YF07.
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
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFX_IMG_END, kBatchBytes, SHADOW_OFF, TFX_TP, TFX_TSD, TFX_INST, A_QUAR, A_ALLOCATOR, o_quar, o_space, o_rinfo, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize, kLowMemEnd, EV_MAX, kChunkHeaderSize, kHighShadowBeg, kHighShadowEnd in *.
Lemma recycle_chunk_prim : forall k X off, mem_chunk k (st_chunks X) = true -> ck_beg k = PPrim off ->
recycle_chunk k X = cache_dealloc (prim_class off) off (YF0x.X1 X k).
Proof.
intros k X off Hm Hb. unfold recycle_chunk, bind, get. cbn [ibind]. rewrite Hm. unfold mcheck, ret, put. cbn [ibind]. unfold YF0x.X1. rewrite Hb. img_refl.
Qed.
Section c. Context {imgk : img}.
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
Local Notation rcl := (YF1l.rcl off).
Local Notation rbase := (YF1l.rbase B ly k).
Local Notation rrz := (YF1l.rrz k).
Local Notation rnn := (YF1l.rnn k).
Local Notation rmuc := (YF1l.rmuc X off).
Local Notation hb1 := (YF1l.hb1 B ly k W mem).
Local Notation j1 := (YF1l.j1 ly W mem).
Local Notation j2 := (YF1l.j2 ly W mem).
Local Notation M := (YF1l.M B ly X k cbp W regs mem md PRE).
Local Notation LO := (am_layout B ly X rd0 M).
Local Notation HI := (YF1l.HI B ly X k cbp W regs mem md PRE).
Local Notation IMG := (YF1l.IMG B ly X k cbp W regs mem md PRE).
Local Notation GE := (YF1l.geom B ly X k cbp W regs mem md off PRE Hb).
Local Notation DRV := (YF1l.derived B ly X k cbp W regs mem md off PRE Hb).
Local Notation HSP := (YF1l.HSP B ly X k cbp W regs mem md PRE).
Local Notation FH := (YF1l.FH_ok B TB ly X k cbp W regs mem md off PRE Hb HTSD).
Local Notation Mv := (YF2n.Mv rbase rrz).
Local Notation SPv := (YF2n.SPv rbase rrz).
Local Notation CNT8v := (YF2n.CNT8v rnn).
Local Notation WINr := (YF2n.WIN ly regs rbase rrz rnn).
Local Notation X1 := (YF0x.X1 X k).
Lemma Hk : In k (st_chunks X). Proof. img_exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. img_exact (proj1 (proj2 (proj2 (proj2 PRE)))). Qed.
Lemma Hni : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. img_exact (proj1 (proj2 (proj2 (proj2 (proj2 PRE))))). Qed.
Lemma Hci : st_cache_inited X = true. Proof. img_exact (proj1 (proj2 PRE)). Qed.
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
zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096.
Proof.
pose proof (lo_disj ly LO) as HD.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear; img_lia)) (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(img_try (clear; img_lia)) (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK. cbn [fst snd] in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
Lemma WIN_zone : forall a, WINr a -> (sp0 - 256 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) \/
(0x2008fff7000 <= a < kHighMemBeg).
Proof.
intros a Hw. pose proof HI as HIx. pose proof DRV as DR. pose proof GE as GEx.
pose proof (YF0x.k_prim B ly X rd0 M k off Hk Hb) as KP. cbv zeta in KP.
unfold YF2n.WIN, YF2n.WINF, YF2n.WINS in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[[Hne Hw]|Hw]]|Hw]].
- left. img_exact Hw.
- do 2 right; left. unfold YF2n.Mv, YF1l.rbase, YF1l.rrz in *. clear - Hw DR GEx KP. numconst. img_lia.
- do 2 right; left. unfold YF1l.rbase in *. clear - Hw GEx KP. numconst. img_lia.
- right; left. clear - Hw. numconst. img_lia.
- do 3 right. clear - Hw DR. img_lia.
Qed.
Lemma WIN_dec : forall a, WINr a \/ ~ WINr a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
assert (ER : rrz = 16 \/ rrz <> 16) by img_lia.
unfold YF2n.WIN, YF2n.WINF, YF2n.WINS. fold sp0.
destruct (EM (sp0 - 256) sp0) as [C|C0]; [img_try (left; left; img_exact C)|].
destruct (EM Mv (Mv + 4)) as [C|C1]; [img_try (left; right; left; left; img_exact C)|].
destruct (EM (T + t_stats + 40) (T + t_stats + 56)) as [C|C3]; [img_try (left; right; left; right; right; img_exact C)|].
destruct (EM SPv (SPv + CNT8v)) as [C|C4]; [img_try (left; right; right; img_exact C)|].
destruct ER as [ER|ER].
- right. intros [X0|[[X1'|[[X2 _]|X3]]|X4]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1')) | img_try (img_exact (X2 ER)) | img_try (img_exact (C3 X3)) | img_try (img_exact (C4 X4))].
- destruct (EM rbase (rbase + 8)) as [C|C2]; [img_try (left; right; left; right; left; split; [img_exact ER | img_exact C])|].
right. intros [X0|[[X1'|[[_ X2]|X3]]|X4]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1')) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (C4 X4))].
Qed.
Definition low_okr {imgk : img} (a w : Z) : bool :=
((TFX_IMG_LO <=? a) && (a + w <=? TFX_IMG_END)) || ((SHADOW_OFF + TFX_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFX_IMG_END / 8)).
Definition const_loc_okr {imgk : img} (ce : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w ce)) in
match c_at ce with
| ANum a => low_okr a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okr (TFX_TSD + o) w
| ATp o => low_okr (TFX_TP + o) w
| AInst o => low_okr (TFX_INST + o) w
| _ => false
end.
Lemma Tfx_const_locr : forallb const_loc_okr (Tfx_const ly) = true.
Proof. clear. img_case; vm_compute. all: img_refl. Qed.
Lemma CONST_OUT : Forall (fun ce => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w ce)) -> ~ WINr (aeval B ly (c_at ce) + i) /\ 0 <= aeval B ly (c_at ce) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros ce Hce i Hi.
pose proof (proj1 (forallb_forall _ _) Tfx_const_locr ce Hce) as K. unfold const_loc_okr in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & ZC & ZD).
assert (ZN : forall a, ~ ((sp0 - 256 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) \/ (0x2008fff7000 <= a < kHighMemBeg)) -> ~ WINr a).
{ intros a Hn Hw. img_exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okr a (Z.max 1 (Z.of_nat (c_w ce))) = true -> ~ WINr (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L'. unfold low_okr in L'.
split; [img_try (img_apply ZN)|]; clear - L' Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, KSTACK, kThreadObjSize in *;
img_change (65536 / 8) with 8192 in *; img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in *; img_lia. }
destruct (c_at ce); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; img_lia.
- split; [img_try (img_apply ZN)|]; clear - K Hi ZC S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi ZD S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; img_lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk'. unfold aview. rewrite (Hv kk Hk'). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma WIN_D : forall a, WINr a -> YF0x.D B ly k sp0 a.
Proof.
intros a Hw. pose proof DRV as DR.
unfold YF0x.D, YF0x.DS, YF0x.DK, YF0x.DJ, YF0x.DH, YF0x.Mv.
unfold YF2n.WIN, YF2n.WINF, YF2n.WINS in Hw. fold sp0 in Hw.
unfold YF2n.Mv, YF2n.SPv, YF2n.CNT8v, YF2n.N8v, YF2n.Uv, YF1l.rbase, YF1l.rrz, YF1l.rnn in *. unfold shadow_addr.
destruct Hw as [Hw|[[Hw|[[Hne Hw]|Hw]]|Hw]].
- left. clear - Hw. unfold KSTACK. img_lia.
- right; left. left. img_exact Hw.
- right; left. right. split; [img_try (img_exact Hne) | img_try (img_exact Hw)].
- do 2 right; left. img_exact Hw.
- do 3 right. rewrite Z_div_mult in Hw by img_lia. img_lia.
Qed.
Lemma CDPRE : forall W' c', YF2n.at_CD W ly regs mem md rcl rbase rrz rnn hb1 W' c' ->
exists regs' mem' mat,
W' = W /\ c' = cfg_at tfxsegs A_CDealloc regs' mem' (with_vm_backing (m_vm_lazy md) mat md) /\
cd_pre B ly X1 rcl off W regs' mem' (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 2 = getr regs 2 /\ getr regs' 1 = getr regs 1 /\ (forall r, In r YF2n.SREGS -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly X a -> ~ ascratch B KSTACK regs a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a).
Proof.
intros W' c' HCD.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
destruct HCD as (-> & regs' & mem' & mat & -> & CSP & CRA & CS & C10 & C11 & C12 & C13 & MEQ' & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & SH).
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (HSP' : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (img_try (split; [img_try (img_exact Hlo) | img_try (clear - Hcb1 Hcb2; img_lia)])).
pose proof HI as HIx. pose proof DRV as DR. pose proof GE as GEx.
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0x.D B ly k sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by img_exact Ha. intros Hw. img_exact (ND (WIN_D a Hw)). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (xw := Z_to_bv 64 a) in *.
destruct (w_H W xw) eqn:Hx'; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs xw) eqn:ROM; [img_try (destruct (mem' xw); discriminate)|].
destruct (mem' xw) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem xw) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned xw). assert (Ex : Z_to_bv 64 a' = xw) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hbb]]. rewrite Ex in Hbb. congruence.
- rewrite (MEQ' xw C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb0 Hx'. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb0; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb0.
unfold w64 in *. set (xw := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned xw = a) by (img_try ((subst xw; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. fold xw in Hh. rewrite Hx' in Hh. discriminate.
- img_apply (MEQ' xw). rewrite Ux. img_exact C. }
assert (NEW_sh : forall a, YF0x.DH B ly k a -> rd a <> None -> rd' a = Some shHeapLeftRz).
{ intros a HD Hv. (subst rd rd'; cbv beta). unfold YF0x.DH, shadow_addr in HD.
assert (E8 : SHADOW_OFF + (ck_base B ly k + ck_rz k) / 8 = SPv) by (img_try (unfold YF2n.SPv, YF2n.Uv, YF1l.rbase, YF1l.rrz; img_lia)).
rewrite E8 in HD. img_change (ck_n k) with rnn in HD. unfold YF2n.CNT8v, YF2n.N8v in SH. rewrite Z_div_mult in SH by img_lia.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - HD DR; numconst; img_lia)).
unfold aview, mbyte, mrestrict in Hv |- *. replace a with (SPv + (a - SPv)) in Hv |- * by img_lia. unfold w64 in SH.
destruct (w_H W (Z_to_bv 64 (SPv + (a - SPv)))) eqn:Hh.
- exfalso. rewrite seg_rom_none_high in Hv by (img_try (clear - HD DR; numconst; img_lia)). img_exact (Hv eq_refl).
- rewrite (SH (a - SPv)) by img_lia. img_refl. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros ce Hce. eapply (cell_holds_agree B ly rd); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') ce Hce))|].
intros i Hi. (subst rd rd'; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUT ce Hce i Hi) as [Y1 Y2]. img_apply aview_same.
img_apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by img_exact Y2. img_exact Y1. }
pose proof (YF0x.rc_fin_ARm B TB ly X rd rd' M' k off Hk Hst Hb Hni Hci sp0 HSP' IMG AG VIS NEW_sh CONST') as MF.
pose proof (YF0x.DEL B ly X rd M' k off Hk Hst Hb Hni) as (W1 & D1 & D2 & D3 & D4 & D5 & D6). cbv zeta in D2, D3, D4, D6.
assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly X a -> ~ ascratch B KSTACK regs a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a).
{ intros a Ha NO NS. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0x.D_owned B ly X rd M' k off Hk Hst Hb sp0 HSP' a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; unfold ascratch, spZ; left; img_exact O)]. }
assert (PUF : forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a).
{ intros a Ha (c' & Hc' & Hr) NK. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _). pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
pose proof (wf_classes _ _ _ _ _ (am_wf B ly X rd M') c' Hc') as CL'. pose proof (wr_alloc _ _ _ _ _ _ CL') as A1.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' (am_wf B ly X rd M') Hc') as MB. unfold kUserMapSize, EV_MAX in MB.
pose proof GEO as (G_PT & _ & _ & G_PS & _).
unfold YF0x.D, YF0x.DS, YF0x.DK, YF0x.DJ, YF0x.DH, YF0x.Mv in HD.
pose proof GEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RZ & _ & RN & RNS & EXT & _). unfold YF1l.rrz, YF1l.rnn in RZ, RN, RNS, EXT.
destruct HD as [Y|[Y|[Y|Y]]].
- clear - Y Hr R1 R2 A1 MB G_PS HSP'. numconst. img_lia.
- img_apply NK. clear - Y RZ RN RNS EXT. numconst. img_lia.
- clear - Y Hr R1 R2 A1 MB G_PT hT1. numconst. img_lia.
- unfold shadow_addr in Y. pose proof (YF0x.k_prim B ly X rd M' k off Hk Hb) as KP. cbv zeta in KP. destruct KP as (KP1 & KP2 & _).
pose proof (YF0x.ext_rounded B ly X rd M' k off Hk) as (ER & _ & QP & _).
clear - Y Hr R1 R2 A1 MB hP1 hP2 RN RZ KP1 KP2 ER QP. numconst.
assert (Y' : (ck_base B ly k + ck_rz k + (ck_n k + 7) / 8 * 8) / 8 <= 140735332483072 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)).
rewrite Z.div_add in Y' by img_lia. img_change (140735332483072 / 8) with 17591916560384 in Y'. img_lia. }
exists regs', mem', mat. split; [img_refl|]. split; [img_refl|]. split; [|img_try (split; [img_exact CSP | split; [img_exact CRA | split; [img_exact CS | split; [img_exact FR | img_exact PUF]]]])].
unfold cd_pre. unfold spZ, raZ. rewrite CSP, CRA. fold sp0.
split.
{   split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
- eapply ALedger_same; [img_try (img_exact (YF0x.ALedger_X1 B ly X rd M' k off Hk Hb tfxsegs md LED)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
- destruct BUD as [BUD PIN]. split; [| img_try (img_exact (YF0x.asecA_S' B ly X rd M' k off Hk Hb _ PIN))].
rewrite (YF0x.abudget' B ly X rd M' k off Hk Hb). img_exact BUD.
- eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
- eapply (ahs_transfer tfxsegs B ly X _ (w_H W) mem mem' (al_img_env tfxsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
+ eapply (aclient_band_same_frames B ly X); [img_try (img_exact MF) | img_try (img_exact (YF0x.frames' X k))].
+ img_exact (YF0x.sec_extents' B ly X rd M' k off Hk Hb).
+
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. img_apply AG; [img_try (clear - SBg; img_lia)|].
intros HD. pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
pose proof (YF0x.k_prim B ly X rd M' k off Hk Hb) as KP. cbv zeta in KP. destruct KP as (KP1 & KP2 & _).
pose proof (YF0x.ext_rounded B ly X rd M' k off Hk) as (ER & NN1 & QP & _).
unfold YF0x.D, YF0x.DS, YF0x.DK, YF0x.DJ, YF0x.Mv in HD.
destruct HD as [Y|[Y|[Y|Y]]].
* clear - Y SBg hS1 HSP'. numconst. img_lia.
* pose proof GEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RZ & _). clear - Y SBg KP1 KP2 hP1 RZ. unfold YF1l.rrz in RZ. numconst. img_lia.
* clear - Y SBg hT1. unfold zone3, zone3cases in hT1. numconst. img_lia.
* apply (YF0x.DH_iff B ly X rd M' k off Hk Hb g Hg) in Y.
unfold hfree in HF. apply Forall_app in HF as [HF _]. unfold static_extents in HF. apply Forall_cons_iff in HF as [HF _]. cbn [fst snd] in HF.
pose proof GEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RZ & _). unfold YF1l.rrz in RZ. clear - Y HF KP1 KP2 ER QP RZ. nia. }
split; [img_try (img_exact Hci)|]. split; [img_try (img_exact D1)|]. split; [img_try (img_exact D2)|]. split; [img_try (img_exact D3)|]. split; [img_try (img_exact D4)|]. split; [img_try (img_exact D6)|].
split; [img_try (img_exact Hra)|]. split; [img_try (img_exact Hra4)|]. split; [img_try (img_exact Hal)|]. split; [img_try (img_exact Hlo)|]. split; [img_try (clear - Hcb1 Hcb2; img_lia)|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 256)) as [Hlow|Hhigh].
- img_apply (apresent_same (w_H W) mem); [|img_try (img_apply HPRES; img_exact Ha)]. img_apply MEQ'. pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha Usp HSP' hS1; numconst; img_lia)). rewrite unsigned_lit_small by img_exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hlow G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2 hS1. numconst. img_lia.
- img_apply PRESW. unfold YF2n.WIN. left. fold sp0. img_lia. }
split; [img_try (rewrite (CS 3%bv ltac:(cbn; tauto)); img_exact Hgp)|]. split; [img_try (rewrite (CS 4%bv ltac:(cbn; tauto)); img_exact Htp)|].
split; [img_try (img_exact C10)|]. split; [img_try (img_exact C11)|]. split; [img_try (img_exact C12)|]. rewrite C13. pose proof GEx as (_ & G2 & _). unfold YF1l.rbase in G2 |- *. rewrite G2. img_refl.
Qed.
Theorem tfx_rchunk_prim_arm : amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
rewrite (recycle_chunk_prim k X off (proj2 (mem_chunk_spec _ _) Hk) Hb).
unfold cfg_at, A_RChunk. rewrite <- (wvb_self md) at 1.
eapply (amreal_SRr_pre tfxsegs _ _ _ _ (YF2n.at_CD W ly regs mem md rcl rbase rrz rnn hb1)).
{ img_exact (YF32.segRC W ly regs mem md rcl rbase rrz rnn hb1 cbp rmuc j1 j2 (m_vm_materialized md) FH). }
intros W' c' _ HCD. destruct (CDPRE W' c' HCD) as (regs' & mem' & mat & -> & -> & PRE' & R2 & R1 & RS & FR & PUF).
eapply amreal_mono; [| img_try (img_exact (YF1v.tfx_cdealloc_ok B TB ly X1 rcl off W regs' mem' _ PRE' HTSD))].
cbv beta. intros [[] S''] W'' c'' HL. destruct HL as (regs'' & mem'' & md'' & -> & AP & UF & CI). exists regs'', mem'', md''.
split; [img_try (unfold cfg_at, raZ; rewrite R1; img_refl)|].
split.
2:{ split; [|img_try (img_exact CI)]. intros a Ha PU NK. rewrite (UF a Ha) by img_exact PU. img_exact (PUF a Ha PU NK). }
destruct AP as (AR'' & LLE & WLE & RP & IO & FRM & PRS). unfold acall_post. unfold spZ in *. rewrite R2 in PRS.
split; [img_try (img_exact AR'')|]. split; [img_try (img_exact LLE)|]. split; [img_try (img_exact WLE)|]. split.
{ intros r Hr. rewrite (RP r Hr). unfold acallee_saved in Hr.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
destruct R as [->|R]; [img_try (img_exact R2)|]. img_apply RS. clear - R. unfold YF2n.SREGS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; (subst r; cbv beta); cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]). }
split. { pose proof (same_io_wvb md mat) as IO1. clear - IO IO1. unfold same_io in *. destruct IO as (I1 & I2 & I3 & I4). destruct IO1 as (J1 & J2 & J3 & J4). repeat split; congruence. }
split.
{ pose proof PRE as PRE2. destruct PRE2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in Hlo, Hcb1.
assert (HSP0 : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (img_try (unfold sp0; clear - Hlo Hcb1 Hcb2; img_lia)).
intros a Ha NO NO' NS NE. rewrite (FRM a Ha); [img_try (img_apply FR; [img_exact Ha | img_exact NO | img_exact NS]) | | img_try (img_exact NO') | img_try (unfold ascratch, spZ in *; rewrite R2; img_exact NS) | img_try (img_exact NE)].
intros O1. img_apply NO. img_exact (proj1 (YF0x.aowned_X1 B ly X _ (YF1l.M B ly X k cbp W regs mem md PRE) k off Hk Hst Hb sp0 HSP0 a) O1). }
img_exact PRS.
Qed.
End c.
Theorem tfx_rchunk_prim {imgk : img} : forall B, TfxSyms B -> forall ly X k cbp W regs mem md off,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PPrim off -> ly_tsd ly = TFX_TSD ->
amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof. intros B TB ly X k cbp W regs mem md off PRE Hb HTSD. img_exact (tfx_rchunk_prim_arm B TB ly X k cbp W regs mem md off PRE Hb HTSD). Qed.
End b.
