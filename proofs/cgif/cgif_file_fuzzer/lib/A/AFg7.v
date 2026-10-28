(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFeu AFfm AFgs AFh7 AFfr AFf3 AFg0 AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_QUAR, A_ALLOCATOR, o_quar, o_space, o_rinfo, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize, kLowMemEnd, EV_MAX, kChunkHeaderSize, kHighShadowBeg, kHighShadowEnd in *.
Lemma recycle_chunk_prim : forall k X off, mem_chunk k (st_chunks X) = true -> ck_beg k = PPrim off ->
recycle_chunk k X = cache_dealloc (prim_class off) off (AFf3.X1 X k).
Proof.
intros k X off Hm Hb. unfold recycle_chunk, bind, get. cbn [ibind]. rewrite Hm. unfold mcheck, ret, put. cbn [ibind]. unfold AFf3.X1. rewrite Hb. reflexivity.
Qed.
Section c.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variable off : Z.
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PPrim off.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation rcl := (AFfr.rcl off).
Local Notation rbase := (AFfr.rbase B ly k).
Local Notation rrz := (AFfr.rrz k).
Local Notation rnn := (AFfr.rnn k).
Local Notation rmuc := (AFfr.rmuc X off).
Local Notation hb1 := (AFfr.hb1 B ly k W mem).
Local Notation j1 := (AFfr.j1 ly W mem).
Local Notation j2 := (AFfr.j2 ly W mem).
Local Notation M := (AFfr.M B ly X k cbp W regs mem md PRE).
Local Notation LO := (am_layout B ly X rd0 M).
Local Notation HI := (AFfr.HI B ly X k cbp W regs mem md PRE).
Local Notation IMG := (AFfr.IMG B ly X k cbp W regs mem md PRE).
Local Notation GE := (AFfr.geom B ly X k cbp W regs mem md off PRE Hb).
Local Notation DRV := (AFfr.derived B ly X k cbp W regs mem md off PRE Hb).
Local Notation HSP := (AFfr.HSP B ly X k cbp W regs mem md PRE).
Local Notation FH := (AFfr.FH_ok B TB ly X k cbp W regs mem md off PRE Hb HTSD).
Local Notation Mv := (AFgs.Mv rbase rrz).
Local Notation SPv := (AFgs.SPv rbase rrz).
Local Notation CNT8v := (AFgs.CNT8v rnn).
Local Notation WINr := (AFgs.WIN ly regs rbase rrz rnn).
Local Notation X1 := (AFf3.X1 X k).
Lemma Hk : In k (st_chunks X). Proof. exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. exact (proj1 (proj2 (proj2 (proj2 PRE)))). Qed.
Lemma Hni : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 PRE))))). Qed.
Lemma Hci : st_cache_inited X = true. Proof. exact (proj1 (proj2 PRE)). Qed.
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
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear; lia) (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(clear; lia) (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
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
pose proof (AFf3.k_prim B ly X rd0 M k off Hk Hb) as KP. cbv zeta in KP.
unfold AFgs.WIN, AFgs.WINF, AFgs.WINS in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[[Hne Hw]|Hw]]|Hw]].
- left. exact Hw.
- do 2 right; left. unfold AFgs.Mv, AFfr.rbase, AFfr.rrz in *. clear - Hw DR GEx KP. numconst. lia.
- do 2 right; left. unfold AFfr.rbase in *. clear - Hw GEx KP. numconst. lia.
- right; left. clear - Hw. numconst. lia.
- do 3 right. clear - Hw DR. lia.
Qed.
Lemma WIN_dec : forall a, WINr a \/ ~ WINr a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
assert (ER : rrz = 16 \/ rrz <> 16) by lia.
unfold AFgs.WIN, AFgs.WINF, AFgs.WINS. fold sp0.
destruct (EM (sp0 - 256) sp0) as [C|C0]; [left; left; exact C|].
destruct (EM Mv (Mv + 4)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM (T + t_stats + 40) (T + t_stats + 56)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct (EM SPv (SPv + CNT8v)) as [C|C4]; [left; right; right; exact C|].
destruct ER as [ER|ER].
- right. intros [X0|[[X1'|[[X2 _]|X3]]|X4]]; [exact (C0 X0) | exact (C1 X1') | exact (X2 ER) | exact (C3 X3) | exact (C4 X4)].
- destruct (EM rbase (rbase + 8)) as [C|C2]; [left; right; left; right; left; split; [exact ER | exact C]|].
right. intros [X0|[[X1'|[[_ X2]|X3]]|X4]]; [exact (C0 X0) | exact (C1 X1') | exact (C2 X2) | exact (C3 X3) | exact (C4 X4)].
Qed.
Definition low_okr (a w : Z) : bool :=
((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) || ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_okr (ce : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w ce)) in
match c_at ce with
| ANum a => low_okr a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okr (TFIB_TSD + o) w
| ATp o => low_okr (TFIB_TP + o) w
| AInst o => low_okr (TFIB_INST + o) w
| _ => false
end.
Lemma Tfib_const_locr : forallb const_loc_okr (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Lemma CONST_OUT : Forall (fun ce => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w ce)) -> ~ WINr (aeval B ly (c_at ce) + i) /\ 0 <= aeval B ly (c_at ce) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros ce Hce i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locr ce Hce) as K. unfold const_loc_okr in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & ZC & ZD).
assert (ZN : forall a, ~ ((sp0 - 256 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) \/ (0x2008fff7000 <= a < kHighMemBeg)) -> ~ WINr a).
{ intros a Hn Hw. exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okr a (Z.max 1 (Z.of_nat (c_w ce))) = true -> ~ WINr (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L'. unfold low_okr in L'.
split; [apply ZN|]; clear - L' Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, KSTACK, kThreadObjSize in *;
change (65536 / 8) with 8192 in *; change (6270976 / 8) with 783872 in *; lia. }
destruct (c_at ce); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- split; [apply ZN|]; clear - K Hi ZC S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi ZD S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk'. unfold aview. rewrite (Hv kk Hk'). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma WIN_D : forall a, WINr a -> AFf3.D B ly k sp0 a.
Proof.
intros a Hw. pose proof DRV as DR.
unfold AFf3.D, AFf3.DS, AFf3.DK, AFf3.DJ, AFf3.DH, AFf3.Mv.
unfold AFgs.WIN, AFgs.WINF, AFgs.WINS in Hw. fold sp0 in Hw.
unfold AFgs.Mv, AFgs.SPv, AFgs.CNT8v, AFgs.N8v, AFgs.Uv, AFfr.rbase, AFfr.rrz, AFfr.rnn in *. unfold shadow_addr.
destruct Hw as [Hw|[[Hw|[[Hne Hw]|Hw]]|Hw]].
- left. clear - Hw. unfold KSTACK. lia.
- right; left. left. exact Hw.
- right; left. right. split; [exact Hne | exact Hw].
- do 2 right; left. exact Hw.
- do 3 right. rewrite Z_div_mult in Hw by lia. lia.
Qed.
Lemma CDPRE : forall W' c', AFgs.at_CD W ly regs mem md rcl rbase rrz rnn hb1 W' c' ->
exists regs' mem' mat,
W' = W /\ c' = cfg_at tfibsegs A_CDealloc regs' mem' (with_vm_backing (m_vm_lazy md) mat md) /\
cd_pre B ly X1 rcl off W regs' mem' (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 2 = getr regs 2 /\ getr regs' 1 = getr regs 1 /\ (forall r, In r AFgs.SREGS -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly X a -> ~ ascratch B KSTACK regs a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
Proof.
intros W' c' HCD.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
destruct HCD as (-> & regs' & mem' & mat & -> & CSP & CRA & CS & C10 & C11 & C12 & C13 & MEQ' & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & SH).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HSP' : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (split; [exact Hlo | clear - Hcb1 Hcb2; lia]).
pose proof HI as HIx. pose proof DRV as DR. pose proof GE as GEx.
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFf3.D B ly k sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros Hw. exact (ND (WIN_D a Hw)). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (xw := Z_to_bv 64 a) in *.
destruct (w_H W xw) eqn:Hx'; [exact (Hv HN)|].
destruct (seg_rom tfibsegs xw) eqn:ROM; [destruct (mem' xw); discriminate|].
destruct (mem' xw) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem xw) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned xw). assert (Ex : Z_to_bv 64 a' = xw) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hbb]]. rewrite Ex in Hbb. congruence.
- rewrite (MEQ' xw C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb0 Hx'. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb0; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb0.
unfold w64 in *. set (xw := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned xw = a) by (subst xw; apply unsigned_lit_small; exact Ha').
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. fold xw in Hh. rewrite Hx' in Hh. discriminate.
- apply (MEQ' xw). rewrite Ux. exact C. }
assert (NEW_sh : forall a, AFf3.DH B ly k a -> rd a <> None -> rd' a = Some shHeapLeftRz).
{ intros a HD Hv. subst rd rd'. unfold AFf3.DH, shadow_addr in HD.
assert (E8 : SHADOW_OFF + (ck_base B ly k + ck_rz k) / 8 = SPv) by (unfold AFgs.SPv, AFgs.Uv, AFfr.rbase, AFfr.rrz; lia).
rewrite E8 in HD. change (ck_n k) with rnn in HD. unfold AFgs.CNT8v, AFgs.N8v in SH. rewrite Z_div_mult in SH by lia.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - HD DR; numconst; lia).
unfold aview, mbyte, mrestrict in Hv |- *. replace a with (SPv + (a - SPv)) in Hv |- * by lia. unfold w64 in SH.
destruct (w_H W (Z_to_bv 64 (SPv + (a - SPv)))) eqn:Hh.
- exfalso. rewrite seg_rom_none_high in Hv by (clear - HD DR; numconst; lia). exact (Hv eq_refl).
- rewrite (SH (a - SPv)) by lia. reflexivity. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros ce Hce. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') ce Hce)|].
intros i Hi. subst rd rd'. destruct (proj1 (Forall_forall _ _) CONST_OUT ce Hce i Hi) as [Y1 Y2]. apply aview_same.
apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact Y2. exact Y1. }
pose proof (AFf3.rc_fin_ARm B TB ly X rd rd' M' k off Hk Hst Hb Hni Hci sp0 HSP' IMG AG VIS NEW_sh CONST') as MF.
pose proof (AFf3.DEL B ly X rd M' k off Hk Hst Hb Hni) as (W1 & D1 & D2 & D3 & D4 & D5 & D6). cbv zeta in D2, D3, D4, D6.
assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly X a -> ~ ascratch B KSTACK regs a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha NO NS. apply AG; [exact Ha|]. intros HD.
destruct (AFf3.D_owned B ly X rd M' k off Hk Hst Hb sp0 HSP' a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; exact O]. }
assert (PUF : forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha (c' & Hc' & Hr) NK. apply AG; [exact Ha|]. intros HD.
pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _). pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
pose proof (wf_classes _ _ _ _ _ (am_wf B ly X rd M') c' Hc') as CL'. pose proof (wr_alloc _ _ _ _ _ _ CL') as A1.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' (am_wf B ly X rd M') Hc') as MB. unfold kUserMapSize, EV_MAX in MB.
pose proof GEO as (G_PT & _ & _ & G_PS & _).
unfold AFf3.D, AFf3.DS, AFf3.DK, AFf3.DJ, AFf3.DH, AFf3.Mv in HD.
pose proof GEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RZ & _ & RN & RNS & EXT & _). unfold AFfr.rrz, AFfr.rnn in RZ, RN, RNS, EXT.
destruct HD as [Y|[Y|[Y|Y]]].
- clear - Y Hr R1 R2 A1 MB G_PS HSP'. numconst. lia.
- apply NK. clear - Y RZ RN RNS EXT. numconst. lia.
- clear - Y Hr R1 R2 A1 MB G_PT hT1. numconst. lia.
- unfold shadow_addr in Y. pose proof (AFf3.k_prim B ly X rd M' k off Hk Hb) as KP. cbv zeta in KP. destruct KP as (KP1 & KP2 & _).
pose proof (AFf3.ext_rounded B ly X rd M' k off Hk) as (ER & _ & QP & _).
clear - Y Hr R1 R2 A1 MB hP1 hP2 RN RZ KP1 KP2 ER QP. numconst.
assert (Y' : (ck_base B ly k + ck_rz k + (ck_n k + 7) / 8 * 8) / 8 <= 140735332483072 / 8) by (apply Z.div_le_mono; lia).
rewrite Z.div_add in Y' by lia. change (140735332483072 / 8) with 17591916560384 in Y'. lia. }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [|split; [exact CSP | split; [exact CRA | split; [exact CS | split; [exact FR | exact PUF]]]]].
unfold cd_pre. unfold spZ, raZ. rewrite CSP, CRA. fold sp0.
split.
{   split; [exact MF | split; [|split; [|split]]].
- eapply ALedger_same; [exact (AFf3.ALedger_X1 B ly X rd M' k off Hk Hb tfibsegs md LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
- destruct BUD as [BUD PIN]. split; [| exact (AFf3.asecA_S' B ly X rd M' k off Hk Hb _ PIN)].
rewrite (AFf3.abudget' B ly X rd M' k off Hk Hb). exact BUD.
- eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
- eapply (ahs_transfer tfibsegs B ly X _ (w_H W) mem mem' (al_img_env tfibsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
+ eapply (aclient_band_same_frames B ly X); [exact MF | exact (AFf3.frames' X k)].
+ exact (AFf3.sec_extents' B ly X rd M' k off Hk Hb).
+
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. apply AG; [clear - SBg; lia|].
intros HD. pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
pose proof (AFf3.k_prim B ly X rd M' k off Hk Hb) as KP. cbv zeta in KP. destruct KP as (KP1 & KP2 & _).
pose proof (AFf3.ext_rounded B ly X rd M' k off Hk) as (ER & NN1 & QP & _).
unfold AFf3.D, AFf3.DS, AFf3.DK, AFf3.DJ, AFf3.Mv in HD.
destruct HD as [Y|[Y|[Y|Y]]].
* clear - Y SBg hS1 HSP'. numconst. lia.
* pose proof GEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RZ & _). clear - Y SBg KP1 KP2 hP1 RZ. unfold AFfr.rrz in RZ. numconst. lia.
* clear - Y SBg hT1. unfold zone3, zone3cases in hT1. numconst. lia.
* apply (AFf3.DH_iff B ly X rd M' k off Hk Hb g Hg) in Y.
unfold hfree in HF. apply Forall_app in HF as [HF _]. unfold static_extents in HF. apply Forall_cons_iff in HF as [HF _]. cbn [fst snd] in HF.
pose proof GEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RZ & _). unfold AFfr.rrz in RZ. clear - Y HF KP1 KP2 ER QP RZ. nia. }
split; [exact Hci|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D6|].
split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hal|]. split; [exact Hlo|]. split; [clear - Hcb1 Hcb2; lia|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 256)) as [Hlow|Hhigh].
- apply (apresent_same (w_H W) mem); [|apply HPRES; exact Ha]. apply MEQ'. pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha Usp HSP' hS1; numconst; lia). rewrite unsigned_lit_small by exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hlow G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2 hS1. numconst. lia.
- apply PRESW. unfold AFgs.WIN. left. fold sp0. lia. }
split; [rewrite (CS 3%bv ltac:(cbn; tauto)); exact Hgp|]. split; [rewrite (CS 4%bv ltac:(cbn; tauto)); exact Htp|].
split; [exact C10|]. split; [exact C11|]. split; [exact C12|]. rewrite C13. pose proof GEx as (_ & G2 & _). unfold AFfr.rbase in G2 |- *. rewrite G2. reflexivity.
Qed.
Theorem tfib_rchunk_prim_arm : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
rewrite (recycle_chunk_prim k X off (proj2 (mem_chunk_spec _ _) Hk) Hb).
unfold cfg_at, A_RChunk. rewrite <- (wvb_self md) at 1.
eapply (amreal_SRr_pre tfibsegs _ _ _ _ (AFgs.at_CD W ly regs mem md rcl rbase rrz rnn hb1)).
{ exact (AFh7.segRC W ly regs mem md rcl rbase rrz rnn hb1 cbp rmuc j1 j2 (m_vm_materialized md) FH). }
intros W' c' _ HCD. destruct (CDPRE W' c' HCD) as (regs' & mem' & mat & -> & -> & PRE' & R2 & R1 & RS & FR & PUF).
eapply amreal_mono; [| exact (AFg0.tfib_cdealloc_ok B TB ly X1 rcl off W regs' mem' _ PRE' HTSD)].
cbv beta. intros [[] S''] W'' c'' HL. destruct HL as (regs'' & mem'' & md'' & -> & AP & UF & CI). exists regs'', mem'', md''.
split; [unfold cfg_at, raZ; rewrite R1; reflexivity|].
split.
2:{ split; [|exact CI]. intros a Ha PU NK. rewrite (UF a Ha) by exact PU. exact (PUF a Ha PU NK). }
destruct AP as (AR'' & LLE & WLE & RP & IO & FRM & PRS). unfold acall_post. unfold spZ in *. rewrite R2 in PRS.
split; [exact AR''|]. split; [exact LLE|]. split; [exact WLE|]. split.
{ intros r Hr. rewrite (RP r Hr). unfold acallee_saved in Hr.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct R as [->|R]; [exact R2|]. apply RS. clear - R. unfold AFgs.SREGS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
split. { pose proof (same_io_wvb md mat) as IO1. clear - IO IO1. unfold same_io in *. destruct IO as (I1 & I2 & I3 & I4). destruct IO1 as (J1 & J2 & J3 & J4). repeat split; congruence. }
split.
{ pose proof PRE as PRE2. destruct PRE2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in Hlo, Hcb1.
assert (HSP0 : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (unfold sp0; clear - Hlo Hcb1 Hcb2; lia).
intros a Ha NO NO' NS NE. rewrite (FRM a Ha); [apply FR; [exact Ha | exact NO | exact NS] | | exact NO' | unfold ascratch, spZ in *; rewrite R2; exact NS | exact NE].
intros O1. apply NO. exact (proj1 (AFf3.aowned_X1 B ly X _ (AFfr.M B ly X k cbp W regs mem md PRE) k off Hk Hst Hb sp0 HSP0 a) O1). }
exact PRS.
Qed.
End c.
Theorem tfib_rchunk_prim : forall B, TfibSyms B -> forall ly X k cbp W regs mem md off,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PPrim off -> ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof. intros B TB ly X k cbp W regs mem md off PRE Hb HTSD. exact (tfib_rchunk_prim_arm B TB ly X k cbp W regs mem md off PRE Hb HTSD). Qed.
End b.
