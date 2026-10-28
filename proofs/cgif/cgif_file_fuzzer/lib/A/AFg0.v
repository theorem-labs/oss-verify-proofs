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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFeu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfh.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFep AFeo AFgk AFgy AFgo AFh2 AFfo AFgz AFfi AFez AB13.
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
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_QUAR, A_ALLOCATOR, o_quar, o_space, o_rinfo, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize, kLowMemEnd, EV_MAX in *.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_io. destruct md as [fd [maps lazy mat0] io fs proc lim tm]. cbn. repeat split; reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (c off : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : cd_pre B ly X c off W regs mem md.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation kcnt := (AFfi.kcnt X c).
Local Notation kold := (AFfi.kold X c).
Local Notation kmf := (AFfi.kmf X c).
Local Notation M := (AFfi.M B ly X c off W regs mem md PRE).
Local Notation LO := (am_layout B ly X rd0 M).
Local Notation HI := (AFfi.HI B ly X c off W regs mem md PRE).
Local Notation IMG := (AFfi.IMG B ly X c off W regs mem md PRE).
Local Notation DRV := (AFfi.derived B ly X c off W regs mem md PRE).
Local Notation HSP := (AFfi.HSP B ly X c off W regs mem md PRE).
Local Notation Hc := (AFfi.Hc B ly X c off W regs mem md PRE).
Local Notation KF := (AFfi.class_facts B ly X c off W regs mem md PRE).
Local Notation RF := (AFfi.reg_facts B ly X c off W regs mem md PRE).
Local Notation PCv := (AFgk.PCv ly c).
Local Notation MAXv := (AFgk.MAXv c).
Local Notation Nv := (AFgk.Nv c).
Local Notation RGv := (AFgk.RGv ly c).
Local Notation DSTv := (AFgk.DSTv ly c kold).
Local Notation SRCv := (AFgk.SRCv ly c kcnt).
Local Notation SLOTv := (AFgk.SLOTv ly c kcnt).
Local Notation WINk := (AFgk.WIN ly regs c kcnt kold).
Local Notation S' := (AFez.S' X c off).
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
assert (C12 : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by (clear - IC; ceil; unfold zone3, TFIB_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia).
assert (D12 : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by (clear - ID; ceil; unfold zone3, TFIB_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia). clear IC ID.
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
assert (CNTP : 0 <= AFgk.CNTPv c kcnt < MAXv) by (unfold AFgk.CNTPv; destruct (Z.eqb_spec kcnt MAXv); clear - RFx KFx e || clear - RFx KFx n; lia).
unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[Hf Hw]]].
- left. exact Hw.
- right; left. unfold AFgk.SLOTv in Hw. clear - Hw DR CNTP KFx. numconst. lia.
- right; right. unfold AFgk.DSTv, AFfi.kold, AFfi.kmf, AFgk.Nv, AFgk.MAXv in *. clear - Hw HIx DR RFx KFx Hf. numconst. lia.
Qed.
Lemma WIN_dec : forall a, WINk a \/ ~ WINk a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
assert (EF : kcnt = MAXv \/ kcnt <> MAXv) by lia.
unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG. fold sp0.
destruct (EM (sp0 - 320) sp0) as [C|C0]; [left; left; exact C|].
destruct (EM PCv (PCv + 4)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM SLOTv (SLOTv + 4)) as [C|C2]; [left; right; left; right; left; exact C|].
destruct (EM (T + t_cache + 2576) (T + t_cache + 2584)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct EF as [EF|EF].
- destruct (EM RGv (RGv + 8)) as [C|C4]; [left; do 2 right; split; [exact EF | left; left; exact C]|].
destruct (EM (RGv + 16) (RGv + 24)) as [C|C5]; [left; do 2 right; split; [exact EF | left; right; left; exact C]|].
destruct (EM (RGv + 80) (RGv + 88)) as [C|C6]; [left; do 2 right; split; [exact EF | left; right; right; exact C]|].
destruct (EM DSTv (DSTv + 4 * Nv)) as [C|C7]; [left; do 2 right; split; [exact EF | right; exact C]|].
right. intros [X0|[[X1|[X2|X3]]|[_ [[X4|[X5|X6]]|X7]]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C4 X4) | exact (C5 X5) | exact (C6 X6) | exact (C7 X7)].
- right. intros [X0|[[X1|[X2|X3]]|[X4 _]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (EF X4)].
Qed.
Definition low_okq (a w : Z) : bool :=
((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) || ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_okq (ce : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w ce)) in
match c_at ce with
| ANum a => low_okq a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okq (TFIB_TSD + o) w
| ATp o => low_okq (TFIB_TP + o) w
| AInst o => low_okq (TFIB_INST + o) w
| _ => false
end.
Lemma Tfib_const_locq : forallb const_loc_okq (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Lemma CONST_OUT : Forall (fun ce => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w ce)) -> ~ WINk (aeval B ly (c_at ce) + i) /\ 0 <= aeval B ly (c_at ce) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros ce Hce i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locq ce Hce) as K. unfold const_loc_okq in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 320 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINk a).
{ intros a Hn Hw. exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okq a (Z.max 1 (Z.of_nat (c_w ce))) = true -> ~ WINk (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L'. unfold low_okq in L'.
split; [apply ZN|]; clear - L' Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, KSTACK, kThreadObjSize in *;
change (65536 / 8) with 8192 in *; change (6270976 / 8) with 783872 in *; lia. }
destruct (c_at ce); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- split; [apply ZN|]; clear - K Hi C1 C2 S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi D1 D2 S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma WIN_D : forall a, WINk a -> AFez.D ly X c sp0 a.
Proof.
intros a Hw. unfold AFez.D, AFez.DT, AFez.DR, AFez.DF, AFez.DS.
unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG in Hw. fold sp0 in Hw.
assert (EFULL : kcnt = MAXv -> AFez.full X c = true) by (intros E; unfold AFez.full; apply Z.eqb_eq; exact E).
assert (ESLOT : AFez.SLOTv ly X c = SLOTv).
{ unfold AFez.SLOTv, AFez.CNTP, AFez.PCv, AFez.full, AFgk.SLOTv, AFgk.CNTPv, AFgk.PCv, AFgk.Nv, AFgk.MAXv, AFfi.kcnt.
destruct (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c); reflexivity. }
assert (EPC : AFez.PCv ly c = PCv) by reflexivity.
assert (ERG : AFez.RGv ly c = RGv) by (unfold AFez.RGv, AFgk.RGv, AFgk.RIv; lia).
assert (EDST : AFez.DSTv ly X c = DSTv) by (unfold AFez.DSTv, AFez.FAv, AFgk.DSTv, AFgk.FAv, AFgk.RBv, AFfi.kold, fa_base; lia).
rewrite ESLOT, EPC, ERG, EDST. change (max_cached c / 2) with Nv.
destruct Hw as [Hw|[Hw|[Hf Hw]]].
- do 3 right. clear - Hw. unfold KSTACK. lia.
- left. exact Hw.
- destruct Hw as [Hw|Hw]; [right; left | right; right; left]; (split; [exact (EFULL Hf) | exact Hw]).
Qed.
Lemma PREF : st_cache_inited X = true /\ 1 <= c <= 30 /\ 0 <= off - region_off c < rg_alloc_user (reg X c) /\ (off - region_off c) mod class_size c = 0 /\
~ In (off - region_off c) (class_elems X c) /\
4 * (Z.of_nat (length (class_elems X c)) + 1 + (0 + bslack c 0 + 2 * (EV_MAX - st_nev X))) <= rg_mapped_fa (reg X c).
Proof. destruct PRE as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _). repeat split; assumption || tauto. Qed.
Lemma FINKH : forall W' c', AFgk.at_RETK W ly regs mem md c off kcnt kold kmf W' c' -> cd_leaf B ly X W regs mem md (tt, S') W' c'.
Proof.
intros W' c' HR.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hci & Hcc & Hx & Hxm & Hxni & HROOM & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & CSP & CS & MEQ' & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & VF).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof HI as HIx. pose proof RF as RFx. pose proof KF as KFx. pose proof DRV as DR.
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFez.D ly X c sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros X'. exact (ND (WIN_D a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx'; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
- rewrite (MEQ' x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx'. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. fold x in Hh. rewrite Hx' in Hh. discriminate.
- apply (MEQ' x). rewrite Ux. exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0f.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (EFULL : AFez.full X c = (kcnt =? MAXv)) by reflexivity.
assert (ECNTP : AFez.CNTP X c = AFgk.CNTPv c kcnt).
{ unfold AFez.CNTP, AFgk.CNTPv. rewrite EFULL. unfold AFfi.kcnt, AFgk.Nv, AFgk.MAXv. destruct (_ =? _); reflexivity. }
assert (NEW_cnt : forall i, (i < 4)%nat -> rd' (AFez.PCv ly c + Z.of_nat i) = Some (YG0f.le_byte (AFez.CNTP X c + 1) 4 i)).
{ apply (VM _ _ 4%nat _ _ V1); [reflexivity | rewrite ECNTP; reflexivity]. }
assert (NEW_slot : forall i, (i < 4)%nat -> rd' (AFez.SLOTv ly X c + Z.of_nat i) = Some (YG0f.le_byte ((off - region_off c) / 16) 4 i)).
{ apply (VM _ _ 4%nat _ _ V2); [| reflexivity]. unfold AFez.SLOTv, AFgk.SLOTv. rewrite ECNTP. reflexivity. }
assert (ERG : AFez.RGv ly c = RGv) by (unfold AFez.RGv, AFgk.RGv, AFgk.RIv; lia).
assert (EDST : AFez.DSTv ly X c = DSTv) by (unfold AFez.DSTv, AFez.FAv, AFgk.DSTv, AFgk.FAv, AFgk.RBv, AFfi.kold, fa_base; lia).
assert (NEW_rg0 : AFez.full X c = true -> forall i, (i < 8)%nat -> rd' (AFez.RGv ly c + Z.of_nat i) = Some (YG0f.le_byte 0 8 i)).
{ intros Hf. rewrite EFULL in Hf. apply Z.eqb_eq in Hf. destruct (VF Hf) as (R0 & _). apply (VM _ _ 8%nat _ _ R0); [exact (eq_sym ERG) | reflexivity]. }
assert (NEW_rg16 : AFez.full X c = true -> forall i, (i < 8)%nat ->
rd' (AFez.RGv ly c + 16 + Z.of_nat i) = Some (YG0f.le_byte (fa_len (rg_free (reg X c)) + max_cached c / 2) 8 i)).
{ intros Hf. rewrite EFULL in Hf. apply Z.eqb_eq in Hf. destruct (VF Hf) as (_ & R16 & _). apply (VM _ _ 8%nat _ _ R16); [rewrite ERG; reflexivity | reflexivity]. }
assert (NEW_fa : AFez.full X c = true -> forall (j : nat) v, Z.of_nat j < max_cached c / 2 ->
nth_error (pc_chunks (cache X c)) (Z.to_nat (Z.of_nat (length (pc_chunks (cache X c))) - max_cached c / 2) + j) = Some v ->
forall i, (i < 4)%nat -> rd' (AFez.DSTv ly X c + 4 * Z.of_nat j + Z.of_nat i) = Some (YG0f.le_byte (v / 16) 4 i)).
{ intros Hf j v Hj Hv. rewrite EFULL in Hf. apply Z.eqb_eq in Hf. destruct (VF Hf) as (_ & _ & _ & CPY).
pose proof (AFfi.slot_vals B ly X c off W regs mem md PRE _ v Hv) as SV.
assert (ESRC : PCv + 16 + 4 * Z.of_nat (Z.to_nat (Z.of_nat (length (pc_chunks (cache X c))) - max_cached c / 2) + j) = SRCv + 4 * Z.of_nat j).
{ unfold AFgk.SRCv, AFfi.kcnt, AFgk.Nv, AFgk.MAXv. unfold AFfi.kcnt, AFgk.MAXv, AFgk.Nv in Hf, KFx. clear - Hj Hf KFx. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
rewrite ESRC in SV. apply (VM _ _ 4%nat _ _ (CPY (Z.of_nat j) (v / 16) ltac:(unfold AFgk.Nv, AFgk.MAXv; lia) SV)); [rewrite EDST; reflexivity | reflexivity]. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros ce Hce. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') ce Hce)|].
intros i Hi. subst rd rd'. destruct (proj1 (Forall_forall _ _) CONST_OUT ce Hce i Hi) as [X1 X2]. apply aview_same.
apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact X2. exact X1. }
pose proof (AFez.cd_fin_ARm B TB ly X rd rd' M' c off Hci Hcc Hx Hxm Hxni HROOM sp0 HSP' IMG AG VIS NEW_cnt NEW_slot NEW_rg0 NEW_rg16 NEW_fa CONST') as MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
2:{ split; [|exact (AFez.S'_cinit X c off Hci)].
intros a Ha (c' & Hc' & Hr). apply AG; [exact Ha|]. intros HD.
pose proof (wf_classes _ _ _ _ _ (am_wf B ly X rd M') c' Hc') as CL'. pose proof (wr_alloc _ _ _ _ _ _ CL') as A1.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' (am_wf B ly X rd M') Hc') as MB. unfold kUserMapSize, EV_MAX in MB.
pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _).
destruct (AFez.user_vs_D B ly X rd M' c off Hci Hcc Hx Hxm HROOM IMG c' a Hc' ltac:(clear - Hr A1 MB; lia)) as [N1 N2].
destruct (AFez.ok_prim B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG a ltac:(clear - Hr A1 MB R1 R2; lia) N1 N2) as [_ ND]. exact (ND HD). }
split; [|split; [apply layout_le_refl | split; [apply wle_refl | split; [|split; [|split]]]]].
- split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same; [exact (AFez.ALedger_S' B ly X rd M' c off Hcc Hx Hxm sp0 HSP' tfibsegs md LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD as [BUD PIN]. split; [| exact (AFez.asecA_S' ly X c off _ PIN)].
eapply Z.le_trans; [exact BUD|]. rewrite <- (AFez.abudget_S' X c off). apply Z.le_refl.
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly X _ (w_H W) mem mem' (al_img_env tfibsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [exact MF | exact (AFez.frames' X c off)].
* exact (AFez.sec_extents' ly X c off).
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
intros HD. pose proof HIx as (hP1 & _ & hT1 & _ & hS1 & _).
destruct (AFez.D_owned B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG (shadow_addr g) ltac:(clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia) HD) as [O|O].
-- pose proof (AFez.D_cases B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG _ HD) as DC.
clear - DC SBg hP1 hT1 hS1. unfold in_band_rw, zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kThreadObjSize in *. lia.
-- unfold AFez.DS in O. clear - O SBg hS1 HSP'. unfold in_band_rw, zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, KSTACK in *. lia.
- intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct R as [->|R]; [exact CSP|]. apply CS. clear - R. unfold AFgk.SREGS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
- apply same_io_wvb.
- intros a Ha NO NO' NS NE. apply AG; [exact Ha|]. intros HD.
destruct (AFez.D_owned B ly X rd M' c off Hci Hcc Hx Hxm HROOM sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; exact O].
- intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 320)) as [Hb|Hb].
+ apply (apresent_same (w_H W) mem); [|apply HPRES; exact Ha]. apply MEQ'. pose proof HIx as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha Usp HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, KSTACK, kHighMemBeg in *; lia). rewrite unsigned_lit_small by exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *. lia.
+ apply PRESW. unfold AFgk.WIN. left. fold sp0. lia.
Qed.
Theorem tfib_cdealloc_arm : amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (cd_leaf B ly X W regs mem md).
Proof.
pose proof PREF as (Hci & Hcc & Hx & Hxm & Hxni & HROOM).
rewrite (AFez.cache_dealloc_S' B ly X rd0 M c off Hci Hcc Hx Hxm HROOM). cbn [amreal].
destruct (AFfi.junk_vals B ly X c off W regs mem md PRE) as (j80 & j88 & jst & HJ80 & HJ88 & HJST).
pose proof (AFfi.FH_ok B TB ly X c off W regs mem md PRE j80 j88 jst HJ80 HJ88 HJST) as FH.
pose proof RF as RFx.
unfold cfg_at, A_CDealloc. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [| intros W' c' _ HR; exact (FINKH W' c' HR)].
destruct (Z_lt_le_dec kcnt MAXv) as [LT|GE].
- exact (AFgy.segK1 W ly regs mem md c off kcnt kold kmf j80 j88 jst (m_vm_materialized md) FH LT).
- apply (AFgz.segK2 W ly regs mem md c off kcnt kold kmf j80 j88 jst (m_vm_materialized md) FH). clear - RFx GE. unfold AFgk.MAXv in *. lia.
Qed.
End d.
Theorem tfib_cdealloc_ok : forall B, TfibSyms B -> forall ly X c off W regs mem md,
cd_pre B ly X c off W regs mem md -> ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (cd_leaf B ly X W regs mem md).
Proof. intros B TB ly X c off W regs mem md PRE HTSD. exact (tfib_cdealloc_arm B TB ly X c off W regs mem md PRE HTSD). Qed.
End b.
