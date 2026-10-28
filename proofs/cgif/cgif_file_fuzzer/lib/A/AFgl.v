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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition lB : nat := 32.
Definition lNX : nat := 33.
Definition lBS : nat := 34.
Definition lQB : nat := 35.
Definition lNR : nat := 36.
Definition lNP : nat := 37.
Definition lLP : nat := 38.
Definition lTBY : nat := 39.
Definition lTFI : nat := 40.
Definition lGL : nat := 41.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bs qb nr np lp tby tfi gl : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word :=
[ w64 b; w64 nx; w64 bs; w64 qb; w64 nr; w64 np; w64 lp; w64 tby; w64 tfi; w64 gl ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqB : ew E0 32 = w64 b. Proof. reflexivity. Qed.
Lemma EqNX : ew E0 33 = w64 nx. Proof. reflexivity. Qed.
Lemma EqBS : ew E0 34 = w64 bs. Proof. reflexivity. Qed.
Lemma EqQB : ew E0 35 = w64 qb. Proof. reflexivity. Qed.
Lemma EqNR : ew E0 36 = w64 nr. Proof. reflexivity. Qed.
Lemma EqNP : ew E0 37 = w64 np. Proof. reflexivity. Qed.
Lemma EqLP : ew E0 38 = w64 lp. Proof. reflexivity. Qed.
Lemma EqTBY : ew E0 39 = w64 tby. Proof. reflexivity. Qed.
Lemma EqTFI : ew E0 40 = w64 tfi. Proof. reflexivity. Qed.
Lemma EqGL : ew E0 41 = w64 gl. Proof. reflexivity. Qed.
Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 LFRAME 0 32
[YP09.mkChunk 8 (CVal 8 (SOff 40%nat 0)); YP09.mkChunk 24 (CVal 8 (SOff 39%nat 0))].
Definition R_QW : YP09.region :=
YP09.mkRegion None (A_QUAR + 152) (A_QUAR + 156) (A_QUAR + 152) (A_QUAR + 156)
[YP09.mkChunk (A_QUAR + 152) (CVal 1 (SLit 1)); YP09.mkChunk (A_QUAR + 153) (CVal 1 (SLit 1)); YP09.mkChunk (A_QUAR + 154) (CZero 2)].
Definition R_QG : YP09.region :=
YP09.mkRegion None (A_QUAR + 160) (A_QUAR + 192) (A_QUAR + 160) (A_QUAR + 192)
[YP09.mkChunk (A_QUAR + 160) (CVal 8 (SOff 36%nat 0)); YP09.mkChunk (A_QUAR + 168) (CVal 8 (SOff 32%nat 0));
YP09.mkChunk (A_QUAR + 176) (CVal 8 (SOff 41%nat 0)); YP09.mkChunk (A_QUAR + 184) (CVal 8 (SOff 35%nat 0))].
Definition R_B : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 34%nat 0))].
Definition REG0 : smem := [ R_STK; R_QW; R_QG; R_B ].
Definition R_LPN : YP09.region := YP09.mkRegion (Some 38%nat) 0 8 0 8 [].
Definition FFL : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + DRSTACK) (kHighMemEnd - LFRAME) 4);
(32%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(33%nat, mkAF 0 CEIL_MAX 13);
(34%nat, mkAF 0 (2 ^ 31) 0);
(35%nat, mkAF 0 (2 ^ 31) 0);
(36%nat, mkAF 1 (2 ^ 40) 0);
(37%nat, mkAF 0 (2 ^ 40) 0);
(38%nat, mkAF 0 CEIL_MAX 13);
(39%nat, mkAF 0 (2 ^ 31) 0);
(40%nat, mkAF 0 CEIL_MAX 0);
(41%nat, mkAF 0 CEIL_MAX 13) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SLit A_QUAR)) 11%bv (SLit kQuarantineMin))
5%bv (SOff 32%nat 0)) 14%bv (SOff 37%nat 0)) 15%bv (SOff 38%nat 0)) 16%bv (SOff 36%nat 0).
Definition SS0 : sstate := mkSS 0x331c8 SR0 REG0 None FFL.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x331c8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hsp : ly_stk_lo ly + DRSTACK <= sp0 /\ sp0 + LFRAME <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - DRSTACK <= a < sp0 + LFRAME -> apresent (w_H W) mem0 a;
fh_Hb : ly_prim ly <= b /\ b + kBatchBytes <= SB + kSpaceSize /\ b mod 8192 = 0;
fh_Hnx : 0 <= nx < ASAN_CEIL /\ nx mod 8192 = 0;
fh_Hcnt : 1 <= nr < 2 ^ 40 /\ 0 <= np < 2 ^ 40;
fh_Hby : 0 <= bs /\ bs <= qb /\ qb <= 2 ^ 31 /\ 0 <= tby /\ tby + bs <= 2 ^ 31;
fh_Hgl : 0 <= gl < ASAN_CEIL /\ gl mod 8192 = 0;
fh_Htfi : 0 <= tfi < ASAN_CEIL;
fh_Hlp : 0 <= lp < ASAN_CEIL /\ lp mod 8192 = 0 /\
(np <> 0 -> ly_prim ly <= lp /\ lp + kBatchBytes <= SB + kSpaceSize /\ (lp + kBatchBytes <= b \/ b + kBatchBytes <= lp) /\
(forall a, lp <= a < lp + 8 -> apresent (w_H W) mem0 a));
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x331c8) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_Hb FH) as Hb;
pose proof (fh_Hnx FH) as Hnx;
pose proof (fh_Hcnt FH) as Hcnt;
pose proof (fh_Hby FH) as Hby;
pose proof (fh_Hgl FH) as Hgl;
pose proof (fh_Htfi FH) as Htfi;
pose proof (fh_Hlp FH) as Hlp;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly).
Proof.
open_FH.
pose proof (lo_high ly LY) as HI. unfold owned_extents in HI.
repeat match type of HI with Forall _ (_ :: _) => apply Forall_cons_iff in HI as [? HI] end.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PT, PSTK. unfold in_high in *. cbn [fst snd] in *. unfold SB.
repeat split; try lia.
Qed.
Lemma derived_ranges :
kHighMemBeg <= b /\ b + kBatchBytes <= ASAN_CEIL /\ b mod 8192 = 0 /\ 0 <= nx < ASAN_CEIL /\ 1 <= nr < 2 ^ 40 /\ 0 <= np < 2 ^ 40 /\
0 <= bs <= 2 ^ 31 /\ 0 <= qb <= 2 ^ 31 /\ 0 <= tby <= 2 ^ 31 /\ 0 <= gl < ASAN_CEIL /\ 0 <= tfi < ASAN_CEIL /\ 0 <= lp < ASAN_CEIL /\
kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\ kHighMemBeg + DRSTACK <= sp0 /\ sp0 + LFRAME <= kHighMemEnd.
Proof.
open_FH. pose proof LYB as LB. destruct Hb as (B1 & B2 & B3). destruct Hsp as [S1 S2]. destruct Hlp as (P1 & P2 & _).
clear - LB B1 B2 B3 S1 S2 P1 P2 Hnx Hcnt Hby Hgl Htfi. numconst. repeat split; lia.
Qed.
Definition WINF (a : Z) : Prop :=
(A_QUAR + 152 <= a < A_QUAR + 156) \/ (A_QUAR + 160 <= a < A_QUAR + 192) \/ (b <= a < b + 8).
Definition WINA (a : Z) : Prop := np <> 0 /\ lp <= a < lp + 8.
Definition WIN (a : Z) : Prop := (sp0 <= a < sp0 + 32) \/ WINF a \/ WINA a.
Definition win_sub (t w : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst w)) && (snd (fst w) <=? snd (fst t)) && (snd t <=? snd w).
Lemma win_sub_sound : forall E a t w, win_sub t w = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst w)) + snd (fst w) <= a < base_val E (fst (fst w)) + snd w.
Proof.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Definition WSK0 : list (option nat * Z * Z) :=
[(Some 2%nat, 0, 32); (None, A_QUAR + 152, A_QUAR + 156); (None, A_QUAR + 160, A_QUAR + 192); (Some 32%nat, 0, 8)].
Definition WSKL : list (option nat * Z * Z) := WSK0 ++ [(Some 38%nat, 0, 8)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN, WINF.
ceil; unfold kHighMemBeg, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqB in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma WSKL_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> np <> 0 -> sk_ok E WSKL.
Proof.
open_FH. intros E HE Hc t a Hin Hr. unfold WSKL in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (WSK0_ok E HE t a Hin Hr)|].
pose proof derived_ranges as DR. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr.
rewrite HE in Hr by (cbv; lia). rewrite EqLP in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (clear - DR; numconst; lia).
unfold WIN, WINA. do 2 right. split; [exact Hc | lia].
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma WIN_cases : forall a, WIN a -> (A_QUAR + 152 <= a < A_QUAR + 192) \/ kHighMemBeg <= a.
Proof.
open_FH. intros a Hw. pose proof derived_ranges as DR. unfold WIN, WINF, WINA in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hc Hw]]].
- right. clear - Hw DR; numconst; lia.
- left. clear - Hw; lia.
- left. clear - Hw; lia.
- right. clear - Hw DR; numconst; lia.
- right. destruct Hlp as (_ & _ & HL). destruct (HL Hc) as (L1 & _). pose proof LYB as LB. clear - Hw L1 LB. numconst. lia.
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Ltac clear_lets := try clear cfg0; try clear H0.
Definition WIN0 (a : Z) : Prop := (sp0 <= a < sp0 + 32) \/ WINF a.
Lemma WIN0_WIN : forall a, WIN0 a -> WIN a.
Proof. intros a [H|H]; unfold WIN; tauto. Qed.
Definition sk_ok0 (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN0 a.
Lemma WSK0_ok0 : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok0 E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN0, WINF.
ceil; unfold kHighMemBeg, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqB in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Definition MEQ0 (m : word -> option byte) : Prop := forall x : word, ~ WIN0 (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ0_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok0 E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ0 m -> MEQ0 m'.
Proof.
clear_lets.
intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx.
destruct (in_wrange_windows E rs _ Hw) as (b0 & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t _ Hint (win_sub_sound E _ _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma MEQ0_0 : MEQ0 mem0. Proof. intros x _. reflexivity. Qed.
Lemma MEQ0_MEQ : forall m, MEQ0 m -> MEQ m.
Proof. intros m M x Hx. apply M. intros H. apply Hx. apply WIN0_WIN. exact H. Qed.
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition GLn : Z := if nx =? 0 then 0 else gl.
Definition TFIn : Z := if np =? 0 then b else tfi.
Definition at_CONT (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ kQuarantineMin < qb - bs /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x331c8) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = w64 kQuarantineMin /\
getr regs' 12 = getr regs0 12 /\ getr regs' 13 = getr regs0 13 /\ getr regs' 14 = w64 (np + 1) /\ getr regs' 15 = w64 b /\
getr regs' 16 = w64 (nr - 1) /\ getr regs' 5 = w64 nx /\ getr regs' 1 = getr regs0 1 /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (A_QUAR + 152) 1 1 /\ val_mem tfibsegs m (A_QUAR + 153) 1 1 /\
(forall a, A_QUAR + 154 <= a < A_QUAR + 156 -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) /\
val_mem tfibsegs m (A_QUAR + 160) 8 (nr - 1) /\ val_mem tfibsegs m (A_QUAR + 168) 8 nx /\
val_mem tfibsegs m (A_QUAR + 176) 8 GLn /\ val_mem tfibsegs m (A_QUAR + 184) 8 (qb - bs) /\
val_mem tfibsegs m b 8 0 /\ (np <> 0 -> val_mem tfibsegs m lp 8 b) /\
val_mem tfibsegs m (sp0 + 8) 8 TFIn /\ val_mem tfibsegs m (sp0 + 24) 8 (tby + bs).
Definition at_EXIT (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ qb - bs <= kQuarantineMin /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_DoRecycle) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = getr regs0 2 /\
getr regs' 12 = getr regs0 12 /\ getr regs' 13 = getr regs0 13 /\ getr regs' 1 = w64 0x3323c /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
(forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) /\
val_mem tfibsegs m (A_QUAR + 160) 8 (nr - 1) /\ val_mem tfibsegs m (A_QUAR + 168) 8 nx /\
val_mem tfibsegs m (A_QUAR + 176) 8 GLn /\ val_mem tfibsegs m (A_QUAR + 184) 8 (qb - bs) /\
val_mem tfibsegs m b 8 0 /\ (np <> 0 -> val_mem tfibsegs m lp 8 b) /\
val_mem tfibsegs m sp0 8 (np + 1) /\ val_mem tfibsegs m (sp0 + 8) 8 TFIn /\
val_mem tfibsegs m (sp0 + 16) 8 b /\ val_mem tfibsegs m (sp0 + 24) 8 (tby + bs).
Definition postL : world tfibsegs -> config -> Prop := if kQuarantineMin <? qb - bs then at_CONT else at_EXIT.
End d.
End c.
