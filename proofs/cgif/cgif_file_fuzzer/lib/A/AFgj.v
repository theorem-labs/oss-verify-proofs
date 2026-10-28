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
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition dT : nat := 32.
Definition dSB : nat := 33.
Definition dGSZ : nat := 34.
Definition dGF : nat := 35.
Definition dGL : nat := 36.
Definition dGB : nat := 37.
Definition dTSZ : nat := 38.
Definition dTF : nat := 39.
Definition dTL : nat := 40.
Definition dTB : nat := 41.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (gq tq : qcache).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition GSZv : Z := Z.of_nat (length (qc_list gq)).
Definition GFv : Z := match qc_list gq with [] => 0 | b :: _ => SB + b_self b end.
Definition GLv : Z := match rev (qc_list gq) with [] => 0 | b :: _ => SB + b_self b end.
Definition GBv : Z := qc_bytes gq.
Definition TSZv : Z := Z.of_nat (length (qc_list tq)).
Definition TFv : Z := match qc_list tq with [] => 0 | b :: _ => SB + b_self b end.
Definition TLv : Z := match rev (qc_list tq) with [] => 0 | b :: _ => SB + b_self b end.
Definition TBv : Z := qc_bytes tq.
Definition XW : list word :=
[ w64 T; w64 SB; w64 GSZv; w64 GFv; w64 GLv; w64 GBv; w64 TSZv; w64 TFv; w64 TLv; w64 TBv ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. reflexivity. Qed.
Lemma EqGSZ : ew E0 34 = w64 GSZv. Proof. reflexivity. Qed.
Lemma EqGF : ew E0 35 = w64 GFv. Proof. reflexivity. Qed.
Lemma EqGL : ew E0 36 = w64 GLv. Proof. reflexivity. Qed.
Lemma EqGB : ew E0 37 = w64 GBv. Proof. reflexivity. Qed.
Lemma EqTSZ : ew E0 38 = w64 TSZv. Proof. reflexivity. Qed.
Lemma EqTF : ew E0 39 = w64 TFv. Proof. reflexivity. Qed.
Lemma EqTL : ew E0 40 = w64 TLv. Proof. reflexivity. Qed.
Lemma EqTB : ew E0 41 = w64 TBv. Proof. reflexivity. Qed.
Definition R_QW : YP09.region :=
YP09.mkRegion None (A_QUAR + 152) (A_QUAR + 156) (A_QUAR + 152) (A_QUAR + 156) [YP09.mkChunk (A_QUAR + 152) (CVal 4 (SLit 0))].
Definition R_QG : YP09.region :=
YP09.mkRegion None (A_QUAR + 160) (A_QUAR + 192) (A_QUAR + 160) (A_QUAR + 192)
[YP09.mkChunk (A_QUAR + 160) (CVal 8 (SOff 34%nat 0)); YP09.mkChunk (A_QUAR + 168) (CVal 8 (SOff 35%nat 0));
YP09.mkChunk (A_QUAR + 176) (CVal 8 (SOff 36%nat 0)); YP09.mkChunk (A_QUAR + 184) (CVal 8 (SOff 37%nat 0))].
Definition R_QT : YP09.region :=
YP09.mkRegion (Some 32%nat) t_qc (t_qc + 32) t_qc (t_qc + 32)
[YP09.mkChunk t_qc (CVal 8 (SOff 38%nat 0)); YP09.mkChunk (t_qc + 8) (CVal 8 (SOff 39%nat 0));
YP09.mkChunk (t_qc + 16) (CVal 8 (SOff 40%nat 0)); YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 41%nat 0))].
Definition REG0 : smem :=
[ YP09.mkRegion (Some 2%nat) (- 80) 0 (- 80) 0 []; R_QW; R_QG; R_QT;
flit8 (A_QUAR + 64) kQuarantineMax; flit8 (A_QUAR + 72) kQuarantineMin ].
Definition R_GLN : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition FFD : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + DSTACK) kHighMemEnd 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12);
(33%nat, mkAF kHighMemBeg CEIL_MAX 16);
(34%nat, mkAF 0 (2 ^ 40) 0);
(35%nat, mkAF 0 CEIL_MAX 13);
(36%nat, mkAF 0 CEIL_MAX 13);
(37%nat, mkAF 0 (2 ^ 30) 0);
(38%nat, mkAF 1 (2 ^ 40) 0);
(39%nat, mkAF 0 CEIL_MAX 13);
(40%nat, mkAF 0 CEIL_MAX 13);
(41%nat, mkAF 0 (2 ^ 29) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SLit A_QUAR)) 11%bv (SOff 32%nat t_qc)) 12%bv (SOff 32%nat t_cache).
Definition SS0 : sstate := mkSS 0x32f28 SR0 REG0 None FFD.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x32f28) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hra4096 : 4096 <= bv_unsigned (getr regs0 1);
fh_Hsp : ly_stk_lo ly + DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - DSTACK <= a < sp0 -> apresent (w_H W) mem0 a;
fh_Hg : 0 <= GBv <= 2 ^ 30 /\ GSZv < 2 ^ 40 /\ 0 <= GFv < ASAN_CEIL /\ GFv mod 8192 = 0;
fh_Ht : kQuarantineCacheMax < TBv <= 2 ^ 29 /\ 1 <= TSZv < 2 ^ 40 /\ 0 <= TFv < ASAN_CEIL /\ TFv mod 8192 = 0 /\ 0 <= TLv < ASAN_CEIL /\ TLv mod 8192 = 0;
fh_glast : forall lastb initr, rev (qc_list gq) = lastb :: initr ->
ly_prim ly <= GLv /\ GLv + kBatchBytes <= SB + kSpaceSize /\ GLv mod 8192 = 0 /\
val_mem tfibsegs m0 GLv 8 0 /\ (forall a, GLv <= a < GLv + 8 -> apresent (w_H W) mem0 a);
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x32f28) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hra4096 FH) as Hra4096;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_Hg FH) as Hg;
pose proof (fh_Ht FH) as Ht;
pose proof (fh_glast FH) as Hglast;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly).
Proof.
open_FH.
pose proof (lo_high ly LY) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD0.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD0 eq_refl eq_refl)) as ZT. clear HA IT.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof HD0 as HD. clear HD0. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
unfold zdisjoint in PT, PSTK, TSTK. cbn [fst snd] in *. unfold T, SB in *.
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
clear - IP HSP T1 T2 T3 T4 T5 T6 T7 PT PSTK TSTK. unfold kHighMemBeg, kThreadObjSize, kPrimResvSize in *. repeat split; lia.
Qed.
Lemma derived_ranges :
0 <= GSZv < 2 ^ 40 /\ 0 <= GFv < ASAN_CEIL /\ 0 <= GLv < ASAN_CEIL /\ 0 <= GBv <= 2 ^ 30 /\
1 <= TSZv < 2 ^ 40 /\ 0 <= TFv < ASAN_CEIL /\ 0 <= TLv < ASAN_CEIL /\ kQuarantineCacheMax < TBv <= 2 ^ 29 /\
4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\
kHighMemBeg + DSTACK <= sp0 /\ sp0 <= kHighMemEnd.
Proof.
open_FH. pose proof LYB as (F1 & LB). pose proof F1 as (ZT1 & ZT2 & _). destruct Hg as (G1 & G2 & G3 & G4). destruct Ht as (U1 & U2 & U3 & U4 & U5 & U6). destruct Hsp as [S1 S2].
assert (GL : 0 <= GLv < ASAN_CEIL).
{ destruct (rev (qc_list gq)) as [|lb ini] eqn:R.
- unfold GLv. rewrite R. numconst; lia.
- destruct (Hglast lb ini ltac:(first [exact R | reflexivity])) as (L1 & L2 & _). unfold GLv in *. rewrite ?R in *. clear - L1 L2 LB. numconst. lia. }
unfold GSZv, TSZv in *. numconst. repeat split; lia.
Qed.
Definition WINF (a : Z) : Prop :=
(A_QUAR + 152 <= a < A_QUAR + 156) \/ (A_QUAR + 160 <= a < A_QUAR + 192) \/ (T + t_qc <= a < T + t_qc + 32).
Definition WINA (a : Z) : Prop := qc_list gq <> [] /\ GLv <= a < GLv + 8.
Definition WIN (a : Z) : Prop := (sp0 - 80 <= a < sp0) \/ WINF a \/ WINA a.
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
[(Some 2%nat, -80, 0); (None, A_QUAR + 152, A_QUAR + 156); (None, A_QUAR + 160, A_QUAR + 192); (Some 32%nat, t_qc, t_qc + 32)].
Definition WSKL : list (option nat * Z * Z) := WSK0 ++ [(Some 36%nat, 0, 8)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN, WINF.
ceil; unfold kHighMemBeg, ASAN_CEIL, t_qc, t_cache, kThreadObjSize, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma WSKL_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> qc_list gq <> [] -> sk_ok E WSKL.
Proof.
open_FH. intros E HE Hc t a Hin Hr. unfold WSKL in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (WSK0_ok E HE t a Hin Hr)|].
pose proof derived_ranges as DR. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr.
rewrite HE in Hr by (cbv; lia). rewrite EqGL in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (clear - DR; numconst; lia).
unfold WIN, WINA. do 2 right. split; [exact Hc | lia].
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma WIN_cases : forall a, WIN a -> (A_QUAR + 152 <= a < A_QUAR + 192) \/ (~ (TFIB_IMG_LO <= a < TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg) /\ 0 <= a < 2 ^ 64).
Proof.
open_FH. intros a Hw. pose proof derived_ranges as DR. pose proof LYB as (F1 & _). unfold WIN, WINF, WINA in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hc Hw]]].
- right. clear - Hw DR; numconst; unfold TFIB_IMG_END in *; lia.
- left. clear - Hw; lia.
- left. clear - Hw; lia.
- right. clear - Hw F1; numconst; unfold TFIB_IMG_END in *; lia.
- right. destruct (rev (qc_list gq)) as [|lb ini] eqn:R; [exfalso; apply Hc; rewrite <- (rev_involutive (qc_list gq)), R; reflexivity|].
destruct (Hglast lb ini ltac:(first [exact R | reflexivity])) as (L1 & L2 & _). unfold GLv in *. rewrite ?R in *. pose proof LYB as (_ & LB). clear - Hw L1 L2 LB. numconst. unfold TFIB_IMG_END in *. lia.
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Ltac clear_lets := try clear cfg0; try clear H0.
Definition WIN0 (a : Z) : Prop := (sp0 - 80 <= a < sp0) \/ WINF a.
Lemma WIN0_WIN : forall a, WIN0 a -> WIN a.
Proof. intros a [H|H]; unfold WIN; tauto. Qed.
Definition sk_ok0 (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN0 a.
Lemma WSK0_ok0 : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok0 E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN0, WINF.
ceil; unfold kHighMemBeg, ASAN_CEIL, t_qc, t_cache, kThreadObjSize, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Definition MEQ0 (m : word -> option byte) : Prop := forall x : word, ~ WIN0 (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ0_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok0 E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ0 m -> MEQ0 m'.
Proof.
clear_lets.
intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx.
destruct (in_wrange_windows E rs _ Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t _ Hint (win_sub_sound E _ _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma MEQ0_0 : MEQ0 mem0. Proof. intros x _. reflexivity. Qed.
Lemma MEQ0_MEQ : forall m, MEQ0 m -> MEQ m.
Proof. intros m M x Hx. apply M. intros H. apply Hx. apply WIN0_WIN. exact H. Qed.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. intros E r rs H. induction rs as [|r' rs IH]; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx]. Qed.
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> ~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
Lemma aview_eq_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview tfibsegs H' m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Definition R_QW1 : YP09.region :=
YP09.mkRegion None (A_QUAR + 152) (A_QUAR + 156) (A_QUAR + 152) (A_QUAR + 156)
[YP09.mkChunk (A_QUAR + 152) (CVal 1 (SLit 1)); YP09.mkChunk (A_QUAR + 153) (CZero 3)].
Definition R_QW0 : YP09.region :=
YP09.mkRegion None (A_QUAR + 152) (A_QUAR + 156) (A_QUAR + 152) (A_QUAR + 156) [YP09.mkChunk (A_QUAR + 152) (CZero 4)].
Definition LSZv : Z := GSZv + TSZv.
Definition LBv : Z := GBv + TBv.
Definition LFv : Z := match qc_list gq with [] => TFv | _ :: _ => GFv end.
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_RETD (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
(forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) /\
val_mem tfibsegs m (A_QUAR + 160) 8 LSZv /\ val_mem tfibsegs m (A_QUAR + 168) 8 LFv /\
val_mem tfibsegs m (A_QUAR + 176) 8 TLv /\ val_mem tfibsegs m (A_QUAR + 184) 8 LBv /\
val_mem tfibsegs m (T + t_qc) 8 0 /\ val_mem tfibsegs m (T + t_qc + 8) 8 0 /\ val_mem tfibsegs m (T + t_qc + 16) 8 0 /\ val_mem tfibsegs m (T + t_qc + 24) 8 0 /\
(forall lastb initr, rev (qc_list gq) = lastb :: initr -> val_mem tfibsegs m GLv 8 TFv).
Definition at_L0 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x331c8) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 (sp0 - 80) /\ getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = w64 kQuarantineMin /\
getr regs' 12 = w64 (T + t_cache) /\ getr regs' 13 = getr regs0 13 /\ getr regs' 14 = w64 0 /\ getr regs' 15 = w64 0 /\
getr regs' 16 = w64 LSZv /\ getr regs' 5 = w64 LFv /\ getr regs' 1 = getr regs0 1 /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (A_QUAR + 152) 4 257 /\
val_mem tfibsegs m (A_QUAR + 160) 8 LSZv /\ val_mem tfibsegs m (A_QUAR + 168) 8 LFv /\
val_mem tfibsegs m (A_QUAR + 176) 8 TLv /\ val_mem tfibsegs m (A_QUAR + 184) 8 LBv /\
val_mem tfibsegs m (T + t_qc) 8 0 /\ val_mem tfibsegs m (T + t_qc + 8) 8 0 /\ val_mem tfibsegs m (T + t_qc + 16) 8 0 /\ val_mem tfibsegs m (T + t_qc + 24) 8 0 /\
(forall lastb initr, rev (qc_list gq) = lastb :: initr -> val_mem tfibsegs m GLv 8 TFv) /\
val_mem tfibsegs m (sp0 - 80) 8 0 /\ val_mem tfibsegs m (sp0 - 72) 8 0 /\ val_mem tfibsegs m (sp0 - 64) 8 0 /\ val_mem tfibsegs m (sp0 - 56) 8 0 /\
val_mem tfibsegs m (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\ val_mem tfibsegs m (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem tfibsegs m (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\ val_mem tfibsegs m (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem tfibsegs m (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\ val_mem tfibsegs m (sp0 - 8) 8 (bv_unsigned (getr regs0 1)).
Definition postD : world tfibsegs -> config -> Prop := if LBv <=? kQuarantineMax then at_RETD else at_L0.
Definition SKEL_TAIL : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0).
End d.
End c.
