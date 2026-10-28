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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD in *.
Definition pT : nat := 32.
Definition pU : nat := 34.
Definition pN : nat := 35.
Definition pQSZ : nat := 36.
Definition pQL : nat := 38.
Definition pQB : nat := 39.
Definition pCNT : nat := 45.
Definition pBSZ : nat := 46.
Definition pSL : nat := 47.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (u nn qsz ql qb cnt bsz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let m0 := mrestrict (w_H W) mem0.
Definition SLv : Z := ql + 8 * cnt.
Definition XW : list word :=
[ w64 T; w64 0; w64 u; w64 nn; w64 qsz; w64 0; w64 ql; w64 qb; w64 0; w64 0; w64 0; w64 0; w64 0; w64 cnt; w64 bsz; w64 SLv ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqU : ew E0 34 = w64 u. Proof. reflexivity. Qed.
Lemma EqN : ew E0 35 = w64 nn. Proof. reflexivity. Qed.
Lemma EqQSZ : ew E0 36 = w64 qsz. Proof. reflexivity. Qed.
Lemma EqQL : ew E0 38 = w64 ql. Proof. reflexivity. Qed.
Lemma EqQB : ew E0 39 = w64 qb. Proof. reflexivity. Qed.
Lemma EqCNT : ew E0 45 = w64 cnt. Proof. reflexivity. Qed.
Lemma EqBSZ : ew E0 46 = w64 bsz. Proof. reflexivity. Qed.
Lemma EqSL : ew E0 47 = w64 SLv. Proof. reflexivity. Qed.
Definition R_ROOT : YP09.region :=
YP09.mkRegion (Some 32%nat) t_qc (t_qc + 32) (t_qc + 24) (t_qc + 32)
[YP09.mkChunk t_qc (CVal 8 (SOff 36%nat 0)); YP09.mkChunk (t_qc + 16) (CVal 8 (SOff 38%nat 0)); YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 39%nat 0))].
Definition R_LAST : YP09.region :=
YP09.mkRegion (Some 38%nat) 0 24 8 24 [YP09.mkChunk 8 (CVal 8 (SOff 46%nat 0)); YP09.mkChunk 16 (CVal 8 (SOff 45%nat 0))].
Definition R_SLOT : YP09.region := YP09.mkRegion (Some 47%nat) 24 32 24 32 [].
Definition REG0 : smem := [ YP09.mkRegion (Some 2%nat) (- 64) 0 (- 64) 0 []; R_ROOT; R_LAST; R_SLOT ].
Definition FFP : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + QSTACK) kHighMemEnd 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(34%nat, mkAF (4096 + 16) (CEIL_MAX - 16) 4)    ;
(35%nat, mkAF 1 (2 ^ 28) 0);
(36%nat, mkAF 1 (2 ^ 40) 0);
(38%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(39%nat, mkAF 0 (2 ^ 48) 0);
(45%nat, mkAF 0 (kBatchSlots - 1) 0);
(46%nat, mkAF 0 (2 ^ 48) 0);
(47%nat, mkAF kHighMemBeg (CEIL_MAX - 32) 3) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SOff 32%nat t_qc)) 11%bv (SOff 32%nat t_cache))
13%bv (SOff 34%nat (-16))) 14%bv (SOff 35%nat 0).
Definition SS0 : sstate := mkSS 0x357d0 SR0 REG0 None FFP.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x357d0) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hra4096 : 4096 <= bv_unsigned (getr regs0 1);
fh_Hsp : ly_stk_lo ly + QSTACK <= sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - QSTACK <= a < sp0 -> apresent (w_H W) mem0 a;
fh_Hu : zone3 (u - 16) (nn + 16) /\ u mod 16 = 0;
fh_IMG : img_cover ly;
fh_Hnn : 1 <= nn < 2 ^ 28;
fh_Hq : 0 <= qb /\ qb + nn <= 2 ^ 48 /\ 1 <= qsz < 2 ^ 40;
fh_last : ly_prim ly <= ql /\ ql + kBatchBytes <= ly_space ly + kSpaceSize /\ ql mod 8192 = 0 /\ 0 <= cnt < kBatchSlots /\
0 <= bsz /\ bsz + nn <= 2 ^ 48 /\
(forall a, ql + 8 <= a < ql + 24 -> apresent (w_H W) mem0 a) /\ (forall a, SLv + 24 <= a < SLv + 32 -> apresent (w_H W) mem0 a);
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x357d0) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hra4096 FH) as Hra4096;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_Hu FH) as Hu;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Hnn FH) as Hnn;
pose proof (fh_Hq FH) as Hq;
pose proof (fh_last FH) as Hlast;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= ly_space ly /\
ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
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
unfold zdisjoint in PT, PSTK, TSTK. cbn [fst snd] in *. unfold T in *.
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
clear - IP HSP T1 T2 T3 T4 T5 T6 T7 PT PSTK TSTK. unfold kHighMemBeg, kThreadObjSize, kPrimResvSize in *. repeat split; lia.
Qed.
Lemma derived_ranges :
4096 + 16 <= u /\ u + nn <= ASAN_CEIL /\ 1 <= nn < 2 ^ 28 /\ 1 <= qsz < 2 ^ 40 /\ 0 <= qb /\ qb + nn <= 2 ^ 48 /\
kHighMemBeg <= ql /\ ql + kBatchBytes <= ASAN_CEIL /\ ql mod 8192 = 0 /\ 0 <= cnt < kBatchSlots /\ 0 <= bsz /\ bsz + nn <= 2 ^ 48 /\
SLv = ql + 8 * cnt /\ 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg + 1024 <= sp0 /\ sp0 <= kHighMemEnd.
Proof.
open_FH. pose proof LYB as (F1 & LB). pose proof F1 as (ZT1 & ZT2 & _). destruct Hu as ((U1 & U2 & _) & U3). destruct Hq as (Q1 & Q2 & Q3). destruct Hsp as [S1 S2].
destruct Hlast as (L1 & L2 & L3 & L4 & L5 & L6 & _). unfold SLv. clear - LB ZT1 ZT2 U1 U2 U3 Hnn Q1 Q2 Q3 S1 S2 L1 L2 L3 L4 L5 L6. numconst. repeat split; lia.
Qed.
Definition WIN (a : Z) : Prop :=
(sp0 - 64 <= a < sp0) \/ (T + t_qc + 24 <= a < T + t_qc + 32) \/ (ql + 8 <= a < ql + 24) \/ (SLv + 24 <= a < SLv + 32).
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
[(Some 2%nat, -64, 0); (Some 32%nat, t_qc + 24, t_qc + 32); (Some 38%nat, 8, 24); (Some 47%nat, 24, 32)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN.
ceil; unfold kHighMemBeg, ASAN_CEIL, t_qc, t_cache, kThreadObjSize, kBatchBytes, kBatchSlots, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by (cbv; lia); rewrite ?E2, ?EqT, ?EqQL, ?EqSL in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
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
Lemma WIN_zone : forall a, WIN a -> ~ (TFIB_IMG_LO <= a < TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg) /\ 0 <= a < 2 ^ 64.
Proof. open_FH. intros a Hw. pose proof derived_ranges as DR. pose proof LYB as (F1 & _). unfold WIN in Hw. clear - Hw DR F1. numconst. unfold TFIB_IMG_END in *. lia. Qed.
Lemma WIN_off : forall a, WIN a -> off_img a.
Proof. intros a Hw. destruct (WIN_zone a Hw) as (A & B & C). unfold off_img. clear - A B C. unfold TFIB_IMG_LO, TFIB_IMG_END in *. lia. Qed.
Lemma notWIN_img : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ WIN a.
Proof. intros a Ha Hw. destruct (WIN_zone a Hw) as (A & _). exact (A Ha). Qed.
Lemma notWIN_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ WIN a.
Proof. intros a Ha Hw. destruct (WIN_zone a Hw) as (_ & B & _). exact (B Ha). Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold TFIB_IMG_END; tac ].
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition CALLEE_SAVED : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_RETP (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (T + t_qc + 24) 8 (qb + nn) /\ val_mem tfibsegs m (ql + 8) 8 (bsz + nn) /\ val_mem tfibsegs m (ql + 16) 8 (cnt + 1) /\
val_mem tfibsegs m (SLv + 24) 8 (u - 16).
End d.
End c.
