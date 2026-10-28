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
Definition qT : nat := 32.
Definition qSB : nat := 33.
Definition qU : nat := 34.
Definition qN : nat := 35.
Definition qQSZ : nat := 36.
Definition qQF : nat := 37.
Definition qQL : nat := 38.
Definition qQB : nat := 39.
Definition qCNT : nat := 40.
Definition qCP : nat := 41.
Definition qJST : nat := 42.
Definition qNB : nat := 43.
Definition qCSL : nat := 44.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (u nn : Z) (q : qcache) (cnt coff jst : Z).
Variables (ra0 s00 s10 s20 s30 s40 s50 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition QSZv : Z := Z.of_nat (length (qc_list q)).
Definition QFv : Z := match qc_list q with [] => 0 | b :: _ => SB + b_self b end.
Definition QLv : Z := match rev (qc_list q) with [] => 0 | b :: _ => SB + b_self b end.
Definition QBv : Z := qc_bytes q.
Definition CPv : Z := coff / 16.
Definition NBv : Z := SB + region_off kBatchClass + coff.
Definition CSLv : Z := T + t_cache + 1936 + 4 * (cnt - 1).
Definition XW : list word :=
[ w64 T; w64 SB; w64 u; w64 nn; w64 QSZv; w64 QFv; w64 QLv; w64 QBv; w64 cnt; w64 CPv; w64 jst; w64 NBv; w64 CSLv;
w64 ra0; w64 s00; w64 s10; w64 s20; w64 s30; w64 s40; w64 s50 ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. reflexivity. Qed.
Lemma EqU : ew E0 34 = w64 u. Proof. reflexivity. Qed.
Lemma EqN : ew E0 35 = w64 nn. Proof. reflexivity. Qed.
Lemma EqQSZ : ew E0 36 = w64 QSZv. Proof. reflexivity. Qed.
Lemma EqQF : ew E0 37 = w64 QFv. Proof. reflexivity. Qed.
Lemma EqQL : ew E0 38 = w64 QLv. Proof. reflexivity. Qed.
Lemma EqQB : ew E0 39 = w64 QBv. Proof. reflexivity. Qed.
Lemma EqCNT : ew E0 40 = w64 cnt. Proof. reflexivity. Qed.
Lemma EqCP : ew E0 41 = w64 CPv. Proof. reflexivity. Qed.
Lemma EqJST : ew E0 42 = w64 jst. Proof. reflexivity. Qed.
Lemma EqNB : ew E0 43 = w64 NBv. Proof. reflexivity. Qed.
Lemma EqCSL : ew E0 44 = w64 CSLv. Proof. reflexivity. Qed.
Lemma EqRA : ew E0 45 = w64 ra0. Proof. reflexivity. Qed.
Lemma EqS0 : ew E0 46 = w64 s00. Proof. reflexivity. Qed.
Lemma EqS1 : ew E0 47 = w64 s10. Proof. reflexivity. Qed.
Lemma EqS2 : ew E0 48 = w64 s20. Proof. reflexivity. Qed.
Lemma EqS3 : ew E0 49 = w64 s30. Proof. reflexivity. Qed.
Lemma EqS4 : ew E0 50 = w64 s40. Proof. reflexivity. Qed.
Lemma EqS5 : ew E0 51 = w64 s50. Proof. reflexivity. Qed.
Definition R_ROOT : YP09.region :=
YP09.mkRegion (Some 32%nat) t_qc (t_qc + 32) t_qc (t_qc + 32)
[YP09.mkChunk t_qc (CVal 8 (SOff 36%nat 0)); YP09.mkChunk (t_qc + 8) (CVal 8 (SOff 37%nat 0));
YP09.mkChunk (t_qc + 16) (CVal 8 (SOff 38%nat 0)); YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 39%nat 0))].
Definition R_CNT : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_cache + 1920) (t_cache + 1924) (t_cache + 1920) (t_cache + 1924) [YP09.mkChunk (t_cache + 1920) (CVal 4 (SOff 40%nat 0))].
Definition R_JST : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_cache_stats + 16) (t_cache_stats + 24) (t_cache_stats + 16) (t_cache_stats + 24) [YP09.mkChunk (t_cache_stats + 16) (CVal 8 (SOff 42%nat 0))].
Definition R_FRAME : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 51%nat 0)); YP09.mkChunk 16 (CVal 8 (SOff 50%nat 0)); YP09.mkChunk 24 (CVal 8 (SOff 49%nat 0));
YP09.mkChunk 32 (CVal 8 (SOff 48%nat 0)); YP09.mkChunk 40 (CVal 8 (SOff 47%nat 0)); YP09.mkChunk 48 (CVal 8 (SOff 46%nat 0));
YP09.mkChunk 56 (CVal 8 (SOff 45%nat 0))].
Definition REG0 : smem :=
[ R_FRAME; R_ROOT; R_CNT; R_JST;
fatom8 0xa29b8 33%nat; flit8 0x9dfd8 1; flit8 0x9dfe0 0x137b1c; flit4 0x137b1c 0 ].
Definition R_LAST : YP09.region := YP09.mkRegion (Some 38%nat) 0 24 0 8 [YP09.mkChunk 16 (CVal 8 (SLit kBatchSlots))].
Definition R_CSZ : YP09.region := YP09.mkRegion (Some 32%nat) (t_cache + 1928) (t_cache + 1936) 0 0 [YP09.mkChunk (t_cache + 1928) (CVal 8 (SLit 8192))].
Definition R_SLOT : YP09.region := YP09.mkRegion (Some 44%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 41%nat 0))].
Definition R_NB : YP09.region := YP09.mkRegion (Some 43%nat) 0 32 0 32 [].
Definition FFQ : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + RSTACK) (kHighMemEnd - 64) 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(33%nat, mkAF kHighMemBeg CEIL_MAX 16);
(34%nat, mkAF (4096 + 16) (CEIL_MAX - 16) 4)    ;
(35%nat, mkAF 1 (2 ^ 28) 0);
(36%nat, mkAF 0 (2 ^ 40) 0);
(37%nat, mkAF 0 CEIL_MAX 0);
(38%nat, mkAF 0 CEIL_MAX 13);
(39%nat, mkAF 0 (2 ^ 48) 0);
(40%nat, mkAF 0 16 0);
(41%nat, mkAF 0 (2 ^ 27) 0);
(42%nat, mkAF 0 (2 ^ 64 - 1) 0);
(43%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(44%nat, mkAF 4096 (CEIL_MAX - 8) 2)           ;
(45%nat, mkAF 0 (2 ^ 64 - 1) 0); (46%nat, mkAF 0 (2 ^ 64 - 1) 0); (47%nat, mkAF 0 (2 ^ 64 - 1) 0); (48%nat, mkAF 0 (2 ^ 64 - 1) 0);
(49%nat, mkAF 0 (2 ^ 64 - 1) 0); (50%nat, mkAF 0 (2 ^ 64 - 1) 0); (51%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SLit 1)) 8%bv (SOff 32%nat (t_cache + 1920)))
9%bv (SOff 32%nat t_cache)) 18%bv (SOff 34%nat (-16))) 19%bv (SOff 32%nat t_qc)) 21%bv (SOff 35%nat 0).
Definition SS0 : sstate := mkSS 0x35924 SR0 REG0 None FFQ.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x35924) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Ltac clear_lets := try clear cfg0; try clear H0; try clear m0; try clear sp0; try clear SB; try clear T.
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hra : YK0s.ret_ok (w64 ra0);
fh_Hra4096 : 4096 <= ra0;
fh_Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 + 64 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 <= a < sp0 + 64 -> apresent (w_H W) mem0 a;
fh_frame : val_mem tfibsegs m0 (sp0 + 56) 8 ra0 /\ val_mem tfibsegs m0 (sp0 + 48) 8 s00 /\ val_mem tfibsegs m0 (sp0 + 40) 8 s10 /\
val_mem tfibsegs m0 (sp0 + 32) 8 s20 /\ val_mem tfibsegs m0 (sp0 + 24) 8 s30 /\ val_mem tfibsegs m0 (sp0 + 16) 8 s40 /\
val_mem tfibsegs m0 (sp0 + 8) 8 s50;
fh_sv : 0 <= ra0 < 2 ^ 64 /\ 0 <= s00 < 2 ^ 64 /\ 0 <= s10 < 2 ^ 64 /\ 0 <= s20 < 2 ^ 64 /\ 0 <= s30 < 2 ^ 64 /\ 0 <= s40 < 2 ^ 64 /\ 0 <= s50 < 2 ^ 64;
fh_Hu : zone3 (u - 16) (nn + 16) /\ u mod 16 = 0;
fh_IMG : img_cover ly;
fh_Hnn : 1 <= nn < 2 ^ 28;
fh_Hq : 0 <= QBv /\ QBv + nn + kBatchBytes <= 2 ^ 48 /\ QSZv < 2 ^ 40 /\ 0 <= QFv < ASAN_CEIL;
fh_nb : need_new_batch q = true;
fh_last : forall lastb initr, rev (qc_list q) = lastb :: initr ->
ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\
val_mem tfibsegs m0 (QLv + 16) 8 kBatchSlots /\ (forall a, QLv <= a < QLv + 8 -> apresent (w_H W) mem0 a);
fh_Hcnt : 1 <= cnt <= 16;
fh_hit : 1 <= cnt ->
val_mem tfibsegs m0 (T + t_cache + 1928) 8 8192 /\ val_mem tfibsegs m0 CSLv 4 CPv /\
0 <= coff /\ coff + kBatchBytes <= 2 ^ 31 /\ coff mod 16 = 0 /\
ly_prim ly <= NBv /\ NBv + kBatchBytes <= SB + kSpaceSize /\ NBv mod 8192 = 0 /\
(forall a, NBv <= a < NBv + 32 -> apresent (w_H W) mem0 a) /\
(forall lastb initr, rev (qc_list q) = lastb :: initr -> NBv + kBatchBytes <= QLv \/ QLv + kBatchBytes <= NBv);
fh_Hjst : 0 <= jst < 2 ^ 64;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x35924) mem0 (seg_rom tfibsegs)))
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
pose proof (fh_frame FH) as Hframe;
pose proof (fh_sv FH) as Hsv;
pose proof (fh_Hu FH) as Hu;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Hnn FH) as Hnn;
pose proof (fh_Hq FH) as Hq;
pose proof (fh_nb FH) as Hnb;
pose proof (fh_last FH) as Hlast;
pose proof (fh_Hcnt FH) as Hcnt;
pose proof (fh_hit FH) as Hhit;
pose proof (fh_Hjst FH) as Hjst;
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
4096 + 16 <= u /\ u + nn <= ASAN_CEIL /\ 1 <= nn < 2 ^ 28 /\
0 <= QSZv < 2 ^ 40 /\ 0 <= QFv < ASAN_CEIL /\ 0 <= QLv < ASAN_CEIL /\ 0 <= QBv /\ QBv + nn + kBatchBytes <= 2 ^ 48 /\
1 <= cnt <= 16 /\ 0 <= jst < 2 ^ 64 /\ 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\
kHighMemBeg + 1024 <= sp0 /\ sp0 + 64 <= kHighMemEnd.
Proof.
open_FH. pose proof LYB as (F1 & LB). pose proof F1 as (ZT1 & ZT2 & _). destruct Hu as ((U1 & U2 & _) & U3). destruct Hq as (Q1 & Q2 & Q3 & Q4). destruct Hsp as [S1 S2].
assert (QL : 0 <= QLv < ASAN_CEIL).
{ destruct (rev (qc_list q)) as [|lb ini] eqn:R.
- unfold QLv. rewrite R. numconst; lia.
- destruct (Hlast lb ini ltac:(first [exact R | reflexivity])) as (L1 & L2 & _). unfold QLv in *. rewrite ?R in *. clear - L1 L2 LB. numconst. lia. }
unfold QSZv in *. numconst. repeat split; lia.
Qed.
Lemma hit_ranges : 1 <= cnt ->
kHighMemBeg <= NBv /\ NBv + kBatchBytes <= ASAN_CEIL /\ NBv mod 8192 = 0 /\ NBv = SB + 24 * 2 ^ 32 + 16 * CPv /\ 0 <= CPv < 2 ^ 27 /\
CSLv = T + t_cache + 1936 + 4 * (cnt - 1) /\ CSLv mod 4 = 0 /\ T + t_cache + 1936 <= CSLv /\ CSLv + 4 <= T + t_cache + 2000 /\
(NBv + kBatchBytes <= T \/ T + kThreadObjSize <= NBv) /\ (NBv + kBatchBytes <= sp0 - RSTACK \/ sp0 + 64 <= NBv).
Proof.
open_FH. intros Hc. pose proof LYB as LB. destruct (Hhit Hc) as (_ & _ & C1 & C2 & C3 & B1 & B2 & B3 & _ & _). destruct Hsp as [S1 S2].
assert (ECP : coff = 16 * (coff / 16)) by (pose proof (Z.div_mod coff 16 ltac:(lia)); lia).
assert (R24 : region_off kBatchClass = 24 * 2 ^ 32) by (rewrite region_off_eq by (unfold kBatchClass; lia); reflexivity).
pose proof (lo_T_al _ LY) as TAL. unfold page_aligned in TAL.
assert (CA : CSLv mod 4 = 0).
{ unfold CSLv, t_cache. replace (T + 208 + 1936 + 4 * (cnt - 1)) with (4 * (cnt - 1 + 536) + T) by lia.
rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. apply (mod0_factor T 4 1024); [lia | exact TAL]. }
unfold NBv, CPv, CSLv in *. rewrite R24 in *. numconst. repeat split; try lia.
Qed.
Definition WINT (a : Z) : Prop :=
(T + t_qc <= a < T + t_qc + 32) \/ (T + t_cache + 1920 <= a < T + t_cache + 1924) \/ (T + t_cache_stats + 16 <= a < T + t_cache_stats + 24).
Definition WINA (a : Z) : Prop := (1 <= cnt /\ NBv <= a < NBv + 32) \/ (qc_list q <> [] /\ QLv <= a < QLv + 8).
Definition WIN (a : Z) : Prop := WINT a \/ WINA a.
Definition win_sub (t w : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst w)) && (snd (fst w) <=? snd (fst t)) && (snd t <=? snd w).
Lemma win_sub_sound : forall E a t w, win_sub t w = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst w)) + snd (fst w) <= a < base_val E (fst (fst w)) + snd w.
Proof.
clear_lets. intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Definition WSK0 : list (option nat * Z * Z) :=
[(Some 32%nat, t_qc, t_qc + 32); (Some 32%nat, t_cache + 1920, t_cache + 1924); (Some 32%nat, t_cache_stats + 16, t_cache_stats + 24)].
Definition WSKN : list (option nat * Z * Z) := WSK0 ++ [(Some 43%nat, 0, 32)].
Definition WSKL : list (option nat * Z * Z) := WSK0 ++ [(Some 38%nat, 0, 8)].
Definition WSKNL : list (option nat * Z * Z) := WSK0 ++ [(Some 43%nat, 0, 32); (Some 38%nat, 0, 8)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN, WINT.
ceil; unfold kHighMemBeg, ASAN_CEIL, t_qc, t_cache, t_cache_stats, kThreadObjSize, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by (cbv; lia); rewrite ?E2, ?EqT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma WSKN_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> 1 <= cnt -> sk_ok E WSKN.
Proof.
open_FH. intros E HE Hc t a Hin Hr. unfold WSKN in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (WSK0_ok E HE t a Hin Hr)|].
pose proof (hit_ranges Hc) as HR. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr.
rewrite HE in Hr by (cbv; lia). rewrite EqNB in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (clear - HR; numconst; lia).
unfold WIN, WINA. right. left. split; [exact Hc | lia].
Qed.
Lemma WSKL_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> qc_list q <> [] -> sk_ok E WSKL.
Proof.
open_FH. intros E HE Hc t a Hin Hr. unfold WSKL in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (WSK0_ok E HE t a Hin Hr)|].
pose proof derived_ranges as DR. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr.
rewrite HE in Hr by (cbv; lia). rewrite EqQL in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (clear - DR; numconst; lia).
unfold WIN, WINA. right. right. split; [exact Hc | lia].
Qed.
Lemma WSKNL_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> 1 <= cnt -> qc_list q <> [] -> sk_ok E WSKNL.
Proof.
intros E HE Hc Hl t a Hin Hr. unfold WSKNL in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (WSK0_ok E HE t a Hin Hr)|].
cbn [In] in Hin. destruct Hin as [<-|[<-|[]]].
- apply (WSKN_ok E HE Hc (Some 43%nat, 0, 32) a); [|exact Hr]. unfold WSKN, WSK0. cbn. tauto.
- apply (WSKL_ok E HE Hl (Some 38%nat, 0, 8) a); [|exact Hr]. unfold WSKL, WSK0. cbn. tauto.
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
clear_lets. intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma WIN_zone : forall a, WIN a -> ~ (TFIB_IMG_LO <= a < TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg) /\ 0 <= a < 2 ^ 64.
Proof.
open_FH. intros a Hw. pose proof derived_ranges as DR. pose proof LYB as (F1 & _). unfold WIN, WINT, WINA in Hw.
destruct Hw as [Hw|[[Hc Hw]|[Hc Hw]]].
- clear - Hw F1 DR; numconst; unfold TFIB_IMG_END in *; lia.
- pose proof (hit_ranges Hc) as HR. clear - Hw HR. numconst. unfold TFIB_IMG_END in *. lia.
- destruct (rev (qc_list q)) as [|lb ini] eqn:R; [exfalso; apply Hc; rewrite <- (rev_involutive (qc_list q)), R; reflexivity|].
destruct (Hlast lb ini ltac:(first [exact R | reflexivity])) as (L1 & L2 & _). unfold QLv in *. rewrite ?R in *. pose proof LYB as (_ & LB). clear - Hw L1 L2 LB. numconst. unfold TFIB_IMG_END in *. lia.
Qed.
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
Proof. clear_lets. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition WIN0 (a : Z) : Prop := WINT a.
Lemma WIN0_WIN : forall a, WIN0 a -> WIN a.
Proof. intros a H; unfold WIN; tauto. Qed.
Definition sk_ok0 (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN0 a.
Lemma WSK0_ok0 : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok0 E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN0, WINT.
ceil; unfold kHighMemBeg, ASAN_CEIL, t_qc, t_cache, t_cache_stats, kThreadObjSize, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by (cbv; lia); rewrite ?E2, ?EqT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
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
clear_lets. intros E m m1 X r Hfr Hpr Hext Hwin. split.
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
Lemma kept_of_aview : forall (E : env) (W5 : world tfibsegs) (m m' : word -> option byte) r,
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
aview tfibsegs (w_H W5) m' a = aview tfibsegs (w_H W) m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
aview tfibsegs (w_H W5) m' a = aview tfibsegs (w_H W) m a /\ ((0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64))) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W5) m') r.
Proof.
intros E W5 m m' r Hext Hwin. split.
- intros a Ha. apply aview_eq_mbyte. apply Hext. exact Ha.
- intros a Ha Hw. destruct (Hwin a Ha) as [EQ Hh]. change (off_img a) in Hh. apply apresent_writable_off; [exact Hh|].
pose proof (writable_off_apresent (w_H W) m a Hh Hw) as P. apply apresent_mbyte in P as [b Hb].
assert (A : aview tfibsegs (w_H W) m a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
rewrite <- EQ in A. apply aview_some in A as (b' & Hb' & _). exact (mbyte_off_apresent (w_H W5) m' a b' Hh Hb').
Qed.
End d.
End c.
