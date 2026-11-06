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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0r YF0w YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF19 YF0o YF0s YF2e YF2g YF2v YF0p YF07.
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
Lemma nth_error_last : forall {A} (l : list A) a, nth_error (l ++ [a]) (length l) = Some a.
Proof. intros A l a. rewrite nth_error_app2 by img_lia. rewrite Nat.sub_diag. img_refl. Qed.
Lemma rev_last : forall {A} (l : list A) a, rev (l ++ [a]) = a :: rev l.
Proof. intros A l a. rewrite rev_app_distr. img_refl. Qed.
Section d. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : drain_pre B ly X W regs mem md.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Local Notation GLv := (YF2e.GLv ly gq).
Local Notation TFv := (YF2e.TFv ly tq).
Local Notation TLv := (YF2e.TLv ly tq).
Local Notation M := (YF0p.M B ly X W regs mem md PRE).
Local Notation HSP := (YF0p.HSP B ly X W regs mem md PRE).
Local Notation HI := (YF0p.HI B ly X W regs mem md PRE).
Local Notation batch_facts := (YF0p.batch_facts B ly X W regs mem md PRE).
Local Notation g_facts := (YF0p.g_facts B ly X W regs mem md PRE).
Local Notation t_facts := (YF0p.t_facts B ly X W regs mem md PRE).
Definition L : list batch := G ++ Tq.
Definition addr (b : batch) : Z := SB + b_self b.
Definition firstaddr (l : list batch) : Z := match l with [] => 0 | b :: _ => addr b end.
Definition lastaddr (l : list batch) : Z := match rev l with [] => 0 | b :: _ => addr b end.
Definition zlen (l : list batch) : Z := Z.of_nat (length l).
Definition sp1 : Z := sp0 - LFRAME.
Let WF : Wf (as_universe B) X := am_wf B ly X _ M.
Let LO : layout_ok ly := am_layout B ly X _ M.
Lemma L_all : forall b, In b L <-> In b (all_batches X).
Proof. intros b. unfold L, all_batches. rewrite !in_app_iff. tauto. Qed.
Lemma L_nodup : List.NoDup (map b_self L).
Proof.
pose proof (YF0s.batches_nodup B ly X _ M) as ND. unfold all_batches in ND. unfold L. rewrite map_app in ND |- *.
apply NoDup_app_iff in ND as (N1 & N2 & N3). img_apply NoDup_app_iff. splits; [img_try (img_exact N2) | img_try (img_exact N1) |]. intros x A1 A2. img_exact (N3 x A2 A1).
Qed.

Lemma L_apart : forall l1 b1 l2 b2 l3, L = l1 ++ b1 :: l2 ++ b2 :: l3 -> addr b1 + kBatchBytes <= addr b2 \/ addr b2 + kBatchBytes <= addr b1.
Proof.
intros l1 b1 l2 b2 l3 E. pose proof L_nodup as ND. rewrite E, map_app in ND. cbn [map] in ND. rewrite map_app in ND. cbn [map] in ND.
apply NoDup_app_iff in ND as (_ & ND & _). inversion ND as [|x l N1 N2]; (subst; cbv beta).
assert (NE : b_self b1 <> b_self b2) by (img_try (intros EQ; img_apply N1; rewrite EQ; img_apply in_app_iff; right; left; img_refl)).
assert (I1 : In b1 (all_batches X)) by (img_try (img_apply L_all; rewrite E; img_apply in_app_iff; right; left; img_refl)).
assert (I2 : In b2 (all_batches X)) by (img_try (img_apply L_all; rewrite E; img_apply in_app_iff; right; right; img_apply in_app_iff; right; left; img_refl)).
pose proof (YF0s.batches_apart B ly X _ M _ HSP b1 b2 I1 I2 NE) as D. unfold zdisjoint, YF0s.addr in D. cbn [fst snd] in D. unfold addr. img_lia.
Qed.
Lemma sum_L : sum_bytes L = qc_bytes gq + qc_bytes tq.
Proof. pose proof g_facts as (_ & _ & _ & _ & _ & _ & EG). pose proof t_facts as (_ & _ & _ & _ & _ & _ & ET). unfold L. rewrite sum_bytes_app. unfold YF2e.GBv, YF2e.TBv in *. img_lia. Qed.
Lemma sum_lb : forall l, (forall b, In b l -> In b L) -> 0 <= sum_bytes l.
Proof. intros l Hl. img_apply (YF0s.sum_bytes_lb B ly X _ M). intros b Hb. apply L_all, Hl, Hb. Qed.
Lemma sum_bound : sum_bytes L <= 2 ^ 30 + 2 ^ 29.
Proof. rewrite sum_L. pose proof g_facts as (Ga & _). pose proof t_facts as (Ta & _). unfold YF2e.GBv, YF2e.TBv in *. img_lia. Qed.
Lemma len_L : zlen L <= 16384.
Proof.
pose proof (YG0s.batches_len_fuel _ _ _ _ X WF (proj1 (proj2 (proj2 PRE)))) as BE. unfold all_batches in BE. unfold L, zlen. rewrite length_app in BE |- *. img_lia.
Qed.
Lemma first_range : forall l, (forall b, In b l -> In b L) -> 0 <= firstaddr l < ASAN_CEIL /\ firstaddr l mod 8192 = 0 /\ (l <> [] -> kHighMemBeg <= firstaddr l).
Proof.
intros l Hl. unfold firstaddr. destruct l as [|b2 t]; [img_try (ceil; unfold ASAN_CEIL; splits; [img_lia | img_lia | img_refl | intros NE; exfalso; img_exact (NE eq_refl)])|].
destruct (batch_facts b2 (proj1 (L_all b2) (Hl b2 (or_introl eq_refl)))) as (L1 & L2 & L3 & L4 & L5 & _). unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kBatchBytes, kHighMemBeg in *. splits; try img_lia; try img_exact L3.
Qed.
Lemma last_range : forall l, (forall b, In b l -> In b L) -> 0 <= lastaddr l < ASAN_CEIL /\ lastaddr l mod 8192 = 0 /\
(l <> [] -> exists lb ini, rev l = lb :: ini /\ l = rev ini ++ [lb] /\ lastaddr l = addr lb /\ In lb l).
Proof.
intros l Hl. unfold lastaddr. destruct (rev l) as [|lb ini] eqn:ER.
- ceil; unfold ASAN_CEIL. splits; [img_lia | img_lia | img_refl |]. intros NE. exfalso. img_apply NE. rewrite <- (rev_involutive l), ER. img_refl.
- assert (EP : l = rev ini ++ [lb]) by (img_try (rewrite <- (rev_involutive l), ER; img_refl)).
assert (IN : In lb l) by (img_try (rewrite EP; img_apply in_app_iff; right; left; img_refl)).
destruct (batch_facts lb (proj1 (L_all lb) (Hl lb IN))) as (L1 & L2 & L3 & L4 & L5 & _).
unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kBatchBytes, kHighMemBeg in *. splits; [img_lia | img_lia | img_try (img_exact L3) |]. intros _. exists lb, ini. splits; [img_refl | img_try (img_exact EP) | img_refl | img_try (img_exact IN)].
Qed.
Definition DW (P1 : list batch) (a : Z) : Prop :=
(sp0 - LFRAME <= a < sp0) \/ YF2e.WINF ly a \/ (G <> [] /\ GLv <= a < GLv + 8) \/ (exists b, In b P1 /\ addr b <= a < addr b + 8).
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition LST (P1 R : list batch) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 (0x337d0 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 2 = w64 sp1 /\ getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = w64 kQuarantineMin /\ getr regs' 12 = w64 (T + t_cache) /\
getr regs' 13 = getr regs 13 /\ getr regs' 14 = w64 (zlen P1) /\ getr regs' 15 = w64 (lastaddr P1) /\ getr regs' 16 = w64 (zlen R) /\
getr regs' 5 = w64 (firstaddr R) /\ getr regs' 1 = getr regs 1 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs r) /\
(forall x : word, ~ DW P1 (bv_unsigned x) -> mem' x = mem x) /\
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem' a) /\
let m := mrestrict H0 mem' in
val_mem tfxsegs m (A_QUAR + 152) 4 257 /\
val_mem tfxsegs m (A_QUAR + 160) 8 (zlen R) /\ val_mem tfxsegs m (A_QUAR + 168) 8 (firstaddr R) /\
val_mem tfxsegs m (A_QUAR + 176) 8 TLv /\ val_mem tfxsegs m (A_QUAR + 184) 8 (sum_bytes R) /\
val_mem tfxsegs m (T + t_qc) 8 0 /\ val_mem tfxsegs m (T + t_qc + 8) 8 0 /\ val_mem tfxsegs m (T + t_qc + 16) 8 0 /\ val_mem tfxsegs m (T + t_qc + 24) 8 0 /\
((length P1 < length G)%nat -> forall lb initr, rev G = lb :: initr -> val_mem tfxsegs m (addr lb) 8 TFv) /\
(forall i b, nth_error P1 i = Some b -> val_mem tfxsegs m (addr b) 8 (next_addr ly P1 i)) /\
(forall i b, nth_error R i = Some b -> val_mem tfxsegs m (addr b) 8 (next_addr ly R i) /\ val_mem tfxsegs m (addr b + 8) 8 (b_bytes b)) /\
val_mem tfxsegs m (sp1 + 8) 8 (firstaddr P1) /\ val_mem tfxsegs m (sp1 + 24) 8 (sum_bytes P1) /\
val_mem tfxsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfxsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfxsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfxsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfxsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfxsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1)).
Definition ATDR (P R : list batch) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_DoRecycle) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 2 = w64 sp1 /\ getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = w64 sp1 /\ getr regs' 12 = w64 (T + t_cache) /\
getr regs' 13 = getr regs 13 /\ getr regs' 1 = w64 (0x33844 + D_150) /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs r) /\
(forall x : word, ~ DW P (bv_unsigned x) -> mem' x = mem x) /\
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem' a) /\
let m := mrestrict H0 mem' in
(forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfxsegs m a = Some (Z_to_bv 8 0)) /\
val_mem tfxsegs m (A_QUAR + 160) 8 (zlen R) /\ val_mem tfxsegs m (A_QUAR + 168) 8 (firstaddr R) /\
val_mem tfxsegs m (A_QUAR + 176) 8 (lastaddr R) /\ val_mem tfxsegs m (A_QUAR + 184) 8 (sum_bytes R) /\
val_mem tfxsegs m (T + t_qc) 8 0 /\ val_mem tfxsegs m (T + t_qc + 8) 8 0 /\ val_mem tfxsegs m (T + t_qc + 16) 8 0 /\ val_mem tfxsegs m (T + t_qc + 24) 8 0 /\
((length P < length G)%nat -> forall lb initr, rev G = lb :: initr -> val_mem tfxsegs m (addr lb) 8 TFv) /\
(forall i b, nth_error P i = Some b -> val_mem tfxsegs m (addr b) 8 (next_addr ly P i)) /\
val_mem tfxsegs m sp1 8 (zlen P) /\ val_mem tfxsegs m (sp1 + 8) 8 (firstaddr P) /\ val_mem tfxsegs m (sp1 + 16) 8 (lastaddr P) /\ val_mem tfxsegs m (sp1 + 24) 8 (sum_bytes P) /\
val_mem tfxsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfxsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfxsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfxsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfxsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfxsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1)).
Section e.
Variables (P1 R' : list batch) (b : batch) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Hypothesis HL : L = P1 ++ b :: R'.
Let R : list batch := b :: R'.
Hypothesis Q2 : getr regs' 2 = w64 sp1.
Hypothesis Q10 : getr regs' 10 = w64 A_QUAR.
Hypothesis Q11 : getr regs' 11 = w64 kQuarantineMin.
Hypothesis Q12 : getr regs' 12 = w64 (T + t_cache).
Hypothesis Q14 : getr regs' 14 = w64 (zlen P1).
Hypothesis Q15 : getr regs' 15 = w64 (lastaddr P1).
Hypothesis Q16 : getr regs' 16 = w64 (zlen R).
Hypothesis Q5 : getr regs' 5 = w64 (firstaddr R).
Hypothesis Q1 : getr regs' 1 = getr regs 1.
Hypothesis QS : forall r : bv 5, In r SREGS -> getr regs' r = getr regs r.
Hypothesis FRM : forall x : word, ~ DW P1 (bv_unsigned x) -> mem' x = mem x.
Hypothesis PRS : forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem' a.
Let m := mrestrict H0 mem'.
Hypothesis VQW : val_mem tfxsegs m (A_QUAR + 152) 4 257.
Hypothesis VQS : val_mem tfxsegs m (A_QUAR + 160) 8 (zlen R).
Hypothesis VQF : val_mem tfxsegs m (A_QUAR + 168) 8 (firstaddr R).
Hypothesis VQL : val_mem tfxsegs m (A_QUAR + 176) 8 TLv.
Hypothesis VQB : val_mem tfxsegs m (A_QUAR + 184) 8 (sum_bytes R).
Hypothesis VRL : forall i b2, nth_error R i = Some b2 -> val_mem tfxsegs m (addr b2) 8 (next_addr ly R i) /\ val_mem tfxsegs m (addr b2 + 8) 8 (b_bytes b2).
Hypothesis VPL : forall i b2, nth_error P1 i = Some b2 -> val_mem tfxsegs m (addr b2) 8 (next_addr ly P1 i).
Hypothesis VT8 : val_mem tfxsegs m (sp1 + 8) 8 (firstaddr P1).
Hypothesis VT24 : val_mem tfxsegs m (sp1 + 24) 8 (sum_bytes P1).
Hypothesis Q13 : getr regs' 13 = getr regs 13.
Hypothesis VQ0 : val_mem tfxsegs m (T + t_qc) 8 0.
Hypothesis VQ8 : val_mem tfxsegs m (T + t_qc + 8) 8 0.
Hypothesis VQ16 : val_mem tfxsegs m (T + t_qc + 16) 8 0.
Hypothesis VQ24 : val_mem tfxsegs m (T + t_qc + 24) 8 0.
Hypothesis VG : (length P1 < length G)%nat -> forall lb initr, rev G = lb :: initr -> val_mem tfxsegs m (addr lb) 8 TFv.
Hypothesis VS32 : val_mem tfxsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)).
Hypothesis VS40 : val_mem tfxsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)).
Hypothesis VS48 : val_mem tfxsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)).
Hypothesis VS56 : val_mem tfxsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)).
Hypothesis VS64 : val_mem tfxsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)).
Hypothesis VS72 : val_mem tfxsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1)).
Definition pb : Z := addr b.
Definition pnx : Z := firstaddr R'.
Definition pbs : Z := b_bytes b.
Definition pqb : Z := sum_bytes R.
Definition pnr : Z := zlen R.
Definition pnp : Z := zlen P1.
Definition plp : Z := lastaddr P1.
Definition ptby : Z := sum_bytes P1.
Definition ptfi : Z := firstaddr P1.
Definition pgl : Z := TLv.
Lemma InL_b : In b L. Proof. rewrite HL. img_apply in_app_iff. right. left. img_refl. Qed.
Lemma InL_P1 : forall b2, In b2 P1 -> In b2 L. Proof. intros b2 Hb2. rewrite HL. img_apply in_app_iff. left. img_exact Hb2. Qed.
Lemma InL_R' : forall b2, In b2 R' -> In b2 L. Proof. intros b2 Hb2. rewrite HL. img_apply in_app_iff. right. right. img_exact Hb2. Qed.
Lemma sp1_val : sp1 = sp0 - 80. Proof. img_refl. Qed.
Lemma Usp1 : kHighMemBeg + DRSTACK <= sp1 /\ sp1 + LFRAME <= kHighMemEnd /\ ly_stk_lo ly + DRSTACK <= sp1 /\ sp1 + LFRAME <= ly_stk_hi ly /\ 0 <= sp1 < 2 ^ 64.
Proof. pose proof HSP as [S1 S2]. pose proof HI as (_ & _ & _ & _ & hS1 & hS2 & _). unfold sp1. fold sp0 in S1, S2. unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, DRSTACK, LFRAME, kHighMemBeg, kHighMemEnd in *. img_lia. Qed.
Lemma b_facts : ly_prim ly <= pb /\ pb + kBatchBytes <= SB + kSpaceSize /\ pb mod 8192 = 0 /\ kHighMemBeg <= pb /\ pb + kBatchBytes <= ASAN_CEIL /\ kBatchBytes <= pbs /\ pbs <= pqb /\ pqb <= sum_bytes L.
Proof.
destruct (batch_facts b (proj1 (L_all b) InL_b)) as (L1 & L2 & L3 & L4 & L5 & _ & L7). unfold pb, pbs, pqb, addr.
pose proof (sum_lb R' InL_R') as S1. pose proof (sum_lb P1 InL_P1) as S2.
assert (E : sum_bytes L = sum_bytes P1 + (b_bytes b + sum_bytes R')) by (img_try (rewrite HL, sum_bytes_app, sum_bytes_cons; img_lia)).
unfold R. rewrite sum_bytes_cons. splits; try assumption; img_lia.
Qed.
Lemma nx_facts : 0 <= pnx < ASAN_CEIL /\ pnx mod 8192 = 0.
Proof. destruct (first_range R' InL_R') as (A1 & A2 & _). unfold pnx. split; [img_try (img_exact A1) | img_try (img_exact A2)]. Qed.
Lemma lp_facts : 0 <= plp < ASAN_CEIL /\ plp mod 8192 = 0 /\
(pnp <> 0 -> exists lb ini, rev P1 = lb :: ini /\ plp = addr lb /\ ly_prim ly <= plp /\ plp + kBatchBytes <= SB + kSpaceSize /\ (plp + kBatchBytes <= pb \/ pb + kBatchBytes <= plp) /\ In lb P1).
Proof.
destruct (last_range P1 InL_P1) as (A1 & A2 & A3). unfold plp. splits; [img_lia | img_lia | img_try (img_exact A2) |]. intros NE.
destruct (A3 ltac:(img_try (intros E; img_apply NE; unfold pnp, zlen; rewrite E; img_refl))) as (lb & ini & ER & EP & EL & IN).
destruct (batch_facts lb (proj1 (L_all lb) (InL_P1 lb IN))) as (L1 & L2 & L3 & L4 & L5 & _).
exists lb, ini. rewrite EL. splits; try img_refl; try assumption; try (unfold addr in *; img_lia).
pose proof (L_apart (rev ini) lb [] b R' ltac:(img_try (rewrite HL, EP, <- app_assoc; img_refl))) as D. unfold pb. img_exact D.
Qed.
Lemma tfi_facts : 0 <= ptfi < ASAN_CEIL.
Proof. destruct (first_range P1 InL_P1) as (A1 & _). img_exact A1. Qed.
Lemma cnt_facts : 1 <= pnr < 2 ^ 40 /\ 0 <= pnp < 2 ^ 40.
Proof. pose proof len_L as LL. unfold pnr, pnp, zlen, R in *. rewrite HL, length_app in LL. cbn [length] in LL |- *. unfold EV_MAX in LL. img_lia. Qed.
Local Notation E1 := (YF2g.E0 regs' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl).
Lemma E1r (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E1 k = getr regs' r.
Proof. intros Hk. img_exact (YF2g.Er regs' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl k r Hk). Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Lemma chunk_atom1 : forall base a (w : BinNums.N) k0 x, ew E1 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfxsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E1 m base (YQ0b.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Lemma REG1_ok : Forall (region_ok tfxsegs E1 m) YF2g.REG0.
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). pose proof sum_bound as SBD.
pose proof nx_facts as [N1 N2]. pose proof cnt_facts as [C1 C2]. pose proof tfi_facts as F1. pose proof (sum_lb P1 InL_P1) as SP1.
pose proof t_facts as (_ & _ & _ & _ & Te & Tf & _).
assert (EP : sum_bytes L = sum_bytes P1 + sum_bytes R) by (img_try (rewrite HL, sum_bytes_app; img_refl)).
pose proof (YF0p.AQ B TB) as EAQ. unfold o_quar in EAQ. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & hI1 & hI2).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, kLowMemEnd in U1, U2, B4, B5, B6, N1, F1, Te, hI1, hI2.
assert (BV2 : bv_unsigned (ew E1 2) = sp1) by (img_try (rewrite (E1r 2 2%bv eq_refl), Q2; img_apply unsigned_lit_small; img_lia)).
assert (SR : 0 <= sum_bytes R') by (img_try (img_apply sum_lb; img_exact InL_R')).
unfold pb, pnx, pbs, pqb, pnr, pnp, plp, ptby, ptfi, pgl in *. unfold R in *. rewrite ?sum_bytes_cons in *.
unfold YF2g.REG0, YF2g.R_STK, YF2g.R_QW, YF2g.R_QG, YF2g.R_B.
img_apply Forall_cons.
{   reg_intro. rewrite BV2. unfold LFRAME. split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; img_lia)|]. img_apply PRS. unfold sp1, LFRAME, DSTACK in *. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom1 _ _ 8 40%nat (firstaddr P1)); [img_refl | img_lia | img_try (img_exact VT8) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 _ _ 8 39%nat (sum_bytes P1)); [img_refl | img_lia | img_try (img_exact VT24) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (rewrite EAQ; img_lia)|]. split.
{ intros o Ho. img_apply rw_writable. rewrite EAQ, (ts_inst _ TB) in Ho. unfold TFX_INST in Ho. img_lia. }
pose proof (proj1 (val_mem4_bytes _ _ _) VQW) as (W0 & W1 & W2 & W3).
img_change (YP0g.le_byte 257 4 0) with 1 in W0. img_change (YP0g.le_byte 257 4 1) with 1 in W1. img_change (YP0g.le_byte 257 4 2) with 0 in W2. img_change (YP0g.le_byte 257 4 3) with 0 in W3.
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- eapply chunk_ok_val; [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (img_apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; img_exact W0)].
- eapply chunk_ok_val; [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (img_apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; replace (A_QUAR + 153) with (A_QUAR + 152 + 1) by img_lia; img_exact W1)].
- img_apply chunk_ok_zero_mb. intros i Hi. rewrite Z.add_0_l.
assert (C : i = 0 \/ i = 1) by img_lia. destruct C as [-> | ->]; [img_try (replace (A_QUAR + 154 + 0) with (A_QUAR + 152 + 2) by img_lia; img_exact W2) | img_try (replace (A_QUAR + 154 + 1) with (A_QUAR + 152 + 3) by img_lia; img_exact W3)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (rewrite EAQ; img_lia)|]. split.
{ intros o Ho. img_apply rw_writable. rewrite EAQ, (ts_inst _ TB) in Ho. unfold TFX_INST in Ho. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom1 0 _ 8 36%nat (zlen (b :: R'))); [img_refl | img_lia | img_try (rewrite Z.add_0_l; img_exact VQS) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 0 _ 8 32%nat (addr b)); [img_refl | img_lia | img_try (rewrite Z.add_0_l; img_exact VQF) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 0 _ 8 41%nat TLv); [img_refl | img_lia | img_try (rewrite Z.add_0_l; img_exact VQL) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 0 _ 8 35%nat (b_bytes b + sum_bytes R')); [img_refl | img_lia | img_try (rewrite Z.add_0_l; img_exact VQB) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{
destruct (VRL 0%nat b eq_refl) as [V0 V8]. unfold next_addr in V0. cbn [nth_error] in V0.
reg_intro. rewrite YF2g.EqB. unfold w64. rewrite unsigned_lit_small by img_lia. split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. pose proof (V0 (Z.to_nat o) ltac:(img_lia)) as E. rewrite Z2Nat.id in E by img_lia. eapply mbyte_high_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; img_lia) | img_try (img_exact E)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom1 _ _ 8 33%nat (firstaddr R')); [img_refl | img_lia | | img_try (r8) | img_try (cbn; img_lia)].
rewrite Z.add_0_r. replace (firstaddr R') with (match nth_error R' 0 with Some b3 => SB + b_self b3 | None => 0 end); [img_try (img_exact V0)|].
unfold firstaddr, addr. destruct R'; img_refl.
- img_apply (chunk_atom1 _ _ 8 34%nat (b_bytes b)); [img_refl | img_lia | img_try (img_exact V8) | img_try (r8) | img_try (cbn; img_lia)]. }
Qed.
Lemma PAIRS1_ok : pairwise_disjoint E1 YF2g.REG0.
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & _).
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2).
pose proof (YF0p.GEO B ly X W regs mem md PRE) as (_ & _ & _ & G_PS & _).
pose proof (YF0p.AQ B TB) as EAQ. unfold o_quar in EAQ.
img_apply pairwise_disjoint_of_extents. unfold YF2g.REG0, YF2g.R_STK, YF2g.R_QW, YF2g.R_QG, YF2g.R_B, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite (E1r 2 2%bv eq_refl), Q2, YF2g.EqB. unfold w64. unfold pb in *.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, kLowMemEnd, kSpaceSize, kPrimResvSize in *.
rewrite !unsigned_lit_small by img_lia. rewrite EAQ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold sp1 in *. fold sp0. pose proof HSP as [S1 S2]. fold sp0 in S1, S2. unfold DSTACK in S1.
repeat split; img_lia.
Qed.
Lemma FACTS1_ok : atoms_ok E1 (f_atoms YF2g.FFL).
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). pose proof sum_bound as SBD.
pose proof nx_facts as [N1 N2]. pose proof cnt_facts as [C1 C2]. pose proof tfi_facts as F1. pose proof (sum_lb P1 InL_P1) as SP1. pose proof (sum_lb R' InL_R') as SR.
pose proof lp_facts as (P1a & P2a & _). pose proof t_facts as (_ & _ & _ & _ & Te & Tf & _).
assert (EP : sum_bytes L = sum_bytes P1 + sum_bytes R) by (img_try (rewrite HL, sum_bytes_app; img_refl)).
pose proof HSP as [S1 S2]. fold sp0 in S1, S2. pose proof PRE as PRE'; destruct PRE' as (_ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
unfold pb, pnx, pbs, pqb, pnr, pnp, plp, ptby, ptfi, pgl in *. unfold R in *. rewrite ?sum_bytes_cons in *.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, kSpaceSize, kPrimResvSize in U1, U2, B4, B5, B6, N1, F1, Te, P1a.
assert (AF : forall k0 Xv lo hi al, ew E1 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E1 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (E2' : ew E1 2 = w64 sp1) by (img_try (rewrite (E1r 2 2%bv eq_refl), Q2; img_refl)).
assert (SAL : sp1 mod 16 = 0). { unfold sp1, LFRAME. rewrite Zminus_mod, Hal. img_refl. }
cbn [YF2g.FFL f_atoms atoms_ok]. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, LFRAME.
split. { img_apply (AF 2%nat sp1); [img_try (img_exact E2')| | | |]. all: clear - CR0 U1 U2 U5 SAL; first [img_lia | img_change (2 ^ 4) with 16; img_exact SAL]. }
split. { img_apply (AF 32%nat (addr b)); [img_refl| | | |]. all: clear - CR0 B3 B4 B5; first [img_lia | img_change (2 ^ 13) with 8192; img_exact B3]. }
split. { img_apply (AF 33%nat (firstaddr R')); [img_refl| | | |]. all: clear - CR0 N1 N2; first [img_lia | img_change (2 ^ 13) with 8192; img_exact N2]. }
split. { img_apply (AF 34%nat (b_bytes b)); [img_refl| | | |]. all: clear - CR0 B6 B7 B8 SBD SP1 SR EP; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 35%nat (b_bytes b + sum_bytes R')); [img_refl| | | |]. all: clear - CR0 B6 B7 B8 SBD SP1 SR EP; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 36%nat (zlen (b :: R'))); [img_refl| | | |]. all: clear - C1; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat (zlen P1)); [img_refl| | | |]. all: clear - C2; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat (lastaddr P1)); [img_refl| | | |]. all: clear - CR0 P1a P2a; first [img_lia | img_change (2 ^ 13) with 8192; img_exact P2a]. }
split. { img_apply (AF 39%nat (sum_bytes P1)); [img_refl| | | |]. all: clear - CR0 B6 SBD SP1 SR EP; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat (firstaddr P1)); [img_refl| | | |]. all: clear - CR0 F1; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 41%nat TLv); [img_refl| | | |]. all: clear - CR0 Te Tf; first [img_lia | img_change (2 ^ 13) with 8192; img_exact Tf]. }
Qed.
Hypothesis Q4 : getr regs' 4 = w64 TFX_TP.
Lemma SEED1_ok : st_ok tfxsegs E1 YF2g.SS0 (restrict H0 (mkst regs' (w64 (0x337d0 + D_150)) mem' (seg_rom tfxsegs))).
Proof.
rewrite restrict_mkst_fx. unfold YF2g.SS0, YF2g.SR0, sr_set. cbn [bv_eqb]. unfold YF2g.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact Q4] | intros XX; discriminate | cbn [sv_denot]; img_exact Q10] | intros XX; discriminate | cbn [sv_denot]; img_exact Q11] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |]) | img_try (intros XX; discriminate) |].
+ cbn [sv_denot]. fold E1. rewrite YF2g.EqB, Q5. unfold w64, R, firstaddr, pb. rewrite Zbv_add_unsigned, Z.add_0_r. img_refl.
+ cbn [sv_denot]. fold E1. rewrite YF2g.EqNP, Q14. unfold w64, pnp. rewrite Zbv_add_unsigned, Z.add_0_r. img_refl.
+ cbn [sv_denot]. fold E1. rewrite YF2g.EqLP, Q15. unfold w64, plp. rewrite Zbv_add_unsigned, Z.add_0_r. img_refl.
+ cbn [sv_denot]. fold E1. rewrite YF2g.EqNR, Q16. unfold w64, pnr, R. rewrite Zbv_add_unsigned, Z.add_0_r. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG1_ok.
- img_exact PAIRS1_ok.
- split; [img_try (img_exact FACTS1_ok) | img_try (split; img_exact I)].
Qed.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Theorem FHL_ok : YF2g.free_hyps W ly regs' mem' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl.
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). pose proof sum_bound as SBD.
pose proof nx_facts as [N1 N2]. pose proof cnt_facts as [C1 C2]. pose proof tfi_facts as F1. pose proof (sum_lb P1 InL_P1) as SP1. pose proof (sum_lb R' InL_R') as SR.
pose proof lp_facts as (P1a & P2a & P3a). pose proof t_facts as (_ & _ & _ & _ & Te & Tf & _).
assert (EP : sum_bytes L = sum_bytes P1 + sum_bytes R) by (img_try (rewrite HL, sum_bytes_app; img_refl)). unfold R in EP. rewrite sum_bytes_cons in EP.
pose proof HSP as [S1 S2]. fold sp0 in S1, S2. pose proof PRE as PRE'; destruct PRE' as (_ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
constructor.
- img_exact LO.
- img_exact Q4.
- rewrite Q1. img_exact Hra.
- rewrite Q2. unfold w64. rewrite unsigned_lit_small by img_lia. split; [img_try (img_exact U3) | img_try (img_exact U4)].
- rewrite Q2. unfold w64. rewrite unsigned_lit_small by img_lia. unfold sp1, LFRAME. rewrite Zminus_mod, Hal. img_refl.
- rewrite Q2. unfold w64. rewrite unsigned_lit_small by img_lia. intros a Ha. img_apply PRS. unfold sp1, DRSTACK, LFRAME, DSTACK in *. img_lia.
- splits; [img_try (img_exact B1) | img_try (img_exact B2) | img_try (img_exact B3)].
- img_exact nx_facts.
- img_exact cnt_facts.
- unfold pbs, pqb, ptby, R in *. rewrite sum_bytes_cons in *. clear - B6 B7 B8 SBD SP1 SR EP. unfold kBatchBytes in *. splits; img_lia.
- unfold pgl. split; [img_try (img_exact Te) | img_try (img_exact Tf)].
- img_exact F1.
- splits; [img_lia | img_lia | img_try (img_exact P2a) |]. intros NE. destruct (P3a NE) as (lb & ini & ER & EL & L1 & L2 & L3 & IN). splits; [img_try (img_exact L1) | img_try (img_exact L2) | img_try (img_exact L3) |].
intros a Ha. assert (EP1 : P1 = rev ini ++ [lb]) by (img_try (rewrite <- (rev_involutive P1), ER; img_refl)).
pose proof (VPL (length (rev ini)) lb ltac:(img_try (rewrite EP1; img_apply nth_error_last))) as V. rewrite <- EL in V.
pose proof (V (Z.to_nat (a - plp)) ltac:(img_lia)) as E. rewrite Z2Nat.id in E by img_lia. replace (plp + (a - plp)) with a in E by img_lia.
destruct (batch_facts lb (proj1 (L_all lb) (InL_P1 lb IN))) as (_ & _ & _ & L4 & L5 & _). unfold addr in EL. rewrite <- EL in L4, L5.
eapply mbyte_high_apresent; [| img_try (img_exact E)]. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, ASAN_CEIL, kBatchBytes in *. img_lia.
- img_exact SEED1_ok.
Qed.
Local Notation WINL := (YF2g.WIN regs' pb pnp plp).
Lemma ND3 : (forall x, In x P1 -> b_self x <> b_self b) /\ (forall y, In y R' -> b_self y <> b_self b) /\
(forall x y, In x P1 -> In y R' -> b_self x <> b_self y) /\ List.NoDup (map b_self P1) /\ List.NoDup (map b_self R').
Proof.
pose proof L_nodup as ND. rewrite HL, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (N1 & N2 & N3). inversion N2 as [|y l N4 N5]; (subst; cbv beta).
splits.
- intros x Hx E. img_apply (N3 (b_self x)); [img_try (img_apply in_map; img_exact Hx) | img_try (left; symmetry; img_exact E)].
- intros y Hy E. img_apply N4. rewrite <- E. img_apply in_map. img_exact Hy.
- intros x y Hx Hy E. img_apply (N3 (b_self x)); [img_try (img_apply in_map; img_exact Hx) | img_try (right; rewrite E; img_apply in_map; img_exact Hy)].
- img_exact N1.
- img_exact N5.
Qed.
Lemma NW_T : forall k, 0 <= k < 32 -> ~ WINL (T + t_qc + k).
Proof.
intros k Hk. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2). pose proof b_facts as (B1 & B2 & _). pose proof lp_facts as (_ & _ & P3a).
pose proof (YF0p.GEO B ly X W regs mem md PRE) as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _). pose proof Usp1 as (U1 & U2 & U3 & U4 & _).
pose proof (YF0p.AQ B TB) as EAQ. unfold o_quar in EAQ.
unfold YF2g.WIN, YF2g.WINF, YF2g.WINA. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (pose proof Usp1; img_lia)).
intros [Y|[[Y|[Y|Y]]|[NE Y]]].
- unfold sp1, LFRAME, DRSTACK, kThreadObjSize, t_qc in *. fold sp0 in U3, U4. img_lia.
- rewrite EAQ in Y. pose proof (ts_inst _ TB) as EI. clear - Y Hk hT1 EI. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, TFX_INST, kThreadObjSize, t_qc in *. img_lia.
- rewrite EAQ in Y. pose proof (ts_inst _ TB) as EI. clear - Y Hk hT1 EI. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, TFX_INST, kThreadObjSize, t_qc in *. img_lia.
- unfold pb, addr, kThreadObjSize, kPrimResvSize, kSpaceSize, kBatchBytes, t_qc in *. img_lia.
- destruct (P3a NE) as (lb & ini & _ & EL & L1 & L2 & _). rewrite EL in Y. unfold addr, kThreadObjSize, kPrimResvSize, kSpaceSize, kBatchBytes, t_qc in *. img_lia.
Qed.
Lemma NW_S : forall k, 32 <= k < 80 -> ~ WINL (sp1 + k).
Proof.
intros k Hk. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2). pose proof b_facts as (B1 & B2 & _). pose proof lp_facts as (_ & _ & P3a).
pose proof (YF0p.GEO B ly X W regs mem md PRE) as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _). pose proof Usp1 as (U1 & U2 & U3 & U4 & _).
pose proof (YF0p.AQ B TB) as EAQ. unfold o_quar in EAQ.
unfold YF2g.WIN, YF2g.WINF, YF2g.WINA. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (pose proof Usp1; img_lia)).
intros [Y|[[Y|[Y|Y]]|[NE Y]]].
- img_lia.
- rewrite EAQ in Y. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd, DRSTACK in *. img_lia.
- rewrite EAQ in Y. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd, DRSTACK in *. img_lia.
- unfold pb, addr, sp1, LFRAME, DRSTACK, kPrimResvSize, kSpaceSize, kBatchBytes in *. fold sp0 in U3, U4. img_lia.
- destruct (P3a NE) as (lb & ini & _ & EL & L1 & L2 & _). rewrite EL in Y. unfold addr, sp1, LFRAME, DRSTACK, kPrimResvSize, kSpaceSize, kBatchBytes in *. fold sp0 in U3, U4. img_lia.
Qed.
Lemma NW_batch : forall b2 k, In b2 L -> b_self b2 <> b_self b -> (forall lb ini, rev P1 = lb :: ini -> b_self b2 <> b_self lb) ->
0 <= k < kBatchBytes -> ~ WINL (addr b2 + k).
Proof.
intros b2 k Hb2 NEb NEl Hk. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2). pose proof lp_facts as (_ & _ & P3a).
pose proof (YF0p.GEO B ly X W regs mem md PRE) as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _). pose proof Usp1 as (U1 & U2 & U3 & U4 & _).
destruct (batch_facts b2 (proj1 (L_all b2) Hb2)) as (L1 & L2 & _).
pose proof (YF0p.AQ B TB) as EAQ. unfold o_quar in EAQ.
unfold YF2g.WIN, YF2g.WINF, YF2g.WINA. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (pose proof Usp1; img_lia)).
intros [Y|[[Y|[Y|Y]]|[NE Y]]].
- unfold addr, sp1, LFRAME, DRSTACK, kPrimResvSize, kSpaceSize, kBatchBytes in *. fold sp0 in U3, U4. img_lia.
- rewrite EAQ in Y. unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, kLowMemEnd in *. img_lia.
- rewrite EAQ in Y. unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, kLowMemEnd in *. img_lia.
- pose proof (YF0s.batches_apart B ly X _ M _ HSP b2 b (proj1 (L_all _) Hb2) (proj1 (L_all _) InL_b) NEb) as D.
unfold zdisjoint, YF0s.addr in D. cbn [fst snd] in D. unfold pb, addr, kBatchBytes in *. img_lia.
- destruct (P3a NE) as (lb & ini & ER & EL & _ & _ & _ & IN). rewrite EL in Y.
pose proof (YF0s.batches_apart B ly X _ M _ HSP b2 lb (proj1 (L_all _) Hb2) (proj1 (L_all _) (InL_P1 _ IN)) (NEl lb ini ER)) as D.
unfold zdisjoint, YF0s.addr in D. cbn [fst snd] in D. unfold addr, kBatchBytes in *. img_lia.
Qed.
Lemma WINL_dec : forall a, WINL a \/ ~ WINL a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
unfold YF2g.WIN, YF2g.WINF, YF2g.WINA. set (s := bv_unsigned (getr regs' 2)).
destruct (EM s (s + 32)) as [C|C0]; [img_try (left; left; img_exact C)|].
destruct (EM (A_QUAR + 152) (A_QUAR + 156)) as [C|C1]; [img_try (left; right; left; left; img_exact C)|].
destruct (EM (A_QUAR + 160) (A_QUAR + 192)) as [C|C2]; [img_try (left; right; left; right; left; img_exact C)|].
destruct (EM pb (pb + 8)) as [C|C3]; [img_try (left; right; left; right; right; img_exact C)|].
destruct (Z.eq_dec pnp 0) as [Z0|NZ].
- right. intros [X0|[[X1|[X2|X3]]|[X5 _]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (X5 Z0))].
- destruct (EM plp (plp + 8)) as [C|C4]; [img_try (left; right; right; split; [img_exact NZ | img_exact C])|].
right. intros [X0|[[X1|[X2|X3]]|[_ X5]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (C4 X5))].
Qed.
Lemma keep : forall mem'' a (n : nat) v, (forall x : word, ~ WINL (bv_unsigned x) -> mem'' x = mem' x) ->
(forall i, 0 <= i < Z.of_nat n -> ~ WINL (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfxsegs m a n v -> val_mem tfxsegs (mrestrict H0 mem'') a n v.
Proof.
intros mem'' a n v HM Hn Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(img_lia)) as [N1 N2].
img_apply HM. rewrite unsigned_lit_small by img_exact N2. img_exact N1.
Qed.
Lemma DW_mono : forall a, DW P1 a -> DW (P1 ++ [b]) a.
Proof. intros a [Y|[Y|[Y|(b2 & Hb2 & Y)]]]; unfold DW; [img_try (tauto) | img_try (tauto) | img_try (tauto) |]. do 3 right. exists b2. split; [img_try (img_apply in_app_iff; left; img_exact Hb2) | img_try (img_exact Y)]. Qed.
Lemma WINL_DW : forall a, WINL a -> DW (P1 ++ [b]) a.
Proof.
intros a Hw. pose proof lp_facts as (_ & _ & P3a). pose proof Usp1 as U.
unfold YF2g.WIN, YF2g.WINF, YF2g.WINA in Hw. rewrite Q2 in Hw. unfold w64 in Hw. rewrite unsigned_lit_small in Hw by img_lia.
unfold DW. destruct Hw as [Y|[[Y|[Y|Y]]|[NE Y]]].
- left. unfold sp1, LFRAME in *. img_lia.
- right; left. unfold YF2e.WINF. tauto.
- right; left. unfold YF2e.WINF. tauto.
- do 3 right. exists b. split; [img_try (img_apply in_app_iff; right; left; img_refl) | img_try (unfold pb in Y; img_exact Y)].
- destruct (P3a NE) as (lb & ini & ER & EL & _ & _ & _ & IN). do 3 right. exists lb. split; [img_try (img_apply in_app_iff; left; img_exact IN) | img_try (rewrite <- EL; img_exact Y)].
Qed.
Lemma zlen_snoc : zlen (P1 ++ [b]) = pnp + 1.
Proof. unfold pnp, zlen. rewrite length_app. cbn [length]. img_lia. Qed.
Lemma lastaddr_snoc : lastaddr (P1 ++ [b]) = pb.
Proof. unfold lastaddr. rewrite rev_last. img_refl. Qed.
Lemma firstaddr_snoc : firstaddr (P1 ++ [b]) = YF2g.TFIn pb pnp ptfi.
Proof.
unfold YF2g.TFIn, pnp, ptfi, zlen, firstaddr. destruct P1 as [|x t]; cbn [app length Z.of_nat]; [img_refl|].
destruct (Z.eqb_spec (Z.pos (Pos.of_succ_nat (length t))) 0); [img_lia | img_refl].
Qed.
Lemma sum_snoc : sum_bytes (P1 ++ [b]) = ptby + pbs.
Proof. unfold ptby, pbs. rewrite sum_bytes_app, sum_bytes_cons, sum_bytes_nil. img_lia. Qed.
Lemma zlen_R' : zlen R' = pnr - 1.
Proof. unfold pnr, zlen, R. cbn [length]. img_lia. Qed.
Lemma sum_R' : sum_bytes R' = pqb - pbs.
Proof. unfold pqb, pbs, R. rewrite sum_bytes_cons. img_lia. Qed.
Lemma R'_ne : kQuarantineMin < pqb - pbs -> R' <> [].
Proof. rewrite <- sum_R'. intros H E. rewrite E in H. cbn in H. unfold kQuarantineMin in H. img_lia. Qed.
Lemma GLn_cont : R' <> [] -> YF2g.GLn pnx pgl = TLv.
Proof.
intros NE. unfold YF2g.GLn, pgl. destruct (Z.eqb_spec pnx 0) as [E|_]; [|img_refl]. exfalso.
destruct (first_range R' InL_R') as (_ & _ & A3). unfold pnx in E. pose proof (A3 NE). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
Qed.
Lemma GLn_exit : YF2g.GLn pnx pgl = lastaddr R'.
Proof.
unfold YF2g.GLn, pgl, pnx. destruct (Z.eqb_spec (firstaddr R') 0) as [E|NE].
- destruct (first_range R' InL_R') as (_ & _ & A3).
assert (CASES : R' = [] \/ R' <> []) by (img_try (clear; destruct R'; [img_try (left; img_refl) | img_try (right; discriminate)])).
destruct CASES as [E0|NE0]; [img_try (rewrite E0; img_refl)|]. exfalso. pose proof (A3 NE0). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
- assert (RN : R' <> []) by (img_try (intros E; img_apply NE; rewrite E; img_refl)).
destruct (last_range R' InL_R') as (_ & _ & A3). destruct (A3 RN) as (lb & ini & ER & EP & EL & IN). rewrite EL.
unfold YF2e.TLv, addr. pose proof (YF0p.Tq_ne B ly X W regs mem md PRE) as TNE.
assert (EL2 : rev L = lb :: (ini ++ rev (P1 ++ [b]))).
{ unfold L in *. rewrite HL, EP. rewrite !rev_app_distr. cbn [rev app]. rewrite rev_app_distr, rev_involutive, <- !app_assoc. img_refl. }
unfold L in EL2. rewrite rev_app_distr in EL2. destruct (rev Tq) as [|y u] eqn:ERT.
+ exfalso. img_apply TNE. rewrite <- (rev_involutive Tq), ERT. img_refl.
+ cbn [app] in EL2. injection EL2 as -> _. img_refl.
Qed.
Lemma LST_cont : forall W' c', YF2g.at_CONT W regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl W' c' -> LST (P1 ++ [b]) R' W' c'.
Proof.
intros W' c' (-> & HLT & regs2 & mem2 & mat2 & -> & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R5 & R1 & RS & MQ & PRES2 & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C153 & C154 & C160 & C168 & C176 & C184 & Cb & Clp & Ct8 & Ct24).
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & _). pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2).
pose proof ND3 as (D1 & D2 & D3 & D4 & D5). pose proof (R'_ne HLT) as RNE.
split; [img_refl|]. exists regs2, mem2, mat2. split; [img_refl|].
split; [img_try (rewrite R2; img_exact Q2)|]. split; [img_try (img_exact R10)|]. split; [img_try (img_exact R11)|]. split; [img_try (rewrite R12; img_exact Q12)|]. split; [img_try (rewrite R13; img_exact Q13)|].
split; [img_try (rewrite R14, zlen_snoc; img_refl)|]. split; [img_try (rewrite R15, lastaddr_snoc; img_refl)|]. split; [img_try (rewrite R16, zlen_R'; img_refl)|].
split; [img_try (rewrite R5; img_refl)|]. split; [img_try (rewrite R1; img_exact Q1)|]. split; [img_try (intros r Hr; rewrite (RS r Hr); img_apply QS; img_exact Hr)|].
split. { intros x Hx. rewrite (MQ x ltac:(img_try (intros Hw; img_exact (Hx (WINL_DW _ Hw))))). img_apply FRM. intros HD. img_exact (Hx (DW_mono _ HD)). }
split. { intros a Ha. destruct (WINL_dec a) as [Hw|Hw].
- img_apply PRES2; [img_try (img_exact Hw)|]. pose proof HSP as [S1 S2]. fold sp0 in S1, S2. unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *. img_lia.
- pose proof HSP as [S1 S2]. fold sp0 in S1, S2. img_apply (apresent_same H0 mem'); [img_try (img_apply MQ; rewrite unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; img_lia); img_exact Hw) | img_try (img_apply PRS; img_exact Ha)]. }
cbv zeta.
split. { img_apply (proj2 (val_mem4_bytes _ _ _)). img_change (YP0g.le_byte 257 4 0) with 1. img_change (YP0g.le_byte 257 4 1) with 1. img_change (YP0g.le_byte 257 4 2) with 0. img_change (YP0g.le_byte 257 4 3) with 0.
pose proof (proj1 (val_mem1_byte _ _ _) C152) as E0. pose proof (proj1 (val_mem1_byte _ _ _) C153) as E1'.
splits; [img_try (img_exact E0) | img_try (replace (A_QUAR + 152 + 1) with (A_QUAR + 153) by img_lia; img_exact E1') | img_try (img_apply C154; img_lia) | img_try (img_apply C154; img_lia)]. }
split; [img_try (rewrite zlen_R'; img_exact C160)|]. split; [img_try (img_exact C168)|]. split; [img_try (rewrite <- (GLn_cont RNE); img_exact C176)|]. split; [img_try (rewrite sum_R'; img_exact C184)|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ0])|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 8 + i) with (T + t_qc + (8 + i)) by img_lia; img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ8])|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 16 + i) with (T + t_qc + (16 + i)) by img_lia; img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ16])|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 24 + i) with (T + t_qc + (24 + i)) by img_lia; img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ24])|].
split. {
intros LT lb initr Hrev. rewrite length_app in LT. cbn [length] in LT.
destruct (YF0p.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (INlb & _ & L1 & L2 & _).
assert (EG : G = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive G), Hrev; img_refl)).
assert (INR : In lb R').
{ assert (NL : nth_error L (length (rev initr)) = Some lb) by (img_try (unfold L; rewrite EG, <- app_assoc; rewrite nth_error_app2 by img_lia; rewrite Nat.sub_diag; img_refl)).
rewrite HL in NL. rewrite nth_error_app2 in NL by (img_try (rewrite EG, length_app in LT; cbn [length] in LT; img_lia)).
destruct (length (rev initr) - length P1)%nat as [|k] eqn:EK; [img_try (rewrite EG, length_app in LT; cbn [length] in LT; img_lia)|]. cbn [nth_error] in NL. eapply nth_error_In. img_exact NL. }
destruct (batch_facts lb INlb) as (_ & _ & _ & L4 & L5 & _).
img_apply (keep _ _ _ _ MQ); [| img_try (img_exact (VG ltac:(img_lia) lb initr Hrev))]. intros i Hi. split; [img_try (img_apply (NW_batch lb i (proj2 (L_all _) INlb) (D2 _ INR)); [|unfold kBatchBytes; img_lia]) | img_try (ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; img_lia)].
intros lb' ini' ER E. img_apply (D3 lb' lb); [img_try (rewrite <- (rev_involutive P1), ER; cbn; img_apply in_app_iff; right; left; img_refl) | img_try (img_exact INR) | img_try (symmetry; img_exact E)]. }
split. {
intros i b2 Hi. destruct (Nat.lt_ge_cases i (length P1)) as [LT|GE].
- rewrite nth_error_app1 in Hi by img_exact LT. pose proof (nth_error_In _ _ Hi) as IN1.
destruct (Nat.eq_dec (S i) (length P1)) as [LAST|NL].
+
assert (NE0 : pnp <> 0) by (img_try (unfold pnp, zlen; img_lia)). pose proof lp_facts as (_ & _ & P3a). destruct (P3a NE0) as (lb & ini & ER & EL & _ & _ & _ & _).
assert (EP1 : P1 = rev ini ++ [lb]) by (img_try (rewrite <- (rev_involutive P1), ER; img_refl)).
assert (Eb2 : b2 = lb). { rewrite EP1 in Hi. rewrite nth_error_app2 in Hi by (img_try (rewrite EP1, length_app in LAST; cbn [length] in LAST; img_lia)).
replace (i - length (rev ini))%nat with 0%nat in Hi by (img_try (rewrite EP1, length_app in LAST; cbn [length] in LAST; img_lia)). cbn in Hi. congruence. }
(subst b2; cbv beta). unfold next_addr. rewrite nth_error_app2 by img_lia. rewrite <- LAST, Nat.sub_diag. cbn [nth_error]. fold (addr b). fold pb. rewrite <- EL. img_exact (Clp NE0).
+
unfold next_addr. rewrite nth_error_app1 by img_lia. pose proof (VPL i b2 Hi) as V. unfold next_addr in V.
destruct (batch_facts b2 (proj1 (L_all _) (InL_P1 _ IN1))) as (_ & _ & _ & L4 & L5 & _).
img_apply (keep _ _ _ _ MQ); [| img_try (img_exact V)]. intros j Hj. split; [img_try (img_apply (NW_batch b2 j (InL_P1 _ IN1) (D1 _ IN1)); [|unfold kBatchBytes; img_lia]) | img_try (ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; img_lia)].
intros lb ini ER E. assert (EP1 : P1 = rev ini ++ [lb]) by (img_try (rewrite <- (rev_involutive P1), ER; img_refl)).
pose proof D4 as ND. rewrite EP1, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (_ & _ & ND). img_apply (ND (b_self b2)); [|img_try (left; symmetry; img_exact E)].
img_apply in_map. rewrite EP1 in Hi. rewrite nth_error_app1 in Hi by (img_try (rewrite EP1, length_app in NL, LT; cbn [length] in NL, LT; img_lia)). eapply nth_error_In. img_exact Hi.
-
rewrite nth_error_app2 in Hi by img_exact GE. destruct (i - length P1)%nat as [|k] eqn:EK; [|img_try (cbn in Hi; destruct k; discriminate)]. cbn in Hi. injection Hi as <-.
unfold next_addr. rewrite nth_error_app2 by img_lia. replace (S i - length P1)%nat with 1%nat by img_lia. cbn [nth_error]. img_exact Cb. }
split. {
intros i b2 Hi. pose proof (nth_error_In _ _ Hi) as IN2. destruct (VRL (S i) b2 Hi) as [V1 V2].
assert (EN : next_addr ly R (S i) = next_addr ly R' i) by img_refl. rewrite EN in V1.
destruct (batch_facts b2 (proj1 (L_all _) (InL_R' _ IN2))) as (_ & _ & _ & L4 & L5 & _).
assert (NWb : forall j, 0 <= j < 16 -> ~ WINL (addr b2 + j) /\ 0 <= addr b2 + j < 2 ^ 64).
{ intros j Hj. split; [img_try (img_apply (NW_batch b2 j (InL_R' _ IN2) (D2 _ IN2)); [|unfold kBatchBytes; img_lia]) | img_try (ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; img_lia)].
intros lb ini ER E. img_apply (D3 lb b2); [img_try (rewrite <- (rev_involutive P1), ER; cbn; img_apply in_app_iff; right; left; img_refl) | img_try (img_exact IN2) | img_try (symmetry; img_exact E)]. }
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros j Hj; img_apply NWb; img_lia | img_exact V1]) | img_try (img_apply (keep _ _ _ _ MQ); [intros j Hj; replace (addr b2 + 8 + j) with (addr b2 + (8 + j)) by img_lia; img_apply NWb; img_lia | img_exact V2])]. }
split; [img_try (rewrite firstaddr_snoc; rewrite Q2 in Ct8; unfold w64 in Ct8; rewrite unsigned_lit_small in Ct8 by img_lia; img_exact Ct8)|].
split; [img_try (rewrite sum_snoc; rewrite Q2 in Ct24; unfold w64 in Ct24; rewrite unsigned_lit_small in Ct24 by img_lia; img_exact Ct24)|].
assert (KS : forall k v, 32 <= k -> k + 8 <= 80 -> val_mem tfxsegs m (sp1 + k) 8 v -> val_mem tfxsegs (mrestrict H0 mem2) (sp1 + k) 8 v).
{ intros k v Hk1 Hk2 V. img_apply (keep _ _ _ _ MQ); [|img_try (img_exact V)]. intros i Hi. split; [img_try (replace (sp1 + k + i) with (sp1 + (k + i)) by img_lia; img_apply NW_S; img_lia) | img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, DRSTACK, LFRAME, kHighMemBeg, kHighMemEnd in *; img_lia)]. }
splits; (img_apply KS; [img_lia | img_lia | img_try (assumption)]).
Qed.
Lemma LST_exit : forall W' c', YF2g.at_EXIT W regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl W' c' -> ATDR (P1 ++ [b]) R' W' c'.
Proof.
intros W' c' (-> & HLE & regs2 & mem2 & mat2 & -> & R2 & R10 & R11 & R12 & R13 & R1 & RS & MQ & PRES2 & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cb & Clp & Ct0 & Ct8 & Ct16 & Ct24).
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & _). pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _ & hI1 & hI2).
pose proof ND3 as (D1 & D2 & D3 & D4 & D5).
split; [img_refl|]. exists regs2, mem2, mat2. split; [img_refl|].
split; [img_try (rewrite R2; img_exact Q2)|]. split; [img_try (img_exact R10)|]. split; [img_try (rewrite R11; img_exact Q2)|]. split; [img_try (rewrite R12; img_exact Q12)|]. split; [img_try (rewrite R13; img_exact Q13)|].
split; [img_try (img_exact R1)|]. split; [img_try (intros r Hr; rewrite (RS r Hr); img_apply QS; img_exact Hr)|].
split. { intros x Hx. rewrite (MQ x ltac:(img_try (intros Hw; img_exact (Hx (WINL_DW _ Hw))))). img_apply FRM. intros HD. img_exact (Hx (DW_mono _ HD)). }
split. { intros a Ha. destruct (WINL_dec a) as [Hw|Hw].
- img_apply PRES2; [img_try (img_exact Hw)|]. pose proof HSP as [S1 S2]. fold sp0 in S1, S2. unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *. img_lia.
- pose proof HSP as [S1 S2]. fold sp0 in S1, S2. img_apply (apresent_same H0 mem'); [img_try (img_apply MQ; rewrite unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; img_lia); img_exact Hw) | img_try (img_apply PRS; img_exact Ha)]. }
cbv zeta.
split; [img_try (img_exact C152)|].
split; [img_try (rewrite zlen_R'; img_exact C160)|]. split; [img_try (img_exact C168)|]. split; [img_try (rewrite <- GLn_exit; img_exact C176)|]. split; [img_try (rewrite sum_R'; img_exact C184)|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ0])|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 8 + i) with (T + t_qc + (8 + i)) by img_lia; img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ8])|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 16 + i) with (T + t_qc + (16 + i)) by img_lia; img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ16])|].
split; [img_try (img_apply (keep _ _ _ _ MQ); [intros i Hi; split; [replace (T + t_qc + 24 + i) with (T + t_qc + (24 + i)) by img_lia; img_apply NW_T; img_lia | ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia] | img_exact VQ24])|].
split. { intros LT lb initr Hrev. rewrite length_app in LT. cbn [length] in LT.
destruct (YF0p.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (INlb & _ & L1 & L2 & _).
assert (EG : G = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive G), Hrev; img_refl)).
assert (INR : In lb R').
{ assert (NL : nth_error L (length (rev initr)) = Some lb) by (img_try (unfold L; rewrite EG, <- app_assoc; rewrite nth_error_app2 by img_lia; rewrite Nat.sub_diag; img_refl)).
rewrite HL in NL. rewrite nth_error_app2 in NL by (img_try (rewrite EG, length_app in LT; cbn [length] in LT; img_lia)).
destruct (length (rev initr) - length P1)%nat as [|k] eqn:EK; [img_try (rewrite EG, length_app in LT; cbn [length] in LT; img_lia)|]. cbn [nth_error] in NL. eapply nth_error_In. img_exact NL. }
destruct (batch_facts lb INlb) as (_ & _ & _ & L4 & L5 & _).
img_apply (keep _ _ _ _ MQ); [| img_try (img_exact (VG ltac:(img_lia) lb initr Hrev))]. intros i Hi. split; [img_try (img_apply (NW_batch lb i (proj2 (L_all _) INlb) (D2 _ INR)); [|unfold kBatchBytes; img_lia]) | img_try (ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; img_lia)].
intros lb' ini' ER E. img_apply (D3 lb' lb); [img_try (rewrite <- (rev_involutive P1), ER; cbn; img_apply in_app_iff; right; left; img_refl) | img_try (img_exact INR) | img_try (symmetry; img_exact E)]. }
split. { intros i b2 Hi. destruct (Nat.lt_ge_cases i (length P1)) as [LT|GE].
- rewrite nth_error_app1 in Hi by img_exact LT. pose proof (nth_error_In _ _ Hi) as IN1.
destruct (Nat.eq_dec (S i) (length P1)) as [LAST|NL].
+ assert (NE0 : pnp <> 0) by (img_try (unfold pnp, zlen; img_lia)). pose proof lp_facts as (_ & _ & P3a). destruct (P3a NE0) as (lb & ini & ER & EL & _ & _ & _ & _).
assert (EP1 : P1 = rev ini ++ [lb]) by (img_try (rewrite <- (rev_involutive P1), ER; img_refl)).
assert (Eb2 : b2 = lb). { rewrite EP1 in Hi. rewrite nth_error_app2 in Hi by (img_try (rewrite EP1, length_app in LAST; cbn [length] in LAST; img_lia)).
replace (i - length (rev ini))%nat with 0%nat in Hi by (img_try (rewrite EP1, length_app in LAST; cbn [length] in LAST; img_lia)). cbn in Hi. congruence. }
(subst b2; cbv beta). unfold next_addr. rewrite nth_error_app2 by img_lia. rewrite <- LAST, Nat.sub_diag. cbn [nth_error]. fold (addr b). fold pb. rewrite <- EL. img_exact (Clp NE0).
+ unfold next_addr. rewrite nth_error_app1 by img_lia. pose proof (VPL i b2 Hi) as V. unfold next_addr in V.
destruct (batch_facts b2 (proj1 (L_all _) (InL_P1 _ IN1))) as (_ & _ & _ & L4 & L5 & _).
img_apply (keep _ _ _ _ MQ); [| img_try (img_exact V)]. intros j Hj. split; [img_try (img_apply (NW_batch b2 j (InL_P1 _ IN1) (D1 _ IN1)); [|unfold kBatchBytes; img_lia]) | img_try (ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; img_lia)].
intros lb ini ER E. assert (EP1 : P1 = rev ini ++ [lb]) by (img_try (rewrite <- (rev_involutive P1), ER; img_refl)).
pose proof D4 as ND. rewrite EP1, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (_ & _ & ND). img_apply (ND (b_self b2)); [|img_try (left; symmetry; img_exact E)].
img_apply in_map. rewrite EP1 in Hi. rewrite nth_error_app1 in Hi by (img_try (rewrite EP1, length_app in NL, LT; cbn [length] in NL, LT; img_lia)). eapply nth_error_In. img_exact Hi.
- rewrite nth_error_app2 in Hi by img_exact GE. destruct (i - length P1)%nat as [|k] eqn:EK; [|img_try (cbn in Hi; destruct k; discriminate)]. cbn in Hi. injection Hi as <-.
unfold next_addr. rewrite nth_error_app2 by img_lia. replace (S i - length P1)%nat with 1%nat by img_lia. cbn [nth_error]. img_exact Cb. }
rewrite Q2 in Ct0, Ct8, Ct16, Ct24. unfold w64 in Ct0, Ct8, Ct16, Ct24. rewrite unsigned_lit_small in Ct0, Ct8, Ct16, Ct24 by img_lia.
split; [img_try (rewrite zlen_snoc; img_exact Ct0)|]. split; [img_try (rewrite firstaddr_snoc; img_exact Ct8)|]. split; [img_try (rewrite lastaddr_snoc; img_exact Ct16)|]. split; [img_try (rewrite sum_snoc; img_exact Ct24)|].
assert (KS : forall k v, 32 <= k -> k + 8 <= 80 -> val_mem tfxsegs m (sp1 + k) 8 v -> val_mem tfxsegs (mrestrict H0 mem2) (sp1 + k) 8 v).
{ intros k v Hk1 Hk2 V. img_apply (keep _ _ _ _ MQ); [|img_try (img_exact V)]. intros i Hi. split; [img_try (replace (sp1 + k + i) with (sp1 + (k + i)) by img_lia; img_apply NW_S; img_lia) | img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, DRSTACK, LFRAME, kHighMemBeg, kHighMemEnd in *; img_lia)]. }
splits; (img_apply KS; [img_lia | img_lia | img_try (assumption)]).
Qed.
Theorem ITER_step :
SRr tfxsegs W (mkCfg (mkst regs' (w64 (0x337d0 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => if kQuarantineMin <? pqb - pbs then LST (P1 ++ [b]) R' W' c' else ATDR (P1 ++ [b]) R' W' c').
Proof.
eapply SRr_mono; [img_try (img_exact (YF2v.segL W ly regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl mat FHL_ok))|].
intros W' c' _ HP. unfold YF2g.postL in HP. destruct (kQuarantineMin <? pqb - pbs); [img_try (img_exact (LST_cont W' c' HP)) | img_try (img_exact (LST_exit W' c' HP))].
Qed.
End e.
Lemma pop_step : forall f b R' s acc, kQuarantineMin < s ->
pop_batches (S f) (mkQC (b :: R') s) acc = pop_batches f (mkQC R' (s - b_bytes b)) (b :: acc).
Proof. intros f b R' s acc H. cbn [pop_batches qc_bytes qc_list]. destruct (Z.leb_spec s kQuarantineMin); [img_lia | img_refl]. Qed.
Lemma pop_stop : forall f R' s acc, s <= kQuarantineMin -> pop_batches f (mkQC R' s) acc = (mkQC R' s, rev acc).
Proof. intros f R' s acc H. destruct f; cbn [pop_batches qc_bytes qc_list]; [img_refl|]. destruct (Z.leb_spec s kQuarantineMin); [img_refl | img_lia]. Qed.
Theorem LOOP : forall R P1 fuel W' c',
LST P1 R W' c' -> L = P1 ++ R -> kQuarantineMin < sum_bytes R -> (length R < fuel)%nat ->
SRr tfxsegs W' c' (fun W'' c'' => let gp := pop_batches fuel (mkQC R (sum_bytes R)) (rev P1) in ATDR (snd gp) (qc_list (fst gp)) W'' c'').
Proof.
induction R as [|b R' IH]; intros P1 fuel W' c' HLST HL HGT Hfuel.
- exfalso. cbn in HGT. unfold kQuarantineMin in HGT. img_lia.
- destruct fuel as [|f]; [img_try (cbn in Hfuel; img_lia)|]. rewrite (pop_step f b R' _ _ HGT).
pose proof PRE as PRE'. destruct PRE' as (_ & _ & _ & Hra & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
destruct HLST as (-> & regs' & mem' & mat & -> & Q2 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q5 & Q1 & QS & FRM & PRS & CELLS).
cbv zeta in CELLS. destruct CELLS as (VQW & VQS & VQF & VQL & VQB & VQ0 & VQ8 & VQ16 & VQ24 & VG & VPL & VRL & VT8 & VT24 & VS32 & VS40 & VS48 & VS56 & VS64 & VS72).
assert (Q4 : getr regs' 4 = w64 TFX_TP) by (img_try (rewrite (QS 4%bv ltac:(cbn; tauto)); img_exact Htp)).
pose proof (ITER_step P1 R' b regs' mem' mat HL Q2 Q10 Q11 Q12 Q14 Q15 Q16 Q5 Q1 QS FRM PRS VQW VQS VQF VQL VQB VRL VPL VT8 VT24 Q13 VQ0 VQ8 VQ16 VQ24 VG VS32 VS40 VS48 VS56 VS64 VS72 Q4 Hra) as STEP.
unfold pqb, pbs in STEP. rewrite sum_bytes_cons in STEP |- *. replace (b_bytes b + sum_bytes R' - b_bytes b) with (sum_bytes R') in STEP |- * by img_lia.
destruct (Z.ltb_spec kQuarantineMin (sum_bytes R')) as [GT|LE].
+
eapply SRr_bind; [img_try (img_exact STEP)|]. intros W2 c2 _ HL2. cbn beta in HL2.
pose proof (IH (P1 ++ [b]) f W2 c2 HL2 ltac:(img_try (rewrite <- app_assoc; img_exact HL)) GT ltac:(img_try (cbn in Hfuel; img_lia))) as K.
rewrite rev_last in K. img_exact K.
+
rewrite (pop_stop f R' _ _ LE). cbn [fst snd qc_list rev]. rewrite rev_involutive. img_exact STEP.
Qed.
End d.
End c.
