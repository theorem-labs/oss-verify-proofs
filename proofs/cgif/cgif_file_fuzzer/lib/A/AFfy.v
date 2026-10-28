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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG02 YG06 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AFgi AFfv AFga AFgc AFge.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB13 AFex.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma amreal_ask_depot {R} : forall trc s (k : Z -> itree astate R) (Wx : world tfibsegs) c Q,
SRr tfibsegs Wx c (fun W1 c1 => exists z, aok s (KDepot trc) z /\ amreal tfibsegs (k z) W1 c1 Q) ->
amreal tfibsegs (IAsk (KDepot trc) s k) Wx c Q.
Proof. intros trc s k Wx c Q H. exact H. Qed.
Lemma match_nonnull {A} : forall (q : sptr) (a b : A), q <> PNull -> match q with PNull => a | _ => b end = b.
Proof. intros q a b H. destruct q; [congruence | reflexivity | reflexivity | reflexivity]. Qed.
Ltac inlist := cbn [In]; repeat (first [ left; reflexivity | right ]); fail.
Section f.
Variable B : asyms.
Lemma depot_mem_ok_agree : forall ly S S' rd rd',
Wf (as_universe B) S -> universe_ok (as_universe B) -> st_depot S' = st_depot S ->
(forall a, depot_footprint B ly a -> rd' a = rd a) -> depot_mem_ok B ly S rd -> depot_mem_ok B ly S' rd'.
Proof.
intros ly S S' rd rd' W HU HD AG (DC & DO & DV).
assert (NB : depot_ids S <= 4097).
{ unfold depot_ids. pose proof (wf_depot _ _ _ _ _ W) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct HU as (U1 & _). unfold DEPOT_MAX in U1. lia. }
assert (ED : depot_cells ly S' = depot_cells ly S) by (unfold depot_cells, depot_ids, depot_frames; rewrite HD; reflexivity).
split; [|split].
- rewrite ED. apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) DC c Hc)|].
intros k Hk. apply AG. unfold depot_cells in Hc. cbn [In] in Hc. unfold depot_footprint, d_map1, d_nuniq, s_total, s_block0, kNodesBlockSize, kStoreBlockSize in *.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hk |- *; lia.
- destruct DO as (heads & links & D1 & D2 & D3). exists heads, links. unfold depot_ids, depot_traces in *. rewrite HD. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. rewrite AG; [exact (H2 k Hk)|].
unfold depot_footprint, d_tab_words, d_map1 in *. left. lia.
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
split; intros k Hk; rewrite AG; auto; unfold depot_footprint, kNodesBlockSize; right; left; lia.
- apply Forall_forall. intros r Hr i Hi. rewrite AG; [exact (proj1 (Forall_forall _ _) DV r Hr i Hi)|].
cbn [In] in Hr. unfold depot_footprint, d_map1, d_nuniq, kNodesBlockSize, kStoreBlockSize in *.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in Hi |- *; lia.
Qed.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly 0x52a6c regs ch.
Let sp0 : Z := bv_unsigned (getr regs 2).
Let pa : Z := sptr_addr B ly p.
Let nn : Z := req_size n.
Hypothesis PRE : acall_pre tfibsegs B ly S W regs mem md ch.
Hypothesis HBLK : In (p, n) (blocks S).
Hypothesis HA0 : getr regs 10 = w64 pa.
Hypothesis HU : In tr (as_universe B).
Variables (lastb : batch) (initr : list batch).
Hypothesis ARM : rev (qc_list (st_qthread S)) = lastb :: initr /\ Z.of_nat (length (b_items lastb)) < kBatchSlots /\
qc_bytes (st_qthread S) + nn <= kQuarantineCacheMax.
Hypothesis IA1 : tfib_ialloc_spec.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (hb1 j1 j2 j3 : Z).
Hypothesis FH : free_hyps W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S).
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Lemma s1_wf : Wf (as_universe B) s1.
Proof.
destruct PRE as ((M & _ & _) & Hev & _).
apply (WfP_weaken _ 1 1 1); try lia. unfold s1. apply WfP_set_internal_inited. apply WfP_tick; [exact (am_wf B ly S _ M) | exact Hev].
Qed.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Definition low_ok (a w : Z) : bool :=
(TFIB_IMG_LO <=? a) && ((a + w <=? TFIB_IAL_LO) || (TFIB_IAL_HI <=? a) && (a + w <=? TFIB_IAL_FLAG) || (TFIB_IAL_FLAG + 4 <=? a) && (a + w <=? TFIB_IMG_END)
|| (SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_ok (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_ok a w
| AT k => (0 <=? k) && (k + w <=? 80)
| AC k => (0 <=? k) && (k + w <=? 256)
| ATsd k => low_ok (TFIB_TSD + k) w
| ATp k => low_ok (TFIB_TP + k) w
| AInst k => low_ok (TFIB_INST + k) w
| AD k => (0 <=? k) && (k + w <=? 4096)
| _ => false
end.
Lemma Tfib_const_loc : forallb const_loc_ok (Tfib_const ly) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ AFgi.WIN ly regs pa lastb (aeval B ly (c_at c) + i) /\ ~ AFgi.IZONE (aeval B ly (c_at c) + i) /\
0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_loc c Hc) as K. unfold const_loc_ok in K.
assert (LOW : forall a, low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ AFgi.WIN ly regs pa lastb (a + i) /\ ~ AFgi.IZONE (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/ (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
(SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
clear L. unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *.
change (65536 / 8) with 8192 in R. change (6270976 / 8) with 783872 in R.
split; [|lia]. destruct R as [R|[R|[R|R]]].
1-3: apply (AFgi.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia.
apply (AFgi.notWIN_shb W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold kLowShadowBeg, kHighMemBeg; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- pose proof (AFgi.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [apply (AFgi.notWIN_Thead W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); lia|].
unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- pose proof (AFgi.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & _ & _ & _ & _ & LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [apply (AFgi.notWIN_C W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); lia|].
unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof (AFgi.LYBD W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (HD1 & HD2 & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HD1, HD2.
split; [apply (AFgi.notWIN_D W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); lia|].
unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.
Lemma DFP_RANGE : forall a, depot_footprint B ly a -> 0 <= a < 2 ^ 64.
Proof.
destruct PRE as ((M & _) & _). pose proof (AFgi.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as LB.
intros a Ha. unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha.
ceil; unfold zone3, TFIB_DEPOT, TFIB_STORE, d_map1, kHighMemBeg, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *. lia.
Qed.
Lemma DFP_OUT : forall a, depot_footprint B ly a -> ~ AFgi.WIN ly regs pa lastb a /\ ~ AFgi.IZONE a /\ AFgi.DZONE ly a.
Proof.
pose proof (AFgi.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as LB.
intros a Ha. unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha. unfold AFgi.IZONE, AFgi.DZONE.
pose proof LB as (_ & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _). unfold zone3, zone3cases in ZNB, ZSB.
ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, d_map1, kHighMemBeg, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *.
destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- split; [apply (AFgi.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia | lia].
- split; [apply (AFgi.notWIN_NB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold kNodesBlockSize; lia | lia].
- split; [apply (AFgi.notWIN_SB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold kStoreBlockSize; lia | lia].
- split; [apply (AFgi.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia | lia].
Qed.
Lemma CONST_ZONE : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ (AFgi.SPv pa <= aeval B ly (c_at c) + i < AFgi.SPv pa + AFgi.CNT8v nn)) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_loc c Hc) as K. unfold const_loc_ok in K.
pose proof (AFgi.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (ZT & _ & _ & _ & _ & _ & ZC & _).
pose proof (AFgi.LYBD W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (ZD & _).
pose proof (AFgi.derived_ranges W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & SH1 & SH2 & SH3 & P8 & N81 & N82 & N83 & _).
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (_ & _ & ZP).
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, AFgi.N8v in ZT, ZC, ZD, ZP.
unfold AFgi.CNT8v, AFgi.N8v in *. rewrite SH3 in *. ceil. unfold ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *.
assert (LOW : forall a, low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ (2147450880 + pa / 8 <= a + i < 2147450880 + pa / 8 + (nn + 7) / 8 * 8 / 8)).
{ intros a L. unfold low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/ (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
(SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
clear L K. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in R. change (65536 / 8) with 8192 in R. change (6270976 / 8) with 783872 in R.
assert (R' : (65536 <= a /\ a + w <= 6270976) \/ (2147450880 + 8192 <= a /\ a + w <= 2147450880 + 783872)) by (clear - R; lia). clear R. rename R' into R.
rewrite Z_div_mult in * by lia. pose proof (Z.div_pos pa 8 ltac:(lia) ltac:(lia)).
destruct R as [R|R]; [lia|].
destruct ZP as [Z1|[Z2|Z3]].
- assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 65536 / 8) by (apply Z.div_le_mono; lia). rewrite Z.div_add in Y by lia. change (65536 / 8) with 8192 in Y. lia.
- assert (Y : 6270976 / 8 <= pa / 8) by (apply Z.div_le_mono; lia). change (6270976 / 8) with 783872 in Y. lia.
- assert (Y : 17594333495296 / 8 <= pa / 8) by (apply Z.div_le_mono; lia). change (17594333495296 / 8) with 2199291686912 in Y. lia. }
rewrite Z_div_mult in * by lia. pose proof (Z.div_pos pa 8 ltac:(lia) ltac:(lia)).
destruct (c_at c); try discriminate K; cbn [aeval]; try (apply LOW, K).
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia). rewrite Z.div_add in Y by lia. change (140737479966720 / 8) with 17592184995840 in Y. lia.
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia). rewrite Z.div_add in Y by lia. change (140737479966720 / 8) with 17592184995840 in Y. lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia). rewrite Z.div_add in Y by lia. change (140737479966720 / 8) with 17592184995840 in Y. lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Definition fin_hyp : Prop := forall z k (msD : machine_state) mem4 W' c',
find_user (st_chunks S) p = Some k ->
aok s1 (KDepot tr) z ->
MEQI W ly regs mem pa lastb (ms_mem msD) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msD) a) ->
(forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ depot_footprint B ly (bv_unsigned x) -> mem4 x = ms_mem msD x) ->
(forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) mem4 a) ->
depot_mem_ok B ly (depot_after z tr s1) (aview tfibsegs (w_H W) mem4) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem4)) (as_const B ly) ->
AFge.at_RET W ly regs md pa nn hb1 (st_qthread S) lastb mem4 W' c' ->
let k' := {| ck_beg := ck_beg k; ck_req := ck_req k; ck_state := CQuarantined |} in
let sd := depot_after z tr s1 in
free_leaf tfibsegs B ly S W regs mem md p n (tt, set_qthread (qc_push (st_qthread S) k' None) (set_chunks (upd_chunk (st_chunks sd) k') sd)) W' c'.
Lemma FINH : fin_hyp.
Proof.
intros z k msD mem4 W' c' Hf AOK MEQD PRESD Hfr4 Hpr4 DEPOK HC4 HR.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M & LED & BUD & MW & HSH).
pose proof (find_user_block _ 0 0 0 S p n (am_wf B ly S _ M) HBLK) as (k0 & Hf0 & Hk & Hst & Hu & Hr). rewrite Hf in Hf0. injection Hf0 as <-.
destruct ARM as (Hrev & Hroom & Hcache).
destruct HR as (-> & regs' & mem' & mat & -> & CS & EQS4 & PRES' & PRESW & VALS).
pose proof (fh_Hhb1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HB1. pose proof (fh_Hhb1m _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HB1M. unfold AFgi.HB1MASK in HB1M.
cbv zeta. set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Epa : pa = sptr_addr B ly (ck_user k)) by (unfold pa; rewrite Hu; reflexivity).
assert (Enn : nn = ck_n k) by (unfold nn, ck_n; rewrite Hr; reflexivity).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (AFex.ext_rounded B ly S rd M k lastb Hk) as (ER & NN1 & NN2 & NN3).
assert (HSP : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly) by (unfold spZ in *; unfold sp0; lia).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFex.D B ly k lastb sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same.
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
unfold AFex.D, AFex.DT, AFex.DK, AFex.DB, AFex.DS, AFex.DI, AFex.DH in ND. rewrite <- Epa, <- Enn in ND.
assert (NW : ~ AFgi.WIN ly regs pa lastb a).
{ intros X. apply ND. clear ND. unfold AFgi.WIN, AFgi.WINT, AFgi.WINB, AFgi.Bv, AFgi.SLOTv, AFgi.BCv, AFgi.Bv in X. fold sp0 in X.
destruct X as [X|[X|X]]; [do 3 right; left; exact X | left; clear - X; unfold AFex.DT; lia | right].
destruct X as [X|[X|[X|X]]]; [left; left; exact X | left; right; exact X | right; left; left; exact X | right; left; right; exact X]. }
rewrite (proj1 EQS4 (Z_to_bv 64 a)); rewrite ?Ux.
2:{ intros X. apply NW. exact (AFgi.WIN2_WIN ly regs pa lastb a X). }
2:{ intros X. apply ND. do 6 right. clear - X NN2. unfold AFgi.SPv, AFgi.CNT8v, AFgi.N8v, shadow_addr in *. rewrite Z_div_mult in X by lia. lia. }
rewrite Hfr4; rewrite ?Ux.
2:{ intros X. apply ND. do 3 right; left. clear - X. unfold AFex.DS, DEP_STK, ASTACK in *. lia. }
2:{ intros X. apply ND. do 5 right; left; exact X. }
apply (proj1 MEQD); rewrite ?Ux; [exact NW|].
intros X. apply ND. do 4 right; left. unfold AFgi.IZONE in X. unfold AFex.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). exact X. }
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (NIMG : ~ (0x10000 <= a' < 0x5fb000)).
{ intros X. apply (tfib_rom_all a' X). rewrite Ex. exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
destruct (EM (AFgi.SPv pa) (AFgi.SPv pa + AFgi.CNT8v nn) a') as [C1|C1].
{ rewrite (proj2 EQS4 x C1) in E'. discriminate. }
assert (EMW : AFgi.WIN ly regs pa lastb a' \/ ~ AFgi.WIN ly regs pa lastb a').
{ unfold AFgi.WIN, AFgi.WINT, AFgi.WINB. clear - EM.
repeat match goal with |- (?A \/ ?Bq) \/ ~ _ => first [ destruct (EM _ _ a' : A \/ ~ A) as [?|?]; [left; left; assumption|] | idtac ];
cut ((Bq) \/ ~ (Bq)); [tauto|] end. apply EM. }
destruct EMW as [C2|C2].
{ unfold AFgi.WIN in C2. destruct C2 as [C2|C2]; [apply (PRX mem' (PRES' a' C2) E') | apply (PRX mem' (PRESW a' C2) E')]. }
assert (E4 : mem4 x = None).
{ rewrite <- E'. symmetry. apply (proj1 EQS4 x); [intros X; apply C2; exact (AFgi.WIN2_WIN ly regs pa lastb a' X) | exact C1]. }
assert (EMD : depot_footprint B ly a' \/ ~ depot_footprint B ly a') by (unfold depot_footprint; clear - EM;
destruct (EM (as_depot B) (as_depot B + d_map1 + 8 * 32768) a'); [tauto|]; destruct (EM (ly_NB ly) (ly_NB ly + kNodesBlockSize) a'); [tauto|];
destruct (EM (ly_SB ly) (ly_SB ly + kStoreBlockSize) a'); [tauto|]; destruct (EM (as_store B) (as_store B + 64) a'); tauto).
destruct EMD as [C3|C3].
{ destruct DEPOK as (_ & _ & DV). rewrite Forall_forall in DV.
assert (BLK : forall e len, In (e, len) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] ->
aeval B ly e <= a' < aeval B ly e + len -> False).
{ intros e len Hin Hrg. pose proof (DV _ Hin (a' - aeval B ly e) ltac:(cbn [fst snd]; lia)) as V. cbn [fst snd] in V.
replace (aeval B ly e + (a' - aeval B ly e)) with a' in V by lia. apply V. unfold aview, mbyte, mrestrict. rewrite Ex, Hx, E4, ROM. reflexivity. }
unfold depot_footprint in C3. rewrite (ts_depot _ TB), (ts_store _ TB) in C3. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in C3.
destruct C3 as [C3|[C3|[C3|C3]]].
- apply NIMG. lia.
- apply (BLK (ANB 0) kNodesBlockSize); [cbn; tauto | cbn [aeval]; lia].
- apply (BLK (ASB 0) kStoreBlockSize); [cbn; tauto | cbn [aeval]; lia].
- apply NIMG. lia. }
assert (ED : ms_mem msD x = None).
{ rewrite <- E4. symmetry. apply Hfr4; [|exact C3]. intros X. apply C2. unfold AFgi.WIN. left. clear - X. unfold DEP_STK, ASTACK in *. subst a'. fold sp0. lia. }
destruct (EM TFIB_IAL_LO TFIB_IAL_HI a') as [C4|C4]; [apply NIMG; unfold TFIB_IAL_LO, TFIB_IAL_HI in C4; lia|].
destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a') as [C5|C5]; [apply NIMG; unfold TFIB_IAL_FLAG in C5; lia|].
rewrite (proj1 MEQD x) in ED; [congruence | exact C2 | unfold AFgi.IZONE; tauto]. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
assert (ROM : seg_rom tfibsegs x = None) by (subst x; apply seg_rom_none_high; clear - Ha; unfold TFIB_IMG_END, kLowShadowBeg, kHighShadowEnd in *; lia).
assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate).
assert (C1 : ~ (AFgi.SPv pa <= a < AFgi.SPv pa + AFgi.CNT8v nn)).
{ intros C1. exact (PRX mem (fh_Hsh_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH a C1)). }
assert (C2 : ~ AFgi.WIN ly regs pa lastb a).
{ intros C2. unfold AFgi.WIN in C2. destruct C2 as [C2|C2]; [exact (PRX mem' (PRES' a C2)) | exact (PRX mem' (PRESW a C2))]. }
assert (C3 : ~ depot_footprint B ly a).
{ intros C3. destruct DEPOK as (_ & _ & DV). rewrite Forall_forall in DV.
assert (BLK : forall e len, In (e, len) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] ->
aeval B ly e <= a < aeval B ly e + len -> False).
{ intros e len Hin Hrg. pose proof (DV _ Hin (a - aeval B ly e) ltac:(cbn [fst snd]; lia)) as V. cbn [fst snd] in V.
replace (aeval B ly e + (a - aeval B ly e)) with a in V by lia. apply V. unfold aview, mbyte, mrestrict. fold x. rewrite ROM, Hx. reflexivity. }
unfold depot_footprint in C3. rewrite (ts_depot _ TB), (ts_store _ TB) in C3. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in C3.
destruct C3 as [C3|[C3|[C3|C3]]].
- clear - C3 Ha. unfold kLowShadowBeg in Ha. lia.
- apply (BLK (ANB 0) kNodesBlockSize); [cbn; tauto | cbn [aeval]; lia].
- apply (BLK (ASB 0) kStoreBlockSize); [cbn; tauto | cbn [aeval]; lia].
- clear - C3 Ha. unfold kLowShadowBeg in Ha. lia. }
rewrite (proj1 EQS4 x); rewrite ?Ux; [| intros X; apply C2; exact (AFgi.WIN2_WIN ly regs pa lastb a X) | exact C1].
rewrite Hfr4; rewrite ?Ux; [| intros X; apply (PRX (ms_mem msD)); apply PRESD; clear - X; unfold DEP_STK, ASTACK in *; fold sp0; lia | exact C3].
apply (proj1 MEQD x); rewrite ?Ux; [exact C2|].
unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia. }
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i)).
{ intros i Hi. subst rd'. rewrite <- Epa. exact (val_mem_aview _ _ _ _ _ i V1 Hi). }
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 12 + Z.of_nat i) = Some (YG0f.le_byte (ck_n k) 4 i)).
{ intros i Hi. subst rd'. rewrite <- Epa, <- Enn. exact (val_mem_aview _ _ _ _ _ i V2 Hi). }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (qc_list (st_qthread S)))) 8 i)).
{ intros i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i V3 Hi). }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 8 + Z.of_nat i) =
Some (YG0f.le_byte (match qc_list (st_qthread S) with [] => 0 | b0 :: _ => ly_space ly + b_self b0 end) 8 i)).
{ intros i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i V4 Hi). }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte (ly_space ly + b_self lastb) 8 i)).
{ intros i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i V5 Hi). }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes (st_qthread S) + ck_n k) 8 i)).
{ intros i Hi. subst rd'. rewrite <- Enn. exact (val_mem_aview _ _ _ _ _ i V6 Hi). }
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (val_mem_aview _ _ _ _ _ 0 V7 ltac:(lia)). }
assert (NEW_bb : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 8 + Z.of_nat i) = Some (YG0f.le_byte (b_bytes lastb + ck_n k) 8 i)).
{ intros i Hi. subst rd'. rewrite <- Enn. exact (val_mem_aview _ _ _ _ _ i V8 Hi). }
assert (NEW_bc : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 16 + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (b_items lastb)) + 1) 8 i)).
{ intros i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i V9 Hi). }
assert (NEW_slot : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 24 + 8 * Z.of_nat (length (b_items lastb)) + Z.of_nat i) =
Some (YG0f.le_byte (sptr_addr B ly (ck_user k) - 16) 8 i)).
{ intros i Hi. subst rd'. rewrite <- Epa. exact (val_mem_aview _ _ _ _ _ i V10 Hi). }
assert (NEW_sh : forall a, AFex.DH B ly k a -> rd a <> None -> rd' a = Some shHeapFreed).
{ intros a Hd Hv. subst rd rd'. unfold AFex.DH in Hd. rewrite <- Epa, <- Enn in Hd.
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HP. unfold AFgi.N8v in HP.
assert (Ha : 0 <= a < 2 ^ 64).
{ clear - Hd HP NN2 NN3 Enn. rewrite <- Enn in *. ceil; unfold zone3, shadow_addr, SHADOW_OFF, kHighMemBeg, ASAN_CEIL in *.
pose proof (Z.div_pos pa 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound pa 8 pa ltac:(lia) ltac:(lia)). lia. }
unfold aview, mbyte, mrestrict in Hv |- *.
assert (ROM : seg_rom tfibsegs (Z_to_bv 64 a) = None).
{ apply seg_rom_none_high. unfold TFIB_IMG_END. unfold shadow_addr, SHADOW_OFF in Hd. pose proof (Z.div_pos pa 8 ltac:(unfold zone3 in HP; lia) ltac:(lia)). lia. }
destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; [rewrite ROM in Hv; exfalso; exact (Hv eq_refl)|].
rewrite (proj2 EQS4 (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha.
unfold AFgi.SPv, AFgi.CNT8v, AFgi.N8v. unfold shadow_addr in Hd. rewrite Z_div_mult by lia. exact Hd. }
assert (AGI : forall a, AFgi.IZONE a -> mem' (Z_to_bv 64 a) = ms_mem msD (Z_to_bv 64 a)).
{ intros a Hz. assert (Ha : 0 <= a < 2 ^ 64) by (unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Hz; lia).
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HP.
assert (NW : ~ AFgi.WIN ly regs pa lastb a).
{ apply (AFgi.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH).
clear - Hz. unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *. lia. }
rewrite (proj1 EQS4 (Z_to_bv 64 a)); rewrite ?unsigned_lit_small by exact Ha.
2:{ intros X. apply NW. exact (AFgi.WIN2_WIN ly regs pa lastb a X). }
2:{ clear - Hz HP. unfold zone3, AFgi.IZONE, AFgi.SPv, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, kHighMemBeg, SHADOW_OFF in *.
pose proof (Z.div_pos pa 8 ltac:(lia) ltac:(lia)) as X. lia. }
apply Hfr4; rewrite ?unsigned_lit_small by exact Ha.
- pose proof (lo_top ly (am_layout B ly S _ M)) as (_ & _ & _ & _ & _ & _ & T7). clear - Hz HSP T7.
unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, kHighMemBeg, ASTACK, DEP_STK in *. lia.
- intros X. destruct (DFP_OUT a X) as (_ & NI & _). exact (NI Hz). }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (AFex.S' S k z tr)) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ destruct MEQD as [_ IP]. unfold AFgi.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
assert (XF : forall a0 (w : nat) v, AFgi.IZONE a0 -> (forall kk, (kk < w)%nat -> AFgi.IZONE (a0 + Z.of_nat kk)) ->
val_mem tfibsegs (mrestrict (w_H W) (ms_mem msD)) a0 w v -> val_mem tfibsegs (mrestrict (w_H W) mem') a0 w v).
{ intros a0 w v _ Hz Hv. eapply val_mem_frame; [|exact Hv]. intros kk Hkk. apply AGI, Hz, Hkk. }
unfold ialloc_cells, ialloc_zero. rewrite (AFex.S'_inited S k z tr), (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
assert (ZF : AFgi.IZONE TFIB_IAL_FLAG /\ AFgi.IZONE (TFIB_IAL_FLAG + 1) /\ (forall kk, (kk < 8)%nat -> AFgi.IZONE (TFIB_IAL_W + Z.of_nat kk)) /\
(forall kk, (kk < 8)%nat -> AFgi.IZONE (TFIB_IAL_W + 8 + Z.of_nat kk))).
{ unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W. splits; intros; lia. }
destruct ZF as (Z1 & Z2 & Z3 & Z4). subst rd'. split.
- apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia].
assert (ZZ : forall kk : nat, (kk < 1)%nat -> AFgi.IZONE (TFIB_IAL_FLAG + Z.of_nat kk)) by (intros [|] ?; [rewrite Z.add_0_r; exact Z1 | exfalso; lia]).
apply (val_mem_aview _ _ _ _ _ 0 (XF _ _ _ Z1 ZZ I1)). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia].
assert (ZZ : forall kk : nat, (kk < 1)%nat -> AFgi.IZONE (TFIB_IAL_FLAG + 1 + Z.of_nat kk)) by (intros [|] ?; [rewrite Z.add_0_r; exact Z2 | exfalso; lia]).
apply (val_mem_aview _ _ _ _ _ 0 (XF _ _ _ Z2 ZZ I2)). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
intros kk Hkk. exact (val_mem_aview _ _ _ _ _ kk (XF _ _ _ (Z3 0%nat ltac:(lia)) Z3 I3) Hkk). }
apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
intros kk Hkk. exact (val_mem_aview _ _ _ _ _ kk (XF _ _ _ (Z4 0%nat ltac:(lia)) Z4 I4) Hkk). }
- assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> aview tfibsegs (w_H W) mem' a0 = Some 0).
{ intros a0 Ha0. unfold aview. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msD) mem' a0).
- rewrite (I5 a0 Ha0). reflexivity.
- apply AGI. unfold AFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TB); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia. }
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HP. unfold AFgi.N8v in HP.
assert (SHB : kLowShadowBeg <= AFgi.SPv pa /\ AFgi.SPv pa + AFgi.CNT8v nn <= kHighMemBeg).
{ unfold AFgi.SPv, AFgi.CNT8v, AFgi.N8v. rewrite Z_div_mult by lia. unfold zone3 in HP.
pose proof (AFex.hs_bounds lastb pa ltac:(lia) ltac:(ceil; unfold kHighMemEnd, ASAN_CEIL in *; lia)) as [X1 _].
pose proof (AFex.hs_bounds lastb (pa + (nn + 7) / 8 * 8 - 8) ltac:(rewrite <- Enn in *; lia) ltac:(ceil; unfold kHighMemEnd, ASAN_CEIL in *; lia)) as [_ X2].
unfold shadow_addr in X1, X2. replace (pa + (nn + 7) / 8 * 8 - 8) with (pa + ((nn + 7) / 8 - 1) * 8) in X2 by lia. rewrite Z.div_add in X2 by lia. lia. }
assert (AG4 : forall a, 0 <= a < 2 ^ 64 -> ~ AFgi.WIN ly regs pa lastb a -> ~ (AFgi.SPv pa <= a < AFgi.SPv pa + AFgi.CNT8v nn) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem4 a).
{ intros a Ha NW HZ. apply aview_same. apply (proj1 EQS4); rewrite unsigned_lit_small by exact Ha; [|exact HZ].
intros X. apply NW. exact (AFgi.WIN2_WIN ly regs pa lastb a X). }
assert (DEP : depot_mem_ok B ly (depot_after z tr s1) rd').
{ eapply (depot_mem_ok_agree ly (depot_after z tr s1) (depot_after z tr s1)); [| exact (am_universe B ly S _ M) | reflexivity | | exact DEPOK].
- apply (WfP_weaken _ 1 1 1); try lia. exact (AFex.sd_wf B ly S rd M lastb z tr Hev AOK HU).
- intros a Ha. subst rd'.
pose proof (AFgi.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _).
apply AG4; [exact (DFP_RANGE a Ha) | exact (proj1 (DFP_OUT a Ha)) |].
unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha. clear - Ha ZNB ZSB SHB.
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, TFIB_DEPOT, TFIB_STORE, d_map1, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfibsegs (w_H W) mem4)); [exact (proj1 (Forall_forall _ _) HC4 c Hc)|].
intros i Hi. subst rd'. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). apply AG4; [exact X3 | exact X1 |].
exact (proj1 (Forall_forall _ _) CONST_ZONE c Hc i Hi). }
pose proof (free_fin_ARm B TB ly S rd rd' M k lastb initr hb1 Hk Hst Hrev Hroom (conj HB1 HB1M) z tr Hev AOK HU sp0 HSP (img_cover_of_ledger ly S md LED) AG VIS
NEW_hdr NEW_n NEW_qs NEW_qf NEW_ql NEW_qb NEW_unw NEW_bb NEW_bc NEW_slot NEW_sh IAL DEP CONST') as M'.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split. 2:{ apply (AFex.qtight_S' B ly S rd M k lastb initr Hk Hst Hrev z tr); [rewrite <- Enn; exact Hcache | exact (qmeter_tight _ HQT)]. }
split; [|split; [apply layout_le_refl | split; [apply wle_refl | split; [|split; [|split]]]]].
- split; [exact M' | split; [|split; [|split]]].
+ eapply ALedger_same; [exact (AFex.ALedger_S' B ly S rd M k Hk z tr tfibsegs md LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD as [BUD PIN]. split; [| exact (AFex.asecA_S' B ly S rd M k Hk z tr _ PIN)].
eapply Z.le_trans; [exact BUD | exact (AFex.abudget_le B ly S rd M k lastb Hk z tr)].
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly S _ (w_H W) mem mem' (al_img_env tfibsegs ly S md (am_layout B ly S _ M) LED) M HSH VIS HSK).
* eapply (aclient_band_same_frames B ly S); [exact M' | unfold frames, depot_after, s1; cbn [st_fs set_qthread set_chunks set_depot set_internal_inited set_nev fst snd]; destruct (z =? 0); reflexivity].
*   exact (AFex.sec_extents' B ly S rd M k Hk z tr).
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
unfold AFex.D, AFex.DT, AFex.DK, AFex.DB, AFex.DS, AFex.DI, AFex.DH. rewrite <- Epa, <- Enn.
pose proof (AFgi.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (LT1 & _ & LP1 & LP2 & _ & _ & _ & _ & LNB & _ & LSB & _ & _ & _ & _ & _ & LSK).
pose proof (fh_HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (HBv1 & HBv2 & _). unfold AFgi.Bv in HBv1, HBv2.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize in LT1, LNB, LSB. unfold kHighMemBeg in LT1, LP1, LNB, LSB, LSK.
intros [X|[X|[X|[X|[X|[X|X]]]]]].
-- clear - X SBg LT1. unfold t_qc, t_unwinding, t_stats in X. lia.
-- rewrite Epa, G4 in X. clear - X SBg G1 G5 ER NN1 NN3 Enn. rewrite <- Enn in *. ceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G1. lia.
-- clear - X SBg LP1 LP2 HBv1. lia.
-- clear - X SBg LSK HSP. unfold ASTACK in *. lia.
-- rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X. clear - X SBg. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in X. lia.
-- unfold depot_footprint in X. rewrite (ts_depot _ TB), (ts_store _ TB) in X. clear - X SBg LNB LSB. ceil. unfold TFIB_DEPOT, TFIB_STORE, d_map1, kNodesBlockSize, kStoreBlockSize, ASAN_CEIL in *. lia.
-- assert (PA8 : pa mod 8 = 0) by (rewrite Epa, G4; clear - G3 G6; apply Z.mod_divide; [lia|]; apply Z.mod_divide in G3 as [q3 Hq3]; [|lia]; apply Z.mod_divide in G6 as [q6 Hq6]; [|lia]; exists (2 * q3 + 2 * q6); lia).
refine (hfree_shadow_off_range B ly S rd k pa nn g M Hk _ _ PA8 _ Hg HF X); rewrite ?Epa, ?G4; clear - G5 ER NN1 NN3 Enn; rewrite ?Enn in *; lia.
- intros r Hr'. apply CS. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - R. unfold CALLEE_SAVED.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
- unfold same_io. destruct md; cbn; repeat split; reflexivity.
- intros a Ha NO NO' NS NE. apply AG; [exact Ha|]. intros HD.
destruct (AFex.D_owned B TB ly S rd rd' M k lastb initr hb1 Hk Hrev Hroom (conj HB1 HB1M) z tr sp0 HSP (img_cover_of_ledger ly S md LED) M' a (proj1 Ha) HD) as [O|[O|O]];
[exact (NO O) | exact (NO' O) | apply NS; unfold ascratch; left; exact O].
- exact PRES'.
Qed.
Theorem afree_common_arm :
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n).
Proof.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
destruct HAR as (M & LED & BUD & MW & HSH).
pose proof (find_user_block _ 0 0 0 S p n (am_wf B ly S _ M) HBLK) as (k & Hf & Hk & Hst & Hu & Hr).
destruct ARM as (Hrev & Hroom & Hcache).
set (BODY := fun s' : astate =>
(match p with
| PNull => ret ()
| _ => s <- get;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 201364;;
depot_put tr;;
modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
| None => fail (FCheck 201376)
end
end) s').
assert (SPLIT : amreal tfibsegs (BODY s1) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n) ->
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n)).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
- replace (set_nev (st_nev S + 1) S) with s1; [exact MAIN|]. unfold s1. generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. subst. reflexivity.
- exact MAIN. }
apply SPLIT. clear SPLIT. subst BODY. cbn beta.
set (k' := {| ck_beg := ck_beg k; ck_req := ck_req k; ck_state := CQuarantined |}).
assert (MAIN : amreal tfibsegs ((s <- get;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 201364;;
depot_put tr;;
modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
| None => fail (FCheck 201376)
end) s1) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n)).
2:{ rewrite match_nonnull; [exact MAIN|]. intros Hp0.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly S _ M)) k Hk) as CK.
revert Hu. rewrite Hp0. unfold ck_user. destruct CK as [_ CK]. destruct (ck_beg k); cbn; try discriminate; destruct CK. }
cbn [bind get ret ibind]. change (st_chunks s1) with (st_chunks S). rewrite Hf, Hst. cbn [mcheck ret ibind].
unfold depot_put. cbn [bind askz ibind].
apply amreal_ask_depot.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_bind; [exact (segA W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) (m_vm_materialized md) FH)|].
intros W1 c1 _ HU1.
eapply SRr_bind; [exact (segB W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH W1 c1 HU1)|].
clear HU1. intros W2 c2 _ (-> & msD & matD & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rewrite HshD. eapply SRr_bind.
{ pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ _ HS eq_refl) as Hsh.
assert (AGD : forall a, ~ AFgi.WIN ly regs pa lastb a -> ~ AFgi.IZONE a -> 0 <= a < 2 ^ 64 ->
aview tfibsegs (w_H W) (ms_mem msD) a = aview tfibsegs (w_H W) mem a).
{ intros a Hw Hz Ha. apply aview_same. apply (proj1 MEQD); rewrite unsigned_lit_small by exact Ha; assumption. }
rreg HS (2%bv : bv 5) R2. rewrite (HEn3 2%nat ltac:(cbv; lia)), (AFgi.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3) in R2.
pose proof (lo_top ly (am_layout B ly S _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply (D1 W ly s1 (ms_regs msD) (ms_mem msD) _ (sp0 - 2112) tr (am_layout B ly S _ M) (img_cover_of_ledger ly S md (proj1 (proj2 (proj1 PRE)))) s1_wf HU).
-
apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfibsegs (w_H W) mem)).
+ exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc).
+ intros i Hi. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). apply AGD; assumption.
-
assert (DM : depot_mem_ok B ly S (aview tfibsegs (w_H W) mem)).
{ split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)). unfold acells. rewrite !in_app_iff. tauto.
- exact (am_depot B ly S _ M).
- pose proof (am_junk B ly S _ M) as J. pose proof (am_areas B ly S _ M) as A. rewrite Forall_forall in J, A.
repeat apply Forall_cons; try apply Forall_nil;
first [ apply J; unfold ajunk; do 2 right; repeat (apply in_or_app; first [ left; inlist | right ]); inlist
| apply A; unfold aareas; repeat (apply in_or_app; first [ left; inlist | right ]); inlist ]. }
eapply (depot_mem_ok_agree ly S s1); [exact (am_wf B ly S _ M) | exact (am_universe B ly S _ M) | reflexivity | | exact DM].
intros a Ha. destruct (DFP_OUT a Ha) as (X1 & X2 & X3). apply AGD; [exact X1 | exact X2 | exact (DFP_RANGE a Ha)].
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 2%nat ltac:(cbv; lia)), (AFgi.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3). unfold sp0; f_equal; lia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (AFgi.EaLEN ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3). reflexivity.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (AFgi.Er ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 3 3%bv eq_refl). exact Hgp.
- rreg HS (4%bv : bv 5) R; rewrite R. rewrite (ts_tp _ TB) in Htp. reflexivity.
- rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity.
- intros i Hi. apply (TRQ i Hi).
- unfold sp0. replace (bv_unsigned (getr regs 2) - 2112) with (bv_unsigned (getr regs 2) + (-264) * 8) by lia. rewrite Z_mod_plus_full.
apply (mod0_factor _ 8 2); [lia|]. exact Hal.
- unfold spZ, ASTACK in *; unfold sp0; lia.
-   unfold spZ, ASTACK in *; unfold sp0; lia.
- right. rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold sp0; lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
replace (bv_unsigned (getr regs 2) + -2176) with (bv_unsigned (getr regs 2) + (-136) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold spZ, ASTACK, DEP_STK in *; lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold spZ in *; lia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
apply PRESD. unfold DEP_STK, ASTACK, sp0 in *. lia. }
intros W3 c3 _ (-> & z & regs4 & mem4 & mat4 & -> & AOK & HP4 & Hfr4 & Hpr4 & DEPOK & HC4). srr_norm_model.
apply SRr_ret. exists z. split; [exact AOK|].
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
rewrite Q2, (HEn3 2%nat ltac:(cbv; lia)), (AFgi.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3) in Hfr4.
pose proof (lo_top ly (am_layout B ly S _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
rewrite unsigned_lit_small in Hfr4 by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). fold sp0 in Hfr4.
assert (DZ : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ AFgi.DZONE ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. apply Hfr4; [lia|]. intros Hf'. apply Hd. exact (proj2 (proj2 (DFP_OUT _ Hf'))). }
assert (TAIL : let sd := depot_after z tr s1 in
amreal tfibsegs ((modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) k') s0);; enqueue k';; maybe_drain) sd)
W (mkCfg (mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
(free_leaf tfibsegs B ly S W regs mem md p n)).
{ cbn zeta. assert (Qsd : st_qthread (depot_after z tr s1) = st_qthread S) by (unfold depot_after; destruct (z =? 0); reflexivity).
unfold enqueue, maybe_drain. cbn [bind modify ibind get st_qthread set_chunks]. rewrite Qsd.
unfold need_new_batch. rewrite Hrev. replace (Z.of_nat (length (b_items lastb)) =? kBatchSlots) with false by (symmetry; apply Z.eqb_neq; lia).
cbn [bind ret ibind modify st_qthread set_qthread get set_chunks]. rewrite Qsd.
replace (qc_bytes (qc_push (st_qthread S) k' None) <=? kQuarantineCacheMax) with true.
2:{ symmetry. apply Z.leb_le. cbn [qc_push qc_bytes]. subst k'. unfold nn, ck_n in *. cbn [ck_req]. rewrite Hr. exact Hcache. }
cbn [ret amreal]. rewrite Q1.
eapply SRr_mono.
- apply (segC W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH msD E3 regs4 mem4 mat4).
split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact DZ|]. split; [exact Hpr4|]. split; [exact MEQD | exact PRESD].
- intros W' c' _ HR. apply (FINH z k msD mem4 W' c' Hf AOK MEQD PRESD); [intros x Hx; apply Hfr4; lia | exact Hpr4 | exact DEPOK | exact HC4 | exact HR]. }
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. exact TAIL.
- cbn [Z.eqb bind get ret ibind].
destruct (depot_ids s1 + 1 <? kDepotIdsPerBlock); cbn [mcheck ret ibind]; [|exact I].
destruct (kStartFramesMax + depot_frames s1 + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock); cbn [mcheck ret put ibind]; [|exact I].
exact TAIL.
Qed.
End f.
End d.
