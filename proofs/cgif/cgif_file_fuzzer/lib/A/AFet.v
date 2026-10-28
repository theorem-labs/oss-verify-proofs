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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFff AFeu AFey AFgj AFgg AFgh AFgl AFh0 AFgt AFh8 AFev AFer AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_trans : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma same_io_with_vm_backing : forall l p md, same_io md (with_vm_backing l p md). Proof. intros. repeat split; reflexivity. Qed.
Lemma AR_model_same : forall B ly S W mem md md',
AR tfibsegs B ly S W mem md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
AR tfibsegs B ly S W mem md'.
Proof.
intros B ly S W mem md md' (M & L & Bu & MW & HS) Hv Hl He. split; [exact M|]. split; [exact (ALedger_same tfibsegs ly S md md' L Hv Hl He) |].
split; [exact Bu|]. split; [exact (amwf_same md md' Hv Hl MW) | exact HS].
Qed.
Lemma val_mem_aview_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HA Hv k Hk. pose proof (Hv k Hk) as E. pose proof (HA k Hk) as A. unfold aview in A. rewrite E in A. cbn [option_map] in A.
destruct (mbyte tfibsegs (mrestrict H' m') (a + Z.of_nat k)) as [b'|]; cbn [option_map] in A; [|discriminate].
injection A as A. f_equal. apply bv_eq. rewrite A. reflexivity.
Qed.
Lemma val_mem_mbyte_in : forall (m : word -> option byte) a (n : nat) v a', val_mem tfibsegs m a n v -> a <= a' < a + Z.of_nat n ->
exists b, mbyte tfibsegs m a' = Some b.
Proof.
intros m a n v a' Hv Ha. exists (Z_to_bv 8 (YO0f.le_byte v n (Z.to_nat (a' - a)))).
replace a' with (a + Z.of_nat (Z.to_nat (a' - a))) at 1 by lia. apply Hv. lia.
Qed.
Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis DR : tfib_dorecycle_spec B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : drain_pre B ly X W regs mem md.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Local Notation GLv := (AFgj.GLv ly gq).
Local Notation TFv := (AFgj.TFv ly tq).
Local Notation TLv := (AFgj.TLv ly tq).
Local Notation M := (AFev.M B ly X W regs mem md PRE).
Local Notation HSP := (AFev.HSP B ly X W regs mem md PRE).
Local Notation HI := (AFev.HI B ly X W regs mem md PRE).
Local Notation IMG := (AFev.IMG B ly X W regs mem md PRE).
Local Notation batch_facts := (AFev.batch_facts B ly X W regs mem md PRE).
Local Notation g_facts := (AFev.g_facts B ly X W regs mem md PRE).
Local Notation t_facts := (AFev.t_facts B ly X W regs mem md PRE).
Local Notation L := (AFer.L X).
Local Notation addr := (AFer.addr ly).
Local Notation firstaddr := (AFer.firstaddr ly).
Local Notation lastaddr := (AFer.lastaddr ly).
Local Notation zlen := AFer.zlen.
Local Notation sp1 := (AFer.sp1 regs).
Local Notation DW := (AFer.DW ly X regs).
Local Notation LST := (AFer.LST ly X W regs mem md).
Local Notation ATDR := (AFer.ATDR ly X W regs mem md).
Let WF : Wf (as_universe B) X := am_wf B ly X _ M.
Let LO : layout_ok ly := am_layout B ly X _ M.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (am_tsd B ly X _ M). apply (ts_tsd _ TB). Qed.
Lemma L0_LST : forall W' c', AFgj.at_L0 W ly regs mem md gq tq W' c' -> LST [] L W' c'.
Proof.
intros W' c' (-> & regs' & mem' & mat & -> & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R5 & R1 & RS & MQ & PRES & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CGL & Cs80 & Cs72 & Cs64 & Cs56 & Cs48 & Cs40 & Cs32 & Cs24 & Cs16 & Cs8).
pose proof HSP as [S1 S2]. fold sp0 in S1, S2. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & EG). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & ET).
split; [reflexivity|]. exists regs', mem', mat. split; [reflexivity|].
split; [rewrite R2; unfold AFer.sp1, LFRAME; reflexivity|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
split; [rewrite R14; reflexivity|]. split; [rewrite R15; reflexivity|].
split; [rewrite R16; unfold AFgj.LSZv, AFgj.GSZv, AFgj.TSZv, AFer.zlen, AFer.L; rewrite length_app, Nat2Z.inj_add; reflexivity|].
split; [rewrite R5; unfold AFgj.LFv, AFgj.GFv, AFgj.TFv, AFer.firstaddr, AFer.L, AFer.addr; destruct G; [destruct Tq; reflexivity | reflexivity]|].
split; [exact R1|]. split; [exact RS|].
split. { intros x Hx. apply MQ. intros Hw. apply Hx. unfold AFer.DW. unfold AFgj.WIN, AFgj.WINA in Hw. fold sp0 in Hw. unfold LFRAME. fold sp0.
destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw]. }
split. { intros a Ha. destruct (AFev.WIN_dec ly X regs a) as [Hw|Hw].
- apply PRES; [exact Hw | unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia].
- pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
apply (apresent_same H0 mem); [apply MQ; rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; lia); exact Hw | apply HPRES; exact Ha]. }
cbv zeta.
split; [exact C152|].
split; [unfold AFgj.LSZv, AFgj.GSZv, AFgj.TSZv in C160; unfold AFer.zlen, AFer.L; rewrite length_app, Nat2Z.inj_add; exact C160|].
split; [unfold AFgj.LFv, AFgj.GFv, AFgj.TFv in C168; unfold AFer.firstaddr, AFer.L, AFer.addr; destruct G; [destruct Tq; exact C168 | exact C168]|].
split; [exact C176|].
split; [unfold AFgj.LBv, AFgj.GBv, AFgj.TBv in C184; rewrite (AFer.sum_L B ly X W regs mem md PRE); exact C184|].
split; [exact Cq0|]. split; [exact Cq8|]. split; [exact Cq16|]. split; [exact Cq24|].
split. { intros _ lb initr Hrev. destruct (AFev.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (_ & EQ & _). unfold AFer.addr. rewrite <- EQ. exact (CGL lb initr Hrev). }
split. { intros i b Hi. destruct i; discriminate Hi. }
split. {
intros i b Hi. pose proof (nth_error_In _ _ Hi) as INb. apply AFer.L_all in INb.
destruct (batch_facts b INb) as (L1 & L2 & L3 & L4 & L5 & _).
pose proof (AFey.batches_nodup B ly X _ M) as ND. unfold all_batches in ND.
assert (OLDQ : Forall (cell_holds B ly rd0) (quar_cells X)).
{ apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M)). unfold acells. rewrite !in_app_iff. do 4 right; left. exact Hc. }
unfold quar_cells, qc_cells in OLDQ. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_app in OLDQ as [OT OG].
do 4 (apply Forall_cons_iff in OT as [_ OT]). do 4 (apply Forall_cons_iff in OG as [_ OG]).
assert (VMQ : forall a (n : nat) v, (forall j, 0 <= j < Z.of_nat n -> ~ AFgj.WIN ly regs gq (a + j) /\ 0 <= a + j < 2 ^ 64) ->
val_mem tfibsegs (mrestrict H0 mem) a n v -> val_mem tfibsegs (mrestrict H0 mem') a n v).
{ intros a n v Hn Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(lia)) as [N1 N2]. apply MQ. rewrite unsigned_lit_small by exact N2. exact N1. }
assert (NW : forall j, 0 <= j < 16 -> (forall lb initr, rev G = lb :: initr -> b_self b <> b_self lb \/ 8 <= j) -> ~ AFgj.WIN ly regs gq (addr b + j) /\ 0 <= addr b + j < 2 ^ 64).
{ intros j Hj NL. pose proof (AFev.GEO B ly X W regs mem md PRE) as (G_PT & _ & _ & G_PS & _). pose proof (AFev.AQ B TB) as EAQ. unfold o_quar in EAQ.
split; [| ceil; unfold AFer.addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA. fold sp0. unfold AFer.addr. intros [Y|[[Y|[Y|Y]]|[NE Y]]].
- unfold DSTACK, kPrimResvSize, kSpaceSize, kBatchBytes in *. lia.
- rewrite EAQ in Y. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. lia.
- rewrite EAQ in Y. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. lia.
- unfold t_qc, kThreadObjSize, kPrimResvSize, kSpaceSize, kBatchBytes in *. lia.
- destruct (rev G) as [|lb initr] eqn:Hrev; [apply NE; rewrite <- (rev_involutive G), Hrev; reflexivity|].
destruct (AFev.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (INlb & EQ & _). rewrite EQ in Y.
destruct (NL lb initr eq_refl) as [NEQ|J8]; [|unfold kBatchBytes in *; lia].
pose proof (AFey.batches_apart B ly X _ M _ HSP b lb INb INlb NEQ) as D. unfold zdisjoint, AFey.addr, kBatchBytes in D. cbn [fst snd] in D. lia. }
split.
-
destruct (AFey.cat_next X [] L ltac:(reflexivity) i b Hi) as [(i' & Hi' & EN)|[(i' & Hi' & Si & EN)|(initr & Hrev & Sj & EN)]].
+   unfold next_addr. change (AFer.L X) with (G ++ Tq). fold (next_exp (G ++ Tq) i).
pose proof (proj1 (Forall_forall _ _) OT _ (proj2 (In_batch_cells Tq _) (ex_intro _ i' (ex_intro _ b (conj Hi' (or_introl eq_refl)))))) as C.
pose proof (cell_holds_val_mem B ly H0 mem (batch_exp b) 8 (next_exp Tq i') C) as V. cbn [aeval] in V. rewrite <- EN in V.
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with (aeval B ly (next_exp (G ++ Tq) i)) by (unfold next_exp; destruct (nth_error (G ++ Tq) (S i)); reflexivity).
apply (VMQ _ 8%nat); [|exact V]. intros j Hj. apply NW; [lia|]. intros lb initr Hrev. left.
destruct (AFev.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (_ & _ & _). assert (EGr : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
rewrite EGr, map_app, map_app in ND. cbn [map] in ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & _ & N3).
intros E. apply (N3 (b_self b)); [apply in_app_iff; left; apply in_map; eapply nth_error_In; exact Hi' | left; symmetry; exact E].
+   unfold next_addr. change (AFer.L X) with (G ++ Tq). fold (next_exp (G ++ Tq) i).
pose proof (proj1 (Forall_forall _ _) OG _ (proj2 (In_batch_cells G _) (ex_intro _ i' (ex_intro _ b (conj Hi' (or_introl eq_refl)))))) as C.
pose proof (cell_holds_val_mem B ly H0 mem (batch_exp b) 8 (next_exp G i') C) as V. cbn [aeval] in V. rewrite <- EN in V.
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with (aeval B ly (next_exp (G ++ Tq) i)) by (unfold next_exp; destruct (nth_error (G ++ Tq) (S i)); reflexivity).
apply (VMQ _ 8%nat); [|exact V]. intros j Hj. apply NW; [lia|]. intros lb initr Hrev. left.
assert (EGr : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
rewrite EGr, map_app, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (_ & N2 & _). apply NoDup_app_iff in N2 as (_ & _ & N4).
rewrite EGr in Hi', Si. rewrite length_app in Si. cbn [length] in Si. rewrite nth_error_app1 in Hi' by lia.
intros E. apply (N4 (b_self b)); [apply in_map; eapply nth_error_In; exact Hi' | left; symmetry; exact E].
+   unfold next_addr. change (AFer.L X) with (G ++ Tq).
destruct (AFev.glast_facts B ly X W regs mem md PRE b initr Hrev) as (_ & EQ & _).
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with TFv.
2:{ unfold AFgj.TFv. rewrite nth_error_app2 by lia. rewrite Sj, Nat.sub_diag. destruct Tq; reflexivity. }
unfold AFer.addr. rewrite <- EQ. exact (CGL b initr Hrev).
-
assert (C : cell_holds B ly rd0 (z8 (aoff (batch_exp b) 8) (b_bytes b))).
{ unfold all_batches in INb. apply in_app_iff in INb as [INb'|INb'].
- apply In_nth_error in INb' as [i' Hi']. apply (proj1 (Forall_forall _ _) OT). apply In_batch_cells. exists i', b. split; [exact Hi'|]. right. left. reflexivity.
- apply In_nth_error in INb' as [i' Hi']. apply (proj1 (Forall_forall _ _) OG). apply In_batch_cells. exists i', b. split; [exact Hi'|]. right. left. reflexivity. }
pose proof (cell_holds_val_mem B ly H0 mem _ 8 (ANum (b_bytes b)) C) as V. cbn [aeval aoff batch_exp] in V.
replace (SB + (b_self b + 8)) with (addr b + 8) in V by (unfold AFer.addr; lia).
apply (VMQ _ 8%nat); [|exact V]. intros j Hj. replace (addr b + 8 + j) with (addr b + (8 + j)) by lia. apply NW; [lia|]. intros; right; lia. }
unfold AFer.sp1, LFRAME. fold sp0.
split; [replace (sp0 - 80 + 8) with (sp0 - 72) by lia; exact Cs72|]. split; [replace (sp0 - 80 + 24) with (sp0 - 56) by lia; exact Cs56|].
split; [replace (sp0 - 80 + 32) with (sp0 - 48) by lia; exact Cs48|]. split; [replace (sp0 - 80 + 40) with (sp0 - 40) by lia; exact Cs40|].
split; [replace (sp0 - 80 + 48) with (sp0 - 32) by lia; exact Cs32|]. split; [replace (sp0 - 80 + 56) with (sp0 - 24) by lia; exact Cs24|].
split; [replace (sp0 - 80 + 64) with (sp0 - 16) by lia; exact Cs16|]. replace (sp0 - 80 + 72) with (sp0 - 8) by lia; exact Cs8.
Qed.
Local Notation XT := (AFey.XT X).
Local Notation HTB := (AFev.HTB B ly X W regs mem md PRE).
Lemma S'_nil : AFey.S' X [] L = XT.
Proof. unfold AFey.S', AFey.XT, AFer.L. cbn [sum_bytes fold_right st_qglobal qc_bytes set_qglobal set_qthread]. unfold set_qglobal. cbn. f_equal. f_equal. lia. Qed.
Lemma FIN_a : forall W' c', AFgj.at_RETD W ly regs mem md gq tq W' c' -> drain_leaf B ly X W regs mem md (tt, XT) W' c'.
Proof.
intros W' c' HR.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & R2 & CS & MQ & PRESW & CELLS). cbv zeta in CELLS.
destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CGL).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
pose proof (AFev.AQ B TB) as EAQ.
assert (WD : forall a, AFgj.WIN ly regs gq a -> AFey.D B ly X [] sp0 a).
{ intros a Hw. unfold AFey.D, AFey.DT, AFey.DQ, AFey.DL, AFey.DS.
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in Hw. fold sp0 in Hw. rewrite EAQ in Hw.
unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hq Hw]]].
- do 4 right. clear - Hw. unfold DSTACK. lia.
- right; left. left. lia.
- right; left. right. lia.
- left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFey.GLv, AFey.addr. unfold AFgj.GLv in Hw. destruct (rev G); [exact Hw | exact Hw]. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X [] sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MQ (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros X'. exact (ND (WD a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (AFev.WIN_dec ly X regs a') as [C|C].
-
assert (CASE : AFgj.WINF ly a' \/ kHighMemBeg <= a').
{ pose proof C as C'. unfold AFgj.WIN, AFgj.WINA in C'. fold sp0 in C'.
destruct C' as [Y|[Y|[Hq Y]]]; [right | left; exact Y | right].
- clear - Y HSP' hS1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *. lia.
- destruct (rev G) as [|lb initr] eqn:Hrev; [exfalso; apply Hq; rewrite <- (rev_involutive G), Hrev; reflexivity|].
destruct (AFev.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (_ & _ & L1 & _). clear - Y L1 hP1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia. }
destruct CASE as [LOWa|HIGHa].
+
assert (SOMEb : exists b, mbyte tfibsegs (mrestrict (w_H W) mem') a' = Some b).
{ unfold AFgj.WINF in LOWa. destruct LOWa as [IN|[IN|IN]].
- exists (Z_to_bv 8 0); apply C152; exact IN.
- destruct (Z_lt_le_dec a' (A_QUAR + 168)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ C160); lia|].
destruct (Z_lt_le_dec a' (A_QUAR + 176)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ C168); lia|].
destruct (Z_lt_le_dec a' (A_QUAR + 184)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ C176); lia | apply (val_mem_mbyte_in _ _ 8%nat _ _ C184); lia].
- destruct (Z_lt_le_dec a' (T + t_qc + 8)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq0); lia|].
destruct (Z_lt_le_dec a' (T + t_qc + 16)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq8); lia|].
destruct (Z_lt_le_dec a' (T + t_qc + 24)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq16); lia | apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq24); lia]. }
destruct SOMEb as [b Hb]. unfold mbyte, mrestrict in Hb. rewrite Ex, Hx, E', ROM in Hb. discriminate.
+ destruct (PRESW a' C HIGHa) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MQ x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
destruct (AFev.WIN_dec ly X regs a) as [C|C].
- exfalso. pose proof (AFev.WIN_zone B TB ly X W regs mem md PRE a C) as Z3. fold sp0 in Z3.
destruct (Z_lt_le_dec a kHighMemBeg) as [LOWa|HIGHa].
+ pose proof (ts_inst _ TB) as EI. clear - Z3 LOWa Ha hT1 hP1 HSP' hS1 EI. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize, kHighMemBeg, kLowShadowBeg, TFIB_INST, DSTACK, o_q_cmutex, o_q_size in *. lia.
+ destruct (PRESW a C HIGHa) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- apply (MQ x). rewrite Ux. exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0f.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_t : forall j i, 0 <= j < 4 -> (i < 8)%nat -> rd' (T + t_qc + 8 * j + Z.of_nat i) = Some (YG0f.le_byte 0 8 i)).
{ intros j i Hj Hi. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
destruct J as [-> | [-> | [-> | ->]]].
- apply (VM _ _ 8%nat _ _ Cq0); [lia | reflexivity | exact Hi].
- apply (VM _ _ 8%nat _ _ Cq8); [lia | reflexivity | exact Hi].
- apply (VM _ _ 8%nat _ _ Cq16); [lia | reflexivity | exact Hi].
- apply (VM _ _ 8%nat _ _ Cq24); [lia | reflexivity | exact Hi]. }
assert (NEW_mx : forall i, 0 <= i < 4 -> rd' (as_inst B + o_q_cmutex + i) = Some 0).
{ intros i Hi. subst rd'. unfold aview. replace (as_inst B + o_q_cmutex + i) with (A_QUAR + 152 + i) by (rewrite EAQ; unfold o_quar, o_q_cmutex; lia).
rewrite (C152 (A_QUAR + 152 + i)) by lia. reflexivity. }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_size + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length L)) 8 i)).
{ apply (VM _ _ 8%nat _ _ C160); [rewrite EAQ; unfold o_quar, o_q_size; lia|]. unfold AFgj.LSZv, AFgj.GSZv, AFgj.TSZv, AFer.L. rewrite length_app. lia. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_first + Z.of_nat i) = Some (YG0f.le_byte (AFey.RFv ly L) 8 i)).
{ apply (VM _ _ 8%nat _ _ C168); [rewrite EAQ; unfold o_quar, o_q_first; lia|].
unfold AFgj.LFv, AFgj.GFv, AFgj.TFv, AFey.RFv, AFey.addr, AFer.L. destruct G; [destruct Tq; reflexivity | reflexivity]. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_last + Z.of_nat i) = Some (YG0f.le_byte (AFey.RLv ly L) 8 i)).
{ apply (VM _ _ 8%nat _ _ C176); [rewrite EAQ; unfold o_quar, o_q_last; lia|].
unfold AFgj.TLv, AFey.RLv, AFey.addr, AFer.L. rewrite rev_app_distr.
pose proof (AFev.Tq_ne B ly X W regs mem md PRE) as NE. destruct (rev Tq) as [|lb rt] eqn:RT; [exfalso; apply NE; rewrite <- (rev_involutive Tq), RT; reflexivity | reflexivity]. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_bytes + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes gq + qc_bytes tq - sum_bytes []) 8 i)).
{ apply (VM _ _ 8%nat _ _ C184); [rewrite EAQ; unfold o_quar, o_q_bytes; lia|]. unfold AFgj.LBv, AFgj.GBv, AFgj.TBv. cbn [sum_bytes fold_right]. lia. }
assert (NEW_J : forall lb initr, rev G = lb :: initr -> (length ([] : list batch) < length G)%nat ->
forall kk, (kk < 8)%nat -> rd' (AFey.addr ly lb + Z.of_nat kk) = Some (YG0f.le_byte (AFey.TFv ly X) 8 kk)).
{ intros lb initr Hrev _. apply (VM _ _ 8%nat _ _ (CGL lb initr Hrev)).
- unfold AFgj.GLv, AFey.addr. rewrite Hrev. reflexivity.
- unfold AFgj.TFv, AFey.TFv, AFey.addr. destruct Tq; reflexivity. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc) as OLDc.
destruct (proj1 (Forall_forall _ _) (AFev.CONST_OUT B TB ly X W regs mem md PRE HTSD) c Hc) as [[EC EW]|[[EC EW]|OUT]].
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. subst e w.
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfib_const Tfib_const_sym Tfib_const_abs Tfib_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [first [congruence | discriminate] |]). destruct Hc. }
subst v. intros k Hk. subst rd'. unfold aview. cbn [aeval]. rewrite (C152 (0xa2d0a + Z.of_nat k)) by (rewrite EAQ, (ts_inst _ TB); unfold TFIB_INST, o_quar; lia).
cbn [option_map]. f_equal. unfold YG0f.le_byte. rewrite Z.shiftr_0_l. reflexivity.
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. subst e w.
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfib_const Tfib_const_sym Tfib_const_abs Tfib_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [first [congruence | discriminate] |]). destruct Hc. }
subst v. intros k Hk. subst rd'.
rewrite <- (OLDc k Hk). apply AG.
+ cbn [aeval]. lia.
+ cbn [aeval]. intros HD. apply (AFey.D_cases B ly X rd M' [] L eq_refl sp0 HSP' IMG) in HD.
destruct HD as [[Y _]|[[_ Y]|[(b2 & Hb2 & Y & _)|Y]]].
* clear - Y Hk hT1. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
* unfold AFey.DQ in Y. rewrite (ts_inst _ TB) in Y. clear - Y Hk. unfold TFIB_INST, o_q_cmutex, o_q_size in *. lia.
* destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold AFey.addr in Y. clear - Y L4 Hk. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
* clear - Y Hk hS1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
- eapply (cell_holds_agree B ly rd); [exact OLDc|].
intros i Hi. subst rd rd'. destruct (OUT i Hi) as (X1 & X2 & _). apply aview_same.
apply (MQ (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact X2. exact X1. }
pose proof (AFey.drain_fin_ARm B TB ly X rd rd' M' (proj1 (proj2 PRE))   [] L eq_refl sp0 HSP' IMG AG VIS NEW_t NEW_mx NEW_qs NEW_qf NEW_ql NEW_qb NEW_J CONST') as MF.
rewrite S'_nil in MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
cbn [fst snd].
split; [|split; [apply layout_le_refl | split; [apply wle_refl | split; [|split; [|split]]]]].
-   split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same; [| apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
pose proof (AFey.ALedger_S' ly X [] L tfibsegs md LED) as LED'. rewrite S'_nil in LED'. exact LED'.
+ destruct BUD as [BUD PIN]. split; [| pose proof (AFey.asecA_S' ly X [] L _ PIN) as PIN'; rewrite S'_nil in PIN'; exact PIN'].
eapply Z.le_trans; [exact BUD|]. pose proof (AFey.abudget_S' X [] L) as EB. rewrite S'_nil in EB. rewrite EB. apply Z.le_refl.
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly X _ (w_H W) mem mem' (al_img_env tfibsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [exact MF |]. pose proof (AFey.frames' X [] L) as EF. rewrite S'_nil in EF. exact EF.
*   pose proof (AFey.sec_extents' ly X [] L) as ES. rewrite S'_nil in ES. exact ES.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
intros HD. apply (AFey.D_cases B ly X rd M' [] L eq_refl sp0 HSP' IMG) in HD. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
destruct HD as [[Y _]|[[Y _]|[(b2 & Hb2 & Y & _)|Y]]].
-- clear - Y SBg hT1. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
-- rewrite (ts_inst _ TB) in Y. clear - Y SBg. unfold TFIB_INST, o_q_cmutex, o_q_bytes in *. lia.
-- destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold AFey.addr in Y. clear - Y L4 SBg. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
-- clear - Y SBg hS1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - R R2 CS. unfold AFgj.SREGS in CS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn; first [exact R2 | apply CS; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right])].
- apply same_io_with_vm_backing.
-
intros a Ha NO NO' NS NE. apply AG; [exact Ha|]. intros HD.
destruct (AFey.D_owned B ly X rd M' [] L eq_refl sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; exact O].
-
intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (AFev.WIN_dec ly X regs a) as [Hw|Hw].
+ apply PRESW; [exact Hw | clear - Ha hS1 HSP'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia].
+ apply (apresent_same H0 mem); [apply MQ; rewrite unsigned_lit_small by (clear - Ha hS1 hS2 HSP' Usp; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; lia); exact Hw | apply HPRES; exact Ha].
Qed.
Lemma DRPRE : forall P R W' c', ATDR P R W' c' -> L = P ++ R -> sum_bytes R <= kQuarantineMax ->
exists regs2 mem2 mat, W' = W /\ c' = cfg_at tfibsegs A_DoRecycle regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs2 2 = w64 sp1 /\ getr regs2 1 = w64 0x3323c /\ getr regs2 13 = getr regs 13 /\
(forall r : bv 5, In r AFer.SREGS -> getr regs2 r = getr regs r) /\
(forall x : word, ~ DW P (bv_unsigned x) -> mem2 x = mem x) /\
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem2 a) /\
(let m := mrestrict H0 mem2 in
val_mem tfibsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfibsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfibsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfibsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X P sp0 a -> aview tfibsegs H0 mem2 a = rd0 a) /\
dr_pre B ly (AFey.S' X P R) P W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros P R W' c' HA HL HRB.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HA as (-> & regs' & mem' & mat & -> & R2 & R10 & R11 & R12 & R13 & R1 & CS & MQ & PRS & CELLS). cbv zeta in CELLS.
destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CG & CP & Ct0 & Ct8 & Ct16 & Ct24 & Cs32 & Cs40 & Cs48 & Cs56 & Cs64 & Cs72).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
pose proof (AFev.AQ B TB) as EAQ.
assert (PL : forall b, In b P -> In b L) by (intros b Hb; rewrite HL; apply in_app_iff; left; exact Hb).
assert (RL : forall b, In b R -> In b L) by (intros b Hb; rewrite HL; apply in_app_iff; right; exact Hb).
assert (WD : forall a, DW P a -> AFey.D B ly X P sp0 a).
{ intros a Hw. unfold AFey.D, AFey.DT, AFey.DQ, AFey.DL, AFey.DP, AFey.DS.
unfold AFer.DW, AFgj.WINF in Hw. fold sp0 in Hw. rewrite EAQ in Hw. unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[[Hq Hw]|(b & Hb & Hw)]]].
- do 4 right. clear - Hw. unfold DSTACK, LFRAME in *. lia.
- right; left. left. lia.
- right; left. right. lia.
- left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFey.GLv, AFey.addr. unfold AFgj.GLv in Hw. destruct (rev G); [exact Hw | exact Hw].
- right; right; right; left. exists b. split; [exact Hb|]. unfold AFey.addr. unfold AFer.addr in Hw. exact Hw. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X P sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MQ (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros X'. exact (ND (WD a X')). }
assert (DWV : forall a, DW P a -> exists b, mbyte tfibsegs (mrestrict (w_H W) mem') a = Some b).
{ intros a Hw. unfold AFer.DW, AFgj.WINF in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[[Hq Hw]|(b & Hb & Hw)]]].
- apply apresent_mbyte. apply PRS. clear - Hw. unfold DSTACK, LFRAME in *. lia.
- exists (Z_to_bv 8 0). apply C152. exact Hw.
- destruct (Z_lt_le_dec a (A_QUAR + 168)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ C160); lia|].
destruct (Z_lt_le_dec a (A_QUAR + 176)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ C168); lia|].
destruct (Z_lt_le_dec a (A_QUAR + 184)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ C176); lia | apply (val_mem_mbyte_in _ _ 8%nat _ _ C184); lia].
- destruct (Z_lt_le_dec a (T + t_qc + 8)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq0); lia|].
destruct (Z_lt_le_dec a (T + t_qc + 16)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq8); lia|].
destruct (Z_lt_le_dec a (T + t_qc + 24)); [apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq16); lia | apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq24); lia].
-
destruct (rev G) as [|lb initr] eqn:Hrev; [exfalso; apply Hq; rewrite <- (rev_involutive G), Hrev; reflexivity|].
destruct (AFev.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (INlb & EQ & _).
assert (EG3 : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
unfold AFgj.GLv in Hw. rewrite Hrev in Hw.
destruct (Nat.lt_ge_cases (length P) (length G)) as [LT|GE].
+ apply (val_mem_mbyte_in _ _ 8%nat _ _ (CG LT lb initr eq_refl)). unfold AFer.addr. lia.
+
assert (HP : nth_error P (length (rev initr)) = Some lb).
{ pose proof HL as HL'. unfold AFer.L in HL'. rewrite EG3, <- app_assoc in HL'.
pose proof (f_equal (fun l => nth_error l (length (rev initr))) HL') as E1. cbn beta in E1.
rewrite nth_error_app2, Nat.sub_diag in E1 by lia. cbn [app nth_error] in E1. rewrite nth_error_app1 in E1 by (rewrite EG3, length_app in GE; cbn [length] in GE; lia). symmetry. exact E1. }
apply (val_mem_mbyte_in _ _ 8%nat _ _ (CP _ _ HP)). unfold AFer.addr. lia.
-
apply In_nth_error in Hb as [i Hi]. apply (val_mem_mbyte_in _ _ 8%nat _ _ (CP i b Hi)). lia. }
assert (DP_dec : forall l a, (exists b, In b l /\ addr b <= a < addr b + 8) \/ ~ (exists b, In b l /\ addr b <= a < addr b + 8)).
{ clear. induction l as [|b0 t IH]; intros a.
- right. intros (b & Hb & _). exact Hb.
- destruct (IH a) as [(b & Hb & Rg)|N]; [left; exists b; split; [right; exact Hb | exact Rg]|].
destruct (Z_lt_le_dec a (addr b0)) as [L1|L1]; [|destruct (Z_lt_le_dec a (addr b0 + 8)) as [L2|L2]; [left; exists b0; split; [left; reflexivity | lia]|]].
all: right; intros (b & [<-|Hb] & Rg); [lia | exact (N (ex_intro _ b (conj Hb Rg)))]. }
assert (DW_dec : forall a, DW P a \/ ~ DW P a).
{ intros a. destruct (AFev.WIN_dec ly X regs a) as [Hw|Hw].
- left. unfold AFer.DW. unfold AFgj.WIN, AFgj.WINA in Hw. fold sp0 in Hw. unfold LFRAME. fold sp0.
destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw].
- destruct (DP_dec P a) as [Hp|Hp]; [left; unfold AFer.DW; right; right; right; exact Hp|].
right. intros HD. unfold AFer.DW in HD. unfold LFRAME in HD. fold sp0 in HD.
destruct HD as [Y|[Y|[Y|Y]]]; [apply Hw | apply Hw | apply Hw | exact (Hp Y)]; unfold AFgj.WIN, AFgj.WINA; fold sp0; [left; exact Y | right; left; exact Y | right; right; exact Y]. }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (DW_dec a') as [C|C].
- destruct (DWV a' C) as [b Hb]. unfold mbyte, mrestrict in Hb. rewrite Ex, Hx, E', ROM in Hb. discriminate.
- rewrite (MQ x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
destruct (DW_dec a) as [C|C].
- exfalso. destruct (DWV a C) as [b Hb]. unfold mbyte, mrestrict in Hb.
rewrite (seg_rom_none_high a) in Hb by (clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowEnd, TFIB_IMG_END in *; lia).
fold x in Hb. rewrite Hx in Hb. discriminate.
- apply (MQ x). rewrite Ux. exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0f.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_t : forall j i, 0 <= j < 4 -> (i < 8)%nat -> rd' (T + t_qc + 8 * j + Z.of_nat i) = Some (YG0f.le_byte 0 8 i)).
{ intros j i Hj Hi. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
destruct J as [-> | [-> | [-> | ->]]].
- apply (VM _ _ 8%nat _ _ Cq0); [lia | reflexivity | exact Hi].
- apply (VM _ _ 8%nat _ _ Cq8); [lia | reflexivity | exact Hi].
- apply (VM _ _ 8%nat _ _ Cq16); [lia | reflexivity | exact Hi].
- apply (VM _ _ 8%nat _ _ Cq24); [lia | reflexivity | exact Hi]. }
assert (NEW_mx : forall i, 0 <= i < 4 -> rd' (as_inst B + o_q_cmutex + i) = Some 0).
{ intros i Hi. subst rd'. unfold aview. replace (as_inst B + o_q_cmutex + i) with (A_QUAR + 152 + i) by (rewrite EAQ; unfold o_quar, o_q_cmutex; lia).
rewrite (C152 (A_QUAR + 152 + i)) by lia. reflexivity. }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_size + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length R)) 8 i)).
{ apply (VM _ _ 8%nat _ _ C160); [rewrite EAQ; unfold o_quar, o_q_size; lia | reflexivity]. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_first + Z.of_nat i) = Some (YG0f.le_byte (AFey.RFv ly R) 8 i)).
{ apply (VM _ _ 8%nat _ _ C168); [rewrite EAQ; unfold o_quar, o_q_first; lia|]. unfold AFer.firstaddr, AFey.RFv, AFey.addr, AFer.addr. destruct R; reflexivity. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_last + Z.of_nat i) = Some (YG0f.le_byte (AFey.RLv ly R) 8 i)).
{ apply (VM _ _ 8%nat _ _ C176); [rewrite EAQ; unfold o_quar, o_q_last; lia|]. unfold AFer.lastaddr, AFey.RLv, AFey.addr, AFer.addr. destruct (rev R); reflexivity. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_bytes + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes gq + qc_bytes tq - sum_bytes P) 8 i)).
{ apply (VM _ _ 8%nat _ _ C184); [rewrite EAQ; unfold o_quar, o_q_bytes; lia|].
pose proof (AFer.sum_L B ly X W regs mem md PRE) as SL. rewrite HL, sum_bytes_app in SL. lia. }
assert (NEW_P : forall i b2, nth_error P i = Some b2 -> forall kk, (kk < 8)%nat -> rd' (AFey.addr ly b2 + Z.of_nat kk) = Some (YG0f.le_byte (next_addr ly P i) 8 kk)).
{ intros i b2 Hi. apply (VM _ _ 8%nat _ _ (CP i b2 Hi)); reflexivity. }
assert (NEW_J : forall lb initr, rev G = lb :: initr -> (length P < length G)%nat ->
forall kk, (kk < 8)%nat -> rd' (AFey.addr ly lb + Z.of_nat kk) = Some (YG0f.le_byte (AFey.TFv ly X) 8 kk)).
{ intros lb initr Hrev LT. apply (VM _ _ 8%nat _ _ (CG LT lb initr Hrev)); [reflexivity|].
unfold AFgj.TFv, AFey.TFv, AFey.addr. destruct Tq; reflexivity. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc) as OLDc.
destruct (proj1 (Forall_forall _ _) (AFev.CONST_OUT B TB ly X W regs mem md PRE HTSD) c Hc) as [[EC EW]|[[EC EW]|OUT]].
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. subst e w.
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfib_const Tfib_const_sym Tfib_const_abs Tfib_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [first [congruence | discriminate] |]). destruct Hc. }
subst v. intros k Hk. subst rd'. unfold aview. cbn [aeval]. rewrite (C152 (0xa2d0a + Z.of_nat k)) by (rewrite EAQ, (ts_inst _ TB); unfold TFIB_INST, o_quar; lia).
cbn [option_map]. f_equal. unfold YG0f.le_byte. rewrite Z.shiftr_0_l. reflexivity.
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. subst e w.
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfib_const Tfib_const_sym Tfib_const_abs Tfib_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [first [congruence | discriminate] |]). destruct Hc. }
subst v. intros k Hk. subst rd'.
rewrite <- (OLDc k Hk). apply AG.
+ cbn [aeval]. lia.
+ cbn [aeval]. intros HD. apply (AFey.D_cases B ly X rd M' P R HL sp0 HSP' IMG) in HD.
destruct HD as [[Y _]|[[_ Y]|[(b2 & Hb2 & Y & _)|Y]]].
* clear - Y Hk hT1. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
* unfold AFey.DQ in Y. rewrite (ts_inst _ TB) in Y. clear - Y Hk. unfold TFIB_INST, o_q_cmutex, o_q_size in *. lia.
* destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold AFey.addr in Y. clear - Y L4 Hk. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
* clear - Y Hk hS1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
- eapply (cell_holds_agree B ly rd); [exact OLDc|].
intros i Hi. subst rd rd'. destruct (OUT i Hi) as (X1 & X2 & X3 & X4). apply aview_same.
apply (MQ (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact X2. intros HDW.
unfold AFer.DW in HDW. unfold LFRAME in HDW. fold sp0 in HDW.
destruct HDW as [Y|[Y|[Y|(b2 & Hb2 & Y)]]].
+ apply X1. unfold AFgj.WIN. fold sp0. left. exact Y.
+ apply X1. unfold AFgj.WIN. right; left. exact Y.
+ apply X1. unfold AFgj.WIN, AFgj.WINA. right; right. exact Y.
+ apply X4. destruct (batch_facts b2 (proj1 (AFer.L_all X b2) (PL b2 Hb2))) as (L1 & L2 & _). unfold AFer.addr in Y.
clear - Y L1 L2 hSP1 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia. }
pose proof (AFey.drain_fin_ARm B TB ly X rd rd' M' (proj1 (proj2 PRE)) P R HL sp0 HSP' IMG AG VIS NEW_t NEW_mx NEW_qs NEW_qf NEW_ql NEW_qb NEW_J CONST') as MF.
pose proof (AFey.drain_fin_plist B ly X rd rd' M' P R HL sp0 HSP' IMG AG NEW_P) as PLIST.
assert (Usp1 : 0 <= sp1 < 2 ^ 64) by (unfold AFer.sp1, LFRAME; fold sp0; clear - Usp HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia).
assert (SP1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; rewrite unsigned_lit_small by exact Usp1; reflexivity).
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|].
split; [exact R2|]. split; [exact R1|]. split; [exact R13|]. split; [exact CS|]. split; [exact MQ|]. split; [exact PRS|].
split; [cbv zeta; splits; assumption|]. split; [exact AG|].
unfold dr_pre, spZ, raZ. rewrite R2, R1, R11, R12, SP1. unfold w64 at 1. rewrite unsigned_lit_small by (clear; lia).
split; [|split; [exact (AFey.RIS' B ly X rd M' (proj1 (proj2 PRE)) P R HL) | split; [reflexivity | split; [| split; [| split; [apply YK0s.ret_ok_even; reflexivity | split; [clear; lia | split; [|split; [|split; [|split; [|split; [|split; [|split; [reflexivity|split; [reflexivity|split]]]]]]]]]]]]]]].
-   split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same; [| apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb]. exact (AFey.ALedger_S' ly X P R tfibsegs md LED).
+ destruct BUD as [BUD PIN]. split; [| exact (AFey.asecA_S' ly X P R _ PIN)].
eapply Z.le_trans; [exact BUD|]. rewrite (AFey.abudget_S' X P R). apply Z.le_refl.
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly X _ (w_H W) mem mem' (al_img_env tfibsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [exact MF | exact (AFey.frames' X P R)].
*   exact (AFey.sec_extents' ly X P R).
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
intros HD. apply (AFey.D_cases B ly X rd M' P R HL sp0 HSP' IMG) in HD. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
destruct HD as [[Y _]|[[Y _]|[(b2 & Hb2 & Y & _)|Y]]].
-- clear - Y SBg hT1. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
-- rewrite (ts_inst _ TB) in Y. clear - Y SBg. unfold TFIB_INST, o_q_cmutex, o_q_bytes in *. lia.
-- destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold AFey.addr in Y. clear - Y L4 SBg. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
-- clear - Y SBg hS1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
-   cbn. pose proof (AFer.sum_L B ly X W regs mem md PRE) as SL. rewrite HL, sum_bytes_app in SL. cbn in SL. clear - SL HRB. lia.
-
unfold plist_cells, qc_cells. cbn [qc_list qc_bytes].
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. apply (VM _ _ 8%nat _ _ Ct0); [lia | reflexivity | exact Hkk]. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. apply (VM _ _ 8%nat _ _ Ct8); [lia | | exact Hkk].
unfold AFer.firstaddr, AFer.addr. destruct P; reflexivity. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. apply (VM _ _ 8%nat _ _ Ct16); [lia | | exact Hkk].
unfold AFer.lastaddr, AFer.addr. destruct (rev P); reflexivity. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. apply (VM _ _ 8%nat _ _ Ct24); [lia | reflexivity | exact Hkk]. }
exact PLIST.
- replace sp1 with (sp0 + (-5) * 16) by (unfold AFer.sp1, LFRAME; fold sp0; lia). rewrite Z_mod_plus_full. exact Hal.
- unfold AFer.sp1, LFRAME, DRSTACK. fold sp0. clear - Hlo. unfold DSTACK in *. lia.
- unfold AFer.sp1, LFRAME. fold sp0. clear - Hhi. lia.
- intros a Ha. apply PRS. unfold AFer.sp1, LFRAME, DRSTACK in Ha. fold sp0 in Ha. clear - Ha. unfold DSTACK. lia.
- rewrite (CS 3%bv ltac:(cbn; tauto)). exact Hgp.
- rewrite (CS 4%bv ltac:(cbn; tauto)). exact Htp.
-   pose proof (AFer.len_L B ly X W regs mem md PRE) as LL. rewrite HL in LL.
unfold AFer.zlen, EV_MAX in LL. rewrite length_app, Nat2Z.inj_add in LL. clear - LL. lia.
-
unfold AFey.S', AFey.XT. cbn [st_cache_inited set_qglobal set_qthread].
pose proof PRE as PRE2. destruct PRE2 as (_ & DRX & _). apply (wf_qinited _ _ _ _ _ WF). unfold all_batches.
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QB. intros E. apply app_eq_nil in E as [E _]. rewrite E in QB. cbn in QB.
clear - DRX QB. unfold kQuarantineCacheMax in DRX. lia.
Qed.
Lemma EPI : forall P R regs2 mem2 mat r W6 c6,
L = P ++ R ->
getr regs2 2 = w64 sp1 -> getr regs2 1 = w64 0x3323c -> (forall r5 : bv 5, In r5 AFer.SREGS -> getr regs2 r5 = getr regs r5) ->
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem2 a) ->
(let m := mrestrict H0 mem2 in
val_mem tfibsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfibsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfibsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfibsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X P sp0 a -> aview tfibsegs H0 mem2 a = rd0 a) ->
AR tfibsegs B ly (AFey.S' X P R) W mem2 (with_vm_backing (m_vm_lazy md) mat md) ->
dr_leaf B ly (AFey.S' X P R) W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md) r W6 c6 ->
SRr tfibsegs W6 c6 (drain_leaf B ly X W regs mem md r).
Proof.
intros P R regs2 mem2 mat [ru X3] W6 c6 HL R2 R1 CS PRS2 SLOTS AG2 AR2 HDL. cbv zeta in SLOTS. destruct SLOTS as (Cs32 & Cs40 & Cs48 & Cs56 & Cs64 & Cs72).
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
assert (Usp1 : 0 <= sp1 < 2 ^ 64) by (unfold AFer.sp1, LFRAME; fold sp0; clear - Usp HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia).
assert (SP1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; rewrite unsigned_lit_small by exact Usp1; reflexivity).
destruct HDL as (regs3 & mem3 & md3 & -> & (AR3 & LLE & WLE & CS3 & SIO & FR3 & PRS3) & PRE3). cbn [fst snd] in *.
unfold spZ, raZ, ascratch in FR3, PRS3, PRE3. rewrite R2, SP1 in FR3, PRS3, PRE3. unfold spZ in FR3. rewrite R2, SP1 in FR3.
assert (NOWN : forall a, sp0 - DSTACK <= a < sp0 -> ~ aowned B ly (AFey.S' X P R) a /\ ~ aowned B ly X3 a).
{ intros a Ha. split.
- apply (AR_stack_law_ok tfibsegs B ly _ W mem2 _ a AR2). clear - Ha Hlo Hhi. unfold DSTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X3 W6 mem3 md3 a AR3). clear - Ha Hlo Hhi. unfold DSTACK in *. lia. }
assert (AGS : forall a, sp0 - DSTACK <= a < sp0 -> ~ (sp1 - DRSTACK <= a < sp1 + 32) -> aview tfibsegs (w_H W6) mem3 a = aview tfibsegs H0 mem2 a).
{ intros a Ha Hn. destruct (NOWN a Ha) as [N1 N2]. apply FR3; [clear - Ha Usp hS1 HSP'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia | exact N1 | exact N2 | | clear - Hn; unfold DRSTACK in *; lia].
intros [Hs|Hs]; [clear - Hs Hn; unfold DRSTACK in *; lia|]. rewrite (ts_errno _ TB) in Hs. clear - Hs Ha hS1 HSP'. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, DSTACK, kHighMemBeg in *. lia. }
assert (PRS6 : forall a, sp0 - DSTACK <= a < sp0 -> apresent (w_H W6) mem3 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp1 - DRSTACK)) as [L1|L1]; [|destruct (Z_lt_le_dec a sp1) as [L2|L2]; [apply PRS3; lia | destruct (Z_lt_le_dec a (sp1 + 32)) as [L3|L3]; [apply PRE3; lia|]]].
all: pose proof (PRS2 a Ha) as P0; apply apresent_mbyte in P0 as [b Hb];
assert (A : aview tfibsegs H0 mem2 a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- (AGS a Ha ltac:(lia)) in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W6) mem3 a b' ltac:(clear - Ha Usp hS1 HSP'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, TFIB_IMG_END in *; lia) Hb'). }
set (vra := bv_unsigned (getr regs 1)). set (vs0 := bv_unsigned (getr regs 8)). set (vs1 := bv_unsigned (getr regs 9)).
set (vs2 := bv_unsigned (getr regs 18)). set (vs3 := bv_unsigned (getr regs 19)). set (vs4 := bv_unsigned (getr regs 20)).
assert (CS3' : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs3 r = getr regs2 r) by (intros r5 z Hz <-; exact (CS3 z Hz)).
assert (Q2 : getr regs3 2 = w64 sp1) by (rewrite (CS3' 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact R2).
assert (Q4 : getr regs3 4 = w64 TFIB_TP).
{ rewrite (CS3' 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)), (CS 4%bv ltac:(cbn; tauto)), Htp, (ts_tp _ TB). reflexivity. }
assert (XF : forall a (n : nat) v, sp1 + 32 <= a -> a + Z.of_nat n <= sp0 -> val_mem tfibsegs (mrestrict H0 mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W6) mem3) a n v).
{ intros a n v H1 H2 Hv. eapply val_mem_aview_xfer; [|exact Hv]. intros k Hk. apply AGS; unfold AFer.sp1, LFRAME, DRSTACK in *; fold sp0 in H1 |- *; clear - H1 H2 Hk HSP' hS1; unfold DSTACK in *; lia. }
assert (FHX : AFgt.free_hyps W6 regs3 mem3 vra vs0 vs1 vs2 vs3 vs4).
{ constructor.
- exact Q4.
- subst vra. unfold w64. rewrite Z_to_bv_bv_unsigned. exact Hra.
- rewrite Q2, SP1. unfold AFer.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. lia.
- rewrite Q2, SP1. replace sp1 with (sp0 + (-5) * 16) by (unfold AFer.sp1, LFRAME; fold sp0; lia). rewrite Z_mod_plus_full. exact Hal.
- subst vra vs0 vs1 vs2 vs3 vs4. splits; apply u64_range.
-
rewrite restrict_mkst_fx. unfold AFgt.SS0, AFgt.SR0, sr_set. cbn [bv_eqb]. unfold AFgt.E0, w64. apply (entry_st_ok_full tfibsegs).
+ apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Q4].
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. fold (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). unfold AFgt.REG0, AFgt.R_STK. apply Forall_cons; [|apply Forall_nil].
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (AFgt.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2, SP1. unfold LFRAME.
split; [clear - Usp1; lia|]. split; [unfold AFer.sp1, LFRAME; fold sp0; clear - HSP' hS2; unfold kHighMemEnd in *; lia|]. split; [intros o Ho; lia|].
assert (CA : forall a k0 x, ew (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W6) mem3) (sp1 + a) (N.to_nat 8) x ->
YP09.chunk_ok tfibsegs (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) (mrestrict (w_H W6) mem3) sp1 (YP09.mkChunk a (CVal 8 (SOff k0 0)))).
{ intros a k0 x Hk0 Hr Hm. eapply chunk_ok_val; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr | cbn; lia | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia. }
repeat apply Forall_cons; try apply Forall_nil.
* apply (CA 72 32%nat vra); [reflexivity | subst vra; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs72]].
* apply (CA 64 33%nat vs0); [reflexivity | subst vs0; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs64]].
* apply (CA 56 34%nat vs1); [reflexivity | subst vs1; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs56]].
* apply (CA 48 35%nat vs2); [reflexivity | subst vs2; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs48]].
* apply (CA 40 36%nat vs3); [reflexivity | subst vs3; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs40]].
* apply (CA 32 37%nat vs4); [reflexivity | subst vs4; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs32]].
+   cbn [pairwise_disjoint all_disjoint AFgt.REG0]. split; exact I.
+ fold (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). split; [|split; exact I].
assert (AF : forall k0 Xv lo hi al, ew (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (SAL : sp1 mod 16 = 0) by (replace sp1 with (sp0 + (-5) * 16) by (unfold AFer.sp1, LFRAME; fold sp0; lia); rewrite Z_mod_plus_full; exact Hal).
cbn [AFgt.FFX f_atoms atoms_ok].
split. { apply (AF 2%nat sp1); [rewrite (AFgt.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2; reflexivity | exact Usp1 | | change (2 ^ 4) with 16; exact SAL | lia].
unfold AFer.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. lia. }
split. { apply (AF 32%nat vra); [reflexivity | subst vra; apply u64_range | pose proof (u64_range (getr regs 1)); subst vra; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 33%nat vs0); [reflexivity | subst vs0; apply u64_range | pose proof (u64_range (getr regs 8)); subst vs0; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 34%nat vs1); [reflexivity | subst vs1; apply u64_range | pose proof (u64_range (getr regs 9)); subst vs1; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 35%nat vs2); [reflexivity | subst vs2; apply u64_range | pose proof (u64_range (getr regs 18)); subst vs2; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 36%nat vs3); [reflexivity | subst vs3; apply u64_range | pose proof (u64_range (getr regs 19)); subst vs3; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split; [|exact I]. { apply (AF 37%nat vs4); [reflexivity | subst vs4; apply u64_range | pose proof (u64_range (getr regs 20)); subst vs4; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. } }
unfold cfg_at, raZ. rewrite <- (wvb_self md3) at 1. rewrite R1. unfold w64 at 2. rewrite (unsigned_lit_small 0x3323c) by (clear; lia).
eapply SRr_mono; [exact (AFh8.segX W6 regs3 mem3 md3 vra vs0 vs1 vs2 vs3 vs4 (m_vm_materialized md3) FHX)|].
intros W7 c7 _ (-> & regs4 & mat4 & -> & T2 & T1 & T8 & T9 & T18 & T19 & T20 & TS).
rewrite Q2, SP1 in T2. unfold LFRAME in T2.
exists regs4, mem3, (with_vm_backing (m_vm_lazy md3) mat4 md3). split; [subst vra; reflexivity|].
assert (CSx : forall z (r5 : bv 5), Z_to_bv 5 z = r5 -> getr regs4 r5 = getr regs r5 -> getr regs4 (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)) by (intros z r5 <- E; exact E).
assert (VIA3 : forall (r5 : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r5 -> In r5 AFgt.SREGS -> In r5 AFer.SREGS -> getr regs4 r5 = getr regs r5).
{ intros r5 z Hz Ez I1 I2. rewrite (TS r5 I1), (CS3' r5 z Hz Ez). apply CS. exact I2. }
split; [|split; [apply layout_le_refl | split; [exact WLE | split; [|split; [|split]]]]].
- apply (AR_model_same B ly X3 W6 mem3 md3); [exact AR3 | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
- intros r Hr. pose proof Hr as Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr'.
repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; subst r.
+ apply (CSx _ 2%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T2. unfold AFer.sp1, LFRAME. fold sp0. replace (sp0 - 80 + 80) with sp0 by lia. unfold sp0, w64. apply Z_to_bv_bv_unsigned.
+ apply (VIA3 3%bv 3 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 4%bv 4 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (CSx _ 8%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T8. subst vs0. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 9%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T9. subst vs1. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 18%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T18. subst vs2. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 19%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T19. subst vs3. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 20%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T20. subst vs4. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (VIA3 21%bv 21 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 22%bv 22 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 23%bv 23 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 24%bv 24 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 25%bv 25 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 26%bv 26 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 27%bv 27 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
- eapply same_io_trans; [apply same_io_with_vm_backing|]. eapply same_io_trans; [exact SIO | apply same_io_with_vm_backing].
-
intros a Ha NO NO3 NS NF. unfold ascratch, spZ in NS. fold sp0 in NS.
assert (NOS : ~ aowned B ly (AFey.S' X P R) a).
{ intros O. apply NO. exact (aowned_same_cf B ly X _ a (AFey.S'_chunks X P R) (AFey.S'_fs X P R) O). }
transitivity (aview tfibsegs H0 mem2 a).
+ apply FR3; [exact Ha | exact NOS | exact NO3 | | intros HE; apply NS; left; unfold AFer.sp1, LFRAME in HE; fold sp0 in HE; clear - HE; unfold DSTACK; lia].
intros [Hs|Hs]; apply NS; [left; unfold AFer.sp1, LFRAME, DRSTACK in Hs; fold sp0 in Hs; clear - Hs; unfold DSTACK; lia | right; exact Hs].
+ apply AG2; [exact Ha|]. intros HD.
destruct (AFey.D_owned B ly X _ M P R HL sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; left; exact O].
- intros a Ha. apply PRS6. unfold spZ in Ha. exact Ha.
Qed.
Lemma drain_body_unfold :
drain_body X X = (if qc_bytes gq + qc_bytes tq <=? kQuarantineMax then ret tt else recycle_body (transfer_g X)) XT.
Proof. unfold drain_body, bind, put. cbn [ibind]. reflexivity. Qed.
Theorem tfib_drain_arm : amreal tfibsegs (drain_body X X) W (cfg_at tfibsegs A_Drain regs mem md) (drain_leaf B ly X W regs mem md).
Proof.
pose proof (AFev.FH_ok B TB ly X W regs mem md PRE) as FH.
pose proof (AFer.sum_L B ly X W regs mem md PRE) as SL. pose proof (AFer.len_L B ly X W regs mem md PRE) as LL.
assert (WALK : (kQuarantineMax < qc_bytes gq + qc_bytes tq -> 2 * (kBatchBytes * Z.of_nat (length L)) <= qc_bytes gq + qc_bytes tq) ->
SRr tfibsegs W (cfg_at tfibsegs A_Drain regs mem md) (AFgj.postD W ly regs mem md gq tq)).
{ intros HM. unfold cfg_at, A_Drain. rewrite <- (wvb_self md) at 1.
assert (HM' : kQuarantineMax < AFgj.LBv gq tq -> 2 * (kBatchBytes * AFgj.LSZv gq tq) <= AFgj.LBv gq tq).
{ unfold AFgj.LBv, AFgj.GBv, AFgj.TBv, AFgj.LSZv, AFgj.GSZv, AFgj.TSZv. intros H1.
unfold AFer.L in HM. rewrite length_app, Nat2Z.inj_add in HM. exact (HM H1). }
destruct G as [|g0 G'] eqn:EG.
- apply (AFgg.segDE W ly regs mem md gq tq (m_vm_materialized md) FH); [exact EG | exact HM'].
- apply (AFgh.segDN W ly regs mem md gq tq (m_vm_materialized md) FH); [rewrite EG; discriminate | exact HM']. }
rewrite drain_body_unfold. unfold AFgj.postD, AFgj.LBv, AFgj.GBv, AFgj.TBv in WALK.
destruct (Z.leb_spec (qc_bytes gq + qc_bytes tq) kQuarantineMax) as [LE|GT].
-
cbn [amreal ret]. eapply SRr_mono; [exact (WALK ltac:(intros; lia))|]. intros W' c' _ HR. exact (FIN_a W' c' HR).
-
unfold recycle_body, mcheck. cbn [qc_list qc_bytes transfer_g].
destruct (Z.leb_spec (2 * (kBatchBytes * Z.of_nat (length (G ++ Tq)))) (qc_bytes gq + qc_bytes tq)) as [MC|MC].
2:{   unfold bind, fail. cbn [ibind amreal]. exact I. }
unfold bind at 1. unfold ret. cbn [ibind].
destruct (pop_batches 100000 (transfer_g X) []) as [g' P] eqn:EP.
pose proof (pop_batches_spec _ _ _ _ _ EP) as (P0 & EP0 & EL & EB). cbn [rev app] in EP0. subst P0. cbn [transfer_g qc_list qc_bytes] in EL, EB.
assert (LEN : (length (qc_list (transfer_g X)) < 100000)%nat).
{ cbn [transfer_g qc_list]. unfold AFer.zlen, AFer.L, EV_MAX in LL. apply Nat2Z.inj_lt. rewrite of_nat_100000. lia. }
pose proof (pop_batches_stop _ _ _ _ _ EP LEN) as STOP.
destruct g' as [R s]. cbn [qc_list qc_bytes] in EL, EB, STOP.
assert (HL : L = P ++ R) by exact EL.
assert (SR : sum_bytes R <= kQuarantineMax).
{ rewrite HL, sum_bytes_app in SL. destruct STOP as [S1|S1]; [unfold kQuarantineMin, kQuarantineMax in *; lia | subst R; cbn; unfold kQuarantineMax; lia]. }
unfold bind, modify. cbn [ibind].
change (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (AFey.S' X P R) || (replace (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (AFey.S' X P R) by (unfold AFey.S'; cbn [st_qglobal qc_bytes AFey.XT set_qglobal]; rewrite EB; reflexivity)).
apply amreal_after_SRr.
eapply SRr_bind; [exact (WALK ltac:(intros _; unfold AFer.L; exact MC))|]. intros W1 c1 _ H1.
pose proof (L0_LST W1 c1 H1) as H2.
eapply SRr_bind.
{ apply (AFer.LOOP B TB ly X W regs mem md PRE L [] 100000%nat W1 c1 H2 eq_refl); [rewrite SL; unfold kQuarantineMin, kQuarantineMax in *; lia | exact LEN]. }
intros W2 c2 _ H3. cbn beta zeta in H3. cbn [rev] in H3. rewrite SL in H3. change (AFer.L X) with (G ++ Tq) in H3. unfold transfer_g in EP. rewrite EP in H3. cbn [fst snd qc_list] in H3.
destruct (DRPRE P R W2 c2 H3 HL SR) as (regs2 & mem2 & mat & -> & -> & R2 & R1 & R13 & CS & MQ & PRS & SLOTS & AG & DPRE).
apply SRr_ret. eapply amreal_then_SRr; [exact (DR ly _ P W regs2 mem2 _ DPRE)|].
intros r W6 c6 HDL. exact (EPI P R regs2 mem2 mat r W6 c6 HL R2 R1 CS PRS SLOTS AG (proj1 DPRE) HDL).
Qed.
End f.
Theorem tfib_drain_ok : forall B, TfibSyms B -> tfib_dorecycle_spec B -> tfib_drain_spec B.
Proof. intros B TB DR ly X W regs mem md PRE. exact (tfib_drain_arm B TB DR ly X W regs mem md PRE). Qed.
End d.
