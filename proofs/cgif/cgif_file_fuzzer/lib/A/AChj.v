(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACkc ACj4 ACj8 ACj9 ACjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj3 ACj5 ACjc ACiz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACij ACi4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCib.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Lemma denot_and_ffff : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v <= 65535 ->
sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 65535)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536. rewrite (Z.mod_small v) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl  end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 _ Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
Lemma w_all_disjoint_ext_l : forall E r r' l,
YP09.r_base r' = YP09.r_base r -> YP09.r_lo r' = YP09.r_lo r -> YP09.r_hi r' = YP09.r_hi r ->
all_disjoint E r l -> all_disjoint E r' l.
Proof.
intros E r r' l Hb Hl Hh. induction l as [|x l IH]; cbn; [tauto|]. intros [H1 H2]. split; [|exact (IH H2)].
unfold extent_disjoint in *. rewrite Hb, Hl, Hh. exact H1.
Qed.
Lemma w_all_disjoint_ext_r : forall E y r r' l1 l2,
YP09.r_base r' = YP09.r_base r -> YP09.r_lo r' = YP09.r_lo r -> YP09.r_hi r' = YP09.r_hi r ->
all_disjoint E y (l1 ++ r :: l2) -> all_disjoint E y (l1 ++ r' :: l2).
Proof.
intros E y r r' l1 l2 Hb Hl Hh. induction l1 as [|x l1 IH]; cbn; intros [H1 H2]; (split; [|first [exact H2 | exact (IH H2)]]).
- unfold extent_disjoint in *. rewrite Hb, Hl, Hh. exact H1.
- exact H1.
Qed.
Lemma w_pairwise_disjoint_ext : forall E r r' l1 l2,
YP09.r_base r' = YP09.r_base r -> YP09.r_lo r' = YP09.r_lo r -> YP09.r_hi r' = YP09.r_hi r ->
pairwise_disjoint E (l1 ++ r :: l2) -> pairwise_disjoint E (l1 ++ r' :: l2).
Proof.
intros E r r' l1 l2 Hb Hl Hh. induction l1 as [|y l1 IH]; cbn; intros [H1 H2]; split.
- exact (w_all_disjoint_ext_l E r r' l2 Hb Hl Hh H1).
- exact H2.
- exact (w_all_disjoint_ext_r E y r r' l1 l2 Hb Hl Hh H1).
- exact (IH H2).
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section m.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma w_st_ok_add_chunk0 : forall E ss ms l1 nb lo hi wlo whi cs l2 c,
st_ok SEGS E ss ms -> ss_mem ss = l1 ++ YP09.mkRegion nb lo hi wlo whi cs :: l2 ->
regions_wf (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) = true ->
YP09.chunk_ok SEGS E (ms_mem ms) (base_val E nb) c ->
st_ok SEGS E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 nb lo hi wlo whi cs l2 c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrs Hwf' Hc.
rewrite Hrs in Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb as [|x l Hr Hl]; subst. apply Forall_app. split; [exact Ha|]. constructor; [|exact Hl].
unfold region_ok in Hr |- *. cbv zeta in Hr |- *. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in Hr |- *.
destruct Hr as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. constructor; [exact Hc | exact R4].
- exact (w_pairwise_disjoint_ext E (YP09.mkRegion nb lo hi wlo whi cs) (YP09.mkRegion nb lo hi wlo whi (c :: cs)) l1 l2 eq_refl eq_refl eq_refl Hpd).
Qed.
Lemma w_st_ok_add_chunk : forall E ss ms l1 nb lo hi wlo whi cs l2 c,
st_ok_pi SEGS VAL E ss ms -> ss_mem ss = l1 ++ YP09.mkRegion nb lo hi wlo whi cs :: l2 ->
regions_wf (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) = true ->
YP09.chunk_ok SEGS E (ms_mem ms) (base_val E nb) c ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 nb lo hi wlo whi cs l2 c HS Hrs Hwf' Hc. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0].
exact (w_st_ok_add_chunk0 E _ ms l1 nb lo hi wlo whi cs l2 c HS Hrs Hwf' Hc).
Qed.
Section o.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable wfn : Z.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis HXM : forall N M, 1 <= M <= N -> N <= 100000000 -> mo_malloc MT M + xm_rawadd XN M + mo_free MT <= xm_flush XN N.
Hypothesis HXMN : forall M, 1 <= M <= 100000000 -> 0 <= xn_rawadd XN M <= xm_rawadd XN M.
Hypothesis HTR : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0x2448) \/ (pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x1fd4) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x2124)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac upd_aboveF HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; first [ ltac Hb Hrg | revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac add_fact HS n lo hi Hv tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n (mkAF lo hi 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hv, unsigned_lit_small by tac; rewrite Z.pow_0_r, Z.mod_1_r; split; [tac | split; [reflexivity | clear; lia]])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n (mkAF lo hi 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hv, unsigned_lit_small by tac; rewrite Z.pow_0_r, Z.mod_1_r; split; [tac | split; [reflexivity | clear; lia]])) as HS3;
clear HS; rename HS3 into HS  end.
Ltac seat152 HS na top E60 Ena V152 sptac ttac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let l1 := eval vm_compute in (firstn il rs) in
let rt := eval vm_compute in (nth il rs got_regionP) in
let l2 := eval vm_compute in (skipn (S il) rs) in
lazymatch rt with YP09.mkRegion ?nb ?lo ?hi ?wlo ?whi ?cs =>
let HS3 := fresh "HS3" in
pose proof (w_st_ok_add_chunk Ev ssx msv l1 nb lo hi wlo whi cs l2 (YP09.mkChunk 152 (CVal 8 (SOff na 0))) HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(cbn [base_val]; rewrite ?ew_havoc_old by nat_side; rewrite E60, unsigned_lit_small by sptac;
apply (chunk_ok_val SEGS Ev _ _ 152 8 _ top);
[ cbn [sv_denot]; rewrite Ena, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn [Z.of_N Z.mul]; ttac | cbn; lia | exact V152 ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end | st_ok _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let l1 := eval vm_compute in (firstn il rs) in
let rt := eval vm_compute in (nth il rs got_regionP) in
let l2 := eval vm_compute in (skipn (S il) rs) in
lazymatch rt with YP09.mkRegion ?nb ?lo ?hi ?wlo ?whi ?cs =>
let HS3 := fresh "HS3" in
pose proof (w_st_ok_add_chunk Ev ssx msv l1 nb lo hi wlo whi cs l2 (YP09.mkChunk 152 (CVal 8 (SOff na 0))) HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(cbn [base_val]; rewrite ?ew_havoc_old by nat_side; rewrite E60, unsigned_lit_small by sptac;
apply (chunk_ok_val SEGS Ev _ _ 152 8 _ top);
[ cbn [sv_denot]; rewrite Ena, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn [Z.of_N Z.mul]; ttac | cbn; lia | exact V152 ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end  end.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Lemma fl_D1X_aux : fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B).
Proof.
intros RT0. fl_preludeX.
pose proof HINV as (Hk3 & Eab3 & (gen & E621 & Rgen) & E625 & (fb & Hfb & EB) & (w & h & top & left & E887 & E888 & E889 & E890 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & XD) & E621X & XF2 & MLE0).
pose proof HCUR as (_ & XCg & _ & _ & _ & _ & _ & XCimg & XClen & _). cbn in XCg.
unfold xgen3, xG in XF2. unfold xdims, xG in XD. cbn [c_s x_GPAL x_cur x_bef] in XF2, XD.
destruct (fl_diff_some _ cur bef ltac:(rewrite <- XCg; clear - Q3; lia) XF2) as (xb & ->).
pose proof (fl_tmp_diff _ cur xb w h top left XF2 XD) as XTMP.
cbn [c_i c_s] in Hfb. cbn [c_s] in Hlw, Hth.
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
assert (HW65 : cg_W s <= 65535) by (clear - R7 Hob241 Hob242 Hob253 Huar; lia).
assert (HH65 : cg_H s <= 65535) by (clear - R8 Hob241 Hob242 Hob253 Huar; lia).
assert (Hw65 : w <= 65535) by (clear - Hw1 Hl0 Hlw HW65 Hob241 Hob242 Hob253 Huar; lia). assert (Hh65 : h <= 65535) by (clear - Hh1 Ht0 Hth HH65 Hob241 Hob242 Hob253 Huar; lia).
assert (Hwh1 : 1 <= w * h) by (clear - Hw1 Hh1 Hob241 Hob242 Hob253 Huar; nia).
assert (HwhN : w * h <= N) by (rewrite HN; clear - Hw1 Hh1 Hl0 Hlw Ht0 Hth Hob241 Hob242 Hob253 Huar; nia).
assert (HWH : 1 <= w * h <= 100000000) by (clear - Hwh1 HwhN HNle Hob241 Hob242 Hob253 Huar; lia).
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (rewrite Eab3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hbef_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1fcc.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia). clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (@BV 5 23 I) (Z_to_bv 64 w) (denot_and_ffff Ev 887 w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E887) ltac:(clear - Hw1 Hw65 Hob241 Hob242 Hob253 Huar; lia)) R23;
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 h) (denot_and_ffff Ev 888 h ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E888) ltac:(clear - Hh1 Hh65 Hob241 Hob242 Hob253 Huar; lia)) R18 | st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 23 I) (Z_to_bv 64 w) (denot_and_ffff Ev 887 w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E887) ltac:(clear - Hw1 Hw65 Hob241 Hob242 Hob253 Huar; lia)) R23;
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 h) (denot_and_ffff Ev 888 h ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E888) ltac:(clear - Hh1 Hh65 Hob241 Hob242 Hob253 Huar; lia)) R18  end.
ws_pin HS (@BV 5 23 I) (SOff 887 0) R23 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E887).
ws_pin HS (@BV 5 10 I) (SOff 888 0) R18 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E888).
clear R23 R18. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x528cc.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia). clear_frames.
prreg HS (@BV 5 1 I) Rra. prreg HS (@BV 5 2 I) Rsp. prreg HS (@BV 5 3 I) Rgp. prreg HS (@BV 5 4 I) Rtp. prreg HS (@BV 5 8 I) Rs0.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia);
assert (EraX : raZ rg = (BASE + 0x1fd4)) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (h * w))
(denot_mul_hw Ev 888 887 h w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E888) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E887)
ltac:(clear - Hh1 Hh65 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hw1 Hw65 Hob241 Hob242 Hob253 Huar; lia)) Ra0 | st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (h * w))
(denot_mul_hw Ev 888 887 h w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E888) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E887)
ltac:(clear - Hh1 Hh65 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hw1 Hw65 Hob241 Hob242 Hob253 Huar; lia)) Ra0  end.
replace (h * w) with (w * h) in Ra0 by (apply Z.mul_comm).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi Hob241 Hob242 Hob253 Huar; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ]  end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : st_nev S3 < EV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk3 Hob241 Hob242 Hob253 Huar; lia).
pmkst HS.
ppcs.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (AMALLOC4 W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k (w * h) (sp1 - spZ regs) (Z_to_bv 64 (BASE + 0x1fd4)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- unfold MALLOC_MAX. clear - HWH. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_FLUSH in Hlive. clear - Hlive HWH. lia.
- rewrite EspX. clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
- rewrite FFS. unfold ASTACK. clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- exact HEVc.
- apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | exact Es0X | rewrite EraX; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia].
- apply (HTR (pc_malloc_ra0 (as_code B)) (BASE + 0x1fd4)); [exact Hctx | exact EraX | right; left; split; reflexivity].
-
eapply (mok_station MT S S3 (xm_flush XN N) 0 _ MLAW HMOK MLE0); [apply (mo_malloc_nonneg MT MLAW); clear - HWH; lia|].
pose proof (HXM N (w * h) ltac:(clear - HWH HwhN; lia) HNle) as BM. pose proof (HXMN (w * h) HWH) as BMN. pose proof (mo_free_nonneg MT MLAW) as F0.
clear - BM BMN F0. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hnz4 & Eab4x & HK4x & MLE4).
mresX Hnz4 Eab4x HK4x Hres. clear Eab4x HK4x.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hres by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
pose proof (proj1 HJ4) as HAR4.
clear HUP. assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (2, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
destruct Hres as [(Hres0 & Eab4 & HK) | (Hres4096 & Eab4 & HK)].
+   exfalso. clear - Hres0 Hnz4. lia.
+
assert (Hrq : req_size (w * h) = w * h) by (unfold req_size; destruct (Z.eqb_spec (w * h) 0); [exfalso; clear - HWH e Hob241 Hob242 Hob253 Huar; lia | reflexivity]).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [exfalso; clear - HWH HwhN e Hob241 Hob242 Hob253 Huar; lia | reflexivity]).
assert (Hres_in : In (res, w * h) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hbef3).
assert (Himg4 : In (fr_img f, N) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Himg3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (w * h) HAR4 Hres_in) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & Hnpres & _). pose proof (proj1 Hnh_ia) as Hnh. rewrite Hrq in Hnceil, Hnpres.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR4 Hres_in) as Hnh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N HAR4 Himg4) as (_ & _ & _ & _ & Hipres4 & _). rewrite HrqN in Hipres4.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (w * h) HJ3 HAR4 Eab4 ltac:(clear - HWH Hob241 Hob242 Hob253 Huar; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, w * h) blc -> 0 <= i < w * h ->
awr_byte TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24)] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq ii Hbl Hiq. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (w * h) blc ii lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HWH Hob241 Hob242 Hob253 Huar; lia) Hbl ltac:(rewrite Hrq; exact Hiq)). }
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ [(res, w * h)])) by (rewrite Eab4, Eab3; apply Permutation_refl).
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ res (w * h) 2 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 2) with 256 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) g CGIF_SIZE HAR4 HPerm4 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG. rewrite Hrq in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_ptr f) FRAME_SIZE HAR4 HPerm4 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC. rewrite Hrq in HdPC.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_ptr fb) FRAME_SIZE HAR4 HPerm4 Hbef_in) as HdPB. change (req_size FRAME_SIZE) with 40 in HdPB. rewrite Hrq in HdPB.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_img f) N HAR4 HPerm4 Himg_in) as HdPI. rewrite Hrq, HrqN in HdPI.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPB Hrq Hob241 Hob242 Hob253 Huar; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; clear - Ha Hn Hnh Hnh_ia Hrq HF8lo HF8c HFceil C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha Hob241 Hob242 Hob253 Huar; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; clear - Ha Hn HdPF Hrq Hob241 Hob242 Hob253 Huar; lia
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot3 | exact Kgot4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell3 | exact Kcell4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kguar3 | exact Kguar4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 59%nat) _ _ _ _ _) =>
let AGx := lazymatch goal with A : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => A end in
let Bv := rnB in apply (region_kept_val_at Ex _ _ 59%nat (as_uar_cell Bv) 4 1); [evalE AGx | exact Kuar3 | exact Kuar4 | lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPG Hrq Hob241 Hob242 Hob253 Huar; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPC Hrq Hob241 Hob242 Hob253 Huar; lia ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
prreg HS (@BV 5 10 I) Rres. rewrite Ha04 in Rres. symmetry in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (HPTR 4) HS
ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres; unfold w64; rewrite unsigned_lit_small by (clear - Hnh Hnceil HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia);
change (2 ^ 4) with 16; clear - Hnh Hnceil Hn16 HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK FLBspan 0x2038.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia). clear_frames.
lazymatch goal with HS0 : st_ok_pi _ _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HSx : st_ok_pi _ _ _ _ _ |- _ => rename HSx into HS end.
prreg HS (@BV 5 2 I) Rsp. prreg HS (@BV 5 3 I) Rgp. prreg HS (@BV 5 4 I) Rtp.
prreg HS (@BV 5 18 I) R19. prreg HS (@BV 5 23 I) R23. prreg HS (@BV 5 24 I) R26. prreg HS (@BV 5 27 I) R27.
rewrite E887 in R23. rewrite E40 in R26. rewrite Rres in R27.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (@BV 5 20 I) (Z_to_bv 64 h) (denot_and_ffff Ev 888 h E888 ltac:(clear - Hh1 Hh65 Hob241 Hob242 Hob253 Huar; lia)) R18;
rreg_by HS (@BV 5 19 I) (Z_to_bv 64 w) (denot_and_ffff Ev 887 w E887 ltac:(clear - Hw1 Hw65 Hob241 Hob242 Hob253 Huar; lia)) R19s;
rreg_by HS (@BV 5 21 I) (Z_to_bv 64 (fr_img f + left)) (denot_add_atoms Ev 51 890 (fr_img f) left E51 E890 ltac:(clear - Hi4096 Hob241 Hob242 Hob253 Huar; lia) Hl0 ltac:(rewrite HrqN in Hiceil; clear - Hiceil Hl0 Hlw Hw1 HW65 C1 HWH HwhN Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) R20;
rreg_by HS (@BV 5 22 I) (Z_to_bv 64 (top * cg_W s)) (denot_mul_hw Ev 889 40 top (cg_W s) E889 E40 ltac:(clear - Ht0 Hth Hh1 HH65 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - HW1 HW65 Hob241 Hob242 Hob253 Huar; lia)) R21 | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch type of Rres with ew _ ?nx = _ =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 60 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 160 (SOff nx 0) res ltac:(cbn [sv_denot]; rewrite Rres, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; clear - Hnh Hnceil HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V160;
slot 168 (SOff 51 0) (fr_img f) ltac:(cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; rewrite HrqN in Hiceil; clear - Hi4096 Hiceil C1 HWH HwhN Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V168 end end;
clear HRloc  end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspL : spZ rg = sp1) by (unfold spZ; rewrite Rsp; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia) end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (fl_cpyX B LAWS AMEMCPY (Z.to_nat h) 0 W4 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 _ ly S W mem md ly4 S4 _ fpos
res (fr_img f) N w h top left (cg_W s) (cg_H s)) end.
- rewrite Z2Nat.id by (clear - Hh1 Hob241 Hob242 Hob253 Huar; lia). clear; lia.
- clear - Hh1 Hob241 Hob242 Hob253 Huar; lia.
- exact Hw1. - exact Hl0. - exact Hlw. - exact Hh1. - exact Ht0. - exact Hth.
- clear - HW1 HW65 Hob241 Hob242 Hob253 Huar; lia. - exact HH65. - symmetry; exact HN. - exact HNle.
- exact HJ4.
- exact Hres_in. - exact Himg4.
- intros blc lyq ownq a Hbl Ha. replace a with (res + (a - res)) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). apply (Ares blc lyq ownq (a - res) Hbl). clear - Ha Hob241 Hob242 Hob253 Huar; lia.
- rewrite Hrq, HrqN. clear - HdPI Hob241 Hob242 Hob253 Huar; lia.
- exact EspL. - exact Hsp1. - exact Hsp1al16.
- rewrite Rgp. rewrite (AG 3%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
- rewrite Rtp. rewrite (AG 4%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
- rewrite R18. f_equal. clear; lia.
- exact R19.
- exact R20.
- rewrite R21. f_equal. clear; lia.
- exact R23. - exact R26.
- rewrite R27. unfold w64. f_equal. clear; lia.
- exact R19s. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & Hout5 & Hpres5 & XO5 & XC5).
assert (HdCI : fr_ptr f + 40 <= fr_img f \/ fr_img f + req_size N <= fr_ptr f).
{ destruct (frame_blocks_front g s N rest i f Hf) as (rci & HPci).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR (Permutation_trans HPerm HPci)) as Hd.
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd. change (req_size FRAME_SIZE) with 40 in Hd. exact Hd. }
assert (XG5 : garr8 SEGS (mrestrict (w_H W4) mem5) res (YO07.window (cg_W s) (YO07.f_img cur) w h top left)).
{ lazymatch type of XC5 with forall j kk, _ -> _ -> _ = aview _ _ ?m1 _ =>
apply (cpy_garr8 SEGS (w_H W4) m1 mem5 res (fr_img f) w h top left (cg_W s) (cg_H s) (YO07.f_img cur)); [| rewrite XClen; exact HN | clear - HW1; lia | clear - HH1; lia
| exact Hw1 | exact Hl0 | exact Hlw | exact Hh1 | exact Ht0 | exact Hth | intros j kk Hj Hkk; apply XC5; [clear - Hj; lia | exact Hkk]] end.
eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_img f) N (fr_img f) (YO07.f_img cur) HJ4);
[ exact Himg_in | exact Himg4 | clear; lia | rewrite XClen, HrqN; clear; lia
| intros a Ha (r & Hr0 & Hr); cbn [In] in Hr0; destruct Hr0 as [<- | []]; cbn [fst snd] in Hr; rewrite XClen in Ha; rewrite HrqN in HdCI; clear - Ha Hr HdCI; lia
| exact XCimg ]. }
clear HdCI XO5 XC5. xnew_facts F (fr_ptr f) res (w * h) Hnh_ia Hnh_img Hrq Hn4096 Hnceil HdPF HdPC HWH XBBr.
assert (XLW : Z.of_nat (length (YO07.window (cg_W s) (YO07.f_img cur) w h top left)) = w * h).
{ destruct (window_specZ (cg_W s) (cg_H s) (YO07.f_img cur) w h top left ltac:(clear - HW1; lia) ltac:(clear - HH1; lia) ltac:(rewrite XClen; exact HN) Hw1 Hl0 Hlw Hh1 Ht0 Hth) as [WL _].
rewrite WL. clear - HWH. lia. }
clear Rsp Rgp Rtp R18 R19 R19s R20 R21 R23 R26 R27 EspL.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H W4) mem5) CPY_CLOB 0x205c [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YP09.r_base r) + YP09.r_lo r /\ base_val Ev (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= res \/ res + w * h <= base_val Ev (YP09.r_base r) + YP09.r_lo r) /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= sp1 - ESTACK \/ sp1 <= base_val Ev (YP09.r_base r) + YP09.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with Himg : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite Himg end; rewrite ?RF, ?E60, ?E529; rewrite ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 12%nat), ?(AG 32%nat) by lia; rewrite ?Usp, ?E10, ?E11, ?E12, ?E32;
rewrite ?unsigned_lit_small by (unfold SB; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 C1 C3 HFceil HFhigh HF8lo HF8hi Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia);
unfold CGIF_SIZE, FRAME_SIZE, SB, ESTACK;
clear - HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hshi H47 Hsp1 Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2 Hbceil C1 C2 C3 C4 C5 FFS Hn4096 Hnh Hnh_img Hnh_ia Hrq Hnceil HWH HdPG HdPC HdPB HdPF Hob241 Hob242 Hob253 Huar;
unbox; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; first [zone_lia | match goal with |- ?g => idtac "HRK-FAIL" g; fail end]
| specialize (HS2 HK5 (regions_kept_out2 Ev (w_H W4) (ms_mem msX) mem5 res (res + w * h) (sp1 - ESTACK) sp1 _ Hout5 Hpres5 HRK)) ] end | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H W4) mem5) CPY_CLOB 0x205c [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YP09.r_base r) + YP09.r_lo r /\ base_val Ev (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= res \/ res + w * h <= base_val Ev (YP09.r_base r) + YP09.r_lo r) /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= sp1 - ESTACK \/ sp1 <= base_val Ev (YP09.r_base r) + YP09.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with Himg : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite Himg end; rewrite ?RF, ?E60, ?E529; rewrite ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 12%nat), ?(AG 32%nat) by lia; rewrite ?Usp, ?E10, ?E11, ?E12, ?E32;
rewrite ?unsigned_lit_small by (unfold SB; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 C1 C3 HFceil HFhigh HF8lo HF8hi Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia);
unfold CGIF_SIZE, FRAME_SIZE, SB, ESTACK;
clear - HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hshi H47 Hsp1 Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2 Hbceil C1 C2 C3 C4 C5 FFS Hn4096 Hnh Hnh_img Hnh_ia Hrq Hnceil HWH HdPG HdPC HdPB HdPF Hob241 Hob242 Hob253 Huar;
unbox; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; first [zone_lia | match goal with |- ?g => idtac "HRK-FAIL" g; fail end]
| specialize (HS2 HK5 (regions_kept_out2 Ev (w_H W4) (ms_mem msX) mem5 res (res + w * h) (sp1 - ESTACK) sp1 _ Hout5 Hpres5 HRK)) ] end  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
lazymatch type of HUP with forall a, _ -> aview _ _ ?m4 a = _ =>
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem5 a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (Hout5 a); [apply HUP; exact Ha | clear - Ha Hbot Hslo Hceil Hstk0 C1 FFS Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hnceil HWH C1 Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hsp1 Hob241 Hob242 Hob253 Huar; unfold ESTACK; lia]) end.
clear HUP. rename HUP5 into HUP.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
clear Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ5 Kgot4 Kcell4 Kguar4 Kuar4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 0x20a4.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
lazymatch goal with HFr : frame_of _ _ _ _ |- SRr _ _ (mkCfg ?msn _) _ => xblk_move HFr XG5 msn end.
clear_frames.
lazymatch goal with HS0 : st_ok_pi _ _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
prreg HS (23%bv : bv 5) Q23; prreg HS (27%bv : bv 5) Q27;
rewrite Rres in Q23; rewrite E888 in Q27;
add_atom_win HS 679%nat (Z_to_bv 64 w) E679;
rechunk_off HS 60%nat 168 (SOff 679 0) ltac:(rewrite !sv_denot_SOff0; rewrite E679; rewrite ?ew_havoc_above by nat_side; first [rewrite E887; reflexivity | match goal with |- ?g => idtac "RC168" g; fail end]) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom_win HS 680%nat (Z_to_bv 64 left) E680;
rechunk_off HS 60%nat 144 (SOff 680 0) ltac:(rewrite !sv_denot_SOff0; rewrite E680; rewrite ?ew_havoc_above by nat_side; first [rewrite E890; reflexivity | match goal with |- ?g => idtac "RC144" g; fail end]) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom_win HS 681%nat (Z_to_bv 64 top) E681;
rechunk_off HS 60%nat 152 (SOff 681 0) ltac:(rewrite !sv_denot_SOff0; rewrite E681; rewrite ?ew_havoc_above by nat_side; first [rewrite E889; reflexivity | match goal with |- ?g => idtac "RC152" g; fail end]) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join_win HS ss_T0 682%nat fl_T0_deads_bv ltac:(idtac;
ra_join_val HS 682%nat 0%nat Q23 E682; ra_join_val HS 682%nat 2%nat Q27 E684;
ra_join_fact HS 679%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E679; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hw1 Hw65 Hob241 Hob242 Hob253 Huar; lia); clear - Hw1 Hw65 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 680%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E680; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hl0 Hlw Hw1 HW65 Hob241 Hob242 Hob253 Huar; lia); clear - Hl0 Hlw Hw1 HW65 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 681%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E681; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Ht0 Hth Hh1 HH65 Hob241 Hob242 Hob253 Huar; lia); clear - Ht0 Hth Hh1 HH65 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 684%nat (mkAF 1 65535 0) ltac:(rewrite E684; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hh1 Hh65 Hob241 Hob242 Hob253 Huar; lia); clear - Hh1 Hh65 Hob241 Hob242 Hob253 Huar; lia));
fl_handX RT0 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; repeat (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists res, w, h, top, left. cbn [c_s c_ly c_S c_regs c_f].
split; [rewrite E682; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E679; reflexivity|].
split; [rewrite E684; reflexivity|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E681; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E680; reflexivity|].
split; [clear - Hnh Hnceil HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
assert (Hnz : res <> 0) by (clear - Hnh; lia).
split.
{ right. split; [clear - Hnh C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [first [clear - Hk3 Hob241 Hob242 Hob253 Huar; lia | match goal with |- ?g => idtac "KGOAL" g end]|].
unfold fl_tmpblkX, fl_FP0. cbn [c_ly c_S c_regs c_f c_s].
split; [split; [exact Hnh | rewrite <- Hrq; exact (zone2_of_app _ _ Hnh_ia Hnh_img)]|]. split; [clear - Hnceil HWH C1 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [exact Hn16|].
split; [first [rewrite Eab4, Eab3; reflexivity | match goal with |- ?g => idtac "D-ABL" g end]|].
split; [exact Ares | exact Tres]. }
unfold xdims, xtmp, xG. cbn [c_s c_S x_GPAL x_cur x_bef]. rewrite XTMP.
split; [exact XD|]. split; [intros _; exact XG5|]. split; [intros Hp0; exfalso; exact (Hnz Hp0)|]. split; [exact XLW|].
unfold xmacc. rewrite (proj2 (Z.eqb_neq res 0) Hnz).
exact (mle_station MT S S3 S4 0 _ MLAW MLE0 MLE4).
Qed.
Lemma fl_D1X : fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B).
Proof. exact fl_D1X_aux. Qed.
Ltac seat160 HS na top E60 Ena V160 sptac ttac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let l1 := eval vm_compute in (firstn il rs) in
let rt := eval vm_compute in (nth il rs got_regionP) in
let l2 := eval vm_compute in (skipn (S il) rs) in
lazymatch rt with YP09.mkRegion ?nb ?lo ?hi ?wlo ?whi ?cs =>
let HS3 := fresh "HS3" in
pose proof (w_st_ok_add_chunk Ev ssx msv l1 nb lo hi wlo whi cs l2 (YP09.mkChunk 160 (CVal 8 (SOff na 0))) HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(cbn [base_val]; rewrite ?ew_havoc_old by nat_side; rewrite E60, unsigned_lit_small by sptac;
apply (chunk_ok_val SEGS Ev _ _ 160 8 _ top);
[ cbn [sv_denot]; rewrite Ena, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn [Z.of_N Z.mul]; ttac | cbn; lia | exact V160 ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end | st_ok _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let l1 := eval vm_compute in (firstn il rs) in
let rt := eval vm_compute in (nth il rs got_regionP) in
let l2 := eval vm_compute in (skipn (S il) rs) in
lazymatch rt with YP09.mkRegion ?nb ?lo ?hi ?wlo ?whi ?cs =>
let HS3 := fresh "HS3" in
pose proof (w_st_ok_add_chunk Ev ssx msv l1 nb lo hi wlo whi cs l2 (YP09.mkChunk 160 (CVal 8 (SOff na 0))) HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(cbn [base_val]; rewrite ?ew_havoc_old by nat_side; rewrite E60, unsigned_lit_small by sptac;
apply (chunk_ok_val SEGS Ev _ _ 160 8 _ top);
[ cbn [sv_denot]; rewrite Ena, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn [Z.of_N Z.mul]; ttac | cbn; lia | exact V160 ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end  end.
Ltac d1_joinX RD1 w h top left Qw Qt Ql wtac htac ttac ltac_ :=
let E887 := fresh "E887" in let E888 := fresh "E888" in let E889 := fresh "E889" in let E890 := fresh "E890" in
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
add_atom HS 887%nat (Z_to_bv 64 w) E887; add_fact HS 887%nat 1 65535 E887 wtac;
add_atom HS 888%nat (Z_to_bv 64 h) E888; add_fact HS 888%nat 1 65535 E888 htac;
add_atom HS 889%nat (Z_to_bv 64 top) E889; add_fact HS 889%nat 0 65535 E889 ttac;
add_atom HS 890%nat (Z_to_bv 64 left) E890; add_fact HS 890%nat 0 65535 E890 ltac_;
norm_ss HS;
rechunk_off HS 516%nat 112 (SOff 889 0) ltac:(rewrite !sv_denot_SOff0; rewrite ?ew_havoc_old by nat_side; rewrite E889; cbn [sv_denot]; rewrite ?ew_havoc_old by nat_side;
first [reflexivity | lazymatch goal with E : ew _ 862 = _ |- _ => rewrite E; reflexivity end | match goal with |- ?g => idtac "RECHUNK112" g end]);
rechunk_off HS 516%nat 128 (SOff 890 0) ltac:(rewrite !sv_denot_SOff0; rewrite ?ew_havoc_old by nat_side; rewrite E890; cbn [sv_denot]; rewrite ?ew_havoc_old by nat_side;
first [reflexivity | lazymatch goal with E : ew _ 863 = _ |- _ => rewrite E; reflexivity end | match goal with |- ?g => idtac "RECHUNK128" g end]);
rechunk_off HS 60%nat 160 (SOff 888 0) ltac:(rewrite !sv_denot_SOff0; rewrite ?ew_havoc_old by nat_side; rewrite E888; rewrite ?ew_havoc_old by nat_side;
first [lazymatch goal with E : ew _ 880 = _ |- _ => rewrite E; reflexivity end | match goal with |- ?g => idtac "RECHUNK160" g end]);
ws_pin HS (@BV 5 26 I) (SOff 887 0) Qw ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_havoc_old by nat_side; exact E887);
ws_pin HS (@BV 5 27 I) (SOff 889 0) Qt ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_havoc_old by nat_side; exact E889);
ws_pin HS (@BV 5 23 I) (SOff 890 0) Ql ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_havoc_old by nat_side; exact E890);
ra_join HS ss_D1 891%nat fl_D1_deads_bv ltac:(idtac);
fl_handX RD1 HS end.
Lemma fl_DdX_aux : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B).
Proof.
intros RD1. fl_preludeX.
pose proof HINV as (Hk3 & Eab3 & (gen & E621 & Rgen) & E625 & (fb & Hfb & EB) & (w & h & top & left & E861 & V160 & E862 & E863 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & XD) & E621X & XF2 & MLE0).
cbn [c_i c_s] in Hfb. cbn [c_s] in Hlw, Hth. cbn [c_sp1] in V160.
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
assert (HW65 : cg_W s <= 65535) by (clear - R7 Hob241 Hob242 Hob253 Huar; lia).
assert (HH65 : cg_H s <= 65535) by (clear - R8 Hob241 Hob242 Hob253 Huar; lia).
add_fact HS 861%nat 1 65535 E861 ltac:(clear - Hw1 Hl0 Hlw HW65 Hob241 Hob242 Hob253 Huar; lia).
add_fact HS 862%nat 0 65535 E862 ltac:(clear - Hh1 Ht0 Hth HH65 Hob241 Hob242 Hob253 Huar; lia).
add_fact HS 863%nat 0 65535 E863 ltac:(clear - Hw1 Hl0 Hlw HW65 Hob241 Hob242 Hob253 Huar; lia).
norm_ss HS.
add_atom HS 880%nat (Z_to_bv 64 h) E880. add_fact HS 880%nat 1 65535 E880 ltac:(clear - Hh1 Ht0 Hth HH65 Hob241 Hob242 Hob253 Huar; lia).
seat160 HS 880%nat h E60 E880 V160 ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hh1 Ht0 Hth HH65 Hob241 Hob242 Hob253 Huar; lia).
rebase_goal.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1fb8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
prreg HS (@BV 5 26 I) Qw; prreg HS (@BV 5 27 I) Qt; prreg HS (@BV 5 23 I) Ql end.
rewrite E861 in Qw. rewrite E862 in Qt. rewrite E863 in Ql.
d1_joinX RD1 w h top left Qw Qt Ql ltac:(clear - Hw1 Hl0 Hlw HW65 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hh1 Ht0 Hth HH65 Hob241 Hob242 Hob253 Huar; lia)
ltac:(clear - Hh1 Ht0 Hth HH65 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hw1 Hl0 Hlw HW65 Hob241 Hob242 Hob253 Huar; lia).
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; repeat (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split.
{ exists w, h, top, left. cbn [c_s].
split; [rewrite 4 ew_havoc_old by (clear; lia); exact E887|].
split; [rewrite 3 ew_havoc_old by (clear; lia); exact E888|].
split; [rewrite 2 ew_havoc_old by (clear; lia); exact E889|].
split; [rewrite 1 ew_havoc_old by (clear; lia); exact E890|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
exact XD. }
split; [rewrite !ew_havoc_old by (clear; lia); exact E621X | split; [exact XF2 | exact MLE0]].
Qed.
Lemma fl_DdX : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B).
Proof. exact fl_DdX_aux. Qed.
Lemma fl_DiX_aux : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMSi (INV_DIMSiX MT B).
Proof.
intros RD1. fl_preludeX.
unfold INV_DIMSi in HINV. cbn [c_ly c_S c_s c_i c_sp1] in HINV.
pose proof HINV as ((Hk3 & Eab3 & (gen & E621 & Rgen) & E625 & (fb & Hfb & EB) & V160) & XD & E621X & XF2 & MLE0).
cbn [c_i c_s] in Hfb. cbn [c_sp1] in V160.
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
add_atom HS 880%nat (Z_to_bv 64 1) E880. add_fact HS 880%nat 1 65535 E880 ltac:(clear; lia).
seat160 HS 880%nat 1 E60 E880 V160 ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear; lia).
rebase_goal.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1fb8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
prreg HS (@BV 5 26 I) Qw; prreg HS (@BV 5 27 I) Qt; prreg HS (@BV 5 23 I) Ql end.
d1_joinX RD1 1 1 0 0 Qw Qt Ql ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia).
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; repeat (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split.
{ exists 1, 1, 0, 0. cbn [c_s].
split; [rewrite 4 ew_havoc_old by (clear; lia); exact E887|].
split; [rewrite 3 ew_havoc_old by (clear; lia); exact E888|].
split; [rewrite 2 ew_havoc_old by (clear; lia); exact E889|].
split; [rewrite 1 ew_havoc_old by (clear; lia); exact E890|].
split; [clear; lia|]. split; [clear; lia|]. split; [clear - HW1; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear - HH1; lia|].
exact XD. }
split; [rewrite !ew_havoc_old by (clear; lia); exact E621X | split; [exact XF2 | exact MLE0]].
Qed.
Lemma fl_DiX : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMSi (INV_DIMSiX MT B).
Proof. exact fl_DiX_aux. Qed.
Lemma fl_DX : fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B).
Proof. intros RT0. exact (fl_DdX_aux (fl_D1X_aux RT0)). Qed.
End o.
End m.
End d.
