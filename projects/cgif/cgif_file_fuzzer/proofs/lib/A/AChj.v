(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACkc ACj4 ACj8 ACj9 ACjm.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj3 ACj5 ACjc ACiz.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACij ACi4.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChy.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCib.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Proof using TL LAWS AMEMCPY TLF MLAW AMALLOC4 HXM HXMN HTR.
intros NextT0. clear ML AMALLOC AIL MLAWF HDEEP RO. fl_preludeX.
destruct HINV as (Kle0 & Blk3 & (gv & G621 & Grng) & Np625 & (fb & Bef) & (wv & hv & tv & lv & Aw887 & Ah888 & At889 & Al890 & Wlo & Llo & LWhi & Hlo & Tlo & THhi & Dims) & G621x & Gflag & Meter).
assert (InG3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hing).
assert (InC3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hcur_in).
assert (InP3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hpf_in).
fl_blocks3X InG3 InC3 InP3. fold F in HdFG, HdFC.
assert (WHn : 1 <= wv * hv <= N) by (clear - Wlo Llo LWhi Hlo Tlo THhi HN R7 R8; nia).
assert (Wsp1 : 0 <= sp1 < 2 ^ 64) by (clear - Hsp1 Hslo Hceil Hshi H47 C1 FFS; lia).
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
1: awrFL AG fpos F EFA3.
clear_frames.
prreg HS (2%bv : bv 5) Rsp. prreg HS (1%bv : bv 5) Rra. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) (wv * hv) ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
rewrite Z.mul_comm; apply (U_mul_small1 Ex _ _ hv wv);
[ apply (U_and16 Ex _ hv); [apply (U_atom Ex 888 hv Ah888) | ]
| apply (U_and16 Ex _ wv); [apply (U_atom Ex 887 wv Aw887) | ] | | | ];
clear - Wlo Llo LWhi Hlo Tlo THhi HN HNle R7 R8; nia end) Ra0.
pmkst HS. ppcs.
assert (Bsp : bv_unsigned (getr (ms_regs ms) 2) = sp1) by (rewrite Rsp, E60; exact (unsigned_lit_small sp1 Wsp1)).
assert (Bra : raZ (ms_regs ms) = BASE + 8148) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE; lia).
assert (Bgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Rgp, (AG 3%nat), (EE 3%nat 3%bv eq_refl) by nat_side; exact Hgp).
assert (Btp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Rtp, (AG 4%nat), (EE 4%nat 4%bv eq_refl) by nat_side; exact Htp).
assert (Sp0E : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by nat_side; exact Usp).
assert (Bs0 : s0Z (ms_regs ms) = spZ regs) by (unfold s0Z; rewrite Rs0; exact Sp0E).
pose proof (proj1 (proj2 HJ3)) as Lay3. destruct Lay3 as (_ & _ & _ & _ & _ & _ & _ & _ & Top3 & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Nev3 & _ & Above3 & _).
lazymatch type of HS with st_ok _ _ ?ssm _ =>
let r2 := eval vm_compute in (nth 4 (ss_mem ssm) got_regionP) in
pose proof (st_ok_region_nth E ssm _ 4 r2 HS ltac:(vm_compute; reflexivity)) as Reg2 end.
pose proof (slot_of_region E _ (spZ regs) _ (-104) 0 (-104) 0 (-8) (SOff 1 0) (raZ regs) Reg2 Sp0E
ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
ltac:(rewrite sv_denot_SOff0, (AG 1%nat), (EE 1%nat 1%bv eq_refl) by nat_side; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
(u64_range (getr regs 1))) as SlotRa.
pose proof (slot_of_region E _ (spZ regs) _ (-104) 0 (-104) 0 (-16) (SOff 8 0) (s0Z regs) Reg2 Sp0E
ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
ltac:(rewrite sv_denot_SOff0, (AG 8%nat), (EE 8%nat 8%bv eq_refl) by nat_side; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
(u64_range (getr regs 8))) as SlotS0.
cbn [ms_mem restrict mkst] in SlotRa, SlotS0.
assert (Chain1 : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch)).
{ apply (achain_push ly3 (aview SEGS (w_H W) mem)).
- exact (achain_ly_top ly ly3 _ _ _ _ Top3 Hch).
- rewrite Top3. clear - Htop2 H47. lia.
- intros a Ha. apply Above3; clear - Ha Hceil Hslo FFS C1; lia.
- replace (spZ regs - 8) with (spZ regs + -8) by ring. exact (rdword_of_val_mem _ _ _ _ _ SlotRa (u64_range (getr regs 1))).
- replace (spZ regs - 16) with (spZ regs + -16) by ring. exact (rdword_of_val_mem _ _ _ _ _ SlotS0 (u64_range (getr regs 8))).
- exact Hra4.
- clear - Hceil Hslo FFS; lia.
- clear - Hal16. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hal16 as [q Hq]. exists (2 * q). lia.
- rewrite Top3. clear - Htop32. lia.
- clear - Hsp1. lia. }
assert (Pre1 : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (ms_regs ms) ((spZ regs, raZ regs, s0Z regs) :: ch)).
{ apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ (ms_regs ms) Chain1); [unfold spZ; rewrite Bsp; clear - Hsp1 Hceil Hslo FFS; lia | exact Bs0 | rewrite Bra; clear - PBLO; lia]. }
assert (Trace1 : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B))
by exact (HTR (pc_malloc_ra0 (as_code B)) (BASE + 8148) (ms_regs ms) regs ch Hctx Bra (or_intror (or_introl (conj eq_refl eq_refl)))).
assert (Budget1 : mo_ok MT S3 (mo_malloc MT (wv * hv))).
{ pose proof (HXM N (wv * hv) WHn HNle) as Xm. pose proof (HXMN (wv * hv) ltac:(clear - WHn HNle; lia)) as Xn.
pose proof (mo_free_nonneg MT MLAW) as Fr0. pose proof (mo_malloc_nonneg MT MLAW (wv * hv) ltac:(clear - WHn; lia)) as Ml0.
apply (mok_station MT S S3 (xm_flush XN N) 0 (mo_malloc MT (wv * hv)) MLAW HMOK Meter Ml0). clear - Xm Xn Fr0. lia. }
assert (Live1 : blocks_bytes S3 + wv * hv <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Blk3, <- (blocks_bytes_bsum B ly S). clear - Hlive WHn HNle. unfold LIVE_FLUSH in Hlive. lia. }
eapply SRr_bind.
{ apply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 W3 (ms_regs ms) (ms_mem ms) TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24)]
ly S W mem md [(2, fpos)] ly3 S3 _ k (wv * hv) (sp1 - spZ regs) (Z_to_bv 64 (BASE + 8148)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Ra0).
- unfold MALLOC_MAX. clear - WHn HNle. lia.
- exact Live1.
- unfold spZ at 1. rewrite Bsp. ring.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1. lia.
- unfold ASTACK. rewrite FFS. clear - Hsp1. lia.
- exact Bgp.
- exact Btp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite HEV in Hev. clear - Nev3 Kle0 Hev. unfold EV_MAX in *. lia.
- exact Pre1.
- exact Trace1.
- exact Budget1. }
cbv beta. intros W4 c4 Wle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ra4 & Frs4 & Res4 & Ebl4 & HK4 & MLE4 & HJc4).
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Fin4 : In (2, fpos) (frames S4)) by (rewrite Frs4; exact Hfin3).
assert (Old4 : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly4 S4)) by (intros x Hx; rewrite Ebl4; apply in_app_iff; left; exact Hx).
pose proof Bef as (BefNth & _). cbn [c_i c_s] in BefNth.
destruct (fl_bef_in s i fb Hi Hlen3 BefNth) as (_ & BefIn).
destruct (fl_bef_blocks B ly S g s N rest fb HPerm BefIn) as (InB0 & _ & _).
assert (InB3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Blk3; exact InB0).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR InB0) as (_ & Hb4096 & Hbceil & _).
change (req_size FRAME_SIZE) with 40 in Hbceil.
assert (B12 : bv_unsigned (ew E 12) = fr_ptr fb)
by (rewrite (AG 12%nat), E12, BefNth by nat_side; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hb4096 Hbceil C1; lia).
assert (B10 : bv_unsigned (ew E 10) = g) by (rewrite E10n; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia).
assert (B11 : bv_unsigned (ew E 11) = fr_ptr f) by (rewrite E11n; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia).
assert (B516 : bv_unsigned (ew E 516) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (B529 : bv_unsigned (ew E 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia).
assert (B60 : bv_unsigned (ew E 60) = sp1) by (rewrite E60; exact (unsigned_lit_small sp1 Wsp1)).
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
lazymatch type of HS with st_ok _ _ ?ssm _ =>
let r5 := eval vm_compute in (nth 5 (ss_mem ssm) got_regionP) in
let r6 := eval vm_compute in (nth 6 (ss_mem ssm) got_regionP) in
let r7 := eval vm_compute in (nth 7 (ss_mem ssm) got_regionP) in
let r8 := eval vm_compute in (nth 8 (ss_mem ssm) got_regionP) in
pose proof (st_ok_region_nth E ssm _ 5 r5 HS ltac:(vm_compute; reflexivity)) as Reg5;
pose proof (st_ok_region_nth E ssm _ 6 r6 HS ltac:(vm_compute; reflexivity)) as Reg6;
pose proof (st_ok_region_nth E ssm _ 7 r7 HS ltac:(vm_compute; reflexivity)) as Reg7;
pose proof (st_ok_region_nth E ssm _ 8 r8 HS ltac:(vm_compute; reflexivity)) as Reg8 end.
assert (B241 : bv_unsigned (ew E 241) = VAL 241) by (rewrite E241; apply unsigned_lit_small; clear - Hob241; lia).
assert (B253 : bv_unsigned (ew E 253) = VAL 253) by (rewrite E253; apply unsigned_lit_small; clear - Hob253; lia).
assert (B242 : bv_unsigned (ew E 242) = VAL 242) by (rewrite E242; apply unsigned_lit_small; clear - Hob242; lia).
assert (B59 : bv_unsigned (ew E 59) = as_uar_cell B) by (rewrite E59; apply unsigned_lit_small; clear - Huar; lia).
pose proof (field_of_region E _ 241 (VAL 241) _ 0 8 0 0 0 8 (SOff 253 0) (VAL 253) Reg5 B241 ltac:(cbn [In]; left; reflexivity)
ltac:(rewrite sv_denot_SOff0; exact E253) ltac:(cbn [Z.of_N Z.mul]; clear - Hob253; lia) ltac:(clear; cbn; lia)) as V241.
pose proof (field_of_region E _ 253 (VAL 253) _ 0 8 0 0 0 8 (SOff 32 0) SB Reg6 B253 ltac:(cbn [In]; left; reflexivity)
ltac:(rewrite sv_denot_SOff0; exact E32n) ltac:(cbn [Z.of_N Z.mul]; unfold SB; clear; lia) ltac:(clear; cbn; lia)) as V253.
pose proof (field_of_region E _ 242 (VAL 242) _ 0 8 0 0 0 8 (SOff 59 0) (as_uar_cell B) Reg7 B242 ltac:(cbn [In]; left; reflexivity)
ltac:(rewrite sv_denot_SOff0; exact E59) ltac:(cbn [Z.of_N Z.mul]; clear - Huar; lia) ltac:(clear; cbn; lia)) as V242.
pose proof (field_of_region E _ 59 (as_uar_cell B) _ 0 4 0 0 0 4 (SLit 1) 1 Reg8 B59 ltac:(cbn [In]; left; reflexivity)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear; lia) ltac:(clear; cbn; lia)) as V59.
rewrite Z.add_0_r in V241, V253, V242, V59. cbn [ms_mem restrict mkst N.to_nat] in V241, V253, V242, V59.
jafter_call_keep_hi HS 908%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS4.
match type of HS4 with ?Q -> _ => assert (Kept4 : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- apply (region_kept_block_subw B E ASTACK _ [] ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 1 12 0 40 0 0 _ (fr_ptr fb) FRAME_SIZE HJc4 B12 InB3 (Old4 _ InB3));
[ apply Z.le_refl | change (req_size FRAME_SIZE) with 40; apply Z.le_refl | intros a _ (rr & [] & _) | intros a Ha; clear - Ha; lia ].
- apply (region_kept_fshadow_sub B E ASTACK _ [] ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 1 529 (SB + F / 8) 0 32 0 0 _ 2 fpos HJc4 B529 Hfin3);
[ unfold shadow_addr; rewrite EFA3; fold F; rewrite <- SB_SHADOW_OFF; clear; lia
| unfold shadow_addr; rewrite EFA3; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a _ (rr & [] & _) | intros a Ha; clear - Ha; lia ].
- apply (region_kept_frame_sub B E ASTACK _ [] ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 1 516 F 0 256 0 256 _ 2 fpos HJc4 B516 Hfin3);
[ rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | intros a _ (rr & [] & _) | ].
intros a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Fin4) as (_ & _ & Fp4 & _).
rewrite EFA4 in Fp4. fold F in Fp4. change (fs_frame_bytes 2) with 256 in Fp4. exact (proj1 (Fp4 a ltac:(clear - Ha; lia))).
- apply (region_kept_stack_aj SEGS B E ly3 S3 W3 (ms_mem ms) W4 mem4 _ _ _ 60 0 280 0 280 _ (spZ regs) sp1 TFLUSH_STK _ ly S W mem md _ ly4 S4 md4 (k + 1) HK4 HJ4 B60);
clear - Hsp1 FFS; lia.
- apply (region_kept_stack_aj SEGS B E ly3 S3 W3 (ms_mem ms) W4 mem4 _ _ _ 2 (-104) 0 (-104) 0 _ (spZ regs) (spZ regs) TFLUSH_STK _ ly S W mem md _ ly4 S4 md4 (k + 1) HK4 HJ4 Sp0E);
clear - Hsp1 FFS; lia.
- apply (region_kept_val_at E _ _ 241 (VAL 241) 8 (VAL 253) 0 0 _ B241 V241); [exact Kgot4 | apply Z.le_refl].
- apply (region_kept_val_at E _ _ 253 (VAL 253) 8 SB 0 0 _ B253 V253); [rewrite SB_SHADOW_OFF; exact Kcell4 | apply Z.le_refl].
- apply (region_kept_val_at E _ _ 242 (VAL 242) 8 (as_uar_cell B) 0 0 _ B242 V242); [exact Kguar4 | apply Z.le_refl].
- apply (region_kept_val_at E _ _ 59 (as_uar_cell B) 4 1 0 0 _ B59 V59); [exact Kuar4 | apply Z.le_refl].
- apply (region_kept_block_subw B E ASTACK _ [] ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 1 10 0 96 0 0 _ g CGIF_SIZE HJc4 B10 InG3 (Old4 _ InG3));
[ apply Z.le_refl | change (req_size CGIF_SIZE) with 96; apply Z.le_refl | intros a _ (rr & [] & _) | intros a Ha; clear - Ha; lia ].
- apply (region_kept_block_subw B E ASTACK _ [] ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 1 11 0 40 20 24 _ (fr_ptr f) FRAME_SIZE HJc4 B11 InC3 (Old4 _ InC3));
[ apply Z.le_refl | change (req_size FRAME_SIZE) with 40; apply Z.le_refl | intros a _ (rr & [] & _) | ].
intros a Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR4 (Old4 _ InC3)) as (_ & _ & _ & _ & Cp4 & _).
change (req_size FRAME_SIZE) with 40 in Cp4. exact (proj1 (Cp4 a ltac:(clear - Ha; lia))). }
specialize (HS4 Kept4). rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
assert (A912 : ew (havoc E 908 (map (getr regs4) CLOB)) 912 = w64 res)
by exact (eq_trans (ew_havoc_new E 908 (map (getr regs4) CLOB) 4 (Z_to_bv 64 0) ltac:(nat_side)) Ra4).
pose proof (fl_bef_havoc _ fb E 908 (map (getr regs4) CLOB) ltac:(nat_side) Bef) as BefC.
rebaseF HS AG EnvC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
assert (InC4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by exact (Old4 _ InC3).
assert (InR4 : In (res, wv * hv) (ablocks B ly4 S4)) by (rewrite Ebl4; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (wv * hv) HAR4 InR4) as (Rs16 & Rs4096 & Rsceil & Rs_ia & Rspres & _).
assert (Rq : req_size (wv * hv) = wv * hv) by (unfold req_size; destruct (Z.eqb_spec (wv * hv) 0) as [Z0|NZ]; [clear - WHn Z0; lia | reflexivity]).
rewrite Rq in Rsceil, Rspres, Rs_ia.
hei_havoc HS; paj_run_tok RUN HS HJ4 SHOK FLBspan.
1: awrFL AG fpos F EFA4.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom E1 912 res A912) in Hc by (clear - Rs4096 Rsceil C1 WHn; lia).
rewrite U_lit in Hc by (clear; lia). apply Z.eqb_eq in Hc. clear - Hc Rs4096. lia.
-
rename Hc into NotNull.
assert (InImg4 : In (fr_img f, N) (ablocks B ly4 S4)) by (apply Old4; rewrite Blk3; exact Himg_in).
assert (NotOld : ~ In (res, wv * hv) (ablocks B ly S)).
{ intros InOld.
destruct (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (wv * hv) HJ3 HAR4 Ebl4 ltac:(clear - WHn; lia) InOld 0
ltac:(cbn [snd]; rewrite Rq; clear - WHn; lia)) as (rr & [<- | []] & Inr).
cbn [fst snd] in Inr. pose proof (Z.div_mod res 16 ltac:(clear; lia)) as Dr. pose proof (Z.div_mod (fr_ptr f) 16 ltac:(clear; lia)) as Dc.
rewrite Rs16 in Dr. rewrite Hc16 in Dc. clear - Inr Dr Dc. lia. }
pose proof (sep_blocks _ _ LAWS _ _ _ _ _ res (wv * hv) (fr_img f) N HAR4 InR4 InImg4
ltac:(intros Same; apply NotOld; rewrite Same; exact Himg_in)) as SepI.
unfold zdisjoint in SepI. cbn [fst snd] in SepI.
reshok HS; hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK FLBspan 8248.
1: awrFL AG fpos F EFA4.
clear_frames.
prreg HS (2%bv : bv 5) Lr2. prreg HS (3%bv : bv 5) Lr3. prreg HS (4%bv : bv 5) Lr4.
pose proof (req_size_pos' N ltac:(clear - HN HW1 HH1; nia)) as (_ & ReqN).
rregU HS (20%bv : bv 5) (hv - 0) ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
rewrite Z.sub_0_r; apply (U_and16 Ex _ hv); [apply (U_atom Ex 888 hv Ah888) |]; clear - Hlo Tlo THhi R8; lia end) Lr20.
rregU HS (18%bv : bv 5) 4294967295 ltac:(idtac; apply U_lit; clear; lia) Lr18.
assert (RgImg : 0 <= fr_img f /\ fr_img f + N <= 140737479966720) by (clear - ReqN WHn Hi4096 Hiceil C1; lia).
assert (RgLv : 0 <= lv <= 65535) by (clear - Llo LWhi Wlo R7; lia).
rregU HS (21%bv : bv 5) (fr_img f + lv) ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
apply (U_add_small2 Ex _ _ (fr_img f) lv); [apply (U_atom Ex 51 (fr_img f) E51) | apply (U_atom Ex 890 lv Al890) | | |];
clear - RgImg RgLv WHn LWhi; lia end) Lr21.
rregU HS (22%bv : bv 5) ((tv + 0) * cg_W s) ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
rewrite Z.add_0_r; apply (U_mul_atoms Ex 889 40 tv (cg_W s) At889 E40); clear - Tlo THhi Hlo R7 R8; lia end) Lr22.
rregU HS (23%bv : bv 5) wv ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
apply (U_and16 Ex _ wv); [apply (U_atom Ex 887 wv Aw887) |]; clear - Wlo Llo LWhi R7; lia end) Lr23.
rregU HS (24%bv : bv 5) (cg_W s) ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
apply (U_atom Ex 40 (cg_W s) E40); clear - R7; lia end) Lr24.
rregU HS (27%bv : bv 5) (res + 0 * wv) ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
rewrite Z.mul_0_l, Z.add_0_r; apply (U_atom Ex 912 res A912); clear - Rs4096 Rsceil C1 WHn; lia end) Lr27.
rregU HS (19%bv : bv 5) wv ltac:(idtac; lazymatch goal with |- U ?Ex _ = _ =>
apply (U_and16 Ex _ wv); [apply (U_atom Ex 887 wv Aw887) |]; clear - Wlo Llo LWhi R7; lia end) Lr19.
pmkst HS.
eapply SRr_bind.
{ apply (fl_cpyX B LAWS AMEMCPY (Z.to_nat hv) 0 W4 (ms_regs ms1) (ms_mem ms1) _ (spZ regs) sp1 [(fr_ptr f + 20, fr_ptr f + 24)]
ly S W mem md ly4 S4 (k + 1) fpos res (fr_img f) N wv hv tv lv (cg_W s) (cg_H s)).
- rewrite Z2Nat.id by (clear - Hlo; lia). clear; lia.
- clear - Hlo; lia.
- exact Wlo.
- exact Llo.
- exact LWhi.
- exact Hlo.
- exact Tlo.
- exact THhi.
- clear - HW1 R7; lia.
- clear - R8; lia.
- symmetry; exact HN.
- exact HNle.
- exact HJ4.
- exact InR4.
- exact InImg4.
- intros blc lyq ownq a InBlc Ina. right; right; left. exists res, (wv * hv).
split; [exact InBlc|]. split; [exact NotOld|]. rewrite Rq. exact Ina.
- exact SepI.
- unfold spZ. rewrite Lr2, E60. exact (unsigned_lit_small sp1 Wsp1).
- exact Hsp1.
- exact Hsp1al16.
- rewrite Lr3, (AG 3%nat), (EE 3%nat 3%bv eq_refl) by nat_side. exact Hgp.
- rewrite Lr4, (AG 4%nat), (EE 4%nat 4%bv eq_refl) by nat_side. exact Htp.
- exact Lr20.
- exact Lr18.
- exact Lr21.
- exact Lr22.
- exact Lr23.
- exact Lr24.
- exact Lr27.
- exact Lr19. }
cbv beta. intros W5 c5 Wle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & Keep5 & Out5 & Pres5 & Rows5 & Copy5).
pose proof (blk_off_imgP _ _ _ _ _ _ res (wv * hv) HAR4 InR4) as ResImg. rewrite Rq in ResImg. unfold off_img in ResImg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Rs_ia.
pose proof (sep_block_frame _ _ LAWS _ _ _ _ _ res (wv * hv) 2 fpos HAR4 InR4 Fin4) as ResF.
unfold zdisjoint in ResF. cbn [fst snd] in ResF. rewrite Rq, EFA4 in ResF. fold F in ResF. change (fs_frame_bytes 2) with 256 in ResF.
pose proof (sep_blocks _ _ LAWS _ _ _ _ _ res (wv * hv) g CGIF_SIZE HAR4 InR4 (Old4 _ InG3) ltac:(intros Same; apply NotOld; rewrite Same; exact Hing)) as ResG.
pose proof (sep_blocks _ _ LAWS _ _ _ _ _ res (wv * hv) (fr_ptr f) FRAME_SIZE HAR4 InR4 InC4 ltac:(intros Same; apply NotOld; rewrite Same; exact Hcur_in)) as ResC.
pose proof (sep_blocks _ _ LAWS _ _ _ _ _ res (wv * hv) (fr_ptr fb) FRAME_SIZE HAR4 InR4 (Old4 _ InB3) ltac:(intros Same; apply NotOld; rewrite Same; exact InB0)) as ResB.
unfold zdisjoint in ResG, ResC, ResB. cbn [fst snd] in ResG, ResC, ResB. rewrite Rq in ResG, ResC, ResB.
change (req_size CGIF_SIZE) with 96 in ResG. change (req_size FRAME_SIZE) with 40 in ResC, ResB.
assert (Ub12 : bv_unsigned (ew E1 12) = fr_ptr fb)
by (rewrite (AG 12%nat), E12, BefNth by nat_side; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hb4096 Hbceil C1; lia).
assert (Ub2 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (AG 2%nat) by nat_side; exact Usp).
assert (Ub10 : bv_unsigned (ew E1 10) = g) by (rewrite (AG 10%nat), E10 by nat_side; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia).
assert (Ub11 : bv_unsigned (ew E1 11) = fr_ptr f) by (rewrite (AG 11%nat), E11 by nat_side; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia).
assert (Ub516 : bv_unsigned (ew E1 516) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (Ub529 : bv_unsigned (ew E1 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia).
assert (Ub60 : bv_unsigned (ew E1 60) = sp1) by (rewrite E60; exact (unsigned_lit_small sp1 Wsp1)).
assert (Ub241 : bv_unsigned (ew E1 241) = VAL 241) by (rewrite E241; apply unsigned_lit_small; clear - Hob241; lia).
assert (Ub253 : bv_unsigned (ew E1 253) = VAL 253) by (rewrite E253; apply unsigned_lit_small; clear - Hob253; lia).
assert (Ub242 : bv_unsigned (ew E1 242) = VAL 242) by (rewrite E242; apply unsigned_lit_small; clear - Hob242; lia).
assert (Ub59 : bv_unsigned (ew E1 59) = as_uar_cell B) by (rewrite E59; apply unsigned_lit_small; clear - Huar; lia).
assert (StkGap : alloc_ceiling + ESTACK <= sp1) by (unfold ESTACK; clear - Hsp1 Hceil Hslo FFS; lia).
jafter_stretch_hi HS 930%nat regs5 (mrestrict (w_H W4) mem5) CPY_CLOB 8284 HS5.
match type of HS5 with ?P1 -> ?P2 -> _ => assert (Kept5 : P2) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
all: lazymatch goal with |- region_kept _ _ _ _ {| r_base := Some ?n; r_lo := ?lo; r_hi := ?hi; r_wlo := ?wl; r_whi := ?wh; r_chunks := ?cs |} =>
eapply (region_kept_aview E1 _ _ _ n _ lo hi wl wh cs); [ eassumption | | exact Pres5 ] end.
- intros a Ha; apply Out5; clear - Ha ResB Hb4096 Hbceil StkGap C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha Rs_ia HFq HF8 HF8lo HFceil StkGap C1 WHn; unfold SB, ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha ResF HF4096 HFceil StkGap C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha Rsceil StkGap Hsp1 Hshi H47 C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha Rsceil StkGap Hsp1 Hshi H47 C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha ResImg Hob241 StkGap C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha ResImg Hob253 StkGap C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha ResImg Hob242 StkGap C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha ResImg Huar StkGap C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha ResG Hg4096 Hgceil StkGap C1 WHn; unfold ESTACK in *; lia.
- intros a Ha; apply Out5; clear - Ha ResC Hc4096 Hcceil StkGap C1 WHn; unfold ESTACK in *; lia. }
specialize (HS5 Keep5 Kept5). rewrite <- restrict_mkst_fx in HS5. clear HS. rename HS5 into HS.
rebaseF HS AG EnvS.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 8356.
1: awrFL AG fpos F EFA4.
rename HFr into FrLast. clear HF HG.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 679 Ev ssv msv [Z_to_bv 64 wv; Z_to_bv 64 lv; Z_to_bv 64 tv] HS ltac:(vm_compute; reflexivity)) as HS7;
assert (A679 : ew (havoc Ev 679 [Z_to_bv 64 wv; Z_to_bv 64 lv; Z_to_bv 64 tv]) 679 = Z_to_bv 64 wv)
by exact (ew_havoc_new Ev 679 [Z_to_bv 64 wv; Z_to_bv 64 lv; Z_to_bv 64 tv] 0 (Z_to_bv 64 0) ltac:(nat_side));
assert (A680 : ew (havoc Ev 679 [Z_to_bv 64 wv; Z_to_bv 64 lv; Z_to_bv 64 tv]) 680 = Z_to_bv 64 lv)
by exact (ew_havoc_new Ev 679 [Z_to_bv 64 wv; Z_to_bv 64 lv; Z_to_bv 64 tv] 1 (Z_to_bv 64 0) ltac:(nat_side));
assert (A681 : ew (havoc Ev 679 [Z_to_bv 64 wv; Z_to_bv 64 lv; Z_to_bv 64 tv]) 681 = Z_to_bv 64 tv)
by exact (ew_havoc_new Ev 679 [Z_to_bv 64 wv; Z_to_bv 64 lv; Z_to_bv 64 tv] 2 (Z_to_bv 64 0) ltac:(nat_side)) end.
clear HS; rename HS7 into HS.
rebaseF HS AG EnvA.
rechunk_off HS 60%nat 168 (SOff 679 0) ltac:(idtac; rewrite !sv_denot_SOff0, A679, Aw887; reflexivity).
rechunk_off HS 60%nat 144 (SOff 680 0) ltac:(idtac; rewrite !sv_denot_SOff0, A680, Al890; reflexivity).
rechunk_off HS 60%nat 152 (SOff 681 0) ltac:(idtac; rewrite !sv_denot_SOff0, A681, At889; reflexivity).
add_fact HS 679%nat 1 65535 A679 ltac:(idtac; clear - Wlo Llo LWhi R7; lia).
add_fact HS 680%nat 0 65535 A680 ltac:(idtac; clear - Wlo Llo LWhi R7; lia).
add_fact HS 681%nat 0 65535 A681 ltac:(idtac; clear - Hlo Tlo THhi R8; lia).
prreg HS (27%bv : bv 5) P27. rewrite Ah888 in P27.
prreg HS (23%bv : bv 5) P23. rewrite A912 in P23.
ra_join_win HS ss_T0 682%nat fl_T0_deads_bv ltac:(idtac; ra_join_val HS 682%nat 2%nat P27 A684; ra_join_val HS 682%nat 0%nat P23 A682;
add_fact HS 684%nat 1 65535 A684 ltac:(idtac; clear - Hlo Tlo THhi R8; lia)).
fl_handX NextT0 HS.
1: cbn [c_fpos c_S]; rewrite Frs4; exact Hfrs3.
rewrite A682, A684. rewrite !ew_havoc_old by nat_side.
split; [exists gv; exact (conj G621 Grng)|].
split; [exact Np625|].
split; [exists fb; apply fl_bef_havoc; [nat_side|]; rewrite EnvA; apply fl_bef_havoc; [nat_side|];
rewrite EnvS; apply fl_bef_havoc; [nat_side|]; rewrite EnvC; exact BefC|].
split; [|exact G621x].
exists res, wv, hv, tv, lv.
split; [reflexivity|]. split; [exact A679|]. split; [reflexivity|]. split; [exact A681|]. split; [exact A680|].
split; [clear - Rs4096 Rsceil C1 WHn; lia|].
do 6 (split; [assumption|]).
pose proof HCUR as (_ & GenEq & _ & _ & _ & _ & _ & GImg & LenImg & _). cbn in GenEq.
assert (GenNN : 0 <= YO07.f_gen cur) by (rewrite <- GenEq; clear - Q3; lia).
lazymatch goal with |- context [xtmp ?cxv ?xxv] => assert (TmpW : xtmp cxv xxv = YO07.window (cg_W s) (YO07.f_img cur) wv hv tv lv) end.
{ pose proof Gflag as Gf. pose proof Dims as Dm. unfold xgen3 in Gf. unfold xdims in Dm. cbn [x_cur x_bef] in Gf, Dm.
unfold xtmp. cbn [x_cur x_bef]. destruct bef as [bfr|].
- rewrite (fl_tmp_diff _ cur bfr wv hv tv lv Gf Dm). reflexivity.
- exfalso. lazymatch type of Gf with context [YI0f.fl_gen3 ?gg cur None] => pose proof (fl_gen3_first gg cur GenNN) as L3 end.
unfold YO07.flag in Gf.
lazymatch type of Gf with context [Z.land ?x 2] => assert (Lx : Z.land x 2 = Z.land (Z.land x 3) 2) by (rewrite <- Z.land_assoc; reflexivity) end.
rewrite Lx, L3 in Gf. vm_compute in Gf. discriminate Gf. }
pose proof (window_specZ (cg_W s) (cg_H s) (YO07.f_img cur) wv hv tv lv ltac:(clear - HW1; lia) ltac:(clear - HH1; lia)
ltac:(rewrite LenImg; exact HN) Wlo Llo LWhi Hlo Tlo THhi) as (WinLen & _).
destruct (frame_blocks_front g s N rest i f Hf) as (rr0 & PermF).
pose proof (fasep_head B LAWS ly S W mem md (fr_ptr f, FRAME_SIZE) (fr_img f, N) _ HAR (Permutation_trans HPerm PermF) (or_introl eq_refl)) as SepCI.
unfold zdisjoint, block_rng in SepCI. cbn [fst snd] in SepCI. change (req_size FRAME_SIZE) with 40 in SepCI.
assert (ImgL : garr8 SEGS (mrestrict (w_H W4) (ms_mem ms1)) (fr_img f) (YO07.f_img cur)).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W4) mem (ms_mem ms1) (fr_img f) (YO07.f_img cur)); [|exact GImg].
intros a Ha. rewrite LenImg in Ha.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KeepB & _).
replace a with (fr_img f + (a - fr_img f)) by ring.
apply (KeepB (fr_img f) N (a - fr_img f) Himg_in InImg4); [clear - Ha ReqN; lia |].
intros (rr & [<- | []] & Inr). cbn [fst snd] in Inr. clear - Inr Ha SepCI ReqN. lia. }
pose proof (cpy_garr8 SEGS (w_H W4) (ms_mem ms1) mem5 res (fr_img f) wv hv tv lv (cg_W s) (cg_H s) (YO07.f_img cur) ImgL
ltac:(rewrite LenImg; exact HN) ltac:(clear - HW1; lia) ltac:(clear - HH1; lia) Wlo Llo LWhi Hlo Tlo THhi Copy5) as GT5.
assert (GT2 : garr8 SEGS (mrestrict (w_H W4) (ms_mem ms2)) res (YO07.window (cg_W s) (YO07.f_img cur) wv hv tv lv)).
{ apply (garr8_aview_kept SEGS (w_H W4) (w_H W4) mem5 (ms_mem ms2) res _); [|exact GT5].
intros a Ha. rewrite WinLen, Z2Nat.id in Ha by (clear - WHn; lia).
apply (aview_kept_out E3 _ (w_H W4) mem5 (ms_mem ms2) FrLast a); [clear - Ha Rs4096 Rsceil C1 WHn; lia|].
intros (rg & Hin & Hw).
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end; cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
rewrite ?EnvS, ?ew_havoc_old, ?Ub516, ?Ub60, ?Ub2, ?Ub11 in Hw by nat_side;
clear - Hw Ha ResF ResC Rsceil StkGap Hsp1 FFS WHn Wsp1; unfold ESTACK in *; lia |]); destruct Hin. }
split.
{ right. split; [clear - Rs4096; lia|]. split; [clear - Kle0; lia|].
unfold fl_tmpblkX, fl_FP0. cbn [c_ly c_S c_regs c_f].
split; [split; [exact Rs4096 | unfold zone2, off_img; split; [exact ResImg | destruct Rs_ia as (_ & [ZLo | (ZHi & _)]); [left; exact ZLo | right; exact ZHi]]]|].
split; [exact Rsceil|]. split; [exact Rs16|]. split; [rewrite Ebl4, Blk3; reflexivity|].
split; [intros blc lyq ownq ii InBlc Hii; right; right; left; exists res, (wv * hv); split; [exact InBlc|]; split; [exact NotOld|]; rewrite Rq; clear - Hii; lia|].
exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (wv * hv) HJ3 HAR4 Ebl4 ltac:(clear - WHn; lia)). }
split; [exact Dims|].
split; [intros _; rewrite TmpW; exact GT2|].
split; [intros ResZ; exfalso; clear - ResZ Rs4096; lia|].
split; [rewrite TmpW, WinLen; apply Z2Nat.id; clear - WHn; lia|].
unfold xmacc. destruct (Z.eqb_spec res 0) as [ResZ|_]; [exfalso; clear - ResZ Rs4096; lia|].
pose proof (mle_station MT S S3 S4 0 _ MLAW Meter MLE4) as M4. rewrite Z.add_0_l in M4. exact M4.
Qed.
Lemma fl_D1X : fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B).
Proof. exact fl_D1X_aux. Qed.
Ltac seat160 HS na v Ana Vslot rt :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let regs0 := eval vm_compute in (ss_mem ssx) in
let k60 := idx_of_base regs0 60%nat in let k60 := eval vm_compute in k60 in
let pre := eval vm_compute in (firstn k60 regs0) in
let post := eval vm_compute in (skipn (S k60) regs0) in
lazymatch eval vm_compute in (nth k60 regs0 got_regionP) with YP09.mkRegion ?nb ?lo ?hi ?wlo ?whi ?cs =>
let Slot := fresh "Slot" in
assert (Slot : YP09.chunk_ok SEGS Ev (ms_mem msx) (base_val Ev nb) (YP09.mkChunk 160 (CVal 8 (SOff na 0))));
[ lazymatch goal with Sp : ew Ev 60%nat = Z_to_bv 64 ?sp |- _ =>
cbn [base_val]; rewrite Sp, unsigned_lit_small by rt;
eapply (chunk_ok_val SEGS Ev _ _ 160 8 _ v);
[ rewrite sv_denot_SOff0; exact Ana | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rt | cbn [Z.of_N]; apply Z.le_refl
| cbn [ms_mem restrict mkst N.to_nat]; exact Vslot ] end
| pose proof (w_st_ok_add_chunk Ev ssx msx pre nb lo hi wlo whi cs post (YP09.mkChunk 160 (CVal 8 (SOff na 0))) HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Slot) as Seated;
clear HS Slot; rename Seated into HS; norm_ss HS ] end end.
Ltac d1_joinX HS vt ft :=
let P26 := fresh "P26" in let P27 := fresh "P27" in let P23 := fresh "P23" in
prreg HS (26%bv : bv 5) P26; prreg HS (27%bv : bv 5) P27; prreg HS (23%bv : bv 5) P23;
ws_pin HS (26%bv : bv 5) (SOff 887 0) P26 vt;
ws_pin HS (27%bv : bv 5) (SOff 889 0) P27 vt;
ws_pin HS (23%bv : bv 5) (SOff 890 0) P23 vt;
clear P26 P27 P23;
rechunk_off HS 516%nat 112 (SOff 889 0) vt;
rechunk_off HS 516%nat 128 (SOff 890 0) vt;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch goal with
A7 : ew Ev 887%nat = _, A8 : ew Ev 888%nat = _, A9 : ew Ev 889%nat = _, A0 : ew Ev 890%nat = _ |- _ =>
add_fact HS 887%nat 1 65535 A7 ft; add_fact HS 888%nat 1 65535 A8 ft;
add_fact HS 889%nat 0 65535 A9 ft; add_fact HS 890%nat 0 65535 A0 ft end end;
norm_ss HS.
Lemma fl_DdX_aux : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B).
Proof using TL LAWS TLF.
intros NextD1. clear ML AMALLOC AIL MLAWF HDEEP RO AMEMCPY MLAW AMALLOC4 HXM HXMN HTR. fl_preludeX.
destruct HINV as (Kle0 & Blk3 & (gv & G621 & Grng) & Np625 & (fb & Bef) & (wv & hv & tv & lv & W861 & Slot160 & T862 & L863 & Wlo & Llo & LWhi & Hlo & Tlo & THhi & Dims) & G621x & Gflag & Meter).
assert (InG3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hing).
assert (InC3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hcur_in).
assert (InP3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hpf_in).
fl_blocks3X InG3 InC3 InP3. fold F in HdFG, HdFC.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 887 Ev ssv msv [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv] HS ltac:(vm_compute; reflexivity)) as Fresh4 end.
clear HS; rename Fresh4 into HS.
assert (A887 : ew (havoc E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv]) 887 = Z_to_bv 64 wv)
by exact (ew_havoc_new E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv] 0 (Z_to_bv 64 0) ltac:(nat_side)).
assert (A888 : ew (havoc E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv]) 888 = Z_to_bv 64 hv)
by exact (ew_havoc_new E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv] 1 (Z_to_bv 64 0) ltac:(nat_side)).
assert (A889 : ew (havoc E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv]) 889 = Z_to_bv 64 tv)
by exact (ew_havoc_new E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv] 2 (Z_to_bv 64 0) ltac:(nat_side)).
assert (A890 : ew (havoc E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv]) 890 = Z_to_bv 64 lv)
by exact (ew_havoc_new E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv] 3 (Z_to_bv 64 0) ltac:(nat_side)).
pose proof (fl_bef_havoc _ fb E 887 [Z_to_bv 64 wv; Z_to_bv 64 hv; Z_to_bv 64 tv; Z_to_bv 64 lv] ltac:(nat_side) Bef) as Bef4.
rebaseF HS AG Env4.
relowF HS AG E10 E11 E32 E10n E11n E32n.
seat160 HS 888%nat hv A888 Slot160 ltac:(idtac; clear - Hsp1 Hslo Hceil Hshi H47 C1 FFS Hlo Tlo THhi R8; lia).
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 8120.
1: awrFL AG fpos F EFA3.
d1_joinX HS ltac:(idtac; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
rewrite ?A887, ?A888, ?A889, ?A890, ?W861, ?T862, ?L863; reflexivity)
ltac:(idtac; clear - Wlo Llo LWhi Hlo Tlo THhi R7 R8; lia).
ra_join_win HS ss_D1 891%nat fl_D1_deads_bv idtac.
fl_handX NextD1 HS.
rewrite !ew_havoc_old by nat_side.
refine (conj Kle0 (conj Blk3 (conj (ex_intro _ gv (conj G621 Grng)) (conj Np625 (conj _ (conj _ (conj G621x (conj Gflag Meter)))))))).
- exists fb. apply fl_bef_havoc; [nat_side|]. rewrite Env4. exact Bef4.
- exists wv, hv, tv, lv.
exact (conj A887 (conj A888 (conj A889 (conj A890 (conj Wlo (conj Llo (conj LWhi (conj Hlo (conj Tlo (conj THhi Dims)))))))))).
Qed.
Lemma fl_DdX : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B).
Proof. exact fl_DdX_aux. Qed.
Lemma fl_DiX_aux : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMSi (INV_DIMSiX MT B).
Proof using TL LAWS TLF.
intros NextD1. clear ML AMALLOC AIL MLAWF HDEEP RO AMEMCPY MLAW AMALLOC4 HXM HXMN HTR. fl_preludeX.
destruct HINV as ((Kle0 & Blk3 & (gv & G621 & Grng) & Np625 & (fb & Bef) & One160) & Dims11 & G621x & Gflag & Meter).
assert (InG3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hing).
assert (InC3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hcur_in).
assert (InP3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Blk3; exact Hpf_in).
fl_blocks3X InG3 InC3 InP3. fold F in HdFG, HdFC.
pose proof (fl_bef_havoc _ fb E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0] ltac:(nat_side) Bef) as Bef4.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 887 Ev ssv msv [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0] HS ltac:(vm_compute; reflexivity)) as Fresh4 end.
clear HS; rename Fresh4 into HS.
assert (A890 : ew (havoc E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0]) 890 = Z_to_bv 64 0)
by exact (ew_havoc_new E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0] 3 (Z_to_bv 64 0) ltac:(nat_side)).
assert (A889 : ew (havoc E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0]) 889 = Z_to_bv 64 0)
by exact (ew_havoc_new E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0] 2 (Z_to_bv 64 0) ltac:(nat_side)).
assert (A888 : ew (havoc E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0]) 888 = Z_to_bv 64 1)
by exact (ew_havoc_new E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0] 1 (Z_to_bv 64 0) ltac:(nat_side)).
assert (A887 : ew (havoc E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0]) 887 = Z_to_bv 64 1)
by exact (ew_havoc_new E 887 [Z_to_bv 64 1; Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 0] 0 (Z_to_bv 64 0) ltac:(nat_side)).
rebaseF HS AG Env4.
relowF HS AG E10 E11 E32 E10n E11n E32n.
seat160 HS 888%nat 1 A888 One160 ltac:(idtac; clear - Hsp1 Hslo Hceil Hshi H47 C1 FFS; lia).
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 8120.
1: awrFL AG fpos F EFA3.
d1_joinX HS ltac:(idtac; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?A887, ?A888, ?A889, ?A890; reflexivity)
ltac:(idtac; clear; lia).
ra_join_win HS ss_D1 891%nat fl_D1_deads_bv idtac.
fl_handX NextD1 HS.
rewrite !ew_havoc_old by nat_side.
split; [exact Kle0|]. split; [exact Blk3|]. split; [exists gv; exact (conj G621 Grng)|]. split; [exact Np625|].
split; [exists fb; apply fl_bef_havoc; [nat_side | rewrite Env4; exact Bef4]|].
split; [|exact (conj G621x (conj Gflag Meter))].
exists 1, 1, 0, 0. do 4 (split; [assumption|]).
split; [apply Z.le_refl|]. split; [apply Z.le_refl|]. split; [exact HW1|].
split; [apply Z.le_refl|]. split; [apply Z.le_refl|]. split; [exact HH1 | exact Dims11].
Qed.
Lemma fl_DiX : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMSi (INV_DIMSiX MT B).
Proof. exact fl_DiX_aux. Qed.
Lemma fl_DX : fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B).
Proof. intros RT0. exact (fl_DdX_aux (fl_D1X_aux RT0)). Qed.
End o.
End m.
End d.
