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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChb ACj1 ACjr ACj3 ACgw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac awr_a_rec Usp E32u Hing HTS :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
first
[ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |] ]
| |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPa, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
end
| fail 1 "awr_a: no rule for the head region" ];
awr_a_rec Usp E32u Hing HTS
end.
Ltac awr_a Usp E32u Hing HTS :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_a_rec Usp E32u Hing HTS.
Ltac af_join0 HS target :=
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
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg; fail] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg; fail]  end.
Ltac img_words_vals :=
lazymatch goal with
| |- context [ew ?Ey 241%nat] =>
let HEy := rnHEI Ey in
rewrite ?(img_env_atomP Ey 241%nat HEy ltac:(unfold A_TEXT, A_LIM; clear; lia)), ?(img_env_atomP Ey 253%nat HEy ltac:(unfold A_TEXT, A_LIM; clear; lia)),
?(unsigned_lit_small _ (pa_val_range 241%nat)), ?(unsigned_lit_small _ (pa_val_range 253%nat))
| |- context [ew ?Ey 253%nat] =>
let HEy := rnHEI Ey in
rewrite ?(img_env_atomP Ey 253%nat HEy ltac:(unfold A_TEXT, A_LIM; clear; lia)), ?(unsigned_lit_small _ (pa_val_range 253%nat))
| |- _ => idtac
end.
Ltac rn_join HS target N deads :=
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
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
Ltac af_join HS target N deads := rn_join HS target N deads.
Ltac af_join_nod HS target :=
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
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg; fail] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg; fail]  end.
Ltac af_kill HS N deads :=
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl  end;
norm_ss HS.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section p.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_E_havoc : forall regs g s cfp lpal img fattr fgen delay nlp tidx E N vals,
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E -> (54 <= N)%nat -> (N + length vals <= A_TEXT \/ A_LIM <= N)%nat ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx (havoc E N vals).
Proof.
intros regs g s cfp lpal img fattr fgen delay nlp tidx E N vals HE HN HB.
destruct HE as (EE & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI).
unfold af_E. rewrite !ew_havoc_old by lia.
split; [intros n r Hn; rewrite !ew_havoc_old by (pose proof (bv_unsigned_in_range 5 r); change (bv_modulus 5) with 32 in *; lia); exact (EE n r Hn)|].
repeat (split; [assumption|]). destruct HB; [apply img_env_havoc; [exact HEI | lia] | apply img_env_havoc_hi; [exact HEI | lia]].
Qed.
Lemma af_E_ewset : forall regs g s cfp lpal img fattr fgen delay nlp tidx E n v,
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E -> (54 <= n)%nat -> (n < A_TEXT \/ A_LIM <= n)%nat ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx (ewset E n v).
Proof.
intros regs g s cfp lpal img fattr fgen delay nlp tidx E n v HE HN HB.
destruct HE as (EE & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI).
unfold af_E. rewrite !ew_ewset_other by lia.
split; [intros n' r Hn; rewrite ew_ewset_other by (pose proof (bv_unsigned_in_range 5 r); change (bv_modulus 5) with 32 in *; lia); exact (EE n' r Hn)|].
repeat (split; [assumption|]). intros a Ha; rewrite ew_ewset_other by lia; exact (HEI a Ha).
Qed.
Lemma af_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) wlo whi,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-104) 0 wlo whi
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
af_frame m sp0 regs.
Proof.
intros E m sp0 regs wlo whi HR Hsp HE j r Hj.
assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some af_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
do 13 (destruct j as [|j];
[ cbn in Hj; injection Hj as <-;
lazymatch goal with |- val_mem _ _ (_ + ?od) _ (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
let od' := eval vm_compute in od in change od with od';
let n := eval vm_compute in (Z.to_nat R) in
apply (field_of_region E m 2 sp0 _ (-104) 0 wlo whi od' 8 (SOff n 0) _ HR Hsp);
[ cbn; tauto
| cbn [sv_denot]; rewrite (HE n (Z_to_bv 5 R) eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
| exact HRr
| cbn; lia ] end
| ]). cbn in Hj13. lia.
Qed.
Lemma af_side_kept : forall H (m m' : word -> option byte) g s1 (Zs : Z -> Prop),
af_side (mrestrict H m) g s1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall i, 0 <= i < 48 -> 0 <= cg_raw s1 + i < 2 ^ 64 /\ ~ Zs (cg_raw s1 + i)) ->
(forall f i, In (Some f) (cg_frames s1) -> 0 <= i < 40 -> 0 <= fr_ptr f + i < 2 ^ 64 /\ ~ Zs (fr_ptr f + i)) ->
af_side (mrestrict H m') g s1.
Proof.
intros H m m' g s1 Zs [Hr Hf] UN Zr Zf. split.
- apply (obj_at_blk_kept H H m m' _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. destruct (Zr i Hi) as [Hb Hn]. exact (UN _ Hb Hn).
- intros f Hin. apply (obj_at_blk_kept H H m m' _ LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame).
intros i Hi. destruct (Zf f i Hin Hi) as [Hb Hn]. exact (UN _ Hb Hn).
Qed.
Lemma af_frame_in_blocks : forall g s1 N f, In (Some f) (cg_frames s1) -> In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s1 N).
Proof.
intros g s1 N f Hin. unfold cgif_blocks. right. right. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
Qed.
Definition ZsA (g sp0 : Z) (a : Z) : Prop := (sp0 - 224 <= a < sp0) \/ (g + 88 <= a < g + 92).
Lemma af_sideZ : forall ly S W mem md g s1 N cb lya sp0,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ cb) -> astk_ok TADDFRAME_STK lya sp0 ->
(forall i, 0 <= i < 48 -> 0 <= cg_raw s1 + i < 2 ^ 64 /\ ~ ZsA g sp0 (cg_raw s1 + i)) /\
(forall f i, In (Some f) (cg_frames s1) -> 0 <= i < 40 -> 0 <= fr_ptr f + i < 2 ^ 64 /\ ~ ZsA g sp0 (fr_ptr f + i)).
Proof.
intros ly S W mem md g s1 N cb lya sp0 HAR HP Hstk.
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _). pose proof asan_consts as (C1 & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
assert (HP' : Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: ((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1)) ++ cb)) by exact HP.
assert (Hraw : In (cg_raw s1, RAW_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right. apply in_app_iff. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hraw) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (cg_raw s1, RAW_SIZE) _ HAR HP' ltac:(apply in_app_iff; left; left; reflexivity)) as HdGR.
unfold zdisjoint, block_rng in HdGR. cbn [fst snd] in HdGR. change (req_size CGIF_SIZE) with 96 in HdGR. change (req_size RAW_SIZE) with 48 in HdGR.
split.
- intros i Hi. unfold ZsA. split; [lia|]. lia.
- intros f i Hf Hi.
assert (Hft : In (fr_ptr f, FRAME_SIZE) (((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1)) ++ cb)).
{ apply in_app_iff. left. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hf | left; reflexivity]. }
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right. exact Hft. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HP' Hft) as HdGF.
unfold zdisjoint, block_rng in HdGF. cbn [fst snd] in HdGF. change (req_size CGIF_SIZE) with 96 in HdGF. change (req_size FRAME_SIZE) with 40 in HdGF.
unfold ZsA. split; [lia|]. lia.
Qed.
Lemma U_zext32_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt false 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma land_mod_low : forall x k n, 0 <= n -> 0 <= k < 2 ^ n -> Z.land (x mod 2 ^ n) k = Z.land x k.
Proof.
intros x k n Hn Hk. rewrite <- (Z.land_ones x n Hn).
rewrite <- Z.land_assoc. f_equal. rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma U_sext32_land : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> 0 <= k < 2 ^ 32 ->
Z.land (U E (SExt true 32 (SOff n 0))) k = Z.land v k.
Proof.
intros E n v k Hn Hv Hk. rewrite (cl_U_sext32 E (SOff n 0) v (U_atom E n v Hn ltac:(lia)) Hv).
destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
rewrite <- (land_mod_low (v - 2 ^ 32 + 2 ^ 64) k 32) by lia. rewrite <- (land_mod_low v k 32) by lia.
f_equal. replace (v - 2 ^ 32 + 2 ^ 64) with (v + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma U_zext8_land : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> 0 <= k < 2 ^ 8 ->
Z.land (U E (SExt false 8 (SOff n 0))) k = Z.land v k.
Proof.
intros E n v k Hn Hv Hk. rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 8) with (2 ^ 8).
rewrite zcanon_id by (unfold M64; pose proof (Z.mod_pos_bound v (2 ^ 8) ltac:(lia)); lia). apply land_mod_low; lia.
Qed.
Lemma shq_word : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew E n) + c)) (Z_to_bv 64 3)) (ew E m) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m c v sb Hn Hm Hv Hc Hvc Hsb. pose proof (denot_shx E n m c v sb Hn Hm Hv Hc Hvc Hsb) as D.
cbn [sv_denot] in D. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D. exact D.
Qed.
Lemma land_small_r : forall x k, 0 <= x -> 0 < k -> 0 <= Z.land x k < 2 ^ (Z.log2 k + 1).
Proof.
intros x k Hx Hk. assert (H0 : 0 <= Z.land x k) by (apply Z.land_nonneg; lia). split; [exact H0|].
destruct (Z.eq_dec (Z.land x k) 0) as [->|Hnz]; [apply Z.pow_pos_nonneg; [lia | pose proof (Z.log2_nonneg k); lia]|].
apply Z.log2_lt_pow2; [lia|]. pose proof (Z.log2_land x k Hx ltac:(lia)). lia.
Qed.
Lemma and_sext32_word : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> 0 <= k < 2 ^ 32 ->
sv_denot E (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit k)) = Z_to_bv 64 (Z.land v k).
Proof.
intros E n v k Hn Hv Hk. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (bv_unsigned (sv_denot E (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit k)))) with (U E (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit k))).
rewrite U_and_lit by lia. apply (U_sext32_land E n v k Hn Hv Hk).
Qed.
Lemma U_not_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn Hv). rewrite U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_sltu1_and : forall E a m, 0 <= m < 2 ^ 64 ->
U E (SAlu ALU_SLTU (SAlu ALU_AND a (SLit m)) (SLit 1)) = (if Z.land (U E a) m =? 0 then 1 else 0).
Proof.
intros E a m Hm. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_and_lit E a m Hm), U_lit by lia.
pose proof (proj2 (Z.land_nonneg (U E a) m) ltac:(pose proof (U_range E a); lia)) as H0.
destruct (Z.ltb_spec (Z.land (U E a) m) 1); destruct (Z.eqb_spec (Z.land (U E a) m) 0); try lia; apply zcanon_id; unfold M64; lia.
Qed.
Lemma af_E_agree : forall regs g s cfp lpal img fattr fgen delay nlp tidx E E',
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E -> (forall n, (n < 54)%nat \/ (A_TEXT <= n < A_LIM)%nat -> ew E' n = ew E n) ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E'.
Proof.
intros regs g s cfp lpal img fattr fgen delay nlp tidx E E' HE HA.
destruct HE as (EE & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI).
unfold af_E. rewrite !HA by lia.
split; [intros n r Hn; rewrite HA by (pose proof (bv_unsigned_in_range 5 r); change (bv_modulus 5) with 32 in *; lia); exact (EE n r Hn)|].
repeat (split; [assumption|]). intros a Ha; rewrite HA by (right; exact Ha); exact (HEI a Ha).
Qed.
Lemma af_pre_agree : forall ly S W regs mem md g cfp s N fattr E E' ms1 md1,
af_pre B ly S W regs mem md g cfp s N fattr E ms1 md1 -> (forall n, (n < 512)%nat -> ew E' n = ew E n) ->
af_pre B ly S W regs mem md g cfp s N fattr E' ms1 md1.
Proof.
intros ly S W regs mem md g cfp s N fattr E E' ms1 md1 (H1 & H2 & H3 & H4 & H5 & H6 & H7) HA.
repeat (split; [assumption|]). split; [|exact H7]. rewrite HA by lia. exact H6.
Qed.
Lemma af_ptrs : forall ly S W mem md g s N cb i,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
(nth i (cg_frames s) None = None /\ frame_ptr (nth i (cg_frames s) None) = 0) \/
(exists f, nth i (cg_frames s) None = Some f /\ 4096 <= fr_ptr f /\ fr_ptr f + 40 <= alloc_ceiling).
Proof.
intros ly S W mem md g s N cb i HAR HP.
destruct (nth_in_or_default i (cg_frames s) None) as [Hin | Hd].
- destruct (nth i (cg_frames s) None) as [f|] eqn:Hn; [| left; split; reflexivity].
right. exists f. split; [reflexivity|].
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact (af_frame_in_blocks g s N f Hin). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & H4096 & Hceil & _). change (req_size FRAME_SIZE) with 40 in Hceil. lia.
- rewrite Hd. left. split; reflexivity.
Qed.
Lemma img_env_ewset_lo : forall E n w, img_env VAL A_LIM E -> (n < A_TEXT)%nat -> img_env VAL A_LIM (ewset E n w).
Proof. intros E n w H Hn a Ha. rewrite ew_ewset_other by lia. exact (H a Ha). Qed.
Lemma af_E_img : forall regs g s cfp lpal img fattr fgen delay nlp tidx E,
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E -> img_env VAL A_LIM E.
Proof. intros until E. intros H. repeat (destruct H as [_ H]). exact H. Qed.
Lemma st_ok_respell0 : forall E ss ms (r : bv 5) (e' : sv),
st_ok SEGS E ss ms -> bv_eqb r 0 = false -> sv_denot E e' = sv_denot E (sr_get (ss_regs ss) r) ->
st_ok SEGS E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e') (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e' HS Hr He. apply (st_ok_regs SEGS); [exact HS|].
intros r0. destruct (decide (r0 = r)) as [-> | Hne]; [rewrite sr_get_set_same by exact Hr; exact He | rewrite sr_get_set_other by exact Hne; reflexivity].
Qed.
Lemma st_ok_respell : forall E ss ms (r : bv 5) (e' : sv),
st_ok_pi SEGS VAL E ss ms -> bv_eqb r 0 = false -> sv_denot E e' = sv_denot E (sr_get (ss_regs ss) r) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e') (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e' HS Hr He. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_respell0 E _ ms r e' HS Hr He).
Qed.
Lemma shadow_slot_step : forall E g o, ew E 32 = Z_to_bv 64 g -> ew E 38 = Z_to_bv 64 SB -> 0 <= g -> g + 96 <= alloc_ceiling -> 0 <= o -> o + 8 <= 96 -> g mod 8 = 0 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 (o + 8)) (SLit 3)) (SOff 38 0)) =
alu64 ALU_ADD (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 o) (SLit 3)) (SOff 38 0))) (Z_to_bv 64 1).
Proof.
intros E g o E32 E38 Hg0 Hg Ho0 Ho Hal. pose proof asan_consts as (C1 & _).
rewrite !(denot_shx E 32 38 _ g SB E32 E38) by (unfold SB; lia). rewrite cl_alu64_addw. f_equal.
replace (g + (o + 8)) with ((g + o) + 1 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
End p.
End l.
End h.
Ltac side_win Usp E32u :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?Usp, ?E32u in Hrr; unfold ZsA; clear - Hrr; lia |]);
destruct Hin.
Ltac side_step HSD HGK HZr HZf HZg Usp E32u :=
lazymatch goal with HFr : frame_of _ _ (mrestrict ?Hh _) (mrestrict _ ?m') |- _ =>
lazymatch type of HZr with forall i, _ -> _ /\ ~ ?Zs _ =>
let UN := fresh "UN" in let HSD' := fresh "HSD" in let HGK' := fresh "HGK" in
pose proof (kept_of_frame (segs:=pa_segs) _ _ _ _ _ Zs HFr ltac:(side_win Usp E32u)) as UN;
pose proof (af_side_kept _ _ _ _ _ Zs HSD UN HZr HZf) as HSD'; clear HSD; rename HSD' into HSD;
lazymatch type of HGK with forall i, _ -> _ -> mbyte _ _ (?g + i) = mbyte _ ?m0 (_ + i) =>
assert (HGK' : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte pa_segs (mrestrict Hh m') (g + i) = mbyte pa_segs m0 (g + i))
by (let i := fresh "i" in let Hi := fresh "Hi" in let Hn := fresh "Hn" in intros i Hi Hn; etransitivity; [| exact (HGK i Hi Hn)]; apply (mbyte_of_aview _); apply UN; [|unfold ZsA]; clear - Hi Hn HZg; lia);
clear HGK UN; rename HGK' into HGK end end end.
Ltac cregA HS EEo :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in prreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
apply EEo; reflexivity end.
Ltac hcA E40 E49 Rattr Rfattr Ucur Rcur H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_and_lit in H by (clear; lia);
rewrite ?(U_zext32_atom _ 40 _ E40 Rattr), ?(U_zext32_atom _ 49 _ E49 Rfattr) in H;
rewrite ?(U_sext32_land _ 49 _ _ E49 Rfattr) in H by (clear; lia); rewrite ?(U_zext8_land _ 49 _ _ E49 Rfattr) in H by (clear; lia);
rewrite ?(cl_U_sext32 _ (SOff 37 0) _ Ucur Rcur) in H;
rewrite ?U_lit in H by (clear; lia);
try (apply (proj1 (Bool.negb_true_iff _)) in H); try (apply (proj1 (Bool.negb_false_iff _)) in H);
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H | idtac ].
Ltac kill_not_trap E32 HZg :=
lazymatch goal with H : branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_XOR (SOff 32 0) (SLit (-1)))) (sv_denot _ (SLit ?k)) = true |- _ =>
exfalso; rewrite branch_ltu_U in H;
lazymatch type of E32 with _ = Z_to_bv 64 ?g =>
rewrite (U_not_atom Ex 32 g) in H;
[ rewrite U_lit in H by (clear; lia); apply Z.ltb_lt in H; clear - H HZg; lia
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32
| clear - HZg; lia ] end end.
Ltac agreeE_tac :=
let n := fresh "n" in let Hn := fresh "Hn" in
intros n Hn; lazymatch type of Hn with _ \/ _ => destruct Hn as [Hn|Hn]; unfold A_TEXT, A_LIM in Hn | _ => idtac end;
repeat first [rewrite ew_havoc_old by lia | rewrite ew_havoc_above by (cbn [length]; lia) | rewrite ew_ewset_other by lia]; reflexivity.
Ltac Unorm E HAE H :=
repeat (match type of H with context [U ?Ex _] =>
lazymatch Ex with E => fail | _ =>
let HAGx := fresh "HAG" in
assert (HAGx : env_agree 54 E Ex) by (env_agree_chain HAE);
rewrite !(U_agree 54 E _ _ HAGx) in H by (vm_compute; reflexivity); clear HAGx end end).
Ltac g_widen HS E32u HgP :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 96) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 96 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
rewrite E32u; let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable _); apply HgP; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 96) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 96 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
rewrite E32u; let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable _); apply HgP; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac respell_shadow HS r o E32 E38 Hg0 Hgc Hal :=
lazymatch type of E32 with _ = Z_to_bv 64 ?g =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in let o8 := eval vm_compute in (o + 8) in
pose proof (st_ok_respell Ex ssx msx r (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 o8) (SLit 3)) (SOff 38 0)) HS eq_refl
ltac:(lazymatch goal with |- _ = sv_denot _ (sr_get ?a ?rr) => let v := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with v end;
change o8 with (o + 8);
etransitivity; [apply (shadow_slot_step Ex g o); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E38
| exact Hg0 | exact Hgc | clear; lia | clear; lia | exact Hal] |];
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in let o8 := eval vm_compute in (o + 8) in
pose proof (st_ok_respell Ex ssx msx r (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 o8) (SLit 3)) (SOff 38 0)) HS eq_refl
ltac:(lazymatch goal with |- _ = sv_denot _ (sr_get ?a ?rr) => let v := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with v end;
change o8 with (o + 8);
etransitivity; [apply (shadow_slot_step Ex g o); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E38
| exact Hg0 | exact Hgc | clear; lia | clear; lia | exact Hal] |];
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end end.
Ltac g_field HRg HB32 off n HG :=
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch type of HB32 with _ = ?g =>
lazymatch cs with context [YP09.mkChunk off (CVal n ?e)] =>
lazymatch e with
| SLit ?z =>
let v := eval vm_compute in (z mod 2 ^ (8 * Z.of_N n)) in
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi off n e HRg HB32 ltac:(cbn; tauto) ltac:(cbn; lia)) as HG;
change (bv_unsigned (sv_denot Ex (SLit z)) mod 2 ^ (8 * Z.of_N n)) with v in HG
| SOff ?a 0 =>
match goal with Ea : ew _ a = Z_to_bv 64 ?v |- _ =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi off n e HRg HB32 ltac:(cbn; tauto) ltac:(cbn; lia)) as HG;
cbn [sv_denot] in HG; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in HG; rewrite ?ew_ewset_other in HG by lia; rewrite ?ew_havoc_old in HG by lia;
rewrite Ea, ?Z.add_0_r, ?Z_to_bv_bv_unsigned in HG; rewrite (unsigned_lit_small v) in HG by lia
end
| _ =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi off n e HRg HB32 ltac:(cbn; tauto) ltac:(cbn; lia)) as HG
end
end end end.
Ltac img_word_fact :=
lazymatch goal with |- bv_unsigned (ew ?Ex ?a) = _ => let H := rnHEI Ex in exact (H a ltac:(unfold A_OBJ, A_TEXT, A_LIM; clear; lia)) end.
Ltac hei_prove :=
lazymatch goal with
| |- img_env _ _ (havoc ?Eo ?kk ?ws) => first [ apply img_env_havoc_hi; [hei_prove | cbv; lia] | apply img_env_havoc; [hei_prove | cbv; lia] ]
| |- img_env _ _ (ewset ?Eo ?n ?w) => first [ apply img_env_ewset_hi; [hei_prove | cbv; lia] | apply img_env_ewset_lo; [hei_prove | cbv; lia] ]
| |- img_env _ _ (Eimg _) => apply Eimg_env
| |- img_env _ _ ?Ev => first [ let H := rnHEI Ev in exact H
| lazymatch goal with H : af_E _ _ _ _ _ _ _ _ _ _ _ Ev |- _ => exact (af_E_img _ _ _ _ _ _ _ _ _ _ _ Ev H) end
| progress (cbv delta [Ev]); hei_prove ]
end.
