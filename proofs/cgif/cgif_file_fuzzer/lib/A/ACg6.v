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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 AChd AChe ACjr ACj3 ACgw ACh0 ACgy ACgv ACgu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACgo ACg8 ACg9 ACga ACgb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Ltac af_E_names HEB sp0 g :=
lazymatch type of HEB with af_EB _ _ _ _ _ _ _ _ _ _ _ _ ?E =>
pose proof HEB as (HE & E67 & E70 & E71 & E72);
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI);
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity);
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia);
assert (HAE54 : env_agree 54 E E) by (split; [intros; reflexivity | reflexivity]) end.
Ltac range_app_of Hia :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [Z.min Z.max] in Hx; generalize Hia; clear - Hx; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia.
Ltac evalE := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
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
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis ML : model_laws (as_universe B).
Hypothesis CMP : tcmpF_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_L2X : AF_C_stmtX K MT XN B -> AF_SM_stmtX K MT XN B -> AF_Li_stmtX K MT XN B 2.
Proof.
intros PC PSM n. induction n as [|n IH]; intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 f kk GPAL IMG LPAL gs gsF XHD Hihv CX HEB HPB Hn HS SHOK E657 E658 E648 Hkk HkN Hn1 XL; [lia|].
pose proof (af_xf_in _ XL) as XLm. clear XL.
af_B_namesX LAWS CX HEB HPB Hn. clear Hih. rename Hihv into Hih.
assert (XREL0' : af_xrel K (mrestrict (w_H W) mem) md s N img lpa fattr nlp GPAL IMG LPAL gs) by (split; [exact XREL0 | split; [exact XIMG0 | split; [exact XIMGL | exact XLPAL0]]]).
rewrite Hih in HS, SHOK, Hn; change (Z.to_nat 2) with 2%nat in Hn; change (33 + Z.to_nat 2)%nat with 35%nat in HS, SHOK; cbn [Z.mul Pos.mul] in HS.
assert (B35 : bv_unsigned (ew E 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 2 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N (proj1 HJ) Himg) as (_ & _ & _ & _ & HiP & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N (proj1 HJ) Hfimg) as (_ & _ & _ & _ & HfiP & _).
destruct (block_byte_val (w_H W) (ms_mem ms1) (img + kk) (proj1 (HiP (img + kk) ltac:(clear - HN1 HrN Hkk HkN Hn1; lia)))) as (bc & Abc & Vbc & Rbc).
destruct (block_byte_val (w_H W) (ms_mem ms1) (fr_img f + kk) (proj1 (HfiP (fr_img f + kk) ltac:(clear - HN1 HrN Hkk HkN Hn1; lia)))) as (bb & Abb & Vbb & Rbb).
pose proof (st_ok_pi_havoc_hi 662 E _ _ [Z_to_bv 64 bc; Z_to_bv 64 bb] HS ltac:(vm_compute; reflexivity)) as HS1.
clear HS. rename HS1 into HS.
remember (havoc E 662 [Z_to_bv 64 bc; Z_to_bv 64 bb]) as EP eqn:HEP in HS.
assert (OLDP : forall n, (n < 662)%nat -> ew EP n = ew E n) by (intros n0 Hn0; rewrite HEP; apply YN3v.ew_havoc_old; clear - Hn0; lia).
assert (EP218 : ew EP 662 = Z_to_bv 64 bc) by (rewrite HEP; change 662%nat with (662 + 0)%nat; rewrite (YN3v.ew_havoc_new E 662 _ 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (EP219 : ew EP 663 = Z_to_bv 64 bb) by (rewrite HEP; change 663%nat with (662 + 1)%nat; rewrite (YN3v.ew_havoc_new E 662 _ 1 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (HAEP : env_agree 512 E EP) by (rewrite HEP; apply env_agree_havoc_ge; [clear; lia | apply env_agree_refl]).
clear HEP.
assert (EP657 : ew EP 657 = Z_to_bv 64 (img + kk)) by (rewrite OLDP by (clear; lia); exact E657).
assert (EP658 : ew EP 658 = Z_to_bv 64 (fr_img f + kk)) by (rewrite OLDP by (clear; lia); exact E658).
assert (EP648 : ew EP 648 = Z_to_bv 64 (Z.of_nat (Datatypes.S n))) by (rewrite OLDP by (clear; lia); exact E648).
assert (BP : bv_unsigned (ew EP 657) = img + kk) by (rewrite EP657; apply unsigned_lit_small; clear - Hi4096 Hiceil HrN HN1 Hkk HkN C1; lia).
assert (BQ : bv_unsigned (ew EP 658) = fr_img f + kk) by (rewrite EP658; apply unsigned_lit_small; clear - Hfi4096 Hficeil HrN HN1 Hkk HkN C1; lia).
pose proof (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E EP HEB (proj1 HAEP)) as HEBP.
pose proof (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E EP _ HAEP eq_refl SHOK) as SHOKP.
clear HEB SHOK B35 E657 E658 E648. try clear HE E67 E70 E71 E72 EEo E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 E49 E50 E51 E52 E53 Usp E32u HAE54. rename HEBP into HEB. rename SHOKP into SHOK. af_E_names HEB sp0 g.
assert (B35 : bv_unsigned (ew EP 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (UP : U EP (SOff 657 0) = img + kk) by (apply (U_atom EP 657 _ EP657); clear - Hi4096 Hiceil HrN HN1 Hkk HkN C1; lia).
assert (UQ : U EP (SOff 658 0) = fr_img f + kk) by (apply (U_atom EP 658 _ EP658); clear - Hfi4096 Hficeil HrN HN1 Hkk HkN C1; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 648%nat (mkAF 1 4294967296 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP648, unsigned_lit_small by (clear - HN1 Hkk HkN; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HN1 Hkk HkN Hn1; lia)) as HS3; clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 648%nat (mkAF 1 4294967296 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP648, unsigned_lit_small by (clear - HN1 Hkk HkN; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HN1 Hkk HkN Hn1; lia)) as HS3; clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 657%nat (mkAF 4096 140737479966720 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite BP, Z.pow_0_r, Z.mod_1_r; clear - Hi4096 Hiceil HN1 HrN Hkk HkN Hn1 C1; lia)) as HS3; clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 657%nat (mkAF 4096 140737479966720 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite BP, Z.pow_0_r, Z.mod_1_r; clear - Hi4096 Hiceil HN1 HrN Hkk HkN Hn1 C1; lia)) as HS3; clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 658%nat (mkAF 4096 140737479966720 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite BQ, Z.pow_0_r, Z.mod_1_r; clear - Hfi4096 Hficeil HN1 HrN Hkk HkN Hn1 C1; lia)) as HS3; clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 658%nat (mkAF 4096 140737479966720 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite BQ, Z.pow_0_r, Z.mod_1_r; clear - Hfi4096 Hficeil HN1 HrN Hkk HkN Hn1 C1; lia)) as HS3; clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 662%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP218, unsigned_lit_small by (clear - Rbc; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rbc; lia)) as HS3; clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 662%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP218, unsigned_lit_small by (clear - Rbc; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rbc; lia)) as HS3; clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 663%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP219, unsigned_lit_small by (clear - Rbb; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rbb; lia)) as HS3; clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 663%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP219, unsigned_lit_small by (clear - Rbb; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rbb; lia)) as HS3; clear HS; rename HS3 into HS  end.
assert (Vbc' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (img + kk + 0) 1 bc) by (rewrite Z.add_0_r; exact Vbc).
assert (Vbb' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (fr_img f + kk + 0) 1 bb) by (rewrite Z.add_0_r; exact Vbb).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 657%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 662 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite BP; split; [clear - Hi4096 Hkk; lia|]; split; [clear - Hiceil HrN HN1 Hkk HkN Hn1 C1; lia|]; split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val SEGS Ex _ (img + kk)); [cbn [sv_denot]; rewrite EP218, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rbc; lia | cbn; clear; lia | exact Vbc'] | constructor])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite BP, ?B35, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dig Dic Dih Hi4096 Hih0 Hih0_img Hiceil HrN HN1 Hkk HkN Hn1 Hcfp Hh4096 Hhceil HZg Hceil Hslo HTS C1 C3 C4 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 657%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 662 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite BP; split; [clear - Hi4096 Hkk; lia|]; split; [clear - Hiceil HrN HN1 Hkk HkN Hn1 C1; lia|]; split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val SEGS Ex _ (img + kk)); [cbn [sv_denot]; rewrite EP218, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rbc; lia | cbn; clear; lia | exact Vbc'] | constructor])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite BP, ?B35, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dig Dic Dih Hi4096 Hih0 Hih0_img Hiceil HrN HN1 Hkk HkN Hn1 Hcfp Hh4096 Hhceil HZg Hceil Hslo HTS C1 C3 C4 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 658%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 663 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite BQ; split; [clear - Hfi4096 Hkk; lia|]; split; [clear - Hficeil HrN HN1 Hkk HkN Hn1 C1; lia|]; split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val SEGS Ex _ (fr_img f + kk)); [cbn [sv_denot]; rewrite EP219, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rbb; lia | cbn; clear; lia | exact Vbb'] | constructor])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite BQ, BP, ?B35, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dfg Dfc Dif Dfh Hfi4096 Hfih0 Hfih0_img Hficeil HrN HN1 Hkk HkN Hn1 Hcfp Hh4096 Hhceil HZg Hceil Hslo HTS C1 C3 C4 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 658%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 663 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite BQ; split; [clear - Hfi4096 Hkk; lia|]; split; [clear - Hficeil HrN HN1 Hkk HkN Hn1 C1; lia|]; split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val SEGS Ex _ (fr_img f + kk)); [cbn [sv_denot]; rewrite EP219, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rbb; lia | cbn; clear; lia | exact Vbb'] | constructor])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite BQ, BP, ?B35, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dfg Dfc Dif Dfh Hfi4096 Hfih0 Hfih0_img Hficeil HrN HN1 Hkk HkN Hn1 Hcfp Hh4096 Hhceil HZg Hceil Hslo HTS C1 C3 C4 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. clear Vbc' Vbb'.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_asan3_cmpPixel;
try (lazymatch goal with
| |- context [U _ (SOff 658 0)] =>
rewrite UQ; lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?mm)) _ _ _ =>
eapply (obl_of_block SEGS B LAWS ly S W mm _ EP Bxa (fr_img f + kk) 1 (fr_img f) N (proj1 HJ) Hfimg) end;
[ unfold U, Bxa; cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; clear; lia); reflexivity
| clear - Hkk; lia | clear - HrN HN1 Hkk HkN Hn1; lia ]
| |- context [U _ (SOff 657 0)] =>
rewrite UP; lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?mm)) _ _ _ =>
eapply (obl_of_block SEGS B LAWS ly S W mm _ EP Bxa (img + kk) 1 img N (proj1 HJ) Himg) end;
[ unfold U, Bxa; cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; clear; lia); reflexivity
| clear - Hkk; lia | clear - HrN HN1 Hkk HkN Hn1; lia ]
| |- awr_ok _ _ _ _ _ _ _ _ _ => awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq
end).
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12; prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Q2, Q3, Q4, Q1, Q8, Q10, Q11, Q12, Q13, Q14.
rewrite ?ew_ewset_other in Q2 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in Q3 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in Q4 by (clear - PBASE PBLO; lia).
rewrite ?ew_ewset_other in Q8 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in Q10 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in Q11 by (clear - PBASE PBLO; lia).
rewrite ?ew_ewset_other in Q12 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in Q13 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in Q14 by (clear - PBASE PBLO; lia).
pmkst HS.
pose proof (cfp_obj_journalN B LAWS sp0 ly S W mem md [] ly S W _ _ 0 g s N _ cfp _ HJ HAR HPerm HFO HCF) as HCF1.
pose proof (afobj_journalN B LAWS sp0 ly S W mem md [] ly S W _ _ 0 g s N _ cfp 32 HJ HAR HPerm HFO) as HFO1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Hgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Htp);
assert (Qsp : spZ rg = sp0 + -224) by (unfold spZ; rewrite Q2, Usp; rewrite unsigned_lit_small by (clear - Hceil Hslo Hshi H47 HTS C1; lia); clear; lia);
assert (Q10' : getr rg 10 = w64 g) by (rewrite Q10; exact E32);
assert (Q11' : getr rg 11 = w64 cfp) by (rewrite Q11; exact E46);
assert (Q12' : getr rg 12 = w64 (fr_ptr f)) by (rewrite Q12, E35, Hn; reflexivity);
assert (Q13' : getr rg 13 = w64 bc) by (rewrite Q13; first [exact EP218 | cbn [sv_denot]; rewrite EP218; reflexivity | rewrite denot_lit_U, (U_zext_small EP 8 _ bc (U_atom EP 662 bc EP218 ltac:(clear - Rbc; lia))) by (clear - Rbc; cbn; lia); reflexivity]);
assert (Q14' : getr rg 14 = w64 bb) by (rewrite Q14; first [exact EP219 | cbn [sv_denot]; rewrite EP219; reflexivity | rewrite denot_lit_U, (U_zext_small EP 8 _ bb (U_atom EP 663 bb EP219 ltac:(clear - Rbb; lia))) by (clear - Rbb; cbn; lia); reflexivity]);
assert (Qs0 : achain ly (aview SEGS (w_H W) mm) (sp0 + -224) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; rewrite E32u, unsigned_lit_small by (clear - Hg4096 Hgceil C1; lia); clear - Hgceil; lia);
assert (HTg : obj_at SEGS (mrestrict (w_H W) mm) g LAY_CGIF (xcgif_vals path hw pf s))
by (rewrite <- (cl_set_cur_same s); apply (obj_cgif_setcurX SEGS path hw pf _ _ g s (cg_cur s) (proj1 HT) HGK); [| exact Rcur];
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rg5 := eval vm_compute in (nth 6 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 6 rg5 HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) (cg_cur s) HRg ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; clear; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc; exact Vc end | st_ok _ ?Ex ?ssx ?msx =>
let rg5 := eval vm_compute in (nth 6 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 6 rg5 HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) (cg_cur s) HRg ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; clear; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc; exact Vc end  end)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS W rg mm _ TADDFRAME_STK sp0 (FPn g) ly S W mem md [] ly S mdq 0 TCMP_STK [] 0 (-224) (Z_to_bv 64 (BASE + 0xa64)) []
(fun ly3 S3 W3 regs3 mem3 md3 => ly3 = ly /\ S3 = S /\ W3 = W /\
(getr regs3 10 = w64 0 <-> AChd.tcmp_zero (aview SEGS (w_H W) mm) (cg_pal s) (cg_ngp s) lpal fattr nlp tidx (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) bc bb)) HJ Qsp);
[ reflexivity | clear; lia | unfold TCMP_STK, ESTACK; clear; lia | rewrite HTS; unfold TCMP_STK, ESTACK; clear; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [clear; lia | reflexivity] | rewrite unsigned_lit_small by (clear - PBASE PBLO; lia); clear - PBASE PBLO; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (CMP ly S W rg mm mdq [] g cfp (fr_ptr f) bc bb (xcgif_vals path hw pf s) [lpal; img; fattr; fgen; delay; nlp; tidx] (frame_vals f)
(cg_pal s) (cg_ngp s) lpal fattr nlp tidx (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f)
HPRE1 Q10' Q11' Q12' Q13' Q14' Rbc Rbb Hing HFO1 Hfb HTg eq_refl eq_refl HCF1 eq_refl eq_refl eq_refl eq_refl (proj2 HSD f HfIn) eq_refl eq_refl eq_refl eq_refl)
| cbv beta; unfold tcmp_post; intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ1 & HP & Hv3 & Hz3);
exists ly, S, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | split; [reflexivity | split; [reflexivity | split; [reflexivity | rewrite Hv3; exact Hz3]]]]]] ]
| intros a Ha; destruct Ha as (rr & Hrr & _); destruct Hrr ]
| ] end.
{
intros Hc1. destruct (Z.land fattr 1 =? 0) eqn:Hq; [apply Z.eqb_eq in Hq; exfalso; exact (Hc1 Hq)|].
assert (Hlpab : In (lpa, 3 * nlp) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. right. try rewrite Hq. left. reflexivity. }
exists (3 * nlp). split; [| clear; lia].
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) HAR Hlpab) as (_ & Hl4096 & Hlceil & _ & _ & _ & Hl0 & _).
pose proof (req_size_pos (3 * nlp) ltac:(clear - Hl0; lia)) as [Hrl _].
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. cbn [snd] in Rlpal. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rlpal.
assert (Elp : lpa = lpal).
{ apply (f_equal bv_unsigned) in Hlpa. rewrite !unsigned_lit_small in Hlpa by (clear - Hl4096 Hlceil Hrl Rlpal C1; lia). exact Hlpa. }
rewrite <- Elp. exact Hlpab. }
{
intros Hb1. exists (3 * fr_nlp f). split; [| clear; lia].
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. left. unfold cgif_blocks. right. right. apply in_or_app. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact HfIn|]. unfold frame_blocks.
destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hq; [apply Z.eqb_eq in Hq; exfalso; exact (Hb1 Hq)|]. right. right. left. reflexivity. }
{
intros Hgl. exists (3 * cg_ngp s). split; [| clear; lia].
assert (Hg4 : Z.land (cg_attr s) 4 = 0).
{ destruct Hgl as [Hc0 | Hb0]; [destruct HnoTab as [X|X]; [exfalso; exact (X Hc0) | exact X] |].
exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))) f HfIn) Hb0). }
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. left. unfold cgif_blocks. right. right. apply in_or_app. left.
unfold pal_blocks. rewrite (proj2 (Z.eqb_eq _ _) Hg4). left. reflexivity. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (-> & -> & -> & XV)).
assert (XVm : af_xf (bc = nth (Z.to_nat kk) IMG 0 /\ bb = nth (Z.to_nat kk) (YO07.f_img XHD) 0 /\ Z.of_nat (length (YO07.f_img XHD)) = N /\
(getr regs2 10 = w64 0 <-> YO07.cmp_pixel (gcfg_of s GPAL) (YI0b.af_nf (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG) XHD bc bb = false))).
{ destruct (af_xf_out _ XLm) as (XLV & _ & XqHD & _).
assert (Hn' : nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f) by (rewrite Hih; exact Hn).
pose proof (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs (proj1 HPB) HPerm Hpfr HWF XREL0') as XR1.
pose proof (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF XREL0') as XR2.
destruct (af_xl_pix K _ (aview SEGS (w_H W) (ms_mem ms1)) _ s N img lpa fattr nlp GPAL IMG LPAL gs f XHD kk bc bb (fun a => eq_refl) XR1 XLV (or_intror Hih) Hn' XqHD ltac:(clear - Hkk HkN Hn1; lia) Abc Abb) as [Ebc Ebb].
pose proof (af_xb_headq K _ _ s N GPAL gs f XHD XREL0 XLV (or_intror Hih) Hn' XqHD) as (_ & _ & _ & _ & _ & _ & _ & _ & LFI & _).
unfold af_xf. split; [exact Ebc|]. split; [exact Ebb|]. split; [exact LFI|].
eapply iff_trans; [exact XV|].
lazymatch type of XV with (_ <-> AChd.tcmp_zero (aview _ _ ?mT) _ _ _ _ _ _ _ _ _ _ _ _) =>
apply (af_xl_verdict K (mrestrict (w_H W) mT) (aview SEGS (w_H W) mT) _ s N img lpa lpal fattr fgen delay nlp tidx GPAL IMG LPAL gs f XHD bc bb (fun a => eq_refl) XR2 XLV (or_intror Hih) Hn' XqHD) end;
[ exact (af_lpa_eq B LAWS ly S W mem md g s N img fattr fgen delay tidx lpa lpal nlp rest cfp HAR HPerm HCF Hlpa)
| intros Hgl; destruct Hgl as [Hc0 | Hb0]; [destruct HnoTab as [X|X]; [exfalso; exact (X Hc0) | exact X] | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))) f HfIn) Hb0)]
| exact Rbc | exact Rbb ]. }
clear Q3' Q4' Q10' Q11' Q12' Q13' Q14' Qs0 HTg HCF1 HFO1.
change (0 + 0) with 0 in HJ2.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K A_LIM Bxa (af_SHB 35) ss) | st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM Bxa (af_SHB 35) ss)  end in
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [2; 3; 4; 5; 6; 7]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | evalE; exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | evalE; exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | clear; lia] end.
- lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | clear; lia] end.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE (proj1 HJ2) Hing) as (_ & _ & _ & _ & HgP2 & _). change (req_size CGIF_SIZE) with 96 in HgP2.
eapply (YC4b.region_kept_block_subw B); [exact HJc2 | evalE; exact E32u | exact Hing | exact Hing | clear; lia
| change (req_size CGIF_SIZE) with 96; clear; lia | intros a Ha HFP; destruct HFP as (rr & Hrr & _); destruct Hrr
| intros a Ha; apply (fun Hq => proj1 (HgP2 a Hq)); clear - Ha; lia].
- eapply (region_kept_frame_sub B); [exact HJc2 | evalE; rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia
| intros a Ha HFP; destruct HFP as (rr & Hrr & _); destruct Hrr
| intros a Ha; exfalso; clear - Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ (havoc ?Ei ?Kx ?vx) _ _ =>
remember (havoc Ei Kx vx) as E2 eqn:HE2 in HS;
assert (OLD2 : forall n, (n < 664)%nat -> ew E2 n = ew EP n) by (intros n0 Hn0; rewrite HE2; rewrite YN3v.ew_havoc_old by (clear - Hn0; lia); rewrite ?ew_ewset_other by (clear - Hn0; lia); reflexivity);
assert (HAE2 : env_agree 512 EP E2) by (rewrite HE2; env_agree_chain (env_agree_refl 512 EP)) | st_ok _ (havoc ?Ei ?Kx ?vx) _ _ =>
remember (havoc Ei Kx vx) as E2 eqn:HE2 in HS;
assert (OLD2 : forall n, (n < 664)%nat -> ew E2 n = ew EP n) by (intros n0 Hn0; rewrite HE2; rewrite YN3v.ew_havoc_old by (clear - Hn0; lia); rewrite ?ew_ewset_other by (clear - Hn0; lia); reflexivity);
assert (HAE2 : env_agree 512 EP E2) by (rewrite HE2; env_agree_chain (env_agree_refl 512 EP))  end.
assert (XA0 : ew E2 668 = getr regs2 10) by (rewrite HE2; change 668%nat with (664 + 4)%nat; rewrite (YN3v.ew_havoc_new _ 664 _ 4 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
clear HE2.
assert (E2_657 : ew E2 657 = Z_to_bv 64 (img + kk)) by (rewrite OLD2 by (clear; lia); exact EP657).
assert (E2_658 : ew E2 658 = Z_to_bv 64 (fr_img f + kk)) by (rewrite OLD2 by (clear; lia); exact EP658).
assert (E2_648 : ew E2 648 = Z_to_bv 64 (Z.of_nat (Datatypes.S n))) by (rewrite OLD2 by (clear; lia); exact EP648).
pose proof (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ EP E2 HEB (proj1 HAE2)) as HEB2.
clear HEB B35 BP BQ UP UQ EP657 EP658 EP648 EP218 EP219 OLDP HAEP. try clear HE E67 E70 E71 E72 EEo E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 E49 E50 E51 E52 E53 Usp E32u HAE54. rename HEB2 into HEB. af_E_names HEB sp0 g.
assert (B35 : bv_unsigned (ew E2 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
pose proof (af_side_blk B ly S W _ mem2 _ g s N _ (proj1 HJ) HPerm HSD G2) as HSD2. clear HSD. rename HSD2 into HSD.
assert (HGK2 : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS (mrestrict (w_H W) mem2) (g + i) = mbyte SEGS (mrestrict (w_H W) mem) (g + i)).
{ intros i Hi Hni. etransitivity; [| exact (HGK i Hi Hni)]. apply (mbyte_of_aview SEGS).
apply (G2 g CGIF_SIZE i Hing Hing); [change (req_size CGIF_SIZE) with 96; clear - Hi; lia | intros X; destruct X as (rr & Hrr & _); destruct Hrr]. }
clear HGK G2. rename HGK2 into HGK.
clear SHOK. assert (SHOK : sh_ok SEGS Bxa (af_SHB 35) E2 (mrestrict (w_H W) mem2)).
{ pose proof (afobj_journalN B LAWS sp0 ly S W mem md [] ly S W _ _ _ g s N _ cfp 32 HJ2 HAR HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SHB, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block SEGS B LAWS ly S W mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE (proj1 HJ2) Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + range_app_of Hcfp_ia.
- apply (shent_ok_of_block SEGS B LAWS ly S W mem2 md2 E2 Bxa 35 (fr_ptr f) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ2) Hfb).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact B35.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
clear HJ HJc2. rename HJ2 into HJ.
assert (HPB2 : af_preBX B ly S W regs mem md g cfp s N fattr (mkst regs2 (Z_to_bv 64 (BASE + 0xa64)) mem2 (seg_rom SEGS)) md2).
{ split; [exact HJ|]. split; [exact HSD|]. split; [exact HGK|]. split; [exact Hcur|]. split; [exact HnoTab | rewrite Hih; clear; lia]. }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{ paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_C; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (xs_C 2 16 35) 644%nat.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E2); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E2); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
destruct (af_xf_out _ XVm) as (Ebc & Ebb & LFI & XVQ);
apply (af_xl_c s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD kk N (af_xf_out _ XLm) ltac:(clear - Hkk HkN Hn1; lia) XIMGL LFI);
rewrite <- Ebc, <- Ebb;
lazymatch goal with |- ?cp = true => destruct (Bool.bool_dec cp true) as [XQ | XQ]; [exact XQ | exfalso; apply Bool.not_true_is_false in XQ] end;
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E9 (SOff 668 0)) _ = true |- _ => exact (af_bbr_a0ne E9 668 _ true XA0 H (proj2 XVQ XQ)) end ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E2); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E2); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
destruct (af_xf_out _ XVm) as (Ebc & Ebb & LFI & XVQ);
apply (af_xl_c s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD kk N (af_xf_out _ XLm) ltac:(clear - Hkk HkN Hn1; lia) XIMGL LFI);
rewrite <- Ebc, <- Ebb;
lazymatch goal with |- ?cp = true => destruct (Bool.bool_dec cp true) as [XQ | XQ]; [exact XQ | exfalso; apply Bool.not_true_is_false in XQ] end;
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E9 (SOff 668 0)) _ = true |- _ => exact (af_bbr_a0ne E9 668 _ true XA0 H (proj2 XVQ XQ)) end ]  end. }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_SAME; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
pose proof (proj2 HSD f HfIn) as HOBf.
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) (fr_img f) HOBf eq_refl eq_refl) as [Vhimg Rhimg].
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) (fr_attr f) HOBf eq_refl eq_refl) as [Vhattr Rhattr].
pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) (fr_delay f) HOBf eq_refl eq_refl) as [Vhdel Rhdel].
cbn [snd N.to_nat] in Vhimg, Rhimg, Vhattr, Rhattr, Vhdel, Rhdel.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rhimg. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rhattr. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rhdel.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (af_hdr 35) HS eq_refl
ltac:(unfold region_ok, af_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
rewrite B35; split; [clear - Hh4096 Hhceil C1; lia|]; split; [clear - Hh4096 Hhceil C1; lia|];
split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val SEGS Ex _ (fr_ptr f)); [cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite E70, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhimg]|];
constructor; [eapply (chunk_ok_val SEGS Ex _ (fr_ptr f)); [cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite E71, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhattr]|];
constructor; [eapply (chunk_ok_val SEGS Ex _ (fr_ptr f)); [cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite E72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhdel]|];
constructor)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
rewrite B35, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgh Dch Hh4096 Hhh Hhh_img Hhceil Hcfp HZg Hceil Hslo HTS C1 C3 C4 Hob241 Hob253; unfold off_img in Hhh_img; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
af_rejoin HS (xs_SM 2 16 35) 644%nat.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | env_agree_chain HAE54 || (split; [intros; reflexivity | reflexivity])]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
destruct (af_xf_out _ XVm) as (Ebc & Ebb & LFI & XVQ);
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E9 (SOff 668 0)) _ = false |- _ => pose proof (proj1 XVQ (af_bbr_a0ne E9 668 _ false XA0 H)) as XQ end;
rewrite Ebc, Ebb in XQ;
pose proof (af_xl_step s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD kk N (af_xf_out _ XLm) ltac:(clear - Hkk HkN Hn1; lia) XIMGL LFI XQ) as XL1;
assert (XkN : N = kk + 1)
by (lazymatch goal with Hz : branch_taken BC_EQ _ _ = true |- _ =>
rewrite branch_eq_U in Hz; rewrite (U_atom_off _ 648 (Z.of_nat (Datatypes.S n)) (-1)) in Hz; [| evalE; exact E2_648 | clear - HN1 Hkk HkN; lia | clear - HN1 Hkk HkN; lia];
rewrite U_lit in Hz by (clear; lia); apply (proj1 (Z.eqb_eq _ _)) in Hz; clear - Hz HkN; lia end);
rewrite <- XkN in XL1;
exact (af_xl_sm K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD XREL0 (or_intror Hih) XL1 XIMGL LFI) ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | env_agree_chain HAE54 || (split; [intros; reflexivity | reflexivity])]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
destruct (af_xf_out _ XVm) as (Ebc & Ebb & LFI & XVQ);
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E9 (SOff 668 0)) _ = false |- _ => pose proof (proj1 XVQ (af_bbr_a0ne E9 668 _ false XA0 H)) as XQ end;
rewrite Ebc, Ebb in XQ;
pose proof (af_xl_step s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD kk N (af_xf_out _ XLm) ltac:(clear - Hkk HkN Hn1; lia) XIMGL LFI XQ) as XL1;
assert (XkN : N = kk + 1)
by (lazymatch goal with Hz : branch_taken BC_EQ _ _ = true |- _ =>
rewrite branch_eq_U in Hz; rewrite (U_atom_off _ 648 (Z.of_nat (Datatypes.S n)) (-1)) in Hz; [| evalE; exact E2_648 | clear - HN1 Hkk HkN; lia | clear - HN1 Hkk HkN; lia];
rewrite U_lit in Hz by (clear; lia); apply (proj1 (Z.eqb_eq _ _)) in Hz; clear - Hz HkN; lia end);
rewrite <- XkN in XL1;
exact (af_xl_sm K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD XREL0 (or_intror Hih) XL1 XIMGL LFI) ]  end. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_LOOP; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hcnt end.
prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R24. prreg HS (20%bv : bv 5) R9.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in R19, R24, R9.
rewrite ?ew_ewset_other in R19 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in R24 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in R9 by (clear - PBASE PBLO; lia).
af_rejoin HS (xs_L0 2 16 35) 644%nat.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (IH ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f (kk + 1) GPAL IMG LPAL gs gsF XHD Hih CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | env_agree_chain HAE54 || (split; [intros; reflexivity | reflexivity])]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
change 657%nat with (644 + 13)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; cbn [sv_denot]; rewrite E2_657, unsigned_lit_small by (clear - Hi4096 Hiceil HrN HN1 Hkk HkN C1; lia); unfold w64; f_equal; clear; lia
| change 658%nat with (644 + 14)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; cbn [sv_denot]; rewrite E2_658, unsigned_lit_small by (clear - Hfi4096 Hficeil HrN HN1 Hkk HkN C1; lia); unfold w64; f_equal; clear; lia
| change 648%nat with (644 + 4)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; cbn [sv_denot]; rewrite E2_648, unsigned_lit_small by (clear - HN1 Hkk HkN; lia); unfold w64; f_equal; clear; lia
| clear - Hkk; lia | clear - HkN; lia
|
rewrite branch_eq_U in Hcnt; rewrite (U_atom_off _ 648 (Z.of_nat (Datatypes.S n)) (-1)) in Hcnt; [| evalE; exact E2_648 | clear - HN1 Hkk HkN; lia | clear - HN1 Hkk HkN; lia];
rewrite U_lit in Hcnt by (clear; lia); apply (proj1 (Z.eqb_neq _ _)) in Hcnt; clear - Hcnt; lia
|
destruct (af_xf_out _ XVm) as (Ebc & Ebb & LFI & XVQ);
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E9 (SOff 668 0)) _ = false |- _ => pose proof (proj1 XVQ (af_bbr_a0ne E9 668 _ false XA0 H)) as XQ end;
rewrite Ebc, Ebb in XQ;
exact (af_xl_step s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD kk N (af_xf_out _ XLm) ltac:(clear - Hkk HkN Hn1; lia) XIMGL LFI XQ) ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (IH ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f (kk + 1) GPAL IMG LPAL gs gsF XHD Hih CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | env_agree_chain HAE54 || (split; [intros; reflexivity | reflexivity])]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
change 657%nat with (644 + 13)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; cbn [sv_denot]; rewrite E2_657, unsigned_lit_small by (clear - Hi4096 Hiceil HrN HN1 Hkk HkN C1; lia); unfold w64; f_equal; clear; lia
| change 658%nat with (644 + 14)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; cbn [sv_denot]; rewrite E2_658, unsigned_lit_small by (clear - Hfi4096 Hficeil HrN HN1 Hkk HkN C1; lia); unfold w64; f_equal; clear; lia
| change 648%nat with (644 + 4)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; cbn [sv_denot]; rewrite E2_648, unsigned_lit_small by (clear - HN1 Hkk HkN; lia); unfold w64; f_equal; clear; lia
| clear - Hkk; lia | clear - HkN; lia
|
rewrite branch_eq_U in Hcnt; rewrite (U_atom_off _ 648 (Z.of_nat (Datatypes.S n)) (-1)) in Hcnt; [| evalE; exact E2_648 | clear - HN1 Hkk HkN; lia | clear - HN1 Hkk HkN; lia];
rewrite U_lit in Hcnt by (clear; lia); apply (proj1 (Z.eqb_neq _ _)) in Hcnt; clear - Hcnt; lia
|
destruct (af_xf_out _ XVm) as (Ebc & Ebb & LFI & XVQ);
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E9 (SOff 668 0)) _ = false |- _ => pose proof (proj1 XVQ (af_bbr_a0ne E9 668 _ false XA0 H)) as XQ end;
rewrite Ebc, Ebb in XQ;
exact (af_xl_step s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XHD kk N (af_xf_out _ XLm) ltac:(clear - Hkk HkN Hn1; lia) XIMGL LFI XQ) ]  end.
Qed.
End d.
End c.
End b.
