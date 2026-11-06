(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCdy YCe9 YCfs YCfr YCgw YCfu YCe1 YCe4 YCe2 YCe0 YCe3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis FLUSH : tflush_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Lemma regsA_ok : forall (regs : bvmap 5 word) g s1,
getr regs 10 = w64 g -> 4096 <= g -> g + 96 <= alloc_ceiling ->
regs_ok (Ereg regs (cl_extra regs g s1)) regsA regs.
Proof.
intros regs g s1 H10 Hlo Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs (cl_extra regs g s1)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity | rewrite E32; exact H10 ]
| ]); try (destruct Hr; fail).
Qed.
Lemma alu64_not : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma cl_frame_of_region0 : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) wlo whi,
region_ok trbsegs E m (YQ0b.mkRegion (Some 2%nat) (-80) 0 wlo whi [YQ0b.mkChunk (-80) (CVal 8 (SOff 24 0)); YQ0b.mkChunk (-72) (CVal 8 (SOff 23 0)); YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0)); YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0)); YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0)); YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0)); YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0)); YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
cl_frame m sp0 regs.
Proof.
intros E m sp0 regs wlo whi HR Hsp HE j r Hj.
assert (Hj9 : (j < 10)%nat) by (apply (proj1 (nth_error_Some cl_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
do 10 (destruct j as [|j];
[ cbn in Hj; injection Hj as <-;
lazymatch goal with |- val_mem _ _ (_ + ?od) _ (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
let od' := eval vm_compute in od in change od with od';
let n := eval vm_compute in (Z.to_nat R) in
apply (field_of_region E m 2 sp0 _ (-80) 0 wlo whi od' 8 (SOff n 0) _ HR Hsp);
[ cbn; tauto
| cbn [sv_denot]; rewrite (HE n (Z_to_bv 5 R) eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
| exact HRr
| cbn; lia ] end
| ]). cbn in Hj9. lia.
Qed.
Ltac awr_clA Usp E32u Hing HTS :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite HTS; lia | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | exact E32u | exact Hing | cbn [YQ0b.r_wlo]; lia
| cbn [YQ0b.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; unfold FPc, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| apply awr_ok_nil ] end.
Lemma cl_A_ok : CL_B_stmt B -> CL_IT_stmt B 1 ->
forall ly S W regs mem md ch g s N rest,
cl_cx B ly S W regs mem md ch g s N rest ->
SRr trbsegs W (cfg_at trbsegs A_cgif_close regs mem md) (cl_post B ly S W regs mem md g s N rest (2 * EV_FLUSH + 16)).
Proof.
intros CLB IT1 ly S W regs mem md ch g s N rest CX.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajournal_init trbsegs B TCLOSE_STK (FPc g s N) ly S W regs mem md ch HPRE) as HJ.
assert (HTS : TCLOSE_STK = 17520) by reflexivity. assert (HEVF : EV_FLUSH = 35) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen.
assert (HOK : cl_obj_ok g s s N) by (split; [exact HWF | repeat split; reflexivity]).
destruct (cl_seed_entry B TL LAWS A_cgif_close regsA W regs regs mem ly S md ly sp0 g s HAR Hing Hstk Hpres
ltac:(unfold sp0, spZ; lia) (regsA_ok regs g s H10 Hgh Hgceil) (proj1 HT)) as [HS SHOK].
unfold cfg_at. change (mkst regs (Z_to_bv 64 A_cgif_close) mem (seg_rom trbsegs)) with (mkst regs (Z_to_bv 64 A_cgif_close) mem (seg_rom trbsegs)) in *.
set (E := Ereg regs (cl_extra regs g s)) in *.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, ew E (32 + j) = nth j (cl_extra regs g s) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo; reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s)) by (change 37%nat with (32 + 5)%nat; rewrite EXo; reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo; reflexivity).
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanC.
{ awr_clA Usp E32u Hing HTS. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
pose proof (U_atom E 37 (cg_cur s) E37 ltac:(clear - Rcur; lia)) as Ucur.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanC.
-
rewrite branch_ne_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity. rewrite (cl_U_sext32 E (SOff 37 0) (cg_cur s) Ucur Rcur) in Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanC CL_B.
{ awr_clA Usp E32u Hing HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H W) E _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) Q2; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4; rreg HS (8%bv : bv 5) Q8; rreg HS (9%bv : bv 5) Q9; rreg HS (19%bv : bv 5) Q19.
rreg HS (20%bv : bv 5) Q20; rreg HS (18%bv : bv 5) Q18.
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : tcgif_at (mrestrict (w_H W) _) g (cl_set_cur s (cg_cur s)))
by (eapply (tcgif_at_stretchA B LAWS ly S W mem md _ g s s N rest (cg_cur s) HAR HPerm HOK HT); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a) by (clear - Ha Hna Hceil Hslo HTS C1; lia); apply UN1; clear - Ha Hna Hceil Hslo HTS C1; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N rest ly S W rg mm mdq 0 (cl_set_cur s (cg_cur s)) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [lia|]. split.
{ exact (cl_frame_of_region0 E _ sp0 regs _ _ HR0 Usp EEo). }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s N _ HOK) | exact HPerm].
+ clear - HEVF. lia.
+
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
* rewrite Q2. cbn [sv_denot]. rewrite Usp. unfold sp0, spZ. reflexivity.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Hgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Htp.
* rewrite Q8. exact E32.
* rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* rewrite Q18. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. exact E38.
*
rewrite Q20, E32. rewrite (alu64_not g) by (clear - Hgh Hgceil C1; lia). reflexivity.
* intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H W) E _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); reflexivity end).
-
rewrite branch_ne_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity. rewrite (cl_U_sext32 E (SOff 37 0) (cg_cur s) Ucur Rcur) in Hc.
assert (Hcur0 : cg_cur s = 0).
{ destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); cbn [negb] in Hc;
[destruct (Z.eqb_spec (cg_cur s) 0); [assumption | discriminate Hc] | destruct (Z.eqb_spec (cg_cur s - 2 ^ 32 + 2 ^ 64) 0); [clear - Rcur e; lia | discriminate Hc]]. }
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanC CL_IT.
{ awr_clA Usp E32u Hing HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H W) E _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) Q2; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4; rreg HS (8%bv : bv 5) Q8; rreg HS (9%bv : bv 5) Q9; rreg HS (19%bv : bv 5) Q19.
rreg HS (20%bv : bv 5) Q20; rreg HS (18%bv : bv 5) Q18; rreg HS (21%bv : bv 5) Q21; rreg HS (22%bv : bv 5) Q22; rreg HS (23%bv : bv 5) Q23; rreg HS (10%bv : bv 5) Q10.
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : tcgif_at (mrestrict (w_H W) _) g (cl_set_cur s (cg_cur s)))
by (eapply (tcgif_at_stretchA B LAWS ly S W mem md _ g s s N rest (cg_cur s) HAR HPerm HOK HT); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a) by (clear - Ha Hna Hceil Hslo HTS C1; lia); apply UN1; clear - Ha Hna Hceil Hslo HTS C1; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (IT1 ly S W regs mem md ch g s N rest ly S W rg mm mdq 0 (cl_set_cur s (cg_cur s)) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [lia|]. split.
{ exact (cl_frame_of_region0 E _ sp0 regs _ _ HR0 Usp EEo). }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s N _ HOK) | exact HPerm].
+ clear - HEVF. lia.
+ cbn [cg_cur cl_set_cur]. exact Hcur0.
+
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
* rewrite Q2. cbn [sv_denot]. rewrite Usp. unfold sp0, spZ. reflexivity.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Hgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Htp.
* rewrite Q8. exact E32.
* rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* rewrite Q18. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. exact E38.
*
rewrite Q20, E32. rewrite (alu64_not g) by (clear - Hgh Hgceil C1; lia). reflexivity.
* intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H W) E _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); reflexivity end).
+ rewrite Q10. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q21. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q22. apply bv_eq. vm_compute. reflexivity.
+ rewrite Q23. apply bv_eq. vm_compute. reflexivity.
Qed.
Theorem trb_cgif_close : tclose_spec B.
Proof.
unfold tclose_spec. intros ly S W regs mem md ch g s N rest HPRE Hctx Hfr7 HROD H10 HT HWF HPerm Hev Hlive.
assert (CX : cl_cx B ly S W regs mem md ch g s N rest).
{ split; [exact HPRE|]. split; [exact Hctx|]. split; [exact Hfr7|]. split; [exact HROD|]. split; [exact H10|].
split; [exact HT|]. split; [exact HWF|]. split; [exact HPerm|]. split; [unfold EV_CLOSE in Hev; lia | exact Hlive]. }
assert (AFT2 : CL_AFTER_stmt B 2) by (apply cl_AFT2_ok; assumption).
assert (FR2 : CL_FR_stmt B 2) by (apply cl_FR2_ok; assumption).
assert (AFT1 : CL_AFTER_stmt B 1) by (apply cl_AFT1_ok; assumption).
assert (FR1 : CL_FR_stmt B 1) by (apply cl_FR1_ok; assumption).
assert (AFT0 : CL_AFTER_stmt B 0) by (apply cl_AFT0_ok; assumption).
assert (FR0 : CL_FR_stmt B 0) by (apply cl_FR0_ok; assumption).
assert (RC : CL_RC_stmt B) by (apply cl_RC_ok; assumption).
assert (CLB : CL_B_stmt B) by (apply cl_B_ok; assumption).
assert (IT2 : CL_IT_stmt B 2) by (apply cl_IT2_ok; assumption).
assert (IT1 : CL_IT_stmt B 1) by (apply cl_IT1_ok; assumption).
eapply SRr_mono; [exact (cl_A_ok CLB IT1 ly S W regs mem md ch g s N rest CX)|].
intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ & HP & HK). unfold apost_base.
exists ly', S', regs', mem', md'. split; [reflexivity|]. split; [| split; [exact HP | exact HK]].
unfold EV_CLOSE. replace (16 + 2 * EV_FLUSH) with (2 * EV_FLUSH + 16) by lia. exact HJ.
Qed.
End f. End c.
