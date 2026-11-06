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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI1h YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC17 YC18 YC0u YC0w YC0j YC0v YC0q YC0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac af_E_names HEB sp0 g :=
lazymatch type of HEB with af_EB _ _ _ _ _ _ _ _ _ _ _ _ ?E =>
pose proof HEB as (HE & E67 & E70 & E71 & E72);
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53);
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity);
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia);
assert (HAE54 : env_agree 54 E E) by (split; [intros; reflexivity | reflexivity]) end.
Ltac range_app_of Hia :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [Z.min Z.max] in Hx; generalize Hia; clear - Hx; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia.
Ltac evalE := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis CMP : tcmpF_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma af_L2 : AF_C_stmt B -> AF_SM_stmt B -> AF_Li_stmt B 2.
Proof.
intros PC PSM n. induction n as [|n IH]; intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 f kk Hihv CX HEB HPB Hn HS SHOK E213 E214 E204 Hkk HkN Hn1; [lia|].
af_B_names LAWS CX HEB HPB Hn. clear Hih. rename Hihv into Hih.
rewrite Hih in HS, SHOK, Hn; change (Z.to_nat 2) with 2%nat in Hn; change (33 + Z.to_nat 2)%nat with 35%nat in HS, SHOK; cbn [Z.mul Pos.mul] in HS.
assert (B35 : bv_unsigned (ew E 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 2 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N (proj1 HJ) Himg) as (_ & _ & _ & _ & HiP & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N (proj1 HJ) Hfimg) as (_ & _ & _ & _ & HfiP & _).
destruct (block_byte_val (w_H W) (ms_mem ms1) (img + kk) (proj1 (HiP (img + kk) ltac:(clear - HN1 HrN Hkk HkN Hn1; lia)))) as (bc & Abc & Vbc & Rbc).
destruct (block_byte_val (w_H W) (ms_mem ms1) (fr_img f + kk) (proj1 (HfiP (fr_img f + kk) ltac:(clear - HN1 HrN Hkk HkN Hn1; lia)))) as (bb & Abb & Vbb & Rbb).
pose proof (st_ok_havoc trasegs 219 E _ _ [Z_to_bv 64 bc; Z_to_bv 64 bb] HS ltac:(vm_compute; reflexivity)) as HS1.
clear HS. rename HS1 into HS.
remember (havoc E 219 [Z_to_bv 64 bc; Z_to_bv 64 bb]) as EP eqn:HEP in HS.
assert (OLDP : forall n, (n < 219)%nat -> ew EP n = ew E n) by (intros n0 Hn0; rewrite HEP; apply YO3v.ew_havoc_old; exact Hn0).
assert (EP219 : ew EP 219 = Z_to_bv 64 bc) by (rewrite HEP; change 219%nat with (219 + 0)%nat; rewrite (YO3v.ew_havoc_new E 219 _ 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (EP220 : ew EP 220 = Z_to_bv 64 bb) by (rewrite HEP; change 220%nat with (219 + 1)%nat; rewrite (YO3v.ew_havoc_new E 219 _ 1 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (HAEP : env_agree 73 E EP) by (rewrite HEP; apply env_agree_havoc_ge; [clear; lia | apply env_agree_refl]).
clear HEP.
assert (EP213 : ew EP 213 = Z_to_bv 64 (img + kk)) by (rewrite OLDP by (clear; lia); exact E213).
assert (EP214 : ew EP 214 = Z_to_bv 64 (fr_img f + kk)) by (rewrite OLDP by (clear; lia); exact E214).
assert (EP204 : ew EP 204 = Z_to_bv 64 (Z.of_nat (Datatypes.S n))) by (rewrite OLDP by (clear; lia); exact E204).
assert (BP : bv_unsigned (ew EP 213) = img + kk) by (rewrite EP213; apply unsigned_lit_small; clear - Hi4096 Hiceil HrN HN1 Hkk HkN C1; lia).
assert (BQ : bv_unsigned (ew EP 214) = fr_img f + kk) by (rewrite EP214; apply unsigned_lit_small; clear - Hfi4096 Hficeil HrN HN1 Hkk HkN C1; lia).
pose proof (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E EP HEB (proj1 HAEP)) as HEBP.
pose proof (sh_ok_agree trasegs Bxa (af_SHB 35) 73 E EP _ HAEP eq_refl SHOK) as SHOKP.
clear HEB SHOK B35 E213 E214 E204. try clear HE E67 E70 E71 E72 EEo E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 E49 E50 E51 E52 E53 Usp E32u HAE54. rename HEBP into HEB. rename SHOKP into SHOK. af_E_names HEB sp0 g.
assert (B35 : bv_unsigned (ew EP 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 213%nat (mkAF 4096 140737479966720 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite BP, Z.pow_0_r, Z.mod_1_r; clear - Hi4096 Hiceil HN1 HrN Hkk HkN Hn1 C1; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 214%nat (mkAF 4096 140737479966720 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite BQ, Z.pow_0_r, Z.mod_1_r; clear - Hfi4096 Hficeil HN1 HrN Hkk HkN Hn1 C1; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 204%nat (mkAF 1 4294967296 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP204, unsigned_lit_small by (clear - HN1 Hkk HkN; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HN1 Hkk HkN Hn1; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 219%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP219, unsigned_lit_small by (clear - Rbc; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rbc; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 220%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EP220, unsigned_lit_small by (clear - Rbb; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rbb; lia)) as HS3; clear HS; rename HS3 into HS end.
assert (Vbc' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms1)) (img + kk + 0) 1 bc) by (rewrite Z.add_0_r; exact Vbc).
assert (Vbb' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms1)) (fr_img f + kk + 0) 1 bb) by (rewrite Z.add_0_r; exact Vbb).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 213%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 219 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite BP; split; [clear - Hi4096 Hkk; lia|]; split; [clear - Hiceil HrN HN1 Hkk HkN Hn1 C1; lia|]; split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val trasegs Ex _ (img + kk)); [cbn [sv_denot]; rewrite EP219, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rbc; lia | cbn; clear; lia | exact Vbc'] | constructor])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite BP, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dig Dic Hi4096 Hih0 Hih0_img Hiceil HrN HN1 Hkk HkN Hn1 Hcfp HZg Hceil Hslo HTS C1 C3 C4; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 214%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 220 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite BQ; split; [clear - Hfi4096 Hkk; lia|]; split; [clear - Hficeil HrN HN1 Hkk HkN Hn1 C1; lia|]; split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val trasegs Ex _ (fr_img f + kk)); [cbn [sv_denot]; rewrite EP220, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rbb; lia | cbn; clear; lia | exact Vbb'] | constructor])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite BQ, BP, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dfg Dfc Dif Hfi4096 Hfih0 Hfih0_img Hficeil HrN HN1 Hkk HkN Hn1 Hcfp HZg Hceil Hslo HTS C1 C3 C4; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear Vbc' Vbb'.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA A_cmpPixel.
{ rewrite (U_atom EP 214 (fr_img f + kk) EP214) by (clear - Hfi4096 Hficeil HrN HN1 Hkk HkN C1; lia).
lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?mm)) _ _ _ =>
eapply (obl_of_block trasegs B LAWS ly S W mm _ EP Bxa (fr_img f + kk) 1 (fr_img f) N (proj1 HJ) Hfimg) end;
[ unfold U, Bxa; cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; clear; lia); reflexivity
| clear - Hkk; lia | clear - HrN HN1 Hkk HkN Hn1; lia ]. }
{ rewrite (U_atom EP 213 (img + kk) EP213) by (clear - Hi4096 Hiceil HrN HN1 Hkk HkN C1; lia).
lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?mm)) _ _ _ =>
eapply (obl_of_block trasegs B LAWS ly S W mm _ EP Bxa (img + kk) 1 img N (proj1 HJ) Himg) end;
[ unfold U, Bxa; cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; clear; lia); reflexivity
| clear - Hkk; lia | clear - HrN HN1 Hkk HkN Hn1; lia ]. }
{ awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq. }
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
rreg HS (2%bv : bv 5) Q2; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4; rreg HS (1%bv : bv 5) Q1; rreg HS (8%bv : bv 5) Q8.
rreg HS (10%bv : bv 5) Q10; rreg HS (11%bv : bv 5) Q11; rreg HS (12%bv : bv 5) Q12; rreg HS (13%bv : bv 5) Q13; rreg HS (14%bv : bv 5) Q14.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Q2, Q3, Q4, Q1, Q8, Q10, Q11, Q12, Q13, Q14.
rewrite ?ew_ewset_other in Q2 by (clear; lia). rewrite ?ew_ewset_other in Q3 by (clear; lia). rewrite ?ew_ewset_other in Q4 by (clear; lia).
rewrite ?ew_ewset_other in Q8 by (clear; lia). rewrite ?ew_ewset_other in Q10 by (clear; lia). rewrite ?ew_ewset_other in Q11 by (clear; lia).
rewrite ?ew_ewset_other in Q12 by (clear; lia). rewrite ?ew_ewset_other in Q13 by (clear; lia). rewrite ?ew_ewset_other in Q14 by (clear; lia).
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ msq HS eq_refl) end. cbn [ss_pc].
pose proof (cfp_obj_journal B LAWS sp0 ly S W mem md [] ly S W _ _ 0 g s N _ cfp _ HJ HAR HPerm HFO HCF) as HCF1.
pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly S W _ _ 0 g s N _ cfp 32 HJ HAR HPerm HFO) as HFO1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Hgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Htp);
assert (Qsp : spZ rg = sp0 + -224) by (unfold spZ; rewrite Q2, Usp; rewrite unsigned_lit_small by (clear - Hceil Hslo Hshi H47 HTS C1; lia); clear; lia);
assert (Q10' : getr rg 10 = w64 g) by (rewrite Q10; exact E32);
assert (Q11' : getr rg 11 = w64 cfp) by (rewrite Q11; exact E46);
assert (Q12' : getr rg 12 = w64 (fr_ptr f)) by (rewrite Q12, E35, Hn; reflexivity);
assert (Q13' : getr rg 13 = w64 bc) by (rewrite Q13; exact EP219);
assert (Q14' : getr rg 14 = w64 bb) by (rewrite Q14; exact EP220);
assert (Qs0 : achain ly (aview trasegs (w_H W) mm) (sp0 + -224) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; rewrite E32u, unsigned_lit_small by (clear - Hg4096 Hgceil C1; lia); clear - Hgceil; lia);
assert (Hctx1 : In (raZ rg :: spine []) CTX_cmpPixel) by (unfold raZ; rewrite Q1, unsigned_lit_small by (clear; lia); cbn; tauto);
assert (HTg : obj_at trasegs (mrestrict (w_H W) mm) g LAY_CGIF (tcgif_vals s))
by (rewrite <- (cl_set_cur_same s); apply (obj_cgif_setcur _ _ g s (cg_cur s) (proj1 HT) HGK); [| exact Rcur];
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rg5 := eval vm_compute in (nth 6 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 6 rg5 HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) (cg_cur s) HRg ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; clear; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc; exact Vc end end)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS W rg mm _ TADDFRAME_STK sp0 (FPa g s N) ly S W mem md [] ly S mdq 0 TCMP_STK [] 0 (-224) (Z_to_bv 64 0x86034) []
(fun ly3 S3 W3 regs3 mem3 md3 => ly3 = ly /\ S3 = S /\ W3 = W) HJ Qsp);
[ reflexivity | clear; lia | unfold TCMP_STK, ESTACK; clear; lia | rewrite HTS; unfold TCMP_STK, ESTACK; clear; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_even; vm_compute; reflexivity | rewrite unsigned_lit_small by (clear; lia); clear; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (CMP ly S W rg mm mdq [] g cfp (fr_ptr f) bc bb (tcgif_vals s) [lpal; img; fattr; fgen; delay; nlp; tidx] (frame_vals f)
(cg_pal s) (cg_ngp s) lpal fattr nlp tidx (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f)
HPRE1 Q10' Q11' Q12' Q13' Q14' Rbc Rbb Hing HFO1 Hfb HTg eq_refl eq_refl HCF1 eq_refl eq_refl eq_refl eq_refl (proj2 HSD f HfIn) eq_refl eq_refl eq_refl eq_refl)
| cbv beta; unfold tcmp_post; intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ1 & HP & _);
exists ly, S, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | split; [reflexivity | split; reflexivity]]]] ]
| intros a Ha; destruct Ha as (rr & Hrr & _); destruct Hrr ]
| ] end.
{
intros Hc1. exact (afobj_journal B LAWS sp0 ly S W mem md [] ly S W _ _ 0 g s N _ lpal (3 * nlp) HJ HAR HPerm (HPAL Hc1)). }
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
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (-> & -> & ->)).
clear Q3' Q4' Q10' Q11' Q12' Q13' Q14' Qs0 Hctx1 HTg HCF1 HFO1.
change (0 + 0) with 0 in HJ2.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 Bxa (af_SHB 35) ss) end in
jafter_call_keep HS K regs2 (mrestrict (w_H W) mem2) HP2 [2; 3; 4; 5; 6; 7]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_sub trasegs B); [exact HJc2 | exact HJ2 | evalE; exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_sub trasegs B); [exact HJc2 | exact HJ2 | evalE; exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgotb) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | clear; lia].
- apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcellb) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | clear; lia].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE (proj1 HJ2) Hing) as (_ & _ & _ & _ & HgP2 & _). change (req_size CGIF_SIZE) with 96 in HgP2.
eapply (region_kept_block_subw B); [exact HJc2 | evalE; exact E32u | exact Hing | exact Hing | clear; lia
| change (req_size CGIF_SIZE) with 96; clear; lia | intros a Ha HFP; destruct HFP as (rr & Hrr & _); destruct Hrr
| intros a Ha; apply (fun Hq => proj1 (HgP2 a Hq)); clear - Ha; lia].
- eapply (region_kept_frame_sub B); [exact HJc2 | evalE; rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia
| intros a Ha HFP; destruct HFP as (rr & Hrr & _); destruct Hrr
| intros a Ha; exfalso; clear - Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ (havoc ?Ei ?Kx ?vx) _ _ =>
remember (havoc Ei Kx vx) as E2 eqn:HE2 in HS;
assert (OLD2 : forall n, (n < 221)%nat -> ew E2 n = ew EP n) by (intros n0 Hn0; rewrite HE2; rewrite YO3v.ew_havoc_old by (clear - Hn0; lia); rewrite ?ew_ewset_other by (clear - Hn0; lia); reflexivity);
assert (HAE2 : env_agree 73 EP E2) by (rewrite HE2; env_agree_chain (env_agree_refl 73 EP)) end.
clear HE2.
assert (E2_213 : ew E2 213 = Z_to_bv 64 (img + kk)) by (rewrite OLD2 by (clear; lia); exact EP213).
assert (E2_214 : ew E2 214 = Z_to_bv 64 (fr_img f + kk)) by (rewrite OLD2 by (clear; lia); exact EP214).
assert (E2_204 : ew E2 204 = Z_to_bv 64 (Z.of_nat (Datatypes.S n))) by (rewrite OLD2 by (clear; lia); exact EP204).
pose proof (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ EP E2 HEB (proj1 HAE2)) as HEB2.
clear HEB B35 BP BQ EP213 EP214 EP204 EP219 EP220 OLDP HAEP. try clear HE E67 E70 E71 E72 EEo E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 E49 E50 E51 E52 E53 Usp E32u HAE54. rename HEB2 into HEB. af_E_names HEB sp0 g.
assert (B35 : bv_unsigned (ew E2 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
pose proof (af_side_blk B ly S W _ mem2 _ g s N _ (proj1 HJ) HPerm HSD G2) as HSD2. clear HSD. rename HSD2 into HSD.
assert (HGK2 : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte trasegs (mrestrict (w_H W) mem2) (g + i) = mbyte trasegs (mrestrict (w_H W) mem) (g + i)).
{ intros i Hi Hni. etransitivity; [| exact (HGK i Hi Hni)]. apply (mbyte_of_aview trasegs).
apply (G2 g CGIF_SIZE i Hing Hing); [change (req_size CGIF_SIZE) with 96; clear - Hi; lia | intros X; destruct X as (rr & Hrr & _); destruct Hrr]. }
clear HGK G2. rename HGK2 into HGK.
clear SHOK. assert (SHOK : sh_ok trasegs Bxa (af_SHB 35) E2 (mrestrict (w_H W) mem2)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly S W _ _ _ g s N _ cfp 32 HJ2 HAR HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SHB, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trasegs B LAWS ly S W mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE (proj1 HJ2) Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + range_app_of Hcfp_ia.
- apply (shent_ok_of_block trasegs B LAWS ly S W mem2 md2 E2 Bxa 35 (fr_ptr f) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ2) Hfb).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact B35.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
clear HJ HJc2. rename HJ2 into HJ.
assert (HPB2 : af_preB B ly S W regs mem md g cfp s N fattr (mkst regs2 (Z_to_bv 64 548916) mem2 (seg_rom trasegs)) md2).
{ split; [exact HJ|]. split; [exact HSD|]. split; [exact HGK|]. split; [exact Hcur|]. split; [exact HnoTab | rewrite Hih; clear; lia]. }
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{ aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_C; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (ss_C 2 16 35) 200%nat.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E2); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E2); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree trasegs Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end ] end. }
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
{
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_SAME; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
pose proof (proj2 HSD f HfIn) as HOBf.
pose proof (obj_at_nth trasegs _ _ _ _ 1 (8, 8%N) (fr_img f) HOBf eq_refl eq_refl) as [Vhimg Rhimg].
pose proof (obj_at_nth trasegs _ _ _ _ 2 (16, 4%N) (fr_attr f) HOBf eq_refl eq_refl) as [Vhattr Rhattr].
pose proof (obj_at_nth trasegs _ _ _ _ 4 (24, 2%N) (fr_delay f) HOBf eq_refl eq_refl) as [Vhdel Rhdel].
cbn [snd N.to_nat] in Vhimg, Rhimg, Vhattr, Rhattr, Vhdel, Rhdel.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rhimg. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rhattr. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rhdel.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (af_hdr 35) HS eq_refl
ltac:(unfold region_ok, af_hdr; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite B35; split; [clear - Hh4096 Hhceil C1; lia|]; split; [clear - Hh4096 Hhceil C1; lia|];
split; [intros o Ho; exfalso; clear - Ho; lia|];
constructor; [eapply (chunk_ok_val trasegs Ex _ (fr_ptr f)); [cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E70, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhimg]|];
constructor; [eapply (chunk_ok_val trasegs Ex _ (fr_ptr f)); [cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E71, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhattr]|];
constructor; [eapply (chunk_ok_val trasegs Ex _ (fr_ptr f)); [cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhdel]|];
constructor)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_hdr; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite B35, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgh Dch Hh4096 Hhh Hhh_img Hhceil Hcfp HZg Hceil Hslo HTS C1 C3 C4; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
af_rejoin HS (ss_SM 2 16 35) 200%nat.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 73 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | env_agree_chain HAE54 || (split; [intros; reflexivity | reflexivity])]);
exact (sh_ok_agree trasegs Bxa (af_SHB 35) 73 E1 E' _ HAG1 eq_refl SHOK) end ] end. }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_LOOP; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hcnt end.
rreg HS (19%bv : bv 5) R19. rreg HS (25%bv : bv 5) R24. rreg HS (20%bv : bv 5) R9.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in R19, R24, R9.
rewrite ?ew_ewset_other in R19 by (clear; lia). rewrite ?ew_ewset_other in R24 by (clear; lia). rewrite ?ew_ewset_other in R9 by (clear; lia).
af_rejoin HS (ss_L0 2 16 35) 200%nat.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (IH ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f (kk + 1) Hih CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 73 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | env_agree_chain HAE54 || (split; [intros; reflexivity | reflexivity])]);
exact (sh_ok_agree trasegs Bxa (af_SHB 35) 73 E1 E' _ HAG1 eq_refl SHOK) end
|
change 213%nat with (200 + 13)%nat; rewrite (YO3v.ew_havoc_new E2 200 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; cbn [sv_denot]; rewrite E2_213, unsigned_lit_small by (clear - Hi4096 Hiceil HrN HN1 Hkk HkN C1; lia); unfold w64; f_equal; clear; lia
| change 214%nat with (200 + 14)%nat; rewrite (YO3v.ew_havoc_new E2 200 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; cbn [sv_denot]; rewrite E2_214, unsigned_lit_small by (clear - Hfi4096 Hficeil HrN HN1 Hkk HkN C1; lia); unfold w64; f_equal; clear; lia
| change 204%nat with (200 + 4)%nat; rewrite (YO3v.ew_havoc_new E2 200 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; cbn [sv_denot]; rewrite E2_204, unsigned_lit_small by (clear - HN1 Hkk HkN; lia); unfold w64; f_equal; clear; lia
| clear - Hkk; lia | clear - HkN; lia
| rewrite branch_eq_U in Hcnt; rewrite (U_atom_off _ 204 (Z.of_nat (Datatypes.S n)) (-1)) in Hcnt; [| evalE; exact E2_204 | clear - HN1 Hkk HkN; lia | clear - HN1 Hkk HkN; lia];
rewrite U_lit in Hcnt by (clear; lia); apply (proj1 (Z.eqb_neq _ _)) in Hcnt; clear - Hcnt; lia ] end.
Qed.
End c.
End b.
