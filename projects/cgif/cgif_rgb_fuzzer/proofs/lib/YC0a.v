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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC0u YC0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsA : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 10 (SOff 32 0)) 11 (SOff 46 0).
Section PA.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsA_ok : forall (regs : bvmap 5 word) g s1 cfp cf more,
getr regs 10 = w64 g -> getr regs 11 = w64 cfp ->
regs_ok (Ereg regs (af_extra regs g s1 cfp cf more)) regsA regs.
Proof.
intros regs g s1 cfp cf more H10 H11.
set (E := Ereg regs (af_extra regs g s1 cfp cf more)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite (ew_Ereg_extra regs _ 14); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity | rewrite E32; exact H10 | rewrite E46; exact H11 ]
| ]); try (destruct Hr; fail).
Qed.
Lemma af_A : AF_OK_stmt B ->
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest,
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
SRr trasegs W (cfg_at trasegs A_cgif_addframe regs mem md) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Proof.
intros OK ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest CX.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajournal_init trasegs B TADDFRAME_STK (FPa g s N) ly S W regs mem md ch HPRE) as HJ.
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (HEV : EV_ADDFRAME = 12 + EV_FLUSH) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen.
destruct (af_seed B TL LAWS A_cgif_addframe regsA (-224) false [] (cg_ihead s) 88 92 W regs regs mem ly S md ly sp0 g s cfp lpal img fattr fgen delay nlp tidx []
HAR Hing HFO Hstk Hpres ltac:(unfold sp0, spZ; lia) ltac:(right; reflexivity) ltac:(clear; lia) ltac:(clear; lia) (regsA_ok regs g s cfp _ [] H10 H11)
ltac:(vm_compute; reflexivity) ltac:(constructor) ltac:(intros X; discriminate X) (proj1 HT) eq_refl HCF) as [HS SHOK].
unfold cfg_at.
set (E := Ereg regs (af_extra regs g s cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [])) in *.
assert (HE : af_E regs g s cfp lpal img fattr fgen delay nlp tidx E).
{ subst E. split; [intros n rr Hn; apply ew_Ereg_nat; exact Hn|].
repeat match goal with |- _ /\ _ => split | _ => idtac end;
lazymatch goal with |- ew _ ?n = _ => let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat; rewrite (ew_Ereg_extra regs _ j); reflexivity end. }
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (obj_at_nth trasegs _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rcur.
pose proof (U_atom E 37 (cg_cur s) E37 ltac:(clear - Rcur; lia)) as Ucur.
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf].
assert (HEV47 : EV_ADDFRAME = 47) by reflexivity. assert (HAE67 : env_agree 67 E E) by (split; [intros n Hn; reflexivity | reflexivity]).
pose proof (obj_at_nth trasegs _ _ _ _ 5 (40, 4%N) (cg_attr s) (proj1 HT) eq_refl eq_refl) as [_ Rattr]. cbn [snd] in Rattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rattr.
pose proof (obj_at_nth trasegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
assert (K880 : forall (msq : machine_state) mdq,
ajournal trasegs B TADDFRAME_STK sp0 (FPa g s N) ly S W mem md [] ly S W (ms_mem msq) mdq 0 ->
af_side (mrestrict (w_H W) (ms_mem msq)) g s ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte trasegs (mrestrict (w_H W) (ms_mem msq)) (g + i) = mbyte trasegs (mrestrict (w_H W) mem) (g + i)) ->
(cg_cur s = 0 \/ cg_cur s = R_PENDING) ->
st_ok trasegs E (ss_880 (cg_ihead s)) (restrict (w_H W) msq) ->
sh_ok trasegs Bxa af_SH E (mrestrict (w_H W) (ms_mem msq)) ->
SRr trasegs W (mkCfg msq mdq) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME)).
{ clear HS SHOK HJ. intros msq mdq HJ HSD HGK Hcur HS SHOK.
let leaf_ret := idtac;
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msF), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- SRr _ _ _ _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat'" in intros mat'; unfold af_post;
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists ly, S, rg, mm, mdx end;
split; [rewrite R1, (EEo 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k trasegs _); [apply (ajournal_materialize trasegs _ LAWS Hsegs); exact HJ | rewrite HEV47; clear; lia]|];
split; [apply aregs_preserved_eqs; cregA HS EEo|];
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs 32%nat in let ix := eval vm_compute in ix in
let HRg := fresh "HRg" in let Vc := fresh "Vc" in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msF) ix _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YQ0b.mkChunk 88 (CVal 4 ?e88)] =>
lazymatch e88 with
| SLit ?z =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi 88 4%N e88 HRg E32u ltac:(cbn; tauto) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc;
let cv' := eval vm_compute in (bv_unsigned (sv_denot Ex (SLit z)) mod 2 ^ (8 * Z.of_N 4)) in
change (bv_unsigned (sv_denot Ex (SLit z)) mod 2 ^ (8 * Z.of_N 4)) with cv' in Vc
| _ =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4%N e88 (cg_cur s) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc
end end end;
clear HRg;
lazymatch type of Vc with val_mem _ _ _ _ ?cv => exists (cl_set_cur s cv) end;
split; [| split; [exact HWF | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact HPerm |]]]]]]];
[ split; [ apply (obj_cgif_setcur _ _ g s _ (proj1 HT) HGK Vc); clear - Rcur; cbn; lia
| split; [exact (proj1 HSD) | exact (proj2 HSD)] ]
| let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; split;
[ intros _ i Hi; unfold FPa; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| intros blc i Hbl Hi; right; left; split;
[ unfold FPa; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| exists (fst b), (snd b); split; [rewrite <- surjective_pairing; exact Hbl | lia] ] ] ]
end in
let leaf_ok := idtac;
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msF) |- _ =>
repeat match goal with H : branch_taken _ _ _ = _ |- _ => hcA E40 E49 Rattr Rfattr Ucur Rcur H end;
let HnoTab := fresh "HnoTab" in
assert (HnoTab : Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0)
by first [ match goal with H : Z.land (cg_attr s) 4 = 0 |- _ => right; exact H end
| match goal with H : Z.land fattr 1 <> 0 |- _ => left; exact H end ];
let Ra4 := fresh "Ra4" in
let e14 := eval vm_compute in (sr_get (ss_regs ssx) (13%bv : bv 5)) in
assert (Ra4 : getr (ms_regs msF) (13%bv : bv 5) = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0))
by (refine (eq_trans (st_ok_restrict_reg trasegs (w_H W) Ex ssx msF (13%bv : bv 5) HS) _);
change (sv_denot Ex e14 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0));
rewrite denot_lit_U; f_equal;
first [ rewrite U_lit by (clear; lia); match goal with H : Z.land fattr 4 = 0 |- _ => rewrite H; reflexivity end
| rewrite (U_sltu1_and _ _ 4) by (clear; lia); rewrite (U_zext32_atom _ 49 fattr E49 Rfattr); reflexivity
| match goal with |- ?g => idtac "A4FAIL" g end ]);
af_join HS (ss_OK (cg_ihead s)) 67%nat af_deads_OK;
lazymatch type of HS with st_ok _ ?E' _ _ =>
eapply (OK ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ CX);
[ apply af_E_havoc; [exact HE | clear; cbv; lia]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split;
[ change 67%nat with (67 + 0)%nat at 1; rewrite (ew_havoc_new _ 67 _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact Ra4
| pose proof HWF as (_ & _ & _ & _ & _ & _ & Hq & _); clear - Hq; lia ]]]]]]
| exact HS
| lazymatch goal with SH' : sh_ok _ _ _ _ _ |- _ =>
exact (sh_ok_agree trasegs Bxa af_SH 67 E E' _ ltac:(env_agree_chain HAE67) eq_refl SH') end ] end end in
let rec go := idtac;
lazymatch goal with HS : st_ok _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA 0x85e80; [awr_a Usp E32u Hing HTS |];
side_step HSD HGK HZr HZf HZg Usp E32u;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with HS' : st_ok _ ?Ex ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let pc := eval vm_compute in (ss_pc ss) in
lazymatch pc with
| 548480 => first [leaf_ok | idtac "OKLEAF-FAIL"]
| _ => let K := eval vm_compute in (run_K 0 Bxa af_SH ss) in
let r := eval vm_compute in (sym_step_tok trasegs tratbl_lib K Bxa RBspanA af_SH (start K Bxa RBspanA af_SH ss)) in
lazymatch r with
| TStop (SR_branch _ _ _) => srr_branch_tok tratbl_lib_ok HS' SHOK' RBspanA; [go | go]
| TStop (SR_jalr _) => first [leaf_ret | idtac "RETLEAF-FAIL"]
| TStop ?why => idtac "STUCK" pc why
| _ => idtac "NOTSTUCK" pc
end
end end end in
go. }
assert (HSD : af_side (mrestrict (w_H W) mem) g s) by (split; [exact (proj1 (proj2 HT)) | exact (proj2 (proj2 HT))]).
assert (HGK : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte trasegs (mrestrict (w_H W) mem) (g + i) = mbyte trasegs (mrestrict (w_H W) mem) (g + i)) by (intros; reflexivity).
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
-
hcA E40 E49 Rattr Rfattr Ucur Rcur Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA 0x85da4; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
af_join0 HS (ss_880 (cg_ihead s)).
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ => apply (K880 msq mdq HJ HSD HGK) end;
[ clear - Hc Rcur; destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); [right; unfold R_PENDING; lia | exfalso; lia] | exact HS | exact SHOK ].
- aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
+
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
idtac;
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msF), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- SRr _ _ _ _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat'" in intros mat'; unfold af_post;
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists ly, S, rg, mm, mdx end;
split; [rewrite R1, (EEo 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k trasegs _); [apply (ajournal_materialize trasegs _ LAWS Hsegs); exact HJ | rewrite HEV47; clear; lia]|];
split; [apply aregs_preserved_eqs; cregA HS EEo|];
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs 32%nat in let ix := eval vm_compute in ix in
let HRg := fresh "HRg" in let Vc := fresh "Vc" in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msF) ix _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YQ0b.mkChunk 88 (CVal 4 ?e88)] =>
lazymatch e88 with
| SLit ?z =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi 88 4%N e88 HRg E32u ltac:(cbn; tauto) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc;
let cv' := eval vm_compute in (bv_unsigned (sv_denot Ex (SLit z)) mod 2 ^ (8 * Z.of_N 4)) in
change (bv_unsigned (sv_denot Ex (SLit z)) mod 2 ^ (8 * Z.of_N 4)) with cv' in Vc
| _ =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4%N e88 (cg_cur s) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc
end end end;
clear HRg;
lazymatch type of Vc with val_mem _ _ _ _ ?cv => exists (cl_set_cur s cv) end;
split; [| split; [exact HWF | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact HPerm |]]]]]]];
[ split; [ apply (obj_cgif_setcur _ _ g s _ (proj1 HT) HGK Vc); clear - Rcur; cbn; lia
| split; [exact (proj1 HSD) | exact (proj2 HSD)] ]
| let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; split;
[ intros _ i Hi; unfold FPa; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| intros blc i Hbl Hi; right; left; split;
[ unfold FPa; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| exists (fst b), (snd b); split; [rewrite <- surjective_pairing; exact Hbl | lia] ] ] ]
end.
+
hcA E40 E49 Rattr Rfattr Ucur Rcur Hc0.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA 0x85da4; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
af_join0 HS (ss_880 (cg_ihead s)).
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ => apply (K880 msq mdq HJ HSD HGK) end;
[ clear - Hc0 Rcur; destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); [left; lia | exfalso; lia] | exact HS | exact SHOK ].
Qed.
End PA.
End c.
