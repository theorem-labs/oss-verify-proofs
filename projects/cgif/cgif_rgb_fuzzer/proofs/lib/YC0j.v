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
Lemma cl_set_cur_same : forall s1, cl_set_cur s1 (cg_cur s1) = s1.
Proof. intros s1; destruct s1; reflexivity. Qed.
Ltac regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1 :=
lazymatch goal with |- getr ?rgG ?r = _ =>
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 ?c) (SLit 3)) (SOff 38 0) =>
let Q := fresh "Q" in
assert (Q : getr rgG r = sv_denot Ex e) by (exact (st_ok_restrict_reg segs Hh Ex ss ms r HS));
rewrite Q; clear Q; unfold w64;
first [ apply (denot_shx Ex 32 38 c _ SB E32 E38); clear - HZg Hcfp Hgceil C1; unfold SB; lia
| idtac "REGV-SHADOW-FAIL" r ]
| _ =>
let Q := fresh "Q" in rreg HS r Q; rewrite Q; clear Q;
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ reflexivity | exact E32 | exact E38 | exact E46 | rewrite E32u; reflexivity | rewrite Usp; unfold w64; f_equal; lia
| rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp | rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| rewrite E46, unsigned_lit_small by lia; reflexivity | apply bv_eq; vm_compute; reflexivity
| idtac "REGV-FAIL" r ]
end end end.
Ltac locv HR0 sp0 E32 E32u E38 E46 E67 Usp Hcfp HZg Hgceil C1 :=
lazymatch goal with |- val_mem _ _ (?spx - 224 + ?off) 8 ?v =>
let od := eval vm_compute in (off - 224) in
replace (spx - 224 + off) with (sp0 + od) by lia;
lazymatch type of HR0 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YQ0b.mkChunk od (CVal 8 ?e)] =>
apply (field_of_region Ex _ 2 sp0 cs lo hi wlo whi od 8 e v HR0 Usp); [cbn; tauto | | | cbn; lia];
[ first [ apply (denot_shx Ex 32 38 _ _ SB E32 E38); clear - HZg Hcfp Hgceil C1; unfold SB; lia
| apply (denot_shx Ex 46 38 _ _ SB E46 E38); clear - HZg Hcfp Hgceil C1; unfold SB; lia
| cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E46 | exact E67 | rewrite E32u; reflexivity | rewrite E46, unsigned_lit_small by lia; reflexivity
| idtac "LOCV-DENOT-FAIL" od ] ]
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
first [ lazymatch goal with |- 0 <= _ + ?x / 8 < _ =>
let Hd := fresh "Hd" in
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (clear - Hcfp HZg C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
clear - Hd Hcfp HZg C1; unfold SB; lia end
| clear - Hcfp HZg C1; lia
| destruct (Z.land _ 4 =? 0); clear; lia
| idtac "LOCV-RANGE-FAIL" od ] ]
end end end.
Ltac leaf_prep HS E32u E37 Rcur :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
cbn [ms_mem restrict mkst] in HR0, HR1, HR4 end;
lazymatch goal with HR4 : region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) |- _ =>
lazymatch type of E32u with _ = ?g => lazymatch type of Rcur with 0 <= ?cur < _ =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) cur HR4 E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc end end end;
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
Ltac leaf_mid HJ HR1 Usp EEo HT HGK Vc Rcur HSD HWF HPerm :=
lazymatch goal with |- af_mid _ _ _ _ _ _ _ _ _ ?s _ _ _ _ _ _ _ _ _ _ _ _ _ =>
split; [exact HJ|]; split; [clear; lia|];
split; [lazymatch type of HR1 with region_ok _ ?Ex _ _ => exact (af_frame_of_region Ex _ _ _ _ _ HR1 Usp EEo) end|];
split; [split; [rewrite <- (cl_set_cur_same s); exact (obj_cgif_setcur _ _ _ s _ (proj1 HT) HGK Vc Rcur) | exact HSD]|];
split; [split; [exact HWF|]; repeat split; reflexivity|];
split; [exact HPerm|]; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; left; exact Hb end.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section PC.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma af_C : AF_D_stmt B -> AF_FL_stmt B -> AF_C_stmt B.
Proof.
intros PD PFL ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 CX HE HPX HS SHOK.
pose proof HPX as (HJ & HSD & HGK & Hcur & HnoTab & E67 & Hih).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (HEVF : EV_FLUSH = 35) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (Hg8 : g mod 8 = 0).
{ clear - Hg16 Hg4096. pose proof (Z.div_mod g 16 ltac:(lia)) as Hdm. rewrite Hg16, Z.add_0_r in Hdm. rewrite Hdm.
replace (16 * (g / 16)) with ((2 * (g / 16)) * 8) by lia. apply Z_mod_mult. }
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
clear Hfin Hcid0 Hfal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img Hcal HRA cid pos.
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf].
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof (proj1 HWF) as Hlen. pose proof HWF as (_ & _ & _ & _ & _ & _ & Hwfq & _).
assert (HAE54 : env_agree 54 E E) by (split; [intros n Hn; reflexivity | reflexivity]).
pose proof (obj_at_nth trasegs _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rcur.
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 1%nat HAR HPerm) as Hslot1.
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 2%nat HAR HPerm) as Hslot2.
Ltac leaf_D PD i HS HJ HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0 tN tS :=
leaf_prep HS E32u E37 Rcur;
lazymatch goal with HR0 : region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) (-224) _ _ _ _), HR1 : region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) (-104) _ _ _ _),
Vc : val_mem _ _ _ 4 _ |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
lazymatch type of CX with af_cx _ ?ly ?S ?W ?regs ?mem ?md ?ch ?g ?cfp ?s ?N ?lpal ?lpa ?img ?fattr ?fgen ?delay ?nlp ?tidx ?rest =>
apply (PD ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 s i CX);
[ leaf_mid HJ HR1 Usp EEo HT HGK Vc Rcur HSD HWF HPerm
| rewrite HEVF; clear; lia
| apply Z.le_refl
| unfold af_regs_at; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split]]]]; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_s1_at; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_locs; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; locv HR0 sp0 E32 E32u E38 E46 E67 Usp Hcfp HZg Hgceil C1
| exact HnoTab
| clear; lia
| tN
| tS ] end end.
Ltac leaf_FL PFL f1 HS HJ HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur sp0 t1 t2 :=
leaf_prep HS E32u E37 Rcur;
lazymatch goal with HR0 : region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) (-224) _ _ _ _), HR1 : region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) (-104) _ _ _ _),
Vc : val_mem _ _ _ 4 _ |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
lazymatch type of CX with af_cx _ ?ly ?S ?W ?regs ?mem ?md ?ch ?g ?cfp ?s ?N ?lpal ?lpa ?img ?fattr ?fgen ?delay ?nlp ?tidx ?rest =>
apply (PFL ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 s f1 CX);
[ leaf_mid HJ HR1 Usp EEo HT HGK Vc Rcur HSD HWF HPerm
| clear; lia
| apply Z.le_refl
| unfold af_regs_at; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split]]]]; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_s1_at; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_locs; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; locv HR0 sp0 E32 E32u E38 E46 E67 Usp Hcfp HZg Hgceil C1
| exact HnoTab
| t1
| t2 ] end end.
Ltac slotq Hq E HAE54 Ej Hslot C1 :=
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear; lia);
rewrite (U_atom E _ _ Ej) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
destruct Hih as [Hih | Hih]; rewrite Hih in HS.
-
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_D; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E34 Hslot1 C1.
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (Hnone : nth 1 (cg_frames s) None = None) by (clear - Hslot1 Hq; destruct Hslot1 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]).
clear Hq.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_D; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_D PD 1 HS HJ HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0
ltac:(exact Hnone) ltac:(let Ha := fresh in intros Ha; exfalso; clear - Ha; lia).
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E34 Hslot1 C1.
assert (Hsome1 : exists f1, nth 1 (cg_frames s) None = Some f1)
by (clear - Hslot1 Hq; destruct Hslot1 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz in Hq; cbn in Hq; discriminate | exists f0; exact Hn]).
clear Hq. destruct Hsome1 as [f1 Hf1].
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_D; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
respell_shadow HS (21%bv : bv 5) 8 E32 E38 (proj1 HZg) Hgceil Hg8.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_D; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
*
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (Hnone : nth 2 (cg_frames s) None = None) by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]).
clear Hq.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_D; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_D PD 2 HS HJ HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0
ltac:(exact Hnone) ltac:(intros _; rewrite Hf1; discriminate).
*
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
assert (Hsome2 : nth 2 (cg_frames s) None <> None)
by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [rewrite Hz in Hq; cbn in Hq; discriminate | rewrite Hn; discriminate]).
clear Hq.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_FL; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_FL PFL f1 HS HJ HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur sp0
ltac:(exact Hf1) ltac:(exact Hsome2).
-
assert (Hsome1 : exists f1, nth 1 (cg_frames s) None = Some f1).
{ clear - Hwfq Hih. destruct Hwfq as [H1 | [_ Hn]]; [exfalso; lia|]. destruct (nth 1 (cg_frames s) None) as [f1|]; [exists f1; reflexivity | exfalso; exact (Hn eq_refl)]. }
destruct Hsome1 as [f1 Hf1].
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_D; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (Hnone : nth 2 (cg_frames s) None = None) by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]).
clear Hq.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_D; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_D PD 2 HS HJ HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0
ltac:(exact Hnone) ltac:(intros _; rewrite Hf1; discriminate).
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
assert (Hsome2 : nth 2 (cg_frames s) None <> None)
by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [rewrite Hz in Hq; cbn in Hq; discriminate | rewrite Hn; discriminate]).
clear Hq.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_FL; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_FL PFL f1 HS HJ HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur sp0
ltac:(exact Hf1) ltac:(exact Hsome2).
Qed.
End PC.
End a.
