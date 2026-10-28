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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACgo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
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
Definition regsA : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 10 (SOff 32 0)) 11 (SOff 46 0).
Section e.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis HXNUM : af_xnums MT XN.
Hypothesis ML : model_laws (as_universe B).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma regsA_ok : forall (regs : bvmap 5 word) g s1 cfp cf more,
getr regs 10 = w64 g -> getr regs 11 = w64 cfp ->
regs_ok (Eimg (Ereg regs (af_extra regs g s1 cfp cf more))) regsA regs.
Proof.
intros regs g s1 cfp cf more H10 H11.
set (E := Eimg (Ereg regs (af_extra regs g s1 cfp cf more))). try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 14); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity | rewrite E32; exact H10 | rewrite E46; exact H11 ]
| ]); try (destruct Hr; fail).
Qed.
Ltac af_errtac Rfattr :=
repeat match goal with
| H : Z.land ?x 6 = 6 |- _ => let H2 := fresh "XB" in let H4 := fresh "XB" in destruct (proj1 (af_land6 x ltac:(clear - Rfattr; lia)) H) as [H2 H4]; clear H
| H : Z.land ?x 6 <> 6 |- _ =>
let Hd := fresh "XB" in
assert (Hd : Z.land x 2 = 0 \/ Z.land x 4 = 0)
by (destruct (Z.eq_dec (Z.land x 2) 0) as [Hq | Hq]; [left; exact Hq |
destruct (Z.eq_dec (Z.land x 4) 0) as [Hq' | Hq']; [right; exact Hq' | exfalso; apply H; apply (proj2 (af_land6 x ltac:(clear - Rfattr; lia))); split; assumption]]);
clear H; destruct Hd as [Hd | Hd]
end;
unfold YI0b.af_err, YI0b.af_hasAlpha, YI0b.af_hasSet, YO07.flag; cbn [YO07.g_attr gcfg_of];
repeat match goal with |- context [Z.land ?x ?k =? 0] => destruct (Z.eqb_spec (Z.land x k) 0) end;
cbn; first [reflexivity | exfalso; tauto].
Lemma af_hc_set : forall E fattr, ew E 49 = Z_to_bv 64 fattr -> 0 <= fattr < 2 ^ 32 ->
U E (SAlu ALU_OR (SLit 0) (SAlu ALU_SLTU (SAlu ALU_AND (SExt true 32 (SOff 49 0)) (SLit 4)) (SLit 1))) = (if Z.land fattr 4 =? 0 then 1 else 0).
Proof.
intros E fattr E49 Rf. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.lor_0_l.
rewrite (U_sltu1_and _ _ 4) by lia. rewrite (U_sext32_land _ 49 _ _ E49 Rf) by lia.
destruct (Z.land fattr 4 =? 0); reflexivity.
Qed.
Lemma af_hc_alpha_set : forall E fattr, ew E 49 = Z_to_bv 64 fattr -> 0 <= fattr < 2 ^ 32 ->
U E (SAlu ALU_OR (SAlu ALU_SLTU (SAlu ALU_AND (SExt false 8 (SOff 49 0)) (SLit 2)) (SLit 1)) (SAlu ALU_SLTU (SAlu ALU_AND (SExt true 32 (SOff 49 0)) (SLit 4)) (SLit 1)))
= Z.lor (if Z.land fattr 2 =? 0 then 1 else 0) (if Z.land fattr 4 =? 0 then 1 else 0).
Proof.
intros E fattr E49 Rf. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_sltu1_and by lia.
rewrite (U_sext32_land _ 49 _ _ E49 Rf), (U_zext8_land _ 49 _ _ E49 Rf) by lia.
destruct (Z.land fattr 2 =? 0), (Z.land fattr 4 =? 0); reflexivity.
Qed.
Ltac af_hcB E49 Rfattr H :=
rewrite ?(af_hc_set _ _ E49 Rfattr), ?(af_hc_alpha_set _ _ E49 Rfattr) in H;
lazymatch type of H with
| context [Z.land ?x 2 =? 0] =>
let q2 := fresh "XQ" in let q4 := fresh "XQ" in
destruct (Z.eqb_spec (Z.land x 2) 0) as [q2 | q2]; destruct (Z.eqb_spec (Z.land x 4) 0) as [q4 | q4]; cbn in H;
first [ discriminate H | exfalso; apply H; reflexivity | clear H ]
| context [Z.land ?x 4 =? 0] =>
let q4 := fresh "XQ" in destruct (Z.eqb_spec (Z.land x 4) 0) as [q4 | q4]; cbn in H;
first [ discriminate H | exfalso; apply H; reflexivity | clear H ]
end.
Lemma af_AX : AF_OK_stmtX K MT XN B ->
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs,
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
SRr SEGS W (cfg_at SEGS (BASE + AF_asan3_cgif_addframe) regs mem md)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) EV_ADDFRAME).
Proof.
intros OK ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs CX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK).
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (XREL0' : af_xrel K (mrestrict (w_H W) mem) md s N img lpa fattr nlp GPAL IMG LPAL gs) by (split; [exact XREL0 | split; [exact XIMG0 | split; [exact XIMGL | exact XLPAL0]]]).
pose proof (proj1 (proj1 XREL0)) as XCUR0.
clear Hpf0 XSMAX XIMGL XMOK.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajournal_init SEGS B TADDFRAME_STK (FPn g) ly S W regs mem md ch HPRE) as HJ.
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (HEV : EV_ADDFRAME = 12 + EV_FLUSH) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen.
destruct (af_seedX B TL LAWS AF_asan3_cgif_addframe regsA (-224) false [] (cg_ihead s) 88 92 W regs regs mem ly S md ly sp0 g s cfp lpal img fattr fgen delay nlp tidx []
HAR Hing HFO Hstk Hpres ltac:(unfold sp0, spZ; lia) ltac:(right; reflexivity) ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia) (regsA_ok regs g s cfp _ [] H10 H11)
ltac:(vm_compute; reflexivity) ltac:(constructor) ltac:(intros X; discriminate X) (proj1 HT) eq_refl HCF) as [HS SHOK].
unfold cfg_at.
set (E := Eimg (Ereg regs (af_extra regs g s cfp [lpal; img; fattr; fgen; delay; nlp; tidx] []))) in *. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HE : af_E regs g s cfp lpal img fattr fgen delay nlp tidx E).
{ subst E. split; [intros n rr Hn; apply ew_Eimg_Ereg_nat; exact Hn|].
repeat match goal with |- _ /\ _ => split | _ => idtac end;
lazymatch goal with |- ew _ ?n = _ => let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ j); reflexivity | |- img_env _ _ _ => apply Eimg_env end. }
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rcur.
pose proof (U_atom E 37 (cg_cur s) E37 ltac:(clear - Rcur; lia)) as Ucur.
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf].
assert (HEV47 : EV_ADDFRAME = 47) by reflexivity. assert (HAE67 : env_agree 67 E E) by (split; [intros n Hn; reflexivity | reflexivity]).
pose proof (obj_at_nth SEGS _ _ _ _ 5 (40, 4%N) (cg_attr s) (proj1 HT) eq_refl eq_refl) as [_ Rattr]. cbn [snd] in Rattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rattr.
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
assert (K880 : forall (msq : machine_state) mdq,
ajournal SEGS B TADDFRAME_STK sp0 (FPn g) ly S W mem md [] ly S W (ms_mem msq) mdq 0 ->
af_side (mrestrict (w_H W) (ms_mem msq)) g s ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS (mrestrict (w_H W) (ms_mem msq)) (g + i) = mbyte SEGS (mrestrict (w_H W) mem) (g + i)) ->
(cg_cur s = 0 \/ cg_cur s = R_PENDING) ->
st_ok_pi SEGS VAL E (xs_880 (cg_ihead s)) (restrict (w_H W) msq) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem msq)) ->
SRr SEGS W (mkCfg msq mdq) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) EV_ADDFRAME)).
{ clear HS SHOK HJ. intros msq mdq HJ HSD HGK Hcur HS SHOK.
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- SRr _ _ _ _ =>
let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat'" in intros mat'; unfold af_postX;
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists ly, S, rg, mm, mdx end;
split; [rewrite R1, (EEo 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k SEGS _); [apply (ajournal_materialize SEGS _ LAWS Hsegs); exact (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) | rewrite HEV47; clear; lia]|];
split; [apply aregs_preserved_eqs; cregA HS EEo|];
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs 32%nat in let ix := eval vm_compute in ix in
let HRg := fresh "HRg" in let Vc := fresh "Vc" in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msF) ix ltac:(let rr := eval vm_compute in (nth ix (ss_mem ssx) got_regionP) in exact rr) HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk 88 (CVal 4 ?e88)] =>
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
split; [| split; [exact HWF | do 7 (split; [reflexivity|]); split; [exact HPerm | split; [|
lazymatch goal with |- cgif_relA _ _ (mrestrict _ ?m0) ?md0 _ _ _ _ _ /\ _ =>
let HJm := fresh "HJm" in let XRm := fresh "XRm" in let XNq := fresh "XNq" in let XA := fresh "XA" in let XB := fresh "XB" in
assert (HJm : ajournal SEGS B TADDFRAME_STK sp0 (FPn g) ly S W mem md [] ly S W m0 md0 0) by (apply (ajournal_materialize SEGS _ LAWS Hsegs); exact HJ);
pose proof (proj1 (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJm HPerm Hpfr HWF XREL0')) as XRm;
assert (XNq : 1 <= N <= 100000000) by (pose proof HWF as (_ & XWge & XHge & XNWH & XNmax & _); clear - XWge XHge XNWH XNmax; nia);
repeat match goal with H : branch_taken _ _ _ = _ |- _ => hcA E40 E49 Rattr Rfattr Ucur Rcur H end;
repeat match goal with H : context [SAlu ALU_OR _ (SAlu ALU_SLTU _ _)] |- _ => af_hcB E49 Rfattr H end;
(lazymatch type of Vc with val_mem _ _ _ _ ?cv => destruct (af_xleaf_err K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs cv XRm (af_xlive_cur s gs Hcur XCUR0) ltac:(af_errtac Rfattr) eq_refl (proj1 XNq)) as [XA XB] end;
(split; [exact XA | split; [exact XB | exact (af_xmle0 MT XN MLAW S N HXNUM XNq)]])) end ]]]];
[ split; [ apply (obj_cgif_setcurX SEGS path hw pf _ _ g s _ (proj1 HT) HGK Vc); clear - Rcur; cbn; lia
| split; [exact (proj1 HSD) | exact (proj2 HSD)] ]
| let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; split;
[ intros _ i Hi; unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); left; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| intros blc i Hbl Hi; right; left; split;
[ unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); left; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| exists (fst b), (snd b); split; [rewrite <- surjective_pairing; exact Hbl | lia] ] ] ]
end in
let leaf_ok := idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF) |- _ =>
repeat match goal with H : branch_taken _ _ _ = _ |- _ => hcA E40 E49 Rattr Rfattr Ucur Rcur H end;
let HnoTab := fresh "HnoTab" in
assert (HnoTab : Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0)
by first [ match goal with H : Z.land (cg_attr s) 4 = 0 |- _ => right; exact H end
| match goal with H : Z.land fattr 1 <> 0 |- _ => left; exact H end ];
let Ra4 := fresh "Ra4" in
let e14 := eval vm_compute in (sr_get (ss_regs ssx) (13%bv : bv 5)) in
assert (Ra4 : getr (ms_regs msF) (13%bv : bv 5) = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0))
by (refine (eq_trans (st_ok_pi_restrict_reg (w_H W) Ex ssx msF (13%bv : bv 5) HS) _);
change (sv_denot Ex e14 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0));
rewrite denot_lit_U; f_equal;
first [ rewrite U_lit by (clear - PBASE PBLO; lia); match goal with H : Z.land fattr 4 = 0 |- _ => rewrite H; reflexivity end
| rewrite (U_sltu1_and _ _ 4) by (clear - PBASE PBLO; lia); rewrite (U_zext32_atom _ 49 fattr E49 Rfattr); reflexivity
| rewrite (U_sltu1_and _ _ 4) by (clear - PBASE PBLO; lia); rewrite (U_sext32_land _ 49 _ _ E49 Rfattr) by (clear - PBASE PBLO; lia); reflexivity
| match goal with |- ?g => idtac "A4FAIL" g end ]);
af_join HS (xs_OK (cg_ihead s)) 67%nat af_deads_OK;
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
eapply (OK ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs _ CX);
[ apply af_E_havoc; [exact HE | clear; cbv; lia | clear; cbv; lia]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split;
[ change 67%nat with (67 + 0)%nat at 1; rewrite (ew_havoc_new _ 67 _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact Ra4
| pose proof HWF as (_ & _ & _ & _ & _ & _ & Hq & _); clear - Hq; lia ]]]]]]
| exact HS
| lazymatch goal with SH' : sh_ok _ _ _ _ _ |- _ =>
exact (sh_ok_agree SEGS Bxa af_SH 67 E E' _ ltac:(env_agree_chain HAE67) eq_refl SH') end
| repeat match goal with H : branch_taken _ _ _ = _ |- _ => hcA E40 E49 Rattr Rfattr Ucur Rcur H end;
repeat match goal with H : context [SAlu ALU_OR _ (SAlu ALU_SLTU _ _)] |- _ => af_hcB E49 Rfattr H end;
exact (af_xleaf_ok s fattr fgen delay nlp tidx GPAL IMG LPAL gs (af_xlive_cur s gs Hcur XCUR0) ltac:(af_errtac Rfattr)) ] | st_ok _ ?E' _ _ =>
eapply (OK ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs _ CX);
[ apply af_E_havoc; [exact HE | clear; cbv; lia | clear; cbv; lia]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split;
[ change 67%nat with (67 + 0)%nat at 1; rewrite (ew_havoc_new _ 67 _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact Ra4
| pose proof HWF as (_ & _ & _ & _ & _ & _ & Hq & _); clear - Hq; lia ]]]]]]
| exact HS
| lazymatch goal with SH' : sh_ok _ _ _ _ _ |- _ =>
exact (sh_ok_agree SEGS Bxa af_SH 67 E E' _ ltac:(env_agree_chain HAE67) eq_refl SH') end
| repeat match goal with H : branch_taken _ _ _ = _ |- _ => hcA E40 E49 Rattr Rfattr Ucur Rcur H end;
repeat match goal with H : context [SAlu ALU_OR _ (SAlu ALU_SLTU _ _)] |- _ => af_hcB E49 Rfattr H end;
exact (af_xleaf_ok s fattr fgen delay nlp tidx GPAL IMG LPAL gs (af_xlive_cur s gs Hcur XCUR0) ltac:(af_errtac Rfattr)) ]  end end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA 0x8b0; [awr_aX Usp E32u Hing HTS |];
side_step HSD HGK HZr HZf HZg Usp E32u;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with HS' : st_ok_pi _ _ ?Ex ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let pc := eval vm_compute in (ss_pc ss) in
lazymatch pc with
| 0x8b0 => first [leaf_ok | idtac "OKLEAF-FAIL"]
| _ => let K := eval vm_compute in (run_K A_LIM Bxa af_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bxa RBspanA af_SH (start K Bxa RBspanA af_SH ss) end in
lazymatch why with
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' RBspanA; [go | go]
| SR_jalr _ => first [leaf_ret | idtac "RETLEAF-FAIL"]
| _ => idtac "STUCK" pc why
end
end end end in
go. }
assert (HSD : af_side (mrestrict (w_H W) mem) g s) by (split; [exact (proj1 (proj2 HT)) | exact (proj2 (proj2 HT))]).
assert (HGK : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS (mrestrict (w_H W) mem) (g + i) = mbyte SEGS (mrestrict (w_H W) mem) (g + i)) by (intros; reflexivity).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
-
hcA E40 E49 Rattr Rfattr Ucur Rcur Hc.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA 0x7d4; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
af_join0 HS (xs_880 (cg_ihead s)).
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ => apply (K880 msq mdq HJ HSD HGK) end;
[ clear - Hc Rcur; destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); [right; unfold R_PENDING; lia | exfalso; lia] | exact HS | exact SHOK ].
- paj_run_tok RUN HS HJ SHOK RBspanA; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
+
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- SRr _ _ _ _ =>
let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat'" in intros mat'; unfold af_postX;
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists ly, S, rg, mm, mdx end;
split; [rewrite R1, (EEo 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k SEGS _); [apply (ajournal_materialize SEGS _ LAWS Hsegs); exact (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) | rewrite HEV47; clear; lia]|];
split; [apply aregs_preserved_eqs; cregA HS EEo|];
let rs := eval vm_compute in (ss_mem ssx) in
let ix := idx_of_base rs 32%nat in let ix := eval vm_compute in ix in
let HRg := fresh "HRg" in let Vc := fresh "Vc" in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msF) ix ltac:(let rr := eval vm_compute in (nth ix (ss_mem ssx) got_regionP) in exact rr) HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk 88 (CVal 4 ?e88)] =>
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
split; [| split; [exact HWF | do 7 (split; [reflexivity|]); split; [exact HPerm | split; [|
lazymatch goal with |- cgif_relA _ _ (mrestrict _ ?m0) ?md0 _ _ _ _ _ /\ _ =>
let HJm := fresh "HJm" in let XRm := fresh "XRm" in let XNq := fresh "XNq" in let XA := fresh "XA" in let XB := fresh "XB" in
assert (HJm : ajournal SEGS B TADDFRAME_STK sp0 (FPn g) ly S W mem md [] ly S W m0 md0 0) by (apply (ajournal_materialize SEGS _ LAWS Hsegs); exact HJ);
pose proof (proj1 (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJm HPerm Hpfr HWF XREL0')) as XRm;
assert (XNq : 1 <= N <= 100000000) by (pose proof HWF as (_ & XWge & XHge & XNWH & XNmax & _); clear - XWge XHge XNWH XNmax; nia);
repeat match goal with H : branch_taken _ _ _ = _ |- _ => hcA E40 E49 Rattr Rfattr Ucur Rcur H end;
let XD := fresh "XD" in
assert (XD : cg_cur s <> 0 /\ cg_cur s <> 6)
by (repeat match goal with H : (if cg_cur s <? 2 ^ 31 then _ else _) <> _ |- _ => revert H end; clear - Rcur; intros; destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); cbv iota in *; lia);
destruct (af_xleaf_dead K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs XRm Rcur (proj1 XD) (proj2 XD) (proj1 XNq)) as [XA XB];
split; [exact XA | split; [exact XB | exact (af_xmle0 MT XN MLAW S N HXNUM XNq)]] end ]]]];
[ split; [ apply (obj_cgif_setcurX SEGS path hw pf _ _ g s _ (proj1 HT) HGK Vc); clear - Rcur; cbn; lia
| split; [exact (proj1 HSD) | exact (proj2 HSD)] ]
| let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; split;
[ intros _ i Hi; unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); left; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| intros blc i Hbl Hi; right; left; split;
[ unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); left; rewrite (surjective_pairing b) in Hb; exact (inFP_ablocks_fp _ _ _ i Hb Hi)
| exists (fst b), (snd b); split; [rewrite <- surjective_pairing; exact Hbl | lia] ] ] ]
end.
+
hcA E40 E49 Rattr Rfattr Ucur Rcur Hc0.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA 0x7d4; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u. clear_frames.
af_join0 HS (xs_880 (cg_ihead s)).
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ => apply (K880 msq mdq HJ HSD HGK) end;
[ clear - Hc0 Rcur; destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); [left; lia | exfalso; lia] | exact HS | exact SHOK ].
Qed.
End e.
End d.
End c.
