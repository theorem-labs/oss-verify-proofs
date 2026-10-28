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
Lemma cl_set_cur_same : forall s1, cl_set_cur s1 (cg_cur s1) = s1.
Proof. intros s1; destruct s1; reflexivity. Qed.
Ltac ew_lift Ex En Hx :=
lazymatch type of En with ew _ ?n = ?v =>
assert (Hx : ew Ex n = v) by (rewrite ?ew_ewset_other by (clear; lia); rewrite ?ew_havoc_old by (clear; lia); exact En) end.
Ltac regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1 :=
lazymatch goal with |- getr _ ?r = _ =>
let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q;
lazymatch goal with
| |- alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew ?Ex ?n) + ?c)) (Z_to_bv 64 3)) (ew _ 38) = _ =>
let Enx := fresh "Enx" in let E38x := fresh "E38x" in
lazymatch n with 32%nat => ew_lift Ex E32 Enx | 46%nat => ew_lift Ex E46 Enx end;
ew_lift Ex E38 E38x;
unfold w64; apply (shq_word Ex n 38 c _ SB Enx E38x); clear - Hcfp HZg Hgceil C1; unfold SB; lia
| |- context [alu64] => idtac "REGV-ALU" r; fail
| |- _ =>
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ reflexivity | exact E32 | exact E38 | exact E46 | rewrite E32u; reflexivity | rewrite Usp; unfold w64; f_equal; lia
| rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp | rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| rewrite E46, unsigned_lit_small by lia; reflexivity | apply bv_eq; vm_compute; reflexivity
| idtac "REGV-FAIL" r; fail ]
end end.
Ltac locv HR0 sp0 E32 E32u E38 E46 E67 Usp Hcfp HZg Hgceil C1 E49 Rfattr :=
lazymatch goal with |- val_mem _ _ (?spx - 224 + ?off) 8 ?v =>
let od := eval vm_compute in (off - 224) in
replace (spx - 224 + off) with (sp0 + od) by lia;
lazymatch type of HR0 with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk od (CVal 8 ?e)] =>
apply (field_of_region Ex _ 2 sp0 cs lo hi wlo whi od 8 e v HR0 Usp); [cbn; tauto | | | cbn; lia];
[ first [ lazymatch goal with |- sv_denot _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff ?n ?c) (SLit 3)) (SOff 38 0)) = _ =>
let Enx := fresh "Enx" in let E38x := fresh "E38x" in
lazymatch n with 32%nat => ew_lift Ex E32 Enx | 46%nat => ew_lift Ex E46 Enx end; ew_lift Ex E38 E38x;
apply (denot_shx Ex n 38 c _ SB Enx E38x); clear - HZg Hcfp Hgceil C1; unfold SB; lia end
|
lazymatch goal with |- sv_denot ?Ex2 (SAlu ALU_AND (SExt true 32 (SOff 49 0)) (SLit ?k)) = _ =>
let E49x := fresh "E49x" in ew_lift Ex2 E49 E49x; apply (and_sext32_word Ex2 49 _ k E49x); clear - Rfattr; lia end
| lazymatch goal with |- sv_denot _ (SAlu _ _ _) = _ => idtac "LOCV-ALU" od; fail | |- _ => idtac end;
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E46 | exact E67 | rewrite E32u; reflexivity | rewrite E46, unsigned_lit_small by lia; reflexivity
| idtac "LOCV-DENOT-FAIL" od; fail ] ]
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
first [ lazymatch goal with |- 0 <= _ + ?x / 8 < _ =>
let Hd := fresh "Hd" in
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (clear - Hcfp HZg C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
clear - Hd Hcfp HZg C1; unfold SB; lia end
| clear - Hcfp HZg C1; lia
| destruct (Z.land _ 4 =? 0); clear; lia
| lazymatch goal with |- 0 <= Z.land ?x 4 < _ => pose proof (land_small_r x 4 ltac:(clear - Rfattr; lia) ltac:(clear; lia)) as Xl; cbn in Xl; clear - Xl; lia end
| idtac "LOCV-RANGE-FAIL" od; fail ] ]
end end end.
Ltac leaf_prep HS E32u E37 Rcur :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_pi_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
cbn [ms_mem restrict mkst] in HR0, HR1, HR4 | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
cbn [ms_mem restrict mkst] in HR0, HR1, HR4  end;
lazymatch goal with HR4 : region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) |- _ =>
lazymatch type of E32u with _ = ?g => lazymatch type of Rcur with 0 <= ?cur < _ =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) cur HR4 E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc end end end;
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst _ Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst _ Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
Ltac leaf_mid HJ HR1 Usp EEo HT HGK Vc Rcur HSD HWF HPerm :=
lazymatch goal with |- af_mid _ _ _ _ _ _ _ _ _ ?s _ _ _ _ _ _ _ _ _ _ _ _ _ =>
split; [exact HJ|]; split; [clear; lia|];
split; [lazymatch type of HR1 with region_ok _ ?Ex _ _ =>
lazymatch type of Usp with bv_unsigned (ew _ 2) = ?sp0 => lazymatch type of EEo with forall n rr, _ -> ew _ n = getr ?regs rr =>
let Uspx := fresh "Uspx" in let EEx := fresh "EEx" in
assert (EEx : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Ex n = getr regs rr)
by (let n := fresh "n" in let rr := fresh "rr" in let Hn := fresh "Hn" in intros n rr Hn;
pose proof (bv_unsigned_in_range 5 rr); change (bv_modulus 5) with 32 in *;
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact (EEo n rr Hn));
assert (Uspx : bv_unsigned (ew Ex 2) = sp0) by (rewrite (EEx 2%nat 2%bv eq_refl); rewrite <- (EEo 2%nat 2%bv eq_refl); exact Usp);
exact (af_frame_of_region Ex _ _ _ _ _ HR1 Uspx EEx) end end end|];
split; [split; [rewrite <- (cl_set_cur_same s); exact (obj_cgif_setcur _ _ _ s _ (proj1 HT) HGK Vc Rcur) | exact HSD]|];
split; [split; [exact HWF|]; repeat split; reflexivity|];
split; [exact HPerm|]; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; left; exact Hb end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section f.
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
Ltac leaf_midX HJb HR1 Usp EEo HT HGK Vc Rcur HSD HWF HPerm :=
lazymatch goal with |- af_midX _ _ _ _ _ _ _ _ _ ?s _ _ _ _ _ _ _ _ _ _ _ _ _ =>
split; [exact HJb|]; split; [clear; lia|];
split; [lazymatch type of HR1 with region_ok _ ?Ex _ _ =>
lazymatch type of Usp with bv_unsigned (ew _ 2) = ?sp0 => lazymatch type of EEo with forall n rr, _ -> ew _ n = getr ?regs rr =>
let Uspx := fresh "Uspx" in let EEx := fresh "EEx" in
assert (EEx : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Ex n = getr regs rr)
by (let n := fresh "n" in let rr := fresh "rr" in let Hn := fresh "Hn" in intros n rr Hn;
pose proof (bv_unsigned_in_range 5 rr); change (bv_modulus 5) with 32 in *;
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact (EEo n rr Hn));
assert (Uspx : bv_unsigned (ew Ex 2) = sp0) by (rewrite (EEx 2%nat 2%bv eq_refl); rewrite <- (EEo 2%nat 2%bv eq_refl); exact Usp);
exact (af_frame_of_region Ex _ _ _ _ _ HR1 Uspx EEx) end end end|];
split; [split; [rewrite <- (cl_set_cur_same s); exact (obj_cgif_setcurX SEGS path hw pf _ _ _ s _ (proj1 HT) HGK Vc Rcur) | exact HSD]|];
split; [split; [exact HWF|]; repeat split; reflexivity|];
split; [exact HPerm|]; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; left; exact Hb end.
Ltac leaf_DX PD i HS HJb HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0 E49 Rfattr GPAL IMG LPAL gs gsF XB tN tS :=
lazymatch goal with HR0 : region_ok _ _ _ (YP09.mkRegion (Some 2%nat) (-224) _ _ _ _), HR1 : region_ok _ _ _ (YP09.mkRegion (Some 2%nat) (-104) _ _ _ _),
Vc : val_mem _ _ _ 4 _ |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
lazymatch type of CX with af_cxX _ _ _ _ ?ly ?S ?W ?regs ?mem ?md ?ch ?g ?cfp ?s ?N ?lpal ?lpa ?img ?fattr ?fgen ?delay ?nlp ?tidx ?rest _ _ _ _ =>
apply (PD ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 s i GPAL IMG LPAL gs gsF gs CX);
[ leaf_midX HJb HR1 Usp EEo HT HGK Vc Rcur HSD HWF HPerm
| rewrite HEVF; clear; lia
| apply Z.le_refl
| unfold af_regs_at; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split]]]]; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_s1_at; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_locs; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; locv HR0 sp0 E32 E32u E38 E46 E67 Usp Hcfp HZg Hgceil C1 E49 Rfattr
| exact HnoTab
| clear; lia
| tN
| tS
| exact XB ] end end.
Ltac leaf_FLX PFL f1 HS HJb HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur sp0 E49 Rfattr GPAL IMG LPAL gs gsF XB t1 t2 :=
lazymatch goal with HR0 : region_ok _ _ _ (YP09.mkRegion (Some 2%nat) (-224) _ _ _ _), HR1 : region_ok _ _ _ (YP09.mkRegion (Some 2%nat) (-104) _ _ _ _),
Vc : val_mem _ _ _ 4 _ |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
lazymatch type of CX with af_cxX _ _ _ _ ?ly ?S ?W ?regs ?mem ?md ?ch ?g ?cfp ?s ?N ?lpal ?lpa ?img ?fattr ?fgen ?delay ?nlp ?tidx ?rest _ _ _ _ =>
apply (PFL ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 s f1 GPAL IMG LPAL gs gsF CX);
[ leaf_midX HJb HR1 Usp EEo HT HGK Vc Rcur HSD HWF HPerm
| clear; lia
| apply Z.le_refl
| unfold af_regs_at; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split]]]]; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_s1_at; regv HS EEo E32 E32u E38 E46 Usp Hgp Htp Hcfp HZg Hgceil C1
| unfold af_locs; change (spZ regs) with sp0;
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; locv HR0 sp0 E32 E32u E38 E46 E67 Usp Hcfp HZg Hgceil C1 E49 Rfattr
| exact HnoTab
| t1
| t2
| exact XB ] end end.
Lemma af_CX : AF_D_stmtX K MT XN B -> AF_FL_stmtX K MT XN B -> AF_C_stmtX K MT XN B.
Proof.
intros PD PFL ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 GPAL IMG LPAL gs gsF CX HE HPX HS SHOK XC.
pose proof (af_xf_in _ XC) as XCm. clear XC.
pose proof HPX as (HJ & HSD & HGK & Hcur & HnoTab & E67 & Hih).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK).
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (XREL0' : af_xrel K (mrestrict (w_H W) mem) md s N img lpa fattr nlp GPAL IMG LPAL gs) by (split; [exact XREL0 | split; [exact XIMG0 | split; [exact XIMGL | exact XLPAL0]]]).
assert (XACC : af_xmtr MT XN S S N (xm_flush XN N + af_needF MT N nlp) (xn_flush XN N + af_needF MT N nlp) /\ af_xmtr MT XN S S N (af_need1 MT N nlp) (af_need1 MT N nlp)).
{ apply (af_xmtr0 MT XN MLAW S N nlp HXNUM).
- pose proof HWF as (_ & XWge & XHge & XNWH & XNmax & _). clear - XWge XHge XNWH XNmax. nia.
- pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rq]. cbn [snd] in Rq. clear - Rq. cbn in Rq. lia. }
clear Hpf0 XSMAX XIMGL XMOK.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (HEVF : EV_FLUSH = 35) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (Hg8 : g mod 8 = 0).
{ clear - Hg16 Hg4096. pose proof (Z.div_mod g 16 ltac:(lia)) as Hdm. rewrite Hg16, Z.add_0_r in Hdm. rewrite Hdm.
replace (16 * (g / 16)) with ((2 * (g / 16)) * 8) by lia. apply Z_mod_mult. }
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
clear Hfin Hcid0 Hfal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img Hcal HRA cid pos.
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf].
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof (proj1 HWF) as Hlen. pose proof HWF as (_ & _ & _ & _ & _ & _ & Hwfq & _).
assert (HAE54 : env_agree 54 E E) by (split; [intros n Hn; reflexivity | reflexivity]).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rcur.
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 1%nat HAR HPerm) as Hslot1.
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 2%nat HAR HPerm) as Hslot2.
Ltac slotq Hq E HAE54 Ej Hslot C1 :=
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear - PBASE PBLO; lia);
rewrite (U_atom E _ _ Ej) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
destruct Hih as [Hih | Hih]; rewrite Hih in HS.
-
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_D; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E34 Hslot1 C1.
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (Hnone : nth 1 (cg_frames s) None = None) by (clear - Hslot1 Hq; destruct Hslot1 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]).
clear Hq.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_D; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_prep HS E32u E37 Rcur.
pose proof (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) as HJb.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (XB : af_xd K MT XN S S (mrestrict (w_H W) mm) mdq s s N 1 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs gsF (af_need1 MT N nlp) (af_need1 MT N nlp)) end.
{ destruct (af_xf_out _ XCm) as [XLV XGF]. split; [| exact (proj2 XACC)]. rewrite XGF.
apply (af_xrel_d K _ _ s N 1 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs ltac:(clear; lia) HWF XLV
(af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF XREL0')); [exact Hnone | let Ha := fresh in intros Ha; exfalso; clear - Ha; lia]. }
leaf_DX PD 1 HS HJb HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0 E49 Rfattr GPAL IMG LPAL gs gsF XB
ltac:(exact Hnone) ltac:(let Ha := fresh in intros Ha; exfalso; clear - Ha; lia).
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E34 Hslot1 C1.
assert (Hsome1 : exists f1, nth 1 (cg_frames s) None = Some f1)
by (clear - Hslot1 Hq; destruct Hslot1 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz in Hq; cbn in Hq; discriminate | exists f0; exact Hn]).
clear Hq. destruct Hsome1 as [f1 Hf1].
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_D; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
respell_shadow HS (21%bv : bv 5) 8 E32 E38 (proj1 HZg) Hgceil Hg8.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_D; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
*
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (Hnone : nth 2 (cg_frames s) None = None) by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]).
clear Hq.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_D; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_prep HS E32u E37 Rcur.
pose proof (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) as HJb.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (XB : af_xd K MT XN S S (mrestrict (w_H W) mm) mdq s s N 2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs gsF (af_need1 MT N nlp) (af_need1 MT N nlp)) end.
{ destruct (af_xf_out _ XCm) as [XLV XGF]. split; [| exact (proj2 XACC)]. rewrite XGF.
apply (af_xrel_d K _ _ s N 2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs ltac:(clear; lia) HWF XLV
(af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF XREL0')); [exact Hnone | intros _; rewrite Hf1; discriminate]. }
leaf_DX PD 2 HS HJb HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0 E49 Rfattr GPAL IMG LPAL gs gsF XB
ltac:(exact Hnone) ltac:(intros _; rewrite Hf1; discriminate).
*
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
assert (Hsome2 : nth 2 (cg_frames s) None <> None)
by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [rewrite Hz in Hq; cbn in Hq; discriminate | rewrite Hn; discriminate]).
clear Hq.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_FL; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_prep HS E32u E37 Rcur.
pose proof (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) as HJb.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (XB : af_xfl K MT XN S S (mrestrict (w_H W) mm) mdq s s N img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF) end.
{ destruct (af_xf_out _ XCm) as [XLV XGF].
split; [exact (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF XREL0') | split; [exact XLV | split; [exact XGF | exact (proj1 XACC)]]]. }
leaf_FLX PFL f1 HS HJb HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur sp0 E49 Rfattr GPAL IMG LPAL gs gsF XB
ltac:(exact Hf1) ltac:(exact Hsome2).
-
assert (Hsome1 : exists f1, nth 1 (cg_frames s) None = Some f1).
{ clear - Hwfq Hih. destruct Hwfq as [H1 | [_ Hn]]; [exfalso; lia|]. destruct (nth 1 (cg_frames s) None) as [f1|]; [exists f1; reflexivity | exfalso; exact (Hn eq_refl)]. }
destruct Hsome1 as [f1 Hf1].
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_D; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (Hnone : nth 2 (cg_frames s) None = None) by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]).
clear Hq.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_D; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_prep HS E32u E37 Rcur.
pose proof (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) as HJb.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (XB : af_xd K MT XN S S (mrestrict (w_H W) mm) mdq s s N 2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs gsF (af_need1 MT N nlp) (af_need1 MT N nlp)) end.
{ destruct (af_xf_out _ XCm) as [XLV XGF]. split; [| exact (proj2 XACC)]. rewrite XGF.
apply (af_xrel_d K _ _ s N 2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs ltac:(clear; lia) HWF XLV
(af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF XREL0')); [exact Hnone | intros _; rewrite Hf1; discriminate]. }
leaf_DX PD 2 HS HJb HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur HEVF sp0 E49 Rfattr GPAL IMG LPAL gs gsF XB
ltac:(exact Hnone) ltac:(intros _; rewrite Hf1; discriminate).
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end. slotq Hq E HAE54 E35 Hslot2 C1.
assert (Hsome2 : nth 2 (cg_frames s) None <> None)
by (clear - Hslot2 Hq; destruct Hslot2 as [[Hn Hz] | (f0 & Hn & Hf0 & Hf2)]; [rewrite Hz in Hq; cbn in Hq; discriminate | rewrite Hn; discriminate]).
clear Hq.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_FL; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
leaf_prep HS E32u E37 Rcur.
pose proof (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) as HJb.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (XB : af_xfl K MT XN S S (mrestrict (w_H W) mm) mdq s s N img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF) end.
{ destruct (af_xf_out _ XCm) as [XLV XGF].
split; [exact (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF XREL0') | split; [exact XLV | split; [exact XGF | exact (proj1 XACC)]]]. }
leaf_FLX PFL f1 HS HJb HSD HGK CX HT HWF HPerm HnoTab EEo E32 E32u E37 E38 E46 E67 Usp Hgp Htp Hcfp HZg Hgceil C1 Rcur sp0 E49 Rfattr GPAL IMG LPAL gs gsF XB
ltac:(exact Hf1) ltac:(exact Hsome2).
Qed.
End f.
End d.
End a.
