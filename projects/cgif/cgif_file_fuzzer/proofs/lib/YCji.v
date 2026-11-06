(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj2 YC8g YC8a YChd YCjr YCj1 YCj0 YCjc YCje.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TCMP : tcmp_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section f.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Let CALL := cmp_callW B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp & Vg & Vcfp);
pose proof HGEO as (RW & RH & HN & V176 & V136 & V168).
Ltac wprelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac efact HS n En G :=
lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => lazymatch type of En with ew _ _ = ?v =>
assert (G : ew Ecur n = v) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En) end | st_ok _ ?Ecur _ _ => lazymatch type of En with ew _ _ = ?v =>
assert (G : ew Ecur n = v) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En) end  end.
Ltac rget R En :=
rewrite R; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En.
Ltac run_ro_kept HFr HG HARx WK L WKn Ln :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG
ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hr)
ltac:(lia) ltac:(lia) ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn;
pose proof (lkept_trans _ _ _ _ _ L (lkept_of_run_ro Ef rs W _ _ sp1 HFr
ltac:(let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn; lia|]); destruct Hr) ltac:(lia) ltac:(lia))) as Ln;
cbn [ms_mem restrict mkst] in Ln; clear HFr HG end.
Definition S2I_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 22; 28; 29; 30; 31]%bv.
Definition S2I_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv.
Lemma s2i_clob_cases : forall r : bv 5, reg_in r S2I_CLOB = false -> r = 0%bv \/ In r S2I_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Definition cpl (p : Z) : Z := 18446744073709551615 - p.
Definition s2i_loc : YP09.region :=
YP09.mkRegion (Some 9%nat) 176 224 176 176
[YP09.mkChunk 176 (CVal 8 (SOff 36 0)); YP09.mkChunk 192 (CVal 8 (SOff 17 0)); YP09.mkChunk 200 (CVal 8 (SOff 15 0)); YP09.mkChunk 208 (CVal 8 (SOff 11 0));
YP09.mkChunk 216 (CVal 8 (SOff 14 0))].
Definition s2i_cur : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition s2i_bef : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition s2i_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (14%nat, mkAF SB SB 0); (32%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
(36%nat, mkAF 1 65535 0); (22%nat, mkAF 0 65534 0); (21%nat, mkAF 0 4294836225 0);
(23%nat, mkAF 18446603336221196288 18446744073709551615 0); (20%nat, mkAF 18446603336221196288 18446744073709551615 0);
(26%nat, mkAF 18446603336221196288 18446744073709551615 0);
(25%nat, HPTR 0); (27%nat, HPTR 0); (15%nat, HPTR 4); (11%nat, HPTR 3); (17%nat, HPTR 3) ] []
[ (SAlu ALU_ADD (SOff 22 0) (SOff 27 0), SOff 32 0); (SAlu ALU_ADD (SOff 22 0) (SOff 25 0), SOff 33 0) ].
Definition ss_s2i : sstate := mkSS 0x1fd8 sr_atoms [s2i_loc; s2i_cur; s2i_bef] None s2i_facts.
Definition s2i_post (regsE : bvmap 5 word) (memE : word -> option byte) (r : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\ lkept W sp1 memE mem' /\
(forall r : bv 5, reg_in r S2I_CLOB = false -> getr regs' r = getr regsE r) /\
((pc' = (BASE + 0x205c) /\ getr regs' 14 = Z_to_bv 64 SB /\ getr regs' 15 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 cfp /\ getr regs' 17 = Z_to_bv 64 bfp) \/
(pc' = (BASE + 0x2100) /\ (exists c0, 0 <= c0 < Wd /\ PDp (r * Wd + c0)))).
Definition s2i_stmt (m : nat) : Prop :=
forall (c : Z) (regsE : bvmap 5 word) memE mdE (r : Z),
Wd - c <= Z.of_nat m -> 0 <= c < Wd -> 0 <= r < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r [2; 3; 4; 8; 9]%bv -> getr regsE r = getr regs r) ->
getr regsE 14 = Z_to_bv 64 SB -> getr regsE 15 = Z_to_bv 64 g -> getr regsE 11 = Z_to_bv 64 cfp -> getr regsE 17 = Z_to_bv 64 bfp ->
getr regsE 27 = Z_to_bv 64 (fimg + r * Wd) -> getr regsE 25 = Z_to_bv 64 (bimg + r * Wd) ->
getr regsE 23 = Z_to_bv 64 (cpl (fimg + r * Wd)) -> getr regsE 20 = Z_to_bv 64 (cpl (bimg + r * Wd)) -> getr regsE 26 = Z_to_bv 64 (cpl bimg) ->
getr regsE 21 = Z_to_bv 64 (Wd * r) -> getr regsE 22 = Z_to_bv 64 c ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1fd8)) memE (seg_rom SEGS)) mdE) (s2i_post regsE memE r).
Lemma fl_s2i_step : forall m, s2i_stmt m -> s2i_stmt (Datatypes.S m).
Proof.
intros m IH. unfold s2i_stmt.
intros c regsE memE mdE i Hm Hcw Hi HJE WK HKE E14r E15r E11r E17r E27r E25r E23r E20r E26r E21r E22r.
wctx_names. wprelude HJE. pose proof HJE as HJE0.
pose proof (proj1 (proj2 HJE)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_imgP _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bfp FRAME_SIZE HAR Hbf) as (Hp16 & Hp4096 & Hpceil & Hpfh_ia & _ & _). pose proof (proj1 Hpfh_ia) as Hpfh.
pose proof (blk_off_imgP _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hpfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi RW RH; nia).
assert (HWi : 0 <= Wd * i <= 4294836225) by (clear - Hi RW RH; nia).
assert (Hp : 0 <= i * Wd + c /\ i * Wd + c + (Wd - c) <= Nb) by (clear - HiW Hcw; lia).
set (p := i * Wd + c) in *.
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi ltac:(lia)) as [VbC RbC].
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi ltac:(lia)) as [VbB RbB].
set (bC := bval (aview SEGS (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview SEGS (w_H W) memc) (bimg + p)) in *.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 192 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 200 g WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vg) as VgE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 208 cfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vcfp) as VcfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 176 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
remember (Eimg (Ereg regsE [Z_to_bv 64 (fimg + p); Z_to_bv 64 (bimg + p); Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 Wd])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 (fimg + p); Z_to_bv 64 (bimg + p); Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 Wd]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 14%nat 14%bv eq_refl) as F14. rewrite E14r in F14.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite E15r in E15. pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite E11r in E11.
pose proof (EE 17%nat 17%bv eq_refl) as E17. rewrite E17r in E17.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 (fimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (bimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 bB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 4)).
assert (HS : st_ok_pi SEGS VAL E ss_s2i (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1fd8)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2i. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1fd8) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok, s2i_loc, s2i_cur, s2i_bef;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VgE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VcfpE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite F14, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_nil.
+ rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s2i_loc, s2i_cur, s2i_bef. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E9, E32, E33, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [s2i_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F14, E32, E33, E34, E35, E36, E22, E21, E23, E20, E26, E25, E27, E15, E11, E17, !unsigned_lit_small by (unfold SB, cpl; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB, cpl. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end].
+ cbn [s2i_facts f_alias alias_ok].
split; [rewrite (denot_add_atoms E 22 27 c (fimg + i * Wd) E22 E27) by lia; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; subst p; lia|].
split; [rewrite (denot_add_atoms E 22 25 c (bimg + i * Wd) E22 E25) by lia; cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; subst p; lia | exact I]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 14 0) E (mrestrict (w_H W) memE).
pose proof (lkept_refl W sp1 memE) as L0.
pose proof (proj1 HJE) as HAR1.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan AF_both3_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 32 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 32 (fimg + p) cc E32) by lia | rewrite (U_atom Ex 32 (fimg + p) E32) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 14 0) _ len fimg Nb (proj1 HJE) Hfi); [rewrite (U_atom Ex 14 SB F14); [reflexivity | unfold SB; lia] | lia | lia] end).
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (bimg + p) cc E33) by lia | rewrite (U_atom Ex 33 (bimg + p) E33) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 14 0) _ len bimg Nb (proj1 HJE) Hbi); [rewrite (U_atom Ex 14 SB F14); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR1 WK L0 WK3 L3. clear HF.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3. prreg HS (14%bv : bv 5) Qa4.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX p (Z_to_bv 64 (BASE + 0x2020)) HJE WK3) end.
- lia.
- unfold spZ. rewrite Qsp, (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp, (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp, (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- unfold s0Z. rewrite Qs0, (EE 8%nat 8%bv eq_refl), (HKE 8%bv ltac:(cbv; tauto)). exact Hs0.
- rewrite Qa0. exact E15. - rewrite Qa1. exact E11. - rewrite Qa2. exact E17. - rewrite Qa3. exact E34. - rewrite Qa4. exact E35.
- exact Qra. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. - rewrite unsigned_lit_small by lia. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hz & WKc & Kc & Lc).
pose proof (lkept_trans _ _ _ _ _ L3 Lc) as L4.
clear Qa0 Qa1 Qa2 Qa3 Qa4 Qra Qsp Qgp Qtp Qs0.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 14 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2 | st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 14 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2  end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil] | specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia
| lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 14%nat.
pose proof (proj1 HJ2) as HAR3.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR3 WKc L4 WK5 L5. clear HF.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (HPD : PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
intros HZ; apply Hc; lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros HP; exact (HP HZ) end. }
reshok_bx HS 14%nat. pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x2100.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR4 WK5 L5 WK6 L6. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S2I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (BASE + 0x2100) end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|]. split; [exact L6|].
split; [intros r Hr; destruct (s2i_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]|].
right. split; [reflexivity|]. exists c. split; [clear - Hcw; lia | exact HPD].
-
assert (HnPD : ~ PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
lazymatch goal with |- getr regs2 10 = w64 0 =>
enough (Hvz : U Ex (SOff n 0) = bv_unsigned (getr regs2 10)) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hvz; exact Hc) end;
rewrite U_SOff; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
unfold CLOB; cbn [map nth]; rewrite Z.add_0_r; apply zcanon_id; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia end. }
reshok_bx HS 14%nat. pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR4 WK5 L5 WK6 L6. clear HF.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
+
rewrite branch_ne_U in Hc0. rewrite (U_atom _ 36 Wd) in Hc0 by (first [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E36 | lia]).
rewrite (U_atom_off _ 22 c 1) in Hc0 by (first [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E22 | lia]).
apply (proj1 (negb_true_iff _)) in Hc0. apply Z.eqb_neq in Hc0.
reshok_bx HS 14%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x1fd8.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR5 WK6 L6 WK7 L7. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S2I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
assert (HK2 : forall r : bv 5, reg_in r S2I_CLOB = false -> getr (ms_regs msx) r = getr regsE r) | st_ok _ _ _ (restrict _ ?msx) =>
assert (HK2 : forall r : bv 5, reg_in r S2I_CLOB = false -> getr (ms_regs msx) r = getr regsE r)  end.
{ intros r Hr. destruct (s2i_clob_cases r Hr) as [-> | Hr']; [rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS), (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]. }
prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15. prreg HS (11%bv : bv 5) R11. prreg HS (17%bv : bv 5) R17. prreg HS (22%bv : bv 5) R22.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (c + 1) _ _ _ i); [ lia | lia | exact Hi | exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HK2; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr | apply HKE; exact Hr]
| rget R14 F14 | rget R15 E15 | rget R11 E11 | rget R17 E17
| rewrite (HK2 27%bv eq_refl); exact E27r | rewrite (HK2 25%bv eq_refl); exact E25r
| rewrite (HK2 23%bv eq_refl); exact E23r | rewrite (HK2 20%bv eq_refl); exact E20r | rewrite (HK2 26%bv eq_refl); exact E26r
| rewrite (HK2 21%bv eq_refl); exact E21r
| rewrite R22; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E22, unsigned_lit_small by lia; f_equal; lia ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & pc3 & -> & HJ3 & WK8 & L8 & HK3 & Hex).
split; [reflexivity|]. exists regs3, mem3, md3, pc3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact WK8|]. split; [exact (lkept_trans _ _ _ _ _ L7 L8)|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK2 r Hr)|].
exact Hex.
+
reshok_bx HS 14%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x205c.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR5 WK6 L6 WK7 L7. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S2I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15. prreg HS (11%bv : bv 5) R11. prreg HS (17%bv : bv 5) R17.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (BASE + 0x205c) end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK7|]. split; [exact L7|].
split; [intros r Hr; destruct (s2i_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]|].
left. split; [reflexivity|]. split; [rget R14 F14|]. split; [rget R15 E15|]. split; [rget R11 E11 | rget R17 E17].
Qed.
Lemma fl_s2i : forall m, s2i_stmt m.
Proof. induction m as [|m IH]; [unfold s2i_stmt; intros; exfalso; lia | exact (fl_s2i_step m IH)]. Qed.
End f.
End e.
End d.
End b.
