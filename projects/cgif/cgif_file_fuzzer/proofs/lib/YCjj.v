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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj2 YCjm YC8g YC8a YChd YCjr YCj1 YCj0 YCjc YCje YCji.
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
Section c.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
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
Ltac run_ro_wkept HFr HG HARx WK WKn :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG
ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hr)
ltac:(lia) ltac:(lia) ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn end.
Ltac run_scr_wkept HFr HG HARx E9x WK WKn :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG
ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw;
rewrite ?ew_ewset_other in Hw by lia; rewrite E9x, unsigned_lit_small in Hw by lia; unfold wscr; lia|]); destruct Hr)
ltac:(lia) ltac:(lia) ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn end.
Ltac awr_scr E9x :=
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E9x; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; assert (FFS' : TFLUSH_STK = 17440) by reflexivity; rewrite FFS'; lia |] ]).
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition cpl (p : Z) : Z := 18446744073709551615 - p.
Definition s2o_lo : YP09.region := YP09.mkRegion (Some 9%nat) 40 48 40 40 [YP09.mkChunk 40 (CVal 8 (SLit 65535))].
Definition s2o_hi : YP09.region :=
YP09.mkRegion (Some 9%nat) 136 224 136 136
[YP09.mkChunk 144 (CVal 8 (SOff 32 0)); YP09.mkChunk 152 (CVal 8 (SOff 19 0)); YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 34 0));
YP09.mkChunk 176 (CVal 8 (SOff 13 0)); YP09.mkChunk 192 (CVal 8 (SOff 17 0)); YP09.mkChunk 200 (CVal 8 (SOff 15 0)); YP09.mkChunk 208 (CVal 8 (SOff 11 0));
YP09.mkChunk 216 (CVal 8 (SOff 14 0))].
Definition s2o_48 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition s2o_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (14%nat, mkAF SB SB 0); (10%nat, mkAF 1 65534 0); (5%nat, mkAF 1 65535 0); (13%nat, mkAF 1 65535 0);
(19%nat, mkAF 0 65534 0); (32%nat, mkAF 18446603336221196288 18446744073709551615 0); (26%nat, mkAF 18446603336221196288 18446744073709551615 0);
(33%nat, HPTR 0); (34%nat, HPTR 0); (15%nat, HPTR 4); (11%nat, HPTR 3); (17%nat, HPTR 3) ] [] [].
Definition ss_s2o : sstate := mkSS 0x1fa0 sr_atoms [s2o_lo; s2o_hi; s2o_48] None s2o_facts.
Definition s2f_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 48 56 48 48 [YP09.mkChunk 48 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 136 224 136 136
[YP09.mkChunk 144 (CVal 8 (SOff 38 0)); YP09.mkChunk 152 (CVal 8 (SOff 39 0)); YP09.mkChunk 160 (CVal 8 (SOff 40 0));
YP09.mkChunk 176 (CVal 8 (SOff 33 0)); YP09.mkChunk 192 (CVal 8 (SOff 34 0)); YP09.mkChunk 200 (CVal 8 (SOff 35 0)); YP09.mkChunk 208 (CVal 8 (SOff 36 0));
YP09.mkChunk 216 (CVal 8 (SOff 37 0))] ].
Definition s2f_facts : facts := mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4) ] [] [].
Definition ss_s2f : sstate := mkSS 0x2100 sr_atoms s2f_mem None s2f_facts.
Definition s2t_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 40 48 40 40 [YP09.mkChunk 40 (CVal 8 (SLit 65535))];
YP09.mkRegion (Some 9%nat) 136 184 136 136
[YP09.mkChunk 144 (CVal 8 (SOff 33 0)); YP09.mkChunk 152 (CVal 8 (SOff 34 0)); YP09.mkChunk 160 (CVal 8 (SOff 35 0)); YP09.mkChunk 176 (CVal 8 (SOff 32 0))] ].
Definition s2t_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (24%nat, mkAF 1 65534 0); (19%nat, mkAF 0 65534 0); (32%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2t : sstate := mkSS 0x205c sr_atoms s2t_mem None s2t_facts.
Definition s2o_post (top : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' bot1,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2118)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
top + 1 <= bot1 <= Hd /\ getr regs' 24 = Z_to_bv 64 bot1 /\ getr regs' 13 = Z_to_bv 64 Wd /\ getr regs' 18 = Z_to_bv 64 top /\ getr regs' 26 = Z_to_bv 64 (cpl bimg) /\
getr regs' 14 = Z_to_bv 64 SB /\ getr regs' 15 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 cfp /\ getr regs' 17 = Z_to_bv 64 bfp /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 144) 8 (cpl fimg) /\ val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 152) 8 top /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 bimg.
Definition s2o_stmt (m : nat) : Prop :=
forall (r top : Z) (regsE : bvmap 5 word) memE mdE,
r - top <= Z.of_nat m -> 0 <= top < r -> r < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 14 = Z_to_bv 64 SB -> getr regsE 15 = Z_to_bv 64 g -> getr regsE 11 = Z_to_bv 64 cfp -> getr regsE 17 = Z_to_bv 64 bfp ->
getr regsE 10 = Z_to_bv 64 r -> getr regsE 5 = Z_to_bv 64 (r + 1) -> getr regsE 13 = Z_to_bv 64 Wd -> getr regsE 19 = Z_to_bv 64 top ->
getr regsE 18 = Z_to_bv 64 top -> getr regsE 26 = Z_to_bv 64 (cpl bimg) ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 40) 8 65535 -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 144) 8 (cpl fimg) ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 152) 8 top -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1fa0)) memE (seg_rom SEGS)) mdE) (s2o_post top).
Lemma fl_s2o_step : forall m, s2o_stmt m -> s2o_stmt (Datatypes.S m).
Proof.
intros m IH. unfold s2o_stmt.
intros i top regsE memE mdE Hm Htr Hi HJE WK HKE E14r E15r E11r E17r E10r E5r E13r E19r E18r E26r V40 V144 V152 V160.
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
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi Htr RW RH; nia).
assert (HWi : 0 <= Wd * i <= 4294836225) by (clear - Hi Htr RW RH; nia).
assert (HSpresE : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 192 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 200 g WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vg) as VgE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 208 cfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vcfp) as VcfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 176 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168E.
remember (Eimg (Ereg regsE [Z_to_bv 64 (cpl fimg); Z_to_bv 64 bimg; Z_to_bv 64 fimg])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 (cpl fimg); Z_to_bv 64 bimg; Z_to_bv 64 fimg]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 14%nat 14%bv eq_refl) as F14. rewrite E14r in F14.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite E15r in E15. pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite E11r in E11.
pose proof (EE 17%nat 17%bv eq_refl) as E17. rewrite E17r in E17.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite E10r in E10. pose proof (EE 5%nat 5%bv eq_refl) as E5. rewrite E5r in E5.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite E13r in E13. pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite E19r in E19.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
assert (E32 : ew E 32 = Z_to_bv 64 (cpl fimg)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (HS : st_ok_pi SEGS VAL E ss_s2o (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1fa0)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2o. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1fa0) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold s2o_lo, s2o_hi, s2o_48. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpres; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 40 8 _ 65535); [reflexivity | zside | zside | exact V40]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 144 8 _ (cpl fimg)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold cpl; zside | unfold cpl; zside | exact V144]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 152 8 _ top); [cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V152]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 160 8 _ bimg); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VgE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VcfpE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite F14, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_nil.
+ apply Forall_nil.
- unfold s2o_lo, s2o_hi, s2o_48. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2o_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F14, E10, E5, E13, E19, E32, E26, E33, E34, E15, E11, E17, !unsigned_lit_small by (unfold SB, cpl; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB, cpl. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 14 0) E (mrestrict (w_H W) memE).
pose proof (proj1 HJE) as HAR1.
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { unfold ss_s2o, s2o_lo, s2o_hi, s2o_48; cbn [ss_mem]. awr_scr E9. }
run_scr_wkept HFr HG HAR1 E9 WK WK1. rename HFr into HFr1. clear HF HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: { exfalso. rewrite branch_ltu_U in Hc. rewrite (U_atom _ 32 (cpl fimg) E32), (U_mul_small1 _ _ _ Wd i (U_atom _ 13 Wd E13 ltac:(lia)) (U_atom _ 10 i E10 ltac:(lia))) in Hc by (unfold cpl; lia).
apply Z.ltb_lt in Hc. unfold cpl in Hc. lia. }
clear Hc.
pose proof (proj1 HJE) as HAR2.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1fd8.
1: { awr_scr E9. }
run_scr_wkept HFr HG HAR2 E9 WK1 WK2. rename HFr into HFr2. clear HF HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ [2; 3; 4; 8; 9; 11; 14; 15; 17; 18; 19; 26]%bv HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr1. cbn [ms_regs restrict] in HKr1.
prreg HS (22%bv : bv 5) R22. prreg HS (24%bv : bv 5) R24h.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
efact HS 13%nat E13 G13; efact HS 10%nat E10 G10; efact HS 33%nat E33 G33; efact HS 34%nat E34 G34;
assert (UM : U Ev (SMd M_MUL (SOff 13 0) (SOff 10 0)) = Wd * i) by (apply U_mul_small1; [apply (U_atom Ev 13 Wd G13); lia | apply (U_atom Ev 10 i G10); lia | lia | lia | lia]);
assert (UF : U Ev (SAlu ALU_ADD (SOff 34 0) (SMd M_MUL (SOff 13 0) (SOff 10 0))) = fimg + Wd * i) by (apply U_add_small2; [apply (U_atom Ev 34 fimg G34); lia | exact UM | lia | lia | lia]);
assert (UB : U Ev (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 13 0) (SOff 10 0))) = bimg + Wd * i) by (apply U_add_small2; [apply (U_atom Ev 33 bimg G33); lia | exact UM | lia | lia | lia]);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (Wd * i)) (denot_of_U2 Ev _ _ UM) R21;
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (fimg + Wd * i)) (denot_of_U2 Ev _ _ UF) R27;
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (bimg + Wd * i)) (denot_of_U2 Ev _ _ UB) R25;
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (NMAX - (fimg + Wd * i))) (denot_of_U2 Ev _ _ (U_not_gen Ev _ _ UF ltac:(lia))) R23;
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 (NMAX - (bimg + Wd * i))) (denot_of_U2 Ev _ _ (U_not_gen Ev _ _ UB ltac:(lia))) R20 | st_ok _ ?Ev _ _ =>
efact HS 13%nat E13 G13; efact HS 10%nat E10 G10; efact HS 33%nat E33 G33; efact HS 34%nat E34 G34;
assert (UM : U Ev (SMd M_MUL (SOff 13 0) (SOff 10 0)) = Wd * i) by (apply U_mul_small1; [apply (U_atom Ev 13 Wd G13); lia | apply (U_atom Ev 10 i G10); lia | lia | lia | lia]);
assert (UF : U Ev (SAlu ALU_ADD (SOff 34 0) (SMd M_MUL (SOff 13 0) (SOff 10 0))) = fimg + Wd * i) by (apply U_add_small2; [apply (U_atom Ev 34 fimg G34); lia | exact UM | lia | lia | lia]);
assert (UB : U Ev (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 13 0) (SOff 10 0))) = bimg + Wd * i) by (apply U_add_small2; [apply (U_atom Ev 33 bimg G33); lia | exact UM | lia | lia | lia]);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (Wd * i)) (denot_of_U2 Ev _ _ UM) R21;
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (fimg + Wd * i)) (denot_of_U2 Ev _ _ UF) R27;
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (bimg + Wd * i)) (denot_of_U2 Ev _ _ UB) R25;
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (NMAX - (fimg + Wd * i))) (denot_of_U2 Ev _ _ (U_not_gen Ev _ _ UF ltac:(lia))) R23;
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 (NMAX - (bimg + Wd * i))) (denot_of_U2 Ev _ _ (U_not_gen Ev _ _ UB ltac:(lia))) R20  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 40 8%N (SLit 65535) 65535 HR0
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V40a end; clear HR0;
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 32 0) (cpl fimg) E32 V144a; slot 152 (SOff 19 0) top E19 V152a; slot 160 (SOff 33 0) bimg E33 V160a end; clear HR1;
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 48 8%N (SOff 5 0) (i + 1) HR2
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V48a end; clear HR2 | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 40 8%N (SLit 65535) 65535 HR0
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V40a end; clear HR0;
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 32 0) (cpl fimg) E32 V144a; slot 152 (SOff 19 0) top E19 V152a; slot 160 (SOff 33 0) bimg E33 V160a end; clear HR1;
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 48 8%N (SOff 5 0) (i + 1) HR2
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V48a end; clear HR2  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V40a, V144a, V152a, V160a, V48a.
pmkst HS.
eapply SRr_bind.
{ pose proof (fl_s2i B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO (Z.to_nat Wd)) as S2I. unfold s2i_stmt in S2I.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (S2I 0 (ms_regs msX) (ms_mem msX) mdX i) end;
[ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJE | exact WK2
| intros r Hr; transitivity (getr regsE r); [apply HKr1; cbv [In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr1 14%bv ltac:(cbv; tauto)); exact E14r | rewrite (HKr1 15%bv ltac:(cbv; tauto)); exact E15r
| rewrite (HKr1 11%bv ltac:(cbv; tauto)); exact E11r | rewrite (HKr1 17%bv ltac:(cbv; tauto)); exact E17r
| rewrite R27; f_equal; lia | rewrite R25; f_equal; lia
| rewrite R23; f_equal; unfold NMAX, YCji.cpl; lia | rewrite R20; f_equal; unfold NMAX, YCji.cpl; lia
| rewrite (HKr1 26%bv ltac:(cbv; tauto)); exact E26r
| exact R21 | exact R22 ]. }
cbv beta. intros W2 c2 _ (-> & regsI & memI & mdI & pcI & -> & HJI & WKI & LI & HKI & HexI).
clear R22 R21 R27 R25 R23 R20.
assert (HK5I : forall r : bv 5, In r WKEPT5 -> getr regsI r = getr regs r).
{ intros r Hr. rewrite (HKI r) by (cbv [WKEPT5 In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr).
transitivity (getr regsE r); [apply HKr1; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]. }
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 40) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V40a) as V40b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 48) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V48a) as V48b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 144) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V144a) as V144b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 152) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V152a) as V152b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 160) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V160a) as V160b.
assert (I9 : getr regsI 9 = Z_to_bv 64 sp1) by (rewrite (HKI 9%bv eq_refl), (HKr1 9%bv ltac:(cbv; tauto)); exact (eq_trans (HKE 9%bv ltac:(cbv; tauto)) H9)).
assert (I18 : getr regsI 18 = Z_to_bv 64 top) by (rewrite (HKI 18%bv eq_refl), (HKr1 18%bv ltac:(cbv; tauto)); exact E18r).
assert (I19 : getr regsI 19 = Z_to_bv 64 top) by (rewrite (HKI 19%bv eq_refl), (HKr1 19%bv ltac:(cbv; tauto)); exact E19r).
assert (I26 : getr regsI 26 = Z_to_bv 64 (cpl bimg)) by (rewrite (HKI 26%bv eq_refl), (HKr1 26%bv ltac:(cbv; tauto)); exact E26r).
pose proof (proj1 HJI) as HARI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 216 SB WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 192 bfp WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 200 g WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vg) as VgI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 208 cfp WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vcfp) as VcfpI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 176 Wd WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176I.
clear HS HS0. try clear SHOK.
destruct HexI as [(-> & H14I & H15I & H11I & H17I) | (-> & Hwit)].
2: {
remember (Eimg (Ereg regsI [Z_to_bv 64 (i + 1); Z_to_bv 64 Wd; Z_to_bv 64 bfp; Z_to_bv 64 g; Z_to_bv 64 cfp; Z_to_bv 64 SB; Z_to_bv 64 (cpl fimg); Z_to_bv 64 top; Z_to_bv 64 bimg])) as Et eqn:HEt. assert (HEIt : img_env VAL A_LIM Et) by (subst Et; apply Eimg_env).
assert (HAEt : env_agree 32 (Ereg regsI [Z_to_bv 64 (i + 1); Z_to_bv 64 Wd; Z_to_bv 64 bfp; Z_to_bv 64 g; Z_to_bv 64 cfp; Z_to_bv 64 SB; Z_to_bv 64 (cpl fimg); Z_to_bv 64 top; Z_to_bv 64 bimg]) Et) by (rewrite HEt; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEt : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regsI r) by (intros n r Hn; subst Et; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EEt 9%nat 9%bv eq_refl) as T9. rewrite I9 in T9.
pose proof (EEt 18%nat 18%bv eq_refl) as T18. rewrite I18 in T18. pose proof (EEt 26%nat 26%bv eq_refl) as T26. rewrite I26 in T26.
assert (T32 : ew Et 32 = Z_to_bv 64 (i + 1)) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 0)).
assert (T33 : ew Et 33 = Z_to_bv 64 Wd) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 1)).
assert (T34 : ew Et 34 = Z_to_bv 64 bfp) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 2)).
assert (T35 : ew Et 35 = Z_to_bv 64 g) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 3)).
assert (T36 : ew Et 36 = Z_to_bv 64 cfp) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 4)).
assert (T37 : ew Et 37 = Z_to_bv 64 SB) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 5)).
assert (T38 : ew Et 38 = Z_to_bv 64 (cpl fimg)) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 6)).
assert (T39 : ew Et 39 = Z_to_bv 64 top) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 7)).
assert (T40 : ew Et 40 = Z_to_bv 64 bimg) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 8)).
assert (HS : st_ok_pi SEGS VAL Et ss_s2f (restrict (w_H W) (mkst regsI (Z_to_bv 64 (BASE + 0x2100)) memI (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2f. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any Et (BASE + 0x2100) _ regsI _ _ (mrestrict (w_H W) memI)).
- subst Et. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold s2f_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite T9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 48 8 _ (i + 1)); [cbn [sv_denot]; rewrite T32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V48b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 144 8 _ (cpl fimg)); [cbn [sv_denot]; rewrite T38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold cpl; zside | unfold cpl; zside | exact V144b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 152 8 _ top); [cbn [sv_denot]; rewrite T39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V152b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 160 8 _ bimg); [cbn [sv_denot]; rewrite T40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176I]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpI]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite T35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VgI]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite T36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VcfpI]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite T37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbI]|].
apply Forall_nil.
- unfold s2f_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite T9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2f_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite T9, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite ?C3 in *. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HEt. pose proof HS as HSt0.
shok_auto SHOK (SOff 37 0) Et (mrestrict (w_H W) memI).
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x2118.
1: { unfold ss_s2f, s2f_mem; cbn [ss_mem]. awr_scr T9. }
run_scr_wkept HFr HG HARI T9 WKI WK4. rename HFr into HFr4. clear HF HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ [2; 3; 4; 8; 9; 18; 26]%bv HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr4. cbn [ms_regs restrict] in HKr4.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 38 0) (cpl fimg) T38 V144n; slot 152 (SOff 39 0) top T39 V152n; slot 160 (SOff 40 0) bimg T40 V160n end; clear HR1 | st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 38 0) (cpl fimg) T38 V144n; slot 152 (SOff 39 0) top T39 V152n; slot 160 (SOff 40 0) bimg T40 V160n end; clear HR1  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V144n, V152n, V160n.
prreg HS (24%bv : bv 5) R24. prreg HS (13%bv : bv 5) R13. prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15. prreg HS (11%bv : bv 5) R11. prreg HS (17%bv : bv 5) R17.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (i + 1) end.
split; [reflexivity|]. split; [exact HJI|]. split; [exact WK4|].
split; [intros r Hr; transitivity (getr regsI r); [apply HKr4; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]|].
split; [lia|]. split; [rget R24 T32|]. split; [rget R13 T33|].
split; [rewrite (HKr4 18%bv ltac:(cbv; tauto)); exact I18|]. split; [rewrite (HKr4 26%bv ltac:(cbv; tauto)); exact I26|].
split; [rget R14 T37|]. split; [rget R15 T35|]. split; [rget R11 T36|]. split; [rget R17 T34|].
split; [exact V144n|]. split; [exact V152n | exact V160n]. }
assert (I24 : getr regsI 24 = Z_to_bv 64 i) by (rewrite (HKI 24%bv eq_refl); rget R24h E10).
remember (Eimg (Ereg regsI [Z_to_bv 64 Wd; Z_to_bv 64 (cpl fimg); Z_to_bv 64 top; Z_to_bv 64 bimg])) as Et eqn:HEt. assert (HEIt : img_env VAL A_LIM Et) by (subst Et; apply Eimg_env).
assert (HAEt : env_agree 32 (Ereg regsI [Z_to_bv 64 Wd; Z_to_bv 64 (cpl fimg); Z_to_bv 64 top; Z_to_bv 64 bimg]) Et) by (rewrite HEt; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEt : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regsI r) by (intros n r Hn; subst Et; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EEt 9%nat 9%bv eq_refl) as T9. rewrite I9 in T9.
pose proof (EEt 24%nat 24%bv eq_refl) as T24. rewrite I24 in T24. pose proof (EEt 19%nat 19%bv eq_refl) as T19. rewrite I19 in T19.
assert (T32 : ew Et 32 = Z_to_bv 64 Wd) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 0)).
assert (T33 : ew Et 33 = Z_to_bv 64 (cpl fimg)) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 1)).
assert (T34 : ew Et 34 = Z_to_bv 64 top) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 2)).
assert (T35 : ew Et 35 = Z_to_bv 64 bimg) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 3)).
assert (HS : st_ok_pi SEGS VAL Et ss_s2t (restrict (w_H W) (mkst regsI (Z_to_bv 64 (BASE + 0x205c)) memI (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2t. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any Et (BASE + 0x205c) _ regsI _ _ (mrestrict (w_H W) memI)).
- subst Et. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold s2t_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite T9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 40 8 _ 65535); [reflexivity | zside | zside | exact V40b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 144 8 _ (cpl fimg)); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold cpl; zside | unfold cpl; zside | exact V144b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 152 8 _ top); [cbn [sv_denot]; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V152b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 160 8 _ bimg); [cbn [sv_denot]; rewrite T35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite T32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176I]|].
apply Forall_nil.
- unfold s2t_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite T9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite T9, T24, T19, T32, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HEt. pose proof HS as HSt0.
shok_auto SHOK (SOff 14 0) Et (mrestrict (w_H W) memI).
hei_havoc HS; paj_run_tok RUN HS HJI SHOK FLBspan.
1: { unfold ss_s2t, s2t_mem; cbn [ss_mem]. awr_scr T9. }
run_scr_wkept HFr HG HARI T9 WKI WK4. rename HFr into HFr4. clear HF HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_geu_U in Hc. rewrite (U_atom _ 19 top T19), (U_and16 _ _ (i - 1) (U_atom_off _ 24 i (-1) T24 ltac:(lia) ltac:(lia))) in Hc by lia.
apply (proj1 (negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc.
pose proof (proj1 HJI) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x2118.
1: { awr_scr T9. }
run_scr_wkept HFr HG HAR5 T9 WK4 WK5. rename HFr into HFr5. clear HF HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ [2; 3; 4; 8; 9; 11; 14; 15; 17; 18; 24; 26]%bv HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr5. cbn [ms_regs restrict] in HKr5.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 33 0) (cpl fimg) T33 V144n; slot 152 (SOff 34 0) top T34 V152n; slot 160 (SOff 35 0) bimg T35 V160n end; clear HR1 | st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 33 0) (cpl fimg) T33 V144n; slot 152 (SOff 34 0) top T34 V152n; slot 160 (SOff 35 0) bimg T35 V160n end; clear HR1  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V144n, V152n, V160n.
prreg HS (13%bv : bv 5) R13.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, i end.
split; [reflexivity|]. split; [exact HJI|]. split; [exact WK5|].
split; [intros r Hr; transitivity (getr regsI r); [apply HKr5; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]|].
split; [lia|]. split; [rewrite (HKr5 24%bv ltac:(cbv; tauto)); exact I24|]. split; [rget R13 T32|].
split; [rewrite (HKr5 18%bv ltac:(cbv; tauto)); exact I18|]. split; [rewrite (HKr5 26%bv ltac:(cbv; tauto)); exact I26|].
split; [rewrite (HKr5 14%bv ltac:(cbv; tauto)); exact H14I|]. split; [rewrite (HKr5 15%bv ltac:(cbv; tauto)); exact H15I|].
split; [rewrite (HKr5 11%bv ltac:(cbv; tauto)); exact H11I|]. split; [rewrite (HKr5 17%bv ltac:(cbv; tauto)); exact H17I|].
split; [exact V144n|]. split; [exact V152n | exact V160n].
-
rewrite branch_geu_U in Hc. rewrite (U_atom _ 19 top T19), (U_and16 _ _ (i - 1) (U_atom_off _ 24 i (-1) T24 ltac:(lia) ltac:(lia))) in Hc by lia.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
pose proof (proj1 HJI) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x1fa0.
1: { awr_scr T9. }
run_scr_wkept HFr HG HAR5 T9 WK4 WK5. rename HFr into HFr5. clear HF HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ [2; 3; 4; 8; 9; 11; 14; 15; 17; 18; 19; 26]%bv HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr5. cbn [ms_regs restrict] in HKr5.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 40 8%N (SLit 65535) 65535 HR0
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V40n end; clear HR0;
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 33 0) (cpl fimg) T33 V144n; slot 152 (SOff 34 0) top T34 V152n; slot 160 (SOff 35 0) bimg T35 V160n end; clear HR1 | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 40 8%N (SLit 65535) 65535 HR0
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V40n end; clear HR0;
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as Hn in
slot 144 (SOff 33 0) (cpl fimg) T33 V144n; slot 152 (SOff 34 0) top T34 V152n; slot 160 (SOff 35 0) bimg T35 V160n end; clear HR1  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V40n, V144n, V152n, V160n.
prreg HS (13%bv : bv 5) R13. prreg HS (5%bv : bv 5) R5.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
efact HS 24%nat T24 GT24;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (i - 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 24 i (-1) GT24 ltac:(lia) ltac:(lia))) R10 | st_ok _ ?Ev _ _ =>
efact HS 24%nat T24 GT24;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (i - 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 24 i (-1) GT24 ltac:(lia) ltac:(lia))) R10  end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (i - 1) top _ _ _); [ lia | lia | lia | exact HJI | exact WK5
| intros r Hr; transitivity (getr regsI r); [apply HKr5; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]
| rewrite (HKr5 14%bv ltac:(cbv; tauto)); exact H14I | rewrite (HKr5 15%bv ltac:(cbv; tauto)); exact H15I
| rewrite (HKr5 11%bv ltac:(cbv; tauto)); exact H11I | rewrite (HKr5 17%bv ltac:(cbv; tauto)); exact H17I
| exact R10 | rewrite R5; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T24; f_equal; lia
| rget R13 T32
| rewrite (HKr5 19%bv ltac:(cbv; tauto)); exact I19 | rewrite (HKr5 18%bv ltac:(cbv; tauto)); exact I18 | rewrite (HKr5 26%bv ltac:(cbv; tauto)); exact I26
| exact V40n | exact V144n | exact V152n | exact V160n ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & bot1 & -> & HJ3 & WK6 & HK3 & Hrest).
split; [reflexivity|]. exists regs3, mem3, md3, bot1. split; [reflexivity|]. split; [exact HJ3|]. split; [exact WK6|]. split; [exact HK3 | exact Hrest].
Qed.
Lemma fl_s2o : forall m, s2o_stmt m.
Proof. induction m as [|m IH]; [unfold s2o_stmt; intros; exfalso; lia | exact (fl_s2o_step m IH)]. Qed.
Definition s2s_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 40 48 40 48 [];
YP09.mkRegion (Some 9%nat) 136 144 136 136 [YP09.mkChunk 136 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
YP09.mkRegion (Some 9%nat) 152 224 152 152
[YP09.mkChunk 152 (CVal 8 (SOff 11 0)); YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 34 0)); YP09.mkChunk 176 (CVal 8 (SOff 35 0));
YP09.mkChunk 192 (CVal 8 (SOff 36 0)); YP09.mkChunk 200 (CVal 8 (SOff 37 0)); YP09.mkChunk 208 (CVal 8 (SOff 38 0)); YP09.mkChunk 216 (CVal 8 (SOff 39 0))] ].
Definition s2s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (11%nat, mkAF 0 65534 0); (24%nat, mkAF 1 65535 0); (32%nat, mkAF 1 65535 0); (33%nat, HPTR 0); (34%nat, HPTR 0);
(35%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2s : sstate := mkSS 0x1f58 sr_atoms s2s_mem None s2s_facts.
Lemma fl_s2 : forall (top : Z) (regsE : bvmap 5 word) memE mdE,
0 <= top < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 11 = Z_to_bv 64 top -> getr regsE 18 = Z_to_bv 64 top -> getr regsE 24 = Z_to_bv 64 Hd ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 152) 8 top -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1f58)) memE (seg_rom SEGS)) mdE) (s2o_post top).
Proof.
intros top regsE memE mdE Htr0 HJE WK HKE E11r E18r E24r V152 V160.
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
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 192 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 200 g WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vg) as VgE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 208 cfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vcfp) as VcfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 176 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 136 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V136) as V136E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168E.
remember (Eimg (Ereg regsE [Z_to_bv 64 Hd; Z_to_bv 64 bimg; Z_to_bv 64 fimg; Z_to_bv 64 Wd; Z_to_bv 64 bfp; Z_to_bv 64 g; Z_to_bv 64 cfp; Z_to_bv 64 SB])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 Hd; Z_to_bv 64 bimg; Z_to_bv 64 fimg; Z_to_bv 64 Wd; Z_to_bv 64 bfp; Z_to_bv 64 g; Z_to_bv 64 cfp; Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite E11r in E11. pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite E24r in E24.
assert (E32 : ew E 32 = Z_to_bv 64 Hd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 cfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 7)).
assert (HS : st_ok_pi SEGS VAL E ss_s2s (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1f58)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2s. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1f58) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold s2s_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpres; lia]|]).
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 136 8 _ Hd); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V136E]|]. apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 152 8 _ top); [cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V152]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 160 8 _ bimg); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VgE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VcfpE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_nil.
- unfold s2s_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E11, E24, E32, E33, E34, E35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 39 0) E (mrestrict (w_H W) memE).
pose proof (proj1 HJE) as HAR1.
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { unfold ss_s2s, s2s_mem; cbn [ss_mem]. awr_scr E9. }
run_scr_wkept HFr HG HAR1 E9 WK WK1. rename HFr into HFr1. clear HF HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_geu_U in Hc. rewrite (U_and16 _ _ top (U_atom _ 11 top E11 ltac:(lia))), (U_and16 _ _ (Hd - 1) (U_atom_off _ 24 Hd (-1) E24 ltac:(lia) ltac:(lia))) in Hc by lia.
apply (proj1 (negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc.
pose proof (proj1 HJE) as HAR2.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x2118.
1: { awr_scr E9. }
run_scr_wkept HFr HG HAR2 E9 WK1 WK2. rename HFr into HFr2. clear HF HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ [2; 3; 4; 8; 9; 18; 24]%bv HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr2. cbn [ms_regs restrict] in HKr2.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 144 8%N (SAlu ALU_XOR (SOff 34 0) (SLit (-1))) (cpl fimg) HR2
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(apply denot_of_U2; rewrite (U_not_gen Ex _ fimg) by (first [apply (U_atom Ex 34 fimg); [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E34 | lia] | lia]); reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as V144n end; clear HR2;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3; cbn [ms_mem restrict mkst] in HR3;
lazymatch type of HR3 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR3
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as Hn in
slot 152 (SOff 11 0) top E11 V152n; slot 160 (SOff 33 0) bimg E33 V160n end; clear HR3 | st_ok _ ?Ex ?ssx ?msx =>
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 144 8%N (SAlu ALU_XOR (SOff 34 0) (SLit (-1))) (cpl fimg) HR2
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(apply denot_of_U2; rewrite (U_not_gen Ex _ fimg) by (first [apply (U_atom Ex 34 fimg); [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E34 | lia] | lia]); reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as V144n end; clear HR2;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3; cbn [ms_mem restrict mkst] in HR3;
lazymatch type of HR3 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR3
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as Hn in
slot 152 (SOff 11 0) top E11 V152n; slot 160 (SOff 33 0) bimg E33 V160n end; clear HR3  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V144n, V152n, V160n.
prreg HS (13%bv : bv 5) R13. prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15. prreg HS (11%bv : bv 5) R11. prreg HS (17%bv : bv 5) R17.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
efact HS 33%nat E33 G33;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (NMAX - bimg)) (denot_of_U2 Ev _ _ (U_not_gen Ev _ bimg (U_atom Ev 33 bimg G33 ltac:(lia)) ltac:(lia))) R26 | st_ok _ ?Ev _ _ =>
efact HS 33%nat E33 G33;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (NMAX - bimg)) (denot_of_U2 Ev _ _ (U_not_gen Ev _ bimg (U_atom Ev 33 bimg G33 ltac:(lia)) ltac:(lia))) R26  end.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, Hd end.
split; [reflexivity|]. split; [exact HJE|]. split; [exact WK2|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr2; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [lia|]. split; [rewrite (HKr2 24%bv ltac:(cbv; tauto)); exact E24r|]. split; [rget R13 E35|].
split; [rewrite (HKr2 18%bv ltac:(cbv; tauto)); exact E18r|]. split; [rewrite R26; reflexivity|].
split; [rget R14 E39|]. split; [rget R15 E37|]. split; [rget R11 E38|]. split; [rget R17 E36|].
split; [exact V144n|]. split; [exact V152n | exact V160n].
-
rewrite branch_geu_U in Hc. rewrite (U_and16 _ _ top (U_atom _ 11 top E11 ltac:(lia))), (U_and16 _ _ (Hd - 1) (U_atom_off _ 24 Hd (-1) E24 ltac:(lia) ltac:(lia))) in Hc by lia.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
pose proof (proj1 HJE) as HAR2.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1fa0.
1: { awr_scr E9. }
run_scr_wkept HFr HG HAR2 E9 WK1 WK2. rename HFr into HFr2. clear HF HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ [2; 3; 4; 8; 9; 18; 24]%bv HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr2. cbn [ms_regs restrict] in HKr2.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 144 8%N (SAlu ALU_XOR (SOff 34 0) (SLit (-1))) (cpl fimg) HR2
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(apply denot_of_U2; rewrite (U_not_gen Ex _ fimg) by (first [apply (U_atom Ex 34 fimg); [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E34 | lia] | lia]); reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as V144n end; clear HR2;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3; cbn [ms_mem restrict mkst] in HR3;
lazymatch type of HR3 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR3
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as Hn in
slot 152 (SOff 11 0) top E11 V152n; slot 160 (SOff 33 0) bimg E33 V160n end; clear HR3 | st_ok _ ?Ex ?ssx ?msx =>
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 144 8%N (SAlu ALU_XOR (SOff 34 0) (SLit (-1))) (cpl fimg) HR2
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(apply denot_of_U2; rewrite (U_not_gen Ex _ fimg) by (first [apply (U_atom Ex 34 fimg); [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E34 | lia] | lia]); reflexivity)
ltac:(cbn [Z.of_N Z.mul]; unfold cpl; lia) ltac:(cbn; lia)) as V144n end; clear HR2;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3; cbn [ms_mem restrict mkst] in HR3;
lazymatch type of HR3 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v En Hn :=
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi off 8%N e v HR3
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as Hn in
slot 152 (SOff 11 0) top E11 V152n; slot 160 (SOff 33 0) bimg E33 V160n end; clear HR3  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V144n, V152n, V160n.
prreg HS (13%bv : bv 5) R13. prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15. prreg HS (11%bv : bv 5) R11. prreg HS (17%bv : bv 5) R17.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
efact HS 33%nat E33 G33;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (NMAX - bimg)) (denot_of_U2 Ev _ _ (U_not_gen Ev _ bimg (U_atom Ev 33 bimg G33 ltac:(lia)) ltac:(lia))) R26 | st_ok _ ?Ev _ _ =>
efact HS 33%nat E33 G33;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (NMAX - bimg)) (denot_of_U2 Ev _ _ (U_not_gen Ev _ bimg (U_atom Ev 33 bimg G33 ltac:(lia)) ltac:(lia))) R26  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 40 8%N (SLit 65535) 65535 HR0
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V40n end; clear HR0 | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s2o_lo) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 40 8%N (SLit 65535) 65535 HR0
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V40n end; clear HR0  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V40n.
prreg HS (5%bv : bv 5) R5.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
efact HS 24%nat E24 G24; efact HS 11%nat E11 G11;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (Hd - 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 24 Hd (-1) G24 ltac:(lia) ltac:(lia))) R10;
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 top) (denot_of_U2 Ev _ _ (U_and16 Ev _ top (U_atom Ev 11 top G11 ltac:(lia)) ltac:(lia))) R19 | st_ok _ ?Ev _ _ =>
efact HS 24%nat E24 G24; efact HS 11%nat E11 G11;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (Hd - 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 24 Hd (-1) G24 ltac:(lia) ltac:(lia))) R10;
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 top) (denot_of_U2 Ev _ _ (U_and16 Ev _ top (U_atom Ev 11 top G11 ltac:(lia)) ltac:(lia))) R19  end.
pmkst HS.
pose proof (fl_s2o (Z.to_nat (Hd - 1 - top))) as S2O. unfold s2o_stmt in S2O.
eapply (S2O (Hd - 1) top _ _ _); [ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJE | exact WK2
| intros r Hr; transitivity (getr regsE r); [apply HKr2; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]
| rget R14 E39 | rget R15 E37 | rget R11 E38 | rget R17 E36
| exact R10 | replace (Hd - 1 + 1) with Hd by lia; rget R5 E32 | rget R13 E35 | exact R19
| rewrite (HKr2 18%bv ltac:(cbv; tauto)); exact E18r | rewrite R26; reflexivity
| exact V40n | exact V144n | exact V152n | exact V160n ].
Qed.
End f.
End d.
End c.
End b.
