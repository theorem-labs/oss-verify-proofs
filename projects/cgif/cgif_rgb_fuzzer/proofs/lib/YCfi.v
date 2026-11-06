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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YCfy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdv YCe5 YCe9 YCfx YCex YCev YCf8 YCfa.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TCMP : tcmp_spec B.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section e.
Variables (W : world trbsegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Let CALL := cmp_callW B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp & Vg & Vcfp);
pose proof HGEO as (RW & RH & HN & V176 & V136 & V168).
Ltac wprelude HJ :=
pose proof Hwx_tfa as Hwx; pose proof trb_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac efact HS n En G :=
lazymatch type of HS with st_ok _ ?Ecur _ _ => lazymatch type of En with ew _ _ = ?v =>
assert (G : ew Ecur n = v) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En) end end.
Ltac rget R En :=
rewrite R; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En.
Ltac run_ro_kept HFr HG HARx WK L WKn Ln :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG
ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia|]); destruct Hr)
ltac:(lia) ltac:(lia) ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn;
pose proof (lkept_trans _ _ _ _ _ L (lkept_of_run_ro Ef rs W _ _ sp1 HFr
ltac:(let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn; lia|]); destruct Hr) ltac:(lia) ltac:(lia))) as Ln;
cbn [ms_mem restrict mkst] in Ln; clear HFr HG end.
Definition S1I_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 28; 29; 30; 31]%bv.
Definition S1I_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 19; 21; 25; 26; 27]%bv.
Lemma s1i_clob_cases : forall r : bv 5, reg_in r S1I_CLOB = false -> r = 0%bv \/ In r S1I_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Definition s1i_regs := sr_set (sr_set (sr_set sr_atoms 18%bv (SLit 1)) 22%bv (SLit 1)) 23%bv (SLit 1).
Definition s1i_loc : YQ0b.region :=
YQ0b.mkRegion (Some 9%nat) 136 224 136 136
[YQ0b.mkChunk 136 (CVal 8 (SOff 40 0)); YQ0b.mkChunk 152 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 160 (CVal 8 (SOff 38 0)); YQ0b.mkChunk 168 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 176 (CVal 8 (SOff 39 0)); YQ0b.mkChunk 192 (CVal 8 (SOff 17 0)); YQ0b.mkChunk 200 (CVal 8 (SOff 15 0)); YQ0b.mkChunk 208 (CVal 8 (SOff 16 0));
YQ0b.mkChunk 216 (CVal 8 (SOff 29 0))].
Definition s1i_cur : YQ0b.region := YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition s1i_bef : YQ0b.region := YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition s1i_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (29%nat, mkAF SB SB 0); (32%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
(36%nat, mkAF 0 65534 0); (37%nat, HPTR 0); (38%nat, HPTR 0); (39%nat, mkAF 1 65535 0); (40%nat, mkAF 1 65535 0); (20%nat, mkAF 0 65534 0);
(19%nat, HPTR 0); (21%nat, HPTR 0); (24%nat, HPTR 0); (25%nat, HPTR 0); (26%nat, HPTR 0); (27%nat, HPTR 0);
(15%nat, HPTR 4); (16%nat, HPTR 3); (17%nat, HPTR 3) ] []
[ (SAlu ALU_ADD (SOff 20 0) (SOff 26 0), SOff 32 0); (SAlu ALU_ADD (SOff 20 0) (SOff 24 0), SOff 32 0);
(SAlu ALU_ADD (SOff 20 0) (SOff 27 0), SOff 33 0); (SAlu ALU_ADD (SOff 20 0) (SOff 25 0), SOff 33 0) ].
Definition ss_s1i : sstate := mkSS 0x87ac0 s1i_regs [s1i_loc; s1i_cur; s1i_bef] None s1i_facts.
Definition s1i_post (regsE : bvmap 5 word) (memE : word -> option byte) (i : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\ lkept W sp1 memE mem' /\
(forall r : bv 5, reg_in r S1I_CLOB = false -> getr regs' r = getr regsE r) /\
((pc' = 0x87b78 /\ getr regs' 24 = getr regsE 24 /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 1 /\
getr regs' 29 = Z_to_bv 64 SB /\ getr regs' 15 = Z_to_bv 64 g /\ getr regs' 16 = Z_to_bv 64 cfp /\ getr regs' 17 = Z_to_bv 64 bfp) \/
(pc' = 0x87bec /\ (exists c0, 0 <= c0 < Wd /\ PDp (i * Wd + c0)) /\
getr regs' 11 = Z_to_bv 64 i /\ getr regs' 18 = Z_to_bv 64 i /\ getr regs' 24 = Z_to_bv 64 Hd)).
Definition s1i_stmt (m : nat) : Prop :=
forall (c : Z) (regsE : bvmap 5 word) memE mdE (i : Z),
Wd - c <= Z.of_nat m -> 0 <= c < Wd -> 0 <= i < Hd ->
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r [2; 3; 4; 8; 9]%bv -> getr regsE r = getr regs r) ->
getr regsE 29 = Z_to_bv 64 SB -> getr regsE 15 = Z_to_bv 64 g -> getr regsE 16 = Z_to_bv 64 cfp -> getr regsE 17 = Z_to_bv 64 bfp ->
getr regsE 26 = Z_to_bv 64 (fimg + i * Wd) -> getr regsE 24 = Z_to_bv 64 (fimg + i * Wd) -> getr regsE 19 = Z_to_bv 64 (fimg + i * Wd) ->
getr regsE 27 = Z_to_bv 64 (bimg + i * Wd) -> getr regsE 25 = Z_to_bv 64 (bimg + i * Wd) -> getr regsE 21 = Z_to_bv 64 (bimg + i * Wd) ->
getr regsE 20 = Z_to_bv 64 c ->
getr regsE 18 = Z_to_bv 64 1 -> getr regsE 22 = Z_to_bv 64 1 -> getr regsE 23 = Z_to_bv 64 1 ->
val_mem trbsegs (mrestrict (w_H W) memE) (sp1 + 152) 8 i -> val_mem trbsegs (mrestrict (w_H W) memE) (sp1 + 160) 8 bimg ->
SRr trbsegs W (mkCfg (mkst regsE (Z_to_bv 64 0x87ac0) memE (seg_rom trbsegs)) mdE) (s1i_post regsE memE i).
Lemma fl_s1i_step : forall m, s1i_stmt m -> s1i_stmt (Datatypes.S m).
Proof.
intros m IH. unfold s1i_stmt.
intros c regsE memE mdE i Hm Hcw Hi HJE WK HKE E29r E15r E16r E17r E26r E24r E19r E27r E25r E21r E20r E18r E22r E23r V152 V160.
wctx_names. wprelude HJE. pose proof HJE as HJE0.
pose proof (proj1 (proj2 HJE)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_img _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_img _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_img _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bfp FRAME_SIZE HAR Hbf) as (Hp16 & Hp4096 & Hpceil & Hpfh_ia & _ & _). pose proof (proj1 Hpfh_ia) as Hpfh.
pose proof (blk_off_img _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hpfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi RW RH; nia).
assert (Hp : 0 <= i * Wd + c /\ i * Wd + c + (Wd - c) <= Nb) by (clear - HiW Hcw; lia).
set (p := i * Wd + c) in *.
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi ltac:(lia)) as [VbC RbC].
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi ltac:(lia)) as [VbB RbB].
set (bC := bval (aview trbsegs (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview trbsegs (w_H W) memc) (bimg + p)) in *.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 192 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 200 g WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vg) as VgE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 208 cfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vcfp) as VcfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 176 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 136 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V136) as V136E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168E.
remember (Ereg regsE [Z_to_bv 64 (fimg + p); Z_to_bv 64 (bimg + p); Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 i; Z_to_bv 64 fimg; Z_to_bv 64 bimg; Z_to_bv 64 Wd; Z_to_bv 64 Hd]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 (fimg + p); Z_to_bv 64 (bimg + p); Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 i; Z_to_bv 64 fimg; Z_to_bv 64 bimg; Z_to_bv 64 Wd; Z_to_bv 64 Hd]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 29%nat 29%bv eq_refl) as F29. rewrite E29r in F29.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite E15r in E15. pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite E16r in E16.
pose proof (EE 17%nat 17%bv eq_refl) as E17. rewrite E17r in E17.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite E24r in E24.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite E19r in E19.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20.
assert (E32 : ew E 32 = Z_to_bv 64 (fimg + p)) by (subst E; exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (bimg + p)) by (subst E; exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bC) by (subst E; exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 bB) by (subst E; exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 i) by (subst E; exact (ew_Ereg_extra regsE _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regsE _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 bimg) by (subst E; exact (ew_Ereg_extra regsE _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 Wd) by (subst E; exact (ew_Ereg_extra regsE _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 Hd) by (subst E; exact (ew_Ereg_extra regsE _ 8)).
assert (HS : st_ok trbsegs E ss_s1i (restrict (w_H W) (mkst regsE (Z_to_bv 64 0x87ac0) memE (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_s1i, s1i_regs.
apply (rn_st_ok_any E 0x87ac0 _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite E18r; cbn [sv_denot]; reflexivity]
| intros X; discriminate X | rewrite E22r; cbn [sv_denot]; reflexivity]
| intros X; discriminate X | rewrite E23r; cbn [sv_denot]; reflexivity].
- reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok, s1i_loc, s1i_cur, s1i_bef;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 136 8 _ Hd); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V136E]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 152 8 _ i); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V152]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 160 8 _ bimg); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168E]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VgE]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VcfpE]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite F29, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_nil.
+ rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trbsegs E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trbsegs E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s1i_loc, s1i_cur, s1i_bef. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E9, E32, E33, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [s1i_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F29, E32, E33, E34, E35, E36, E37, E38, E39, E40, E20, E19, E21, E24, E25, E26, E27, E15, E16, E17, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end].
+ cbn [s1i_facts f_alias alias_ok].
split; [rewrite (denot_add_atoms E 20 26 c (fimg + i * Wd) E20 E26) by lia; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; subst p; lia|].
split; [rewrite (denot_add_atoms E 20 24 c (fimg + i * Wd) E20 E24) by lia; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; subst p; lia|].
split; [rewrite (denot_add_atoms E 20 27 c (bimg + i * Wd) E20 E27) by lia; cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; subst p; lia|].
split; [rewrite (denot_add_atoms E 20 25 c (bimg + i * Wd) E20 E25) by lia; cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; subst p; lia | exact I]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memE).
pose proof (lkept_refl W sp1 memE) as L0.
aj_run_tok trbtbl_lib_ok HS HJE SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR WK L0 WK1 L1. clear HF.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
1: {
exfalso. rewrite branch_ltu_U in Hc. rewrite (U_atom _ 32 (fimg + p) E32), (U_atom _ 19 (fimg + i * Wd) E19) in Hc by lia. apply Z.ltb_lt in Hc. unfold p in Hc. lia. }
clear Hc.
pose proof (proj1 HJE) as HAR1.
aj_run_tok trbtbl_lib_ok HS HJE SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 32 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 32 (fimg + p) cc E32) by lia | rewrite (U_atom Ex 32 (fimg + p) E32) by lia];
eapply (obl_of_block trbsegs _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len fimg Nb (proj1 HJE) Hfi); [rewrite (U_atom Ex 29 SB F29); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR1 WK1 L1 WK2 L2. clear HF.
efact HS 33%nat E33 G33. efact HS 21%nat E21 G21.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
1: { exfalso. rewrite branch_ltu_U in Hc. rewrite (U_atom _ 33 (bimg + p) G33), (U_atom _ 21 (bimg + i * Wd) G21) in Hc by lia. apply Z.ltb_lt in Hc. unfold p in Hc. lia. }
clear Hc.
efact HS 29%nat F29 G29. pose proof (proj1 HJE) as HAR2.
aj_run_to_tok trbtbl_lib_ok HS HJE SHOK FLBspan A_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (bimg + p) cc G33) by lia | rewrite (U_atom Ex 33 (bimg + p) G33) by lia];
eapply (obl_of_block trbsegs _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len bimg Nb (proj1 HJE) Hbi); [rewrite (U_atom Ex 29 SB G29); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR2 WK2 L2 WK3 L3. clear HF.
rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2. rreg HS (13%bv : bv 5) Qa3. rreg HS (14%bv : bv 5) Qa4.
rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX p (Z_to_bv 64 0x87b3c) HJE WK3) end.
- lia.
- unfold spZ. rewrite Qsp, (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp, (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp, (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- unfold s0Z. rewrite Qs0, (EE 8%nat 8%bv eq_refl), (HKE 8%bv ltac:(cbv; tauto)). exact Hs0.
- rewrite Qa0. exact E15. - rewrite Qa1. exact E16. - rewrite Qa2. exact E17. - rewrite Qa3. exact E34. - rewrite Qa4. exact E35.
- exact Qra. - apply ret_ok_even. vm_compute. reflexivity. - rewrite unsigned_lit_small by lia. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hz & WKc & Kc & Lc).
pose proof (lkept_trans _ _ _ _ _ L3 Lc) as L4.
clear Qa0 Qa1 Qa2 Qa3 Qa4 Qra Qsp Qgp Qtp Qs0.
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K 0 (SOff 29 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2 end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil] | specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj trbsegs _); [exact Kc | exact HJ2
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia
| lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 29%nat.
efact HS 29%nat F29 H29c. efact HS 36%nat E36 G36. efact HS 40%nat E40 G40. efact HS 39%nat E39 G39. efact HS 20%nat E20 G20.
pose proof (proj1 HJ2) as HAR3.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR3 WKc L4 WK5 L5. clear HF.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
-
assert (HPD : PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
intros HZ; apply Hc; lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros HP; exact (HP HZ) end. }
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR4.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR4 WK5 L5 WK6 L6. clear HF.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
+
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR5.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan 0x87bec.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR5 WK6 L6 WK7 L7. clear HF.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ S1I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (11%bv : bv 5) R11. rreg HS (18%bv : bv 5) R18. rreg HS (24%bv : bv 5) R24.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 0x87bec end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK7|]. split; [exact L7|].
split; [intros r Hr; destruct (s1i_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]|].
right. split; [reflexivity|]. split; [exists c; split; [clear - Hcw; lia | exact HPD]|].
split; [rget R11 G36|]. split; [rget R18 G36 | rget R24 G40].
+
exfalso. rewrite branch_ne_U in Hc0.
rewrite (U_atom _ 40 Hd) in Hc0 by (first [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E40 | lia]).
rewrite (U_atom _ 36 i) in Hc0 by (first [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E36 | lia]).
apply (proj1 (negb_false_iff _)) in Hc0. apply Z.eqb_eq in Hc0. clear - Hc0 Hi. lia.
-
assert (HnPD : ~ PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
lazymatch goal with |- getr regs2 10 = w64 0 =>
enough (Hvz : U Ex (SOff n 0) = bv_unsigned (getr regs2 10)) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hvz; exact Hc) end;
rewrite U_SOff; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
unfold CLOB; cbn [map nth]; rewrite Z.add_0_r; apply zcanon_id; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia end. }
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR4.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR4 WK5 L5 WK6 L6. clear HF.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
+
rewrite branch_ne_U in Hc0. rewrite (U_atom _ 39 Wd) in Hc0 by (first [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E39 | lia]).
rewrite (U_atom_off _ 20 c 1) in Hc0 by (first [rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E20 | lia]).
apply (proj1 (negb_true_iff _)) in Hc0. apply Z.eqb_neq in Hc0.
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR5.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan 0x87ac0.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR5 WK6 L6 WK7 L7. clear HF.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ S1I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (HK2 : forall r : bv 5, reg_in r S1I_CLOB = false -> getr (ms_regs msx) r = getr regsE r) end.
{ intros r Hr. destruct (s1i_clob_cases r Hr) as [-> | Hr']; [rewrite (st_ok_restrict_reg trbsegs _ _ _ _ 0%bv HS), (st_ok_restrict_reg trbsegs _ _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]. }
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ [24%bv] HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity) 24%bv ltac:(left; reflexivity)) as HK24. cbn [ms_regs restrict] in HK24.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s1i_loc) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR9; cbn [ms_mem restrict mkst] in HR9;
lazymatch type of HR9 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SOff 36 0) i HR9
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152n;
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SOff 38 0) bimg HR9
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160n end; clear HR9 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V152n, V160n.
rreg HS (29%bv : bv 5) R29. rreg HS (15%bv : bv 5) R15. rreg HS (16%bv : bv 5) R16. rreg HS (17%bv : bv 5) R17.
rreg HS (26%bv : bv 5) R26. rreg HS (24%bv : bv 5) R24. rreg HS (19%bv : bv 5) R19. rreg HS (27%bv : bv 5) R27. rreg HS (25%bv : bv 5) R25. rreg HS (21%bv : bv 5) R21.
rreg HS (20%bv : bv 5) R20. rreg HS (18%bv : bv 5) R18. rreg HS (22%bv : bv 5) R22. rreg HS (23%bv : bv 5) R23.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_mono.
{ eapply (IH (c + 1) _ _ _ i); [ lia | lia | exact Hi | exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HK2; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr | apply HKE; exact Hr]
| rget R29 F29 | rget R15 E15 | rget R16 E16 | rget R17 E17
| rget R26 E26 | rget R24 E24 | rget R19 E19 | rget R27 E27 | rget R25 E25 | rget R21 E21
| rewrite R20; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E20, unsigned_lit_small by lia; f_equal; lia
| exact R18 | exact R22 | exact R23
| exact V152n | exact V160n ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & pc3 & -> & HJ3 & WK8 & L8 & HK3 & Hex).
split; [reflexivity|]. exists regs3, mem3, md3, pc3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact WK8|]. split; [exact (lkept_trans _ _ _ _ _ L7 L8)|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK2 r Hr)|].
destruct Hex as [(Hpc3 & H24 & Hrest) | HF]; [left; split; [exact Hpc3 | split; [rewrite H24; exact HK24 | exact Hrest]] | right; exact HF].
+
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR5.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan 0x87b78.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_kept HFr HG HAR5 WK6 L6 WK7 L7. clear HF.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ S1I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ [24%bv] HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity) 24%bv ltac:(left; reflexivity)) as HK24. cbn [ms_regs restrict] in HK24.
rreg HS (29%bv : bv 5) R29. rreg HS (15%bv : bv 5) R15. rreg HS (16%bv : bv 5) R16. rreg HS (17%bv : bv 5) R17.
rreg HS (18%bv : bv 5) R18. rreg HS (22%bv : bv 5) R22. rreg HS (23%bv : bv 5) R23.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 0x87b78 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK7|]. split; [exact L7|].
split; [intros r Hr; destruct (s1i_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]|].
left. split; [reflexivity|]. split; [exact HK24|]. split; [exact R18|]. split; [exact R22|]. split; [exact R23|].
split; [rget R29 F29|]. split; [rget R15 E15|]. split; [rget R16 E16 | rget R17 E17].
Qed.
Lemma fl_s1i : forall m, s1i_stmt m.
Proof. induction m as [|m IH]; [unfold s1i_stmt; intros; exfalso; lia | exact (fl_s1i_step m IH)]. Qed.
End e.
End d.
End b.
