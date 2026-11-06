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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC0x YC17 YC1b YC2u YC1z YC1y YC29 YC2b YC2c YC2l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_icpt.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section d.
Variables (W : world trasegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd a176 a184 : Z) (sv2 sv4 : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HRES : 0 <= a176 < 2 ^ 64 /\ 0 <= a184 < 2 ^ 64 /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 144) 8 a176 /\ val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 176) 8 a184.
Hypothesis HFIMG : val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 224) 8 fimg.
Hypothesis HSAV2 : 0 <= sv2 < 2 ^ 64 /\ val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 96) 8 sv2.
Let BDp := BD W memc fimg bimg.
Let CALL := bcmp_callW B LAWS ABCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp);
pose proof HGEO as (RW & RH & HN & V200 & V112); pose proof HRES as (R176 & R184 & V176 & V184).
Ltac wprelude HJ :=
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (HFB : FBAND = 8192) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Ltac noW := cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia|]); destruct Hr.
Ltac awrRO := repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]); try (match goal with |- ?g => idtac "AWR-LEFT" g end).
Definition F2_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 28; 29; 30; 31]%bv.
Definition F2_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 20; 22; 23; 24; 25; 26; 27]%bv.

Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition f2_regs := sr_set sr_atoms 19%bv (SLit 65535).
Definition f2_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 224 232 224 224 [YQ0b.mkChunk 224 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 240 248 240 240 [YQ0b.mkChunk 240 (CVal 8 (SOff 33 0))];
YQ0b.mkRegion (Some 9%nat) 216 224 216 216 [YQ0b.mkChunk 216 (CVal 8 (SOff 34 0))] ].
Definition f2_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (33%nat, mkAF SB SB 0); (18%nat, mkAF 1 65534 0); (23%nat, mkAF 1 65535 0); (20%nat, mkAF 0 65533 0);
(32%nat, HPTR 0); (25%nat, HPTR 0); (34%nat, HPTR 4); (22%nat, HPTR 3); (27%nat, mkAF 0 65533 0); (26%nat, mkAF 0 65533 0) ] [] [].
Definition ss_f2 : sstate := mkSS 0x87bc4 f2_regs f2_mem None f2_facts.
Definition f2_post (top : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' bot,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x87c00) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
top <= bot < Hd /\
getr regs' 18 = Z_to_bv 64 bot /\ getr regs' 26 = Z_to_bv 64 top /\ getr regs' 19 = Z_to_bv 64 65535 /\
getr regs' 25 = Z_to_bv 64 bimg /\ getr regs' 27 = Z_to_bv 64 top /\ getr regs' 20 = Z_to_bv 64 top /\ getr regs' 24 = Z_to_bv 64 sv4.
Definition f2_stmt (m : nat) : Prop :=
forall (i top v : Z) (regsE : bvmap 5 word) memE mdE,
i - top <= Z.of_nat m -> 0 <= top -> top < i < Hd ->
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 22 = Z_to_bv 64 cfp -> val_mem trasegs (mrestrict (w_H W) memE) (sp1 + 216) 8 g -> getr regsE 19 = Z_to_bv 64 65535 ->
getr regsE 18 = Z_to_bv 64 i -> getr regsE 21 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = i * Wd ->
getr regsE 23 = Z_to_bv 64 Wd -> getr regsE 25 = Z_to_bv 64 bimg -> getr regsE 20 = Z_to_bv 64 top -> getr regsE 27 = Z_to_bv 64 top -> getr regsE 26 = Z_to_bv 64 top -> getr regsE 24 = Z_to_bv 64 sv4 ->
SRr trasegs W (mkCfg (mkst regsE (Z_to_bv 64 0x87bc4) memE (seg_rom trasegs)) mdE) (f2_post top).
Lemma fl_f2l_step : forall m, f2_stmt m -> f2_stmt (Datatypes.S m).
Proof.
intros m IH. unfold f2_stmt.
intros i top v regsE memE mdE Hm Ht0 Hi HJE WK HKE E22r V216g E19r E18r E21r Rv Mv E24r E25r E20r E27r E26r E24s.
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
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi Ht0 RW RH; nia).
assert (HiW32 : i * Wd < 2 ^ 32) by (clear - Hi Ht0 RW RH; nia).
assert (HSpresE : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as V216E.
remember (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 g]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 g]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite E18r in E18. pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21.
pose proof (EE 23%nat 23%bv eq_refl) as E24. rewrite E24r in E24. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. assert (E23 : ew E 34 = Z_to_bv 64 g) by (subst E; exact (ew_Ereg_extra regsE _ 2)).
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regsE _ 1)).
assert (HS : st_ok trasegs E ss_f2 (restrict (w_H W) (mkst regsE (Z_to_bv 64 0x87bc4) memE (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f2, f2_regs.
apply (rn_st_ok_any E 0x87bc4 _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite E19r; reflexivity].
- reflexivity.
- unfold f2_mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
+ apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216E]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 216 8 _ g); [cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216g]|]. apply Forall_nil.
- unfold f2_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f2_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E33, E18, E24, E20, E32, E25, E23, E22, E27, E26, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 33 0) E (mrestrict (w_H W) memE).
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan A_bcmp_icpt.
1: { unfold f2_mem. awrRO. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 ltac:(unfold ss_f2, f2_mem; intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpresE)) as WK1.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 216) 8 g HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(unfold ss_f2, f2_mem; intros kk _; revert kk; noW) V216g) as V216a.
cbn [ms_mem restrict mkst] in V216a.
rreg HS (12%bv : bv 5) Qa2. rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (F32 : ew Ev 32 = Z_to_bv 64 fimg) by (evE; exact E32); assert (F25 : ew Ev 25 = Z_to_bv 64 bimg) by (evE; exact E25); assert (F21 : ew Ev 21 = Z_to_bv 64 v) by (evE; exact E21);
assert (UA : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 32))) = fimg + i * Wd)
by (rewrite (U_add_atom_zext32 Ev 32 _ fimg F32) by lia; rewrite (U_atom Ev 21 v F21) by lia; rewrite Mv; reflexivity);
assert (UB : U Ev (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 32))) = bimg + i * Wd)
by (rewrite (U_add_atom_zext32 Ev 25 _ bimg F25) by lia; rewrite (U_atom Ev 21 v F21) by lia; rewrite Mv; reflexivity);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UA)) Qa0;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) Qa1 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX (i * Wd) Wd (Z_to_bv 64 556000) HJE WK1) end.
- lia. - lia. - lia.
- unfold spZ. rewrite Qsp; evE. rewrite (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp; evE. rewrite (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp; evE. rewrite (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- exact Qa0. - exact Qa1. - rewrite Qa2; evE. exact E24.
- exact Qra. - apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & vv & -> & HJ2 & HP2 & Hv & Hz & WK2 & Kc & Lc).
clear Qa0 Qa1 Qa2 Qra Qsp Qgp Qtp UA UB.
assert (HSpres2 : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) mem2 a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 216) 8 _ Lc ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V216a) as V216b.
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K 0 (SOff 33 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2 end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]] | specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj trasegs _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj trasegs _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj trasegs _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 33%nat.
pose proof (proj1 HJ2) as HAR4.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK FLBspan.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 g HFr4 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk _; revert kk; noW) V216b) as V216c.
cbn [ms_mem restrict mkst] in V216c.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpres2)) as WK5.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
reshok_bx HS 33%nat. pose proof (proj1 HJ2) as HAR5.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x87c00.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK5 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (6%bv : bv 5) R6. rreg HS (21%bv : bv 5) R21. rreg HS (18%bv : bv 5) R18. rreg HS (19%bv : bv 5) R19.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, i end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite R6; evE; exact E33|]. split; [rewrite R21; evE; exact E23|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [lia|].
split; [rewrite R18; evE; exact E18|]. split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [exact R19|].
split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r | rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E24s].
-
reshok_bx HS 33%nat. pose proof (proj1 HJ2) as HAR5.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK FLBspan.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK5 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
clear Hc. srr_branch_tok tratbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HLTU end;
rewrite branch_ltu_U in HLTU; rewrite (U_atom _ 20 top) in HLTU by (first [evE; exact E20 | lia]); rewrite (U_and_ffff_off _ 18 i (-1)) in HLTU by (first [evE; exact E18 | lia]);
[apply Z.ltb_lt in HLTU | apply Z.ltb_ge in HLTU]; reshok_bx HS 33%nat; pose proof (proj1 HJ2) as HAR6.
+
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x87bc4.
1: { awrRO. }
rename HFr into HFr6. rename HG into HG6. clear HF.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 g HFr5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk _; revert kk; noW) V216c) as V216d.
cbn [ms_mem restrict mkst] in V216d.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 g HFr6 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk _; revert kk; noW) V216d) as V216e.
cbn [ms_mem restrict mkst] in V216e.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK6 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR6 HFr6 HG6 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK6 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK7.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (18%bv : bv 5) R18. rreg HS (19%bv : bv 5) R19.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (G21 : ew Ev 21 = Z_to_bv 64 v) by (evE; exact E21); assert (G24 : ew Ev 23 = Z_to_bv 64 Wd) by (evE; exact E24);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (U Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0)))) (denot_lit_U Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0))) R21;
assert (Mv' : U Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0)) mod 2 ^ 32 = (i - 1) * Wd)
by (rewrite U_subw_mod32, (U_atom Ev 21 v G21), (U_atom Ev 23 Wd G24) by lia;
rewrite <- Zminus_mod_idemp_l, Mv; replace (i * Wd - Wd) with ((i - 1) * Wd) by lia; apply Z.mod_small; clear - Hi Ht0 RW HiW32; nia);
pose proof (U_range Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0))) as Rv'; rewrite M64_val in Rv' end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (IH (i - 1) top); [ lia | exact Ht0 | lia | exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r | exact V216e | exact R19
| rewrite R18; evE; rewrite E18, unsigned_lit_small by lia; f_equal; lia
| exact R21 | exact Rv' | exact Mv'
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E24r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r
| rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E24s ].
+
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x87c00.
1: { awrRO. }
rename HFr into HFr6. rename HG into HG6. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK6 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR6 HFr6 HG6 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK6 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK7.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (6%bv : bv 5) R6. rreg HS (21%bv : bv 5) R21. rreg HS (18%bv : bv 5) R18. rreg HS (19%bv : bv 5) R19.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, top end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK7|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite R6; evE; exact E33|]. split; [rewrite R21; evE; exact E23|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [lia|].
split; [rewrite R18; evE; exact E27|]. split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [exact R19|].
split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r | rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E24s].
Qed.
Lemma fl_f2l : forall m, f2_stmt m.
Proof. induction m as [|m IH]; [unfold f2_stmt; intros; exfalso; lia | exact (fl_f2l_step m IH)]. Qed.
Definition f2s_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 96 104 96 96 [YQ0b.mkChunk 96 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 9%nat) 200 224 216 224 [YQ0b.mkChunk 200 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 208 (CVal 8 (SOff 34 0))];
YQ0b.mkRegion (Some 9%nat) 240 248 240 240 [YQ0b.mkChunk 240 (CVal 8 (SOff 33 0))] ].
Definition f2s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (33%nat, mkAF SB SB 0); (27%nat, mkAF 0 65534 0); (34%nat, mkAF 1 65535 0); (36%nat, mkAF 1 65535 0);
(25%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3) ] [] [].
Definition ss_f2s : sstate := mkSS 0x87b74 sr_atoms f2s_mem None f2s_facts.
Ltac wscr_windows E9 :=
cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_ewset_other in Hw by lia;
rewrite ?E9, ?unsigned_lit_small in Hw by lia; unfold wscr; lia |]);
destruct Hr.
Ltac awrW E9 FFS :=
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
Lemma fl_f2 : forall (top : Z) (regsF : bvmap 5 word) memF mdF,
0 <= top < Hd ->
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkeptF B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp ->
getr regsF 27 = Z_to_bv 64 top -> getr regsF 20 = Z_to_bv 64 sv4 -> getr regsF 25 = Z_to_bv 64 bimg ->
SRr trasegs W (mkCfg (mkst regsF (Z_to_bv 64 0x87b74) memF (seg_rom trasegs)) mdF) (f2_post top).
Proof.
intros top regsF memF mdF Htp1 HJF WK HKF E21r E22r E27r E20r E25r.
wctx_names. wprelude HJF. pose proof HJF as HJF0. pose proof HSAV2 as (Rsv2 & V96).
pose proof (proj1 (proj2 HJF)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_img _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_img _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HSpresF : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memF a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbF.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 208 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V112) as V208F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 96 sv2 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V96) as V96F.
remember (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 Hd; Z_to_bv 64 sv2; Z_to_bv 64 Wd]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 Hd; Z_to_bv 64 sv2; Z_to_bv 64 Wd]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regsF _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 Hd) by (subst E; exact (ew_Ereg_extra regsF _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sv2) by (subst E; exact (ew_Ereg_extra regsF _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 Wd) by (subst E; exact (ew_Ereg_extra regsF _ 4)).
assert (HS : st_ok trasegs E ss_f2s (restrict (w_H W) (mkst regsF (Z_to_bv 64 0x87b74) memF (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f2s.
apply (rn_st_ok_any E 0x87b74 _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_Ereg.
- reflexivity.
- unfold f2s_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable trasegs); apply HSpresF; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 96 8 _ sv2); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V96F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200F]|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 208 8 _ Hd); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbF]|]. apply Forall_nil.
- unfold f2s_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f2s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E33, E27, E34, E36, E25, E21, E22, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT3" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 33 0) E (mrestrict (w_H W) memF).
aj_run_tok tratbl_lib_ok HS HJF SHOK FLBspan.
1: { unfold f2s_mem. awrW E9 FFS. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memF _ mdF sp1 HAR HFr1 HG1 ltac:(unfold ss_f2s, f2s_mem; wscr_windows E9) ltac:(lia) ltac:(lia) HSpresF)) as WK1.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
exfalso.
rewrite branch_eq_U in Hc. rewrite (U_atom _ 27 top) in Hc by (first [evE; exact E27 | lia]). rewrite (U_atom _ 34 Hd) in Hc by (first [evE; exact E34 | lia]).
apply Z.eqb_eq in Hc. clear - Hc Htp1. lia.
- clear Hc. reshok_bx HS 33%nat. pose proof (proj1 HJF) as HAR2.
aj_run_tok tratbl_lib_ok HS HJF SHOK FLBspan.
1: { awrW E9 FFS. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HGEU end;
rewrite branch_geu_U in HGEU; rewrite (U_and_ffff_off _ 27 top 0) in HGEU by (first [evE; exact E27 | lia]); rewrite (U_and_ffff_off _ 34 Hd (-1)) in HGEU by (first [evE; exact E34 | lia]);
[apply (proj1 (negb_true_iff _)) in HGEU; apply Z.ltb_ge in HGEU | apply (proj1 (negb_false_iff _)) in HGEU; apply Z.ltb_lt in HGEU];
reshok_bx HS 33%nat; pose proof (proj1 HJF) as HAR3.
+
aj_run_to_tok tratbl_lib_ok HS HJF SHOK FLBspan 0x87c00.
1: { awrW E9 FFS. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsF _ (21%bv :: 22%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (6%bv : bv 5) R6. rreg HS (18%bv : bv 5) R18. rreg HS (26%bv : bv 5) R26. rreg HS (19%bv : bv 5) R19. rreg HS (27%bv : bv 5) R27. rreg HS (24%bv : bv 5) R24.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (UT : U Ev (SAlu ALU_AND (SOff 27 0) (SLit 65535)) = top) by (rewrite (U_and_ffff_off Ev 27 top 0 ltac:(evE; exact E27)) by lia; lia);
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 top) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UT)) R20 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, top end.
split; [reflexivity|]. split; [exact HJF|]. split; [exact WK3|].
split; [intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]|].
split; [rewrite R6; evE; exact E33|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [lia|].
split; [rewrite R18; evE; rewrite E34, unsigned_lit_small by lia; f_equal; lia|]. split; [rewrite R26; evE; exact E27|]. split; [exact R19|].
split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|]. split; [rewrite R27; evE; exact E27|]. split; [exact R20 | rewrite R24; evE; exact E20].
+
aj_run_to_tok tratbl_lib_ok HS HJF SHOK FLBspan 0x87bc4.
1: { awrW E9 FFS. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YQ0b.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 216 8%N (SOff 21 0) g HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; evE; rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V216 end; clear HR1 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V216.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsF _ (22%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (23%bv : bv 5) R23. rreg HS (19%bv : bv 5) R19. rreg HS (18%bv : bv 5) R18. rreg HS (24%bv : bv 5) R24. rreg HS (27%bv : bv 5) R27. rreg HS (26%bv : bv 5) R26.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (G34 : ew Ev 34 = Z_to_bv 64 Hd) by (evE; exact E34); assert (G36 : ew Ev 36 = Z_to_bv 64 Wd) by (evE; exact E36); assert (G27 : ew Ev 27 = Z_to_bv 64 top) by (evE; exact E27);
assert (UT : U Ev (SAlu ALU_AND (SOff 27 0) (SLit 65535)) = top) by (rewrite (U_and_ffff_off Ev 27 top 0 G27) by lia; lia);
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 top) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UT)) R20;
assert (UH1 : U Ev (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Hd - 1) by (apply (U_dec_zext16 Ev 34 Hd G34); lia);
assert (UV : U Ev (SMd M_MUL (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) (SOff 36 0)) = (Hd - 1) * Wd)
by (rewrite U_mul_small; rewrite UH1, (U_atom Ev 36 Wd G36) by lia; [reflexivity | clear - RW RH; nia]);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 ((Hd - 1) * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UV)) R21 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (fl_f2l (Z.to_nat Hd) (Hd - 1) top ((Hd - 1) * Wd));
[ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJF | exact WK3
| intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]
| rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| exact V216
| exact R19
| rewrite R18; evE; rewrite E34, unsigned_lit_small by lia; f_equal; lia
| exact R21 | clear - RW RH; nia | rewrite Z.mod_small; clear - RW RH; nia
| rewrite R23; evE; exact E36
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| exact R20
| rewrite R27; evE; exact E27 | rewrite R26; evE; exact E27
| rewrite R24; evE; exact E20 ].
Qed.
End d.
End c.
End b.
