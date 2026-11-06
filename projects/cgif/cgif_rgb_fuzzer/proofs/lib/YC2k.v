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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC0x YC17 YC1b YC2u YC1z YC1y YC29 YC2b.
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
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis TCMP : tcmp_spec B.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section e.
Variables (W : world trasegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Let CALL := cmp_callW B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp);
pose proof HGEO as (RW & RH & HN & V200 & V112).
Ltac wprelude HJ :=
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Definition S2I_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 26; 28; 29; 30; 31]%bv.
Definition S2I_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 24; 25; 27]%bv.
Lemma s2i_clob_cases : forall r : bv 5, reg_in r S2I_CLOB = false -> r = 0%bv \/ In r S2I_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Definition s2i_regs := sr_set (sr_set sr_atoms 20%bv (SOff 23 0)) 19%bv (SOff 26 0).
Definition s2i_loc : YQ0b.region :=
YQ0b.mkRegion (Some 9%nat) 152 256 152 152
[YQ0b.mkChunk 152 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 192 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 240 (CVal 8 (SOff 6 0)); YQ0b.mkChunk 248 (CVal 8 (SOff 32 0))].
Definition s2i_cur : YQ0b.region := YQ0b.mkRegion (Some 23%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition s2i_bef : YQ0b.region := YQ0b.mkRegion (Some 26%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition s2i_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (23%nat, HPTR 0); (26%nat, HPTR 0); (21%nat, mkAF 1 65535 0);
(25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, HPTR 3); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0);
(35%nat, mkAF 0 65534 0); (36%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2i : sstate := mkSS 0x8725c s2i_regs [s2i_loc; s2i_cur; s2i_bef] None s2i_facts.
Definition s2i_post (regsE : bvmap 5 word) (memE : word -> option byte) (i top : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\ lkept W sp1 memE mem' /\
(forall r : bv 5, reg_in r S2I_CLOB = false -> getr regs' r = getr regsE r) /\
getr regs' 6 = Z_to_bv 64 SB /\
((pc' = 0x872d0 /\ getr regs' 22 = getr regsE 22) \/
(pc' = 0x873a8 /\ (exists c0, 0 <= c0 < Wd /\ PDp (i * Wd + c0)) /\
getr regs' 19 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 (i + 1) /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp)).
Definition s2i_stmt (m : nat) : Prop :=
forall (c : Z) (regsE : bvmap 5 word) memE mdE (i top : Z),
Wd - c <= Z.of_nat m -> 0 <= c < Wd -> 0 <= i < Hd -> 0 <= top < Hd ->
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r [2; 3; 4; 8; 9]%bv -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB -> getr regsE 25 = Z_to_bv 64 g -> getr regsE 24 = Z_to_bv 64 cfp ->
getr regsE 23 = Z_to_bv 64 (fimg + (i * Wd + c)) -> getr regsE 20 = Z_to_bv 64 (fimg + (i * Wd + c)) ->
getr regsE 26 = Z_to_bv 64 (bimg + (i * Wd + c)) -> getr regsE 19 = Z_to_bv 64 (bimg + (i * Wd + c)) ->
getr regsE 21 = Z_to_bv 64 (Wd - c) ->
val_mem trasegs (mrestrict (w_H W) memE) (sp1 + 192) 8 top -> val_mem trasegs (mrestrict (w_H W) memE) (sp1 + 152) 8 (i + 1) ->
SRr trasegs W (mkCfg (mkst regsE (Z_to_bv 64 0x8725c) memE (seg_rom trasegs)) mdE) (s2i_post regsE memE i top).
Lemma fl_s2i_step : forall m, s2i_stmt m -> s2i_stmt (Datatypes.S m).
Proof.
intros m IH. unfold s2i_stmt.
intros c regsE memE mdE i top Hm Hcw Hi HtopR HJE WK HKE E6 E25r E22r E23r E20r E26r E19r E21r V208 V56.
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
assert (Hp : 0 <= i * Wd + c /\ i * Wd + c + (Wd - c) <= Nb) by (rewrite HN; clear - Hcw Hi RW RH; nia).
set (p := i * Wd + c) in *.
assert (HSpresE : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi ltac:(lia)) as [VbC RbC].
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi ltac:(lia)) as [VbB RbB].
set (bC := bval (aview trasegs (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview trasegs (w_H W) memc) (bimg + p)) in *.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 248 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
remember (Ereg regsE [Z_to_bv 64 bfp; Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 top; Z_to_bv 64 (i + 1)]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 bfp; Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 top; Z_to_bv 64 (i + 1)]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 24%nat 24%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 bfp) by (subst E; exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bC) by (subst E; exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bB) by (subst E; exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 top) by (subst E; exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (i + 1)) by (subst E; exact (ew_Ereg_extra regsE _ 4)).
assert (HS : st_ok trasegs E ss_s2i (restrict (w_H W) (mkst regsE (Z_to_bv 64 0x8725c) memE (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_s2i, s2i_regs.
apply (rn_st_ok_any E 0x8725c _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite E20r; cbn [sv_denot]; rewrite (ew_Ereg_nat regsE _ 23 23%bv eq_refl), E23r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity] | intros X; discriminate X |].
rewrite E19r. cbn [sv_denot]. rewrite (ew_Ereg_nat regsE _ 26 26%bv eq_refl), E26r, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok, s2i_loc, s2i_cur, s2i_bef;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 152 8 _ (i + 1)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V56]|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 192 8 _ top); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208]|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite F6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_nil.
+ rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E26, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s2i_loc, s2i_cur, s2i_bef. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E9, E23, E26, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2i_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E23, E26, E21, E25, E22, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memE).
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan A_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 23 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 23 (fimg + p) cc E23) by lia | rewrite (U_atom Ex 23 (fimg + p) E23) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb (proj1 HJE0) Hfi); [rewrite (U_atom Ex 6 SB F6); [reflexivity | unfold SB; lia] | lia | lia] end).
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 26 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 26 (bimg + p) cc E26) by lia | rewrite (U_atom Ex 26 (bimg + p) E26) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb (proj1 HJE0) Hbi); [rewrite (U_atom Ex 6 SB F6); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1
ltac:(unfold ss_s2i, s2i_loc, s2i_cur, s2i_bef; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(lia) ltac:(lia) HSpresE)) as WK1.
rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2. rreg HS (13%bv : bv 5) Qa3. rreg HS (14%bv : bv 5) Qa4.
rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX p (Z_to_bv 64 553620) HJE WK1) end.
- lia.
- unfold spZ. rewrite Qsp, (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp, (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp, (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- unfold s0Z. rewrite Qs0, (EE 8%nat 8%bv eq_refl), (HKE 8%bv ltac:(cbv; tauto)). exact Hs0.
- rewrite Qa0. exact E25. - rewrite Qa1. exact E22. - rewrite Qa2. exact E32. - rewrite Qa3. exact E33. - rewrite Qa4. exact E34.
- exact Qra. - apply ret_ok_even. vm_compute. reflexivity. - rewrite unsigned_lit_small by lia. lia. }
pose proof (lkept_of_run_ro E _ W memE _ sp1 HFr1 ltac:(unfold ss_s2i, s2i_loc, s2i_cur, s2i_bef; cbn [ss_mem]; intros r Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn; lia) ltac:(lia) ltac:(lia)) as L1.
cbn [ms_mem restrict mkst] in L1.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hz & WK2 & Kc & Lc).
pose proof (lkept_trans _ _ _ _ _ L1 Lc) as L2.
clear Qa0 Qa1 Qa2 Qa3 Qa4 Qra Qsp Qgp Qtp Qs0.
assert (HSpres2 : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) mem2 a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K 0 (SOff 6 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2 end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil] | specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj trasegs _); [exact Kc | exact HJ2
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia
| lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 6%nat.
lazymatch type of HS with st_ok _ ?Ecur _ _ =>
assert (G6 : ew Ecur 6 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact F6);
assert (G36 : ew Ecur 36 = Z_to_bv 64 (i + 1)) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E36);
assert (G35 : ew Ecur 35 = Z_to_bv 64 top) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E35);
assert (G21 : ew Ecur 21 = Z_to_bv 64 (Wd - c)) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E21) end.
pose proof (proj1 HJ2) as HAR2.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK2 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(lia) ltac:(lia) HSpres2)) as WK3.
pose proof (lkept_trans _ _ _ _ _ L2 (lkept_of_run_ro _ _ W _ _ sp1 HFr2 ltac:(intros r Hr; cbn [In] in Hr; destruct Hr as [<- | []]; cbn; lia) ltac:(lia) ltac:(lia))) as L3.
cbn [ms_mem restrict mkst] in L3.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
assert (HPD : PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
intros HZ; apply Hc; lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros HP; exact (HP HZ) end. }
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR3.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x873a8.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK3 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
pose proof (lkept_trans _ _ _ _ _ L3 (lkept_of_run_ro _ _ W _ _ sp1 HFr3 ltac:(intros r Hr; cbn [In] in Hr; destruct Hr as [<- | []]; cbn; lia) ltac:(lia) ltac:(lia))) as L4.
cbn [ms_mem restrict mkst] in L4.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ S2I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (6%bv : bv 5) R6. rreg HS (19%bv : bv 5) R11. rreg HS (15%bv : bv 5) R14. rreg HS (21%bv : bv 5) R21. rreg HS (22%bv : bv 5) R22x.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 0x873a8 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK4|]. split; [exact L4|].
split; [intros r Hr; destruct (s2i_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]|].
split; [rewrite R6, ?ew_ewset_other by lia; exact G6|].
right. split; [reflexivity|]. split; [exists c; split; [clear - Hcw; lia | exact HPD]|].
split; [rewrite R11, ?ew_ewset_other by lia; exact G35|]. split; [rewrite R14, ?ew_ewset_other by lia; exact G36|].
split; [rewrite R21, ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E25|].
rewrite R22x, ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E22.
-
assert (HnPD : ~ PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
lazymatch goal with |- getr regs2 10 = w64 0 =>
enough (Hvz : U Ex (SOff n 0) = bv_unsigned (getr regs2 10)) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hvz; exact Hc) end;
rewrite U_SOff; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
unfold CLOB; cbn [map nth]; rewrite Z.add_0_r; apply zcanon_id; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia end. }
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR3.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK3 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
pose proof (lkept_trans _ _ _ _ _ L3 (lkept_of_run_ro _ _ W _ _ sp1 HFr3 ltac:(intros r Hr; cbn [In] in Hr; destruct Hr as [<- | []]; cbn; lia) ltac:(lia) ltac:(lia))) as L4.
cbn [ms_mem restrict mkst] in L4.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
+
rewrite branch_eq_U in Hc0. rewrite (U_atom_off _ 21 (Wd - c) (-1)) in Hc0 by (first [exact G21 | lia]). rewrite U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR4.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x872d0.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK4 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ S2I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (6%bv : bv 5) R6.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 0x872d0 end.
pose proof (lkept_trans _ _ _ _ _ L4 (lkept_of_run_ro _ _ W _ _ sp1 HFr4 ltac:(intros r Hr; cbn [In] in Hr; destruct Hr as [<- | []]; cbn; lia) ltac:(lia) ltac:(lia))) as L5.
cbn [ms_mem restrict mkst] in L5.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK5|]. split; [exact L5|].
split; [intros r Hr; destruct (s2i_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]|].
split; [rewrite R6, ?ew_ewset_other by lia; exact G6|].
left. split; [reflexivity|].
exact (regs_kept_of_st_ok trasegs _ _ _ regsE _ [22%bv] HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity) 22%bv ltac:(left; reflexivity)).
+
rewrite branch_eq_U in Hc0. rewrite (U_atom_off _ 21 (Wd - c) (-1)) in Hc0 by (first [exact G21 | lia]). rewrite U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR4.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x8725c.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK4 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (lkept_trans _ _ _ _ _ L4 (lkept_of_run_ro _ _ W _ _ sp1 HFr4 ltac:(intros r Hr; cbn [In] in Hr; destruct Hr as [<- | []]; cbn; lia) ltac:(lia) ltac:(lia))) as L5.
cbn [ms_mem restrict mkst] in L5.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ S2I_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ [22%bv] HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity) 22%bv ltac:(left; reflexivity)) as HK22. cbn [ms_regs restrict] in HK22.
assert (HK2 : forall r : bv 5, reg_in r S2I_CLOB = false -> getr (ms_regs ms2) r = getr regsE r).
{ intros r Hr. destruct (s2i_clob_cases r Hr) as [-> | Hr']; [rewrite (st_ok_restrict_reg trasegs _ _ _ _ 0%bv HS), (st_ok_restrict_reg trasegs _ _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]. }
rreg HS (6%bv : bv 5) R6. rreg HS (23%bv : bv 5) R23. rreg HS (20%bv : bv 5) R20. rreg HS (26%bv : bv 5) R26. rreg HS (19%bv : bv 5) R19. rreg HS (21%bv : bv 5) R21.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_mono.
{ eapply (IH (c + 1) _ _ _ i top); [ lia | lia | exact Hi | exact HtopR | exact HJ2 | exact WK5
| intros r Hr; transitivity (getr regsE r); [apply HK2; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr | apply HKE; exact Hr]
| rewrite R6, ?ew_ewset_other by lia; exact G6
| rewrite (HK2 25%bv eq_refl); exact E25r
| rewrite (HK2 24%bv eq_refl); exact E22r
| rewrite R23, ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E23, unsigned_lit_small by lia; f_equal; lia
| rewrite R20, ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E23, unsigned_lit_small by lia; f_equal; lia
| rewrite R26, ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E26, unsigned_lit_small by lia; f_equal; lia
| rewrite R19, ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E26, unsigned_lit_small by lia; f_equal; lia
| rewrite R21; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; first [rewrite E21 | rewrite G21]; rewrite unsigned_lit_small by lia; f_equal; lia
| exact (val_mem_lkept W sp1 _ _ (sp1 + 192) 8 _ L5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V208)
| exact (val_mem_lkept W sp1 _ _ (sp1 + 152) 8 _ L5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V56) ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & pc3 & -> & HJ3 & WK6 & L6 & HK3 & H63 & Hex).
split; [reflexivity|]. exists regs3, mem3, md3, pc3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact WK6|]. split; [exact (lkept_trans _ _ _ _ _ L5 L6)|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK2 r Hr)|]. split; [exact H63 |].
destruct Hex as [[Hpc3 H22] | HF]; [left; split; [exact Hpc3 | rewrite H22; exact HK22] | right; exact HF].
Qed.
Lemma fl_s2i : forall m, s2i_stmt m.
Proof. induction m as [|m IH]; [unfold s2i_stmt; intros; exfalso; lia | exact (fl_s2i_step m IH)]. Qed.
End e.
End d.
End b.
