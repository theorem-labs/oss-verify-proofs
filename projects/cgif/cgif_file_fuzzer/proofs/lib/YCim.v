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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj2 YC8g YC8a YChd YCjr YCj1 YCj0 YCjc YCje YCjf.
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
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA AS_memcmp_2).
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
Section e.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Let BDp := BD W memc fimg bimg.
Let CALL := bcmp_callW B LAWS ABCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
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
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (HFB : FBAND = 8192) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Definition F1_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 25; 27]%bv.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition f1_regs := sr_set (sr_set sr_atoms 19%bv (SLit 1)) 20%bv (SLit 1).
Definition f1_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 136 144 136 136 [YP09.mkChunk 136 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 152 160 152 160 [];
YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 216 224 216 216 [YP09.mkChunk 216 (CVal 8 (SOff 34 0))] ].
Definition f1_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (34%nat, mkAF SB SB 0); (27%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0); (33%nat, mkAF 1 65535 0);
(18%nat, mkAF 0 4294967295 0); (32%nat, HPTR 0); (25%nat, HPTR 0) ] [] [].
Definition ss_f1 : sstate := mkSS 0x20a4 f1_regs f1_mem None f1_facts.
Definition f1_postX (i : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 27 = Z_to_bv 64 Wd /\
((pc' = (BASE + 0x2318) /\ exists top c0, 0 <= top < Hd /\ 0 <= c0 < Wd /\ BDp (top * Wd + c0) /\
getr regs' 26 = Z_to_bv 64 top /\ getr regs' 25 = Z_to_bv 64 bimg /\
(forall p, i * Wd <= p < top * Wd -> ~ BDp p)) \/
(pc' = (BASE + 0x25bc) /\ getr regs' 21 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 0 /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 152) 8 0 /\
(forall p, i * Wd <= p < Wd * Hd -> ~ BDp p))).
Ltac wscr_windows E9 :=
cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_havoc_old in Hw by lia; rewrite ?ew_ewset_other in Hw by lia;
rewrite ?E9, ?unsigned_lit_small in Hw by lia; unfold wscr; lia |]);
destruct Hr.
Ltac awrW E9 FFS :=
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
Ltac run_wkeptF HFr HG HARx WK WKn E9 :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG ltac:(wscr_windows E9) ltac:(lia) ltac:(lia)
ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn end.
Definition f1_stmtX (m : nat) : Prop :=
forall (i : Z) (regsE : bvmap 5 word) memE mdE,
Hd - i <= Z.of_nat m -> 0 <= i < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 18 = Z_to_bv 64 (i * Wd) -> getr regsE 26 = Z_to_bv 64 i -> getr regsE 19 = Z_to_bv 64 1 -> getr regsE 20 = Z_to_bv 64 1 ->
getr regsE 25 = Z_to_bv 64 bimg -> getr regsE 27 = Z_to_bv 64 Wd ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x20a4)) memE (seg_rom SEGS)) mdE) (f1_postX i).
Lemma fl_f1_stepX : forall m, f1_stmtX m -> f1_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold f1_stmtX.
intros i regsE memE mdE Hm Hi HJE WK HKE E18r E26r E19r E20r E25r E27r.
wctx_names. wprelude HJE. pose proof HJE as HJE0.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi RW RH; nia).
assert (HSpresE : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 136 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V136) as V136E.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168E.
remember (Eimg (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 Hd; Z_to_bv 64 SB])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 Hd; Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite E18r in E18. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Hd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (HS : st_ok_pi SEGS VAL E ss_f1 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x20a4)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f1, f1_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x20a4) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E19r; cbn [sv_denot]; reflexivity]
| intros X; discriminate X | rewrite E20r; cbn [sv_denot]; reflexivity].
- reflexivity.
- unfold f1_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpresE; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 136 8 _ Hd); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V136E]|]. apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168E]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|]. apply Forall_nil.
- unfold f1_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f1_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E34, E27, E26, E33, E18, E32, E25, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end;
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 34 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { unfold f1_mem. awrW E9 FFS. }
run_wkeptF HFr HG HAR WK WK1 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: {
exfalso. rewrite branch_ltu_U in Hc. rewrite (U_add_atoms2 _ 18 32 (i * Wd) fimg E18 E32), (U_atom _ 32 fimg E32) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
pose proof (proj1 HJE) as HAR2.
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR2 WK1 WK2 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: { exfalso. rewrite branch_ltu_U in Hc. rewrite (U_add_atoms2 _ 18 25 (i * Wd) bimg E18 E25), (U_atom _ 25 bimg E25) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
pose proof (proj1 HJE) as HAR3.
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR3 WK2 WK3 E9. clear HF HFr HG.
prreg HS (12%bv : bv 5) Qa2.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (i * Wd + fimg)) (denot_add_atoms Ev 18 32 (i * Wd) fimg ltac:(evE; exact E18) ltac:(evE; exact E32) ltac:(lia) ltac:(lia) ltac:(lia)) Qa0;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (i * Wd + bimg)) (denot_add_atoms Ev 18 25 (i * Wd) bimg ltac:(evE; exact E18) ltac:(evE; exact E25) ltac:(lia) ltac:(lia) ltac:(lia)) Qa1 | st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (i * Wd + fimg)) (denot_add_atoms Ev 18 32 (i * Wd) fimg ltac:(evE; exact E18) ltac:(evE; exact E32) ltac:(lia) ltac:(lia) ltac:(lia)) Qa0;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (i * Wd + bimg)) (denot_add_atoms Ev 18 25 (i * Wd) bimg ltac:(evE; exact E18) ltac:(evE; exact E25) ltac:(lia) ltac:(lia) ltac:(lia)) Qa1  end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX (i * Wd) Wd (Z_to_bv 64 (BASE + 0x20e0)) HJE WK3) end.
- lia. - lia. - lia.
- unfold spZ. rewrite Qsp; evE. rewrite (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp; evE. rewrite (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp; evE. rewrite (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- rewrite Qa0; f_equal; lia. - rewrite Qa1; f_equal; lia. - rewrite Qa2; evE. exact E27.
- exact Qra. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hz & WK4 & Kc & Lc).
clear Qa0 Qa1 Qa2 Qra Qsp Qgp Qtp.
assert (HSpres2 : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) mem2 a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 34 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2 | st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 34 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2  end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil | specialize (HS2 HQ); clear HQ ] end.
1-4: eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia].
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 34%nat.
pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR4 WK4 WK5 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (Hwit : exists c0, 0 <= c0 < Wd /\ BDp (i * Wd + c0)).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
destruct (Classical_Prop.classic (exists c0, 0 <= c0 < Wd /\ BDp (i * Wd + c0))) as [Y | Y]; [exact Y | exfalso; apply Hc];
lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
evE; unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros j Hj D; apply Y; exists j; split; [exact Hj | exact D] end. }
reshok_bx HS 34%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x2318.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK5 WK6 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F1_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (26%bv : bv 5) R26f.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (BASE + 0x2318) end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F1_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|].
left. split; [reflexivity|]. destruct Hwit as (c0 & Hc0 & HBD). exists i, c0.
split; [exact Hi|]. split; [exact Hc0|]. split; [exact HBD|].
split; [rewrite R26f; evE; exact E26|]. split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|].
intros p Hp; exfalso; clear - Hp; lia.
-
assert (XNI : forall j, 0 <= j < Wd -> ~ BDp (i * Wd + j)).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
enough (Hvz : ew Ex n = getr regs2 10) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hc, U_SOff, Hvz, Z.add_0_r; symmetry; apply zcanon_id;
pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia);
evE; unfold CLOB; cbn [map nth]; reflexivity end. }
assert (XROW : forall p, i * Wd <= p < (i + 1) * Wd -> ~ BDp p).
{ intros p Hp. replace p with (i * Wd + (p - i * Wd)) by (clear; lia). apply XNI. clear - Hp. lia. }
reshok_bx HS 34%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK5 WK6 E9. clear HF HFr HG.
clear Hc. psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HLTU end;
rewrite branch_ltu_U in HLTU; rewrite (U_atom_off _ 26 i 1) in HLTU by (first [evE; exact E26 | lia]); rewrite (U_atom _ 33 Hd) in HLTU by (first [evE; exact E33 | lia]);
[apply Z.ltb_lt in HLTU | apply Z.ltb_ge in HLTU]; reshok_bx HS 34%nat; pose proof (proj1 HJ2) as HAR6.
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x20a4.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR6 WK6 WK7 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F1_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (26%bv : bv 5) R26. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (i * Wd + Wd)) (denot_add_atoms Ev 18 27 (i * Wd) Wd ltac:(evE; exact E18) ltac:(evE; exact E27) ltac:(lia) ltac:(lia) ltac:(lia)) R18 | st_ok _ ?Ev _ _ =>
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (i * Wd + Wd)) (denot_add_atoms Ev 18 27 (i * Wd) Wd ltac:(evE; exact E18) ltac:(evE; exact E27) ltac:(lia) ltac:(lia) ltac:(lia)) R18  end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (i + 1)); [ lia | lia | exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F1_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite R18; f_equal; lia
| rewrite R26; evE; rewrite E26, unsigned_lit_small by lia; reflexivity
| exact R19 | exact R20
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r ]. }
cbv beta. intros W9 c9 _ (-> & regs9 & mem9 & md9 & pc9 & -> & HJ9 & WK9 & HK9 & H279 & Hex9).
split; [reflexivity|]. exists regs9, mem9, md9, pc9. split; [reflexivity|]. split; [exact HJ9|]. split; [exact WK9|].
split; [exact HK9|]. split; [exact H279|].
destruct Hex9 as [(-> & top & c0 & Y1 & Y2 & Y3 & Y4 & Y5 & XN9) | (-> & Y1 & Y2 & Y3 & Y4 & XN9)].
* left. split; [reflexivity|]. exists top, c0. split; [clear - Y1 Hi; lia|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|]. split; [exact Y5|].
intros p Hp. destruct (Z_lt_le_dec p ((i + 1) * Wd)) as [Hlo | Hhi]; [apply XROW; clear - Hp Hlo; lia | apply XN9; clear - Hp Hhi; lia].
* right. split; [reflexivity|]. split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
intros p Hp. destruct (Z_lt_le_dec p ((i + 1) * Wd)) as [Hlo | Hhi]; [apply XROW; clear - Hp Hlo; lia | apply XN9; clear - Hp Hhi; lia].
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x25bc.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR6 WK6 WK7 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F1_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SLit 0) 0 HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152 end; clear HR1 | st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SLit 0) 0 HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152 end; clear HR1  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V152.
prreg HS (21%bv : bv 5) R21. prreg HS (23%bv : bv 5) R23. prreg HS (22%bv : bv 5) R22.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (BASE + 0x25bc) end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK7|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F1_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|].
right. split; [reflexivity|].
split; [exact R21|]. split; [exact R23|]. split; [exact R22|]. split; [exact V152|].
intros p Hp; apply XROW; clear - Hp HLTU RW Hi; nia.
Qed.
Lemma fl_f1X : forall m, f1_stmtX m.
Proof. induction m as [|m IH]; [unfold f1_stmtX; intros; exfalso; lia | exact (fl_f1_stepX m IH)]. Qed.
End e.
End d.
End c.
End b.
