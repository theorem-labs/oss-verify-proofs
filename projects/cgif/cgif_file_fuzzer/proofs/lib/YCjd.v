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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj2 YC8g YC8a YChd YCjr YCj1 YCj0 YCjc.
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
Ltac tin_ctx_names H :=
destruct H as (HJ & Hpt & Hpawr & Hbi & HNb & HsepI & Hg & Hcf & Hbf & Hcb & HsepG & HsepC & HsepB
& Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx & Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp
& Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vtidx & Rtidx & Vsb & Vbfp & Vg & Vcfp & Hnpt32 & H18 & H19 & H21).
Ltac tin_prelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Ltac tctx_regs_of HK := let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; apply HK; cbv [TCTX_REGS In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr.
Definition TOUT_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition TOUT_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 21]%bv.
Lemma tout_clob_cases3 : forall r : bv 5, reg_in r TOUT_CLOB = false -> r = 0%bv \/ r = 19%bv \/ In r TOUT_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma tout_tin_clob : forall r : bv 5, reg_in r TOUT_CLOB = false -> reg_in r TIN_CLOB = false.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [vm_compute in Hr; discriminate | vm_compute; reflexivity] |]). destruct Hin.
Qed.
Definition tout_regs := sr_set sr_atoms 19%bv (SLit 1).
Definition tout_loc : YP09.region :=
YP09.mkRegion (Some 9%nat) 136 224 136 136
[YP09.mkChunk 136 (CVal 8 (SOff 32 0)); YP09.mkChunk 144 (CVal 8 (SOff 33 0)); YP09.mkChunk 160 (CVal 8 (SOff 34 0));
YP09.mkChunk 168 (CVal 8 (SOff 35 0)); YP09.mkChunk 176 (CVal 8 (SOff 36 0)); YP09.mkChunk 184 (CVal 8 (SOff 37 0));
YP09.mkChunk 192 (CVal 8 (SOff 17 0)); YP09.mkChunk 200 (CVal 8 (SOff 15 0)); YP09.mkChunk 208 (CVal 8 (SOff 16 0));
YP09.mkChunk 216 (CVal 8 (SOff 29 0))].
Definition tout_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (29%nat, mkAF SB SB 0); (32%nat, mkAF 281474976710656 18446744073709551615 0);
(34%nat, mkAF 1 65535 0); (35%nat, mkAF 0 4294967295 0); (22%nat, mkAF 0 4294967295 0) ] [] [].
Definition ss_tout : sstate := mkSS 0x2868 tout_regs [tout_loc] None tout_facts.
Definition totl_loc : YP09.region :=
YP09.mkRegion (Some 9%nat) 144 184 168 176
[YP09.mkChunk 144 (CVal 8 (SOff 32 0)); YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 34 0));
YP09.mkChunk 176 (CVal 8 (SOff 35 0))].
Definition totl_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 1 65535 0); (33%nat, mkAF 1 65535 0);
(34%nat, mkAF 0 4294967295 0); (35%nat, mkAF 0 65535 0); (22%nat, mkAF 0 4294967295 0); (23%nat, mkAF 0 65534 0) ] [] [].
Definition ss_totl : sstate := mkSS 0x2944 sr_atoms [totl_loc] None totl_facts.
Definition tout_ctx (W : world SEGS) (memc : word -> option byte) (sp1 w h top left Wd Nb : Z) : Prop :=
1 <= w <= 65535 /\ 1 <= h <= 65535 /\ 0 <= top /\ 0 <= left /\ left + w <= Wd /\ 0 <= Wd <= 65535 /\ (top + h) * Wd <= Nb /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 136) 8 (w * 2 ^ 48) /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 144) 8 h /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 160) 8 w /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd.
Definition tout_post (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model)
(lyc : alayout) (Sc : astate) (k : Z) (fpos pt npt g cfp bfp : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2968)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
(forall r : bv 5, reg_in r TOUT_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 29 = Z_to_bv 64 SB /\ getr regs' 15 = Z_to_bv 64 g /\ getr regs' 16 = Z_to_bv 64 cfp /\ getr regs' 17 = Z_to_bv 64 bfp /\
acall_kept SEGS B lyc Sc W memc W mem' (sp1 - TCMP_STK) (sp1 + 176) (fun a => pt <= a < pt + npt) /\
(forall a, sp1 <= a < sp1 + 168 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a).
Definition tout_stmt (m : nat) : Prop :=
forall (y : Z) W (regs : bvmap 5 word) memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt w h top left Wd bimg Nb g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z),
h - y <= Z.of_nat m -> 0 <= y < h ->
tin_ctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
tout_ctx W memc sp1 w h top left Wd Nb ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 168) 8 (y * w) ->
getr regs 29 = Z_to_bv 64 SB -> getr regs 15 = Z_to_bv 64 g -> getr regs 16 = Z_to_bv 64 cfp -> getr regs 17 = Z_to_bv 64 bfp ->
getr regs 23 = Z_to_bv 64 y -> getr regs 22 = Z_to_bv 64 ((top + y) * Wd + left) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x2868)) memc (seg_rom SEGS)) mdc)
(tout_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt (w * h) g cfp bfp).
Lemma val_mem_frame8 : forall E rs (m m' : word -> option byte) a v lo hi,
frame_of E rs m m' -> (forall x, in_wrange E rs x -> lo <= x < hi) -> (a + 8 <= lo \/ hi <= a) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem SEGS m a 8 v -> val_mem SEGS m' a 8 v.
Proof.
intros E rs m m' a v lo hi HF Hw Hout Ha Ha8 Hv. apply (val_mem_frame E rs m m' a 8 v HF); [| exact Ha | cbn [Z.of_nat]; lia | exact Hv].
intros k Hk Hin. pose proof (Hw _ Hin). cbn [Z.of_nat] in Hk. lia.
Qed.
Lemma U_addiw1_small : forall E a, 0 <= U E a < 2 ^ 31 - 1 -> U E (SAluw ALU_ADD a (SLit 1)) = U E a + 1.
Proof.
intros E a Ha. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 1) with 1.
rewrite (Z.mod_small (U E a)) by lia. change (1 mod 2 ^ 32) with 1.
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (U E a + 1 + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma fl_tout_step : forall m, tout_stmt m -> tout_stmt (S m).
Proof.
intros m IH. unfold tout_stmt.
intros y W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt w h top left Wd bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
Hm Hy HCTX HOUT V168 H29 H15 H16 H17 H23 H22.
pose proof HCTX as HCTX0. tin_ctx_names HCTX. pose proof HOUT as HOUT0.
destruct HOUT as (Rw & Rh & Htop0 & Hleft0 & Hlw & HWd & HthW & V136 & V144 & V160 & V176).
tin_prelude HJ. pose proof HJ as HJ0.
assert (HSpres2 : forall a, sp1 - TCMP_STK <= a < sp1 + 176 -> apresent (w_H W) memc a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt (w * h) HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hpt) as Hqh_img.
pose proof (req_size_pos' (w * h) ltac:(lia)) as [_ Hrnp].
pose proof (proj1 (proj2 HJ)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bfp FRAME_SIZE HAR Hbf) as (Hb16 & Hb4096 & Hbceil & Hbfh_ia & _ & _). pose proof (proj1 Hbfh_ia) as Hbfh.
pose proof (blk_off_imgP _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hbfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
assert (HywL : 0 <= y * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (HywH : y * w + w <= w * h) by (rewrite (Z.mul_comm w h); rewrite <- Z.mul_succ_l; apply Z.mul_le_mono_nonneg_r; lia).
assert (HriL : 0 <= (top + y) * Wd + left) by (assert (0 <= (top + y) * Wd) by (apply Z.mul_nonneg_nonneg; lia); lia).
assert (HriH : (top + y) * Wd + left + w <= Nb).
{ apply (Z.le_trans _ ((top + y + 1) * Wd)); [rewrite Z.mul_add_distr_r; lia|]. apply (Z.le_trans _ ((top + h) * Wd)); [apply Z.mul_le_mono_nonneg_r; lia | exact HthW]. }
assert (Hw48 : 281474976710656 <= w * 2 ^ 48 <= 18446744073709551615) by (change (2 ^ 48) with 281474976710656; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 (w * 2 ^ 48); Z_to_bv 64 h; Z_to_bv 64 w; Z_to_bv 64 (y * w); Z_to_bv 64 Wd; Z_to_bv 64 tidx])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (w * 2 ^ 48); Z_to_bv 64 h; Z_to_bv 64 w; Z_to_bv 64 (y * w); Z_to_bv 64 Wd; Z_to_bv 64 tidx]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9. pose proof (EE 29%nat 29%bv eq_refl) as E29. rewrite H29 in E29.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite H23 in E23. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite H22 in E22.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite H15 in E15. pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite H16 in E16.
pose proof (EE 17%nat 17%bv eq_refl) as E17. rewrite H17 in E17.
assert (E32 : ew E 32 = Z_to_bv 64 (w * 2 ^ 48)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (y * w)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 tidx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (HS : st_ok_pi SEGS VAL E ss_tout (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x2868)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tout, tout_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x2868) _ regs _ _ (mrestrict (w_H W) memc)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]. rewrite H19. cbn [sv_denot]. reflexivity.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tout_loc; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 136 8 _ (w * 2 ^ 48)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V136]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 144 8 _ h); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V144]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 160 8 _ w); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 168 8 _ (y * w)); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 184 8 _ tidx); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vtidx]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vbfp]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vg]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcfp]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact Vsb]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [tout_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E9, E29, E32, E34, E35, E22, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memc).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK FLBspan 0x287c.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (acall_kept_of_run B LAWS E _ lyc Sc W memc _ mdc (sp1 - TCMP_STK) (sp1 + 176) (fun a => pt <= a < pt + w * h) HAR HFr1 HG1
ltac:(unfold ss_tout, tout_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) HSpres2) as K1.
assert (W1 : forall x, in_wrange E (ss_mem ss_tout) x -> sp1 + 168 <= x < sp1 + 176).
{ unfold ss_tout, tout_loc; cbn [ss_mem]. intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
assert (X1 : forall a, sp1 <= a < sp1 + 168 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply (aview_kept_out E _ _ _ _ HFr1 a ltac:(lia)). intros Hin. pose proof (W1 a Hin). lia. }
pose proof (val_mem_frame8 E _ _ _ (sp1 + 136) (w * 2 ^ 48) _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V136) as V136a.
pose proof (val_mem_frame8 E _ _ _ (sp1 + 144) h _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V144) as V144a.
pose proof (val_mem_frame8 E _ _ _ (sp1 + 160) w _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V160) as V160a.
pose proof (val_mem_frame8 E _ _ _ (sp1 + 176) Wd _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V176) as V176a.
pose proof (val_mem_frame E _ _ _ (sp1 + 168) 8 (y * w) HFr1 ltac:(intros kk Hkk Hin; pose proof (W1 _ Hin) as Hq; unfold ss_tout, tout_loc in Hin; cbn [ss_mem] in Hin; destruct Hin as (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V168) as V168a.
cbn [ms_mem restrict mkst] in V136a, V144a, V160a, V176a, V168a.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ (22%bv :: 23%bv :: TOUT_KEPT) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr1. cbn [ms_regs restrict] in HKr1.
assert (HK1 : forall r : bv 5, In r TCTX_REGS -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbv [TCTX_REGS In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [apply HKr1; cbv; tauto | rewrite (st_ok_restrict_reg SEGS _ _ _ _ 19%bv HS); cbn [sv_denot]; rewrite H19; reflexivity] |]). destruct Hr. }
prreg HS (29%bv : bv 5) R29. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
prreg HS (26%bv : bv 5) R26. prreg HS (20%bv : bv 5) R20. prreg HS (24%bv : bv 5) R24.
pose proof (tin_ctx_kept B LAWS W regs _ memc mdc _ _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) bimg Nb g cfp bfp tidx
gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ HCTX0 HJ K1 ltac:(lia) HK1) as HCTX1.
pmkst HS.
eapply SRr_bind.
{ pose proof (fl_tin B LAWS TCMP (Z.to_nat w)) as TIN. unfold tin_stmt in TIN.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (TIN w W (ms_regs msX) (ms_mem msX) mdX sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) (y * w) bimg Nb ((top + y) * Wd + left) g cfp bfp tidx
gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx) end;
[ rewrite Z2Nat.id by lia; lia | lia | exact HCTX1 | lia | lia | lia | lia
| rewrite R29, ?ew_ewset_other by lia; exact E29
| rewrite R15, ?ew_ewset_other by lia; exact E15
| rewrite R16, ?ew_ewset_other by lia; exact E16
| rewrite R17, ?ew_ewset_other by lia; exact E17
| rewrite R26, ?ew_ewset_other by lia; exact E35
| rewrite R20, ?ew_ewset_other by lia; exact E34
| rewrite R24, ?ew_ewset_other by lia; exact E22 ]. }
cbv beta. intros W2 c2 _ (-> & regsI & memI & mdI & -> & HJI & HKI & H29I & H15I & H16I & H17I & KI).
clear R29 R15 R16 R17 R26 R20 R24.
pose proof HJI as HJI0.
assert (HSpresI : forall a, sp1 - TCMP_STK <= a < sp1 + 176 -> apresent (w_H W) memI a).
{ intros a Ha. pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K1 (acall_kept_band B _ _ _ _ _ _ _ (sp1 - TCMP_STK) (sp1 + 176) _ KI ltac:(lia) ltac:(lia) HSpresI)) as K2.
assert (X2 : forall a, sp1 <= a < sp1 + 168 -> aview SEGS (w_H W) memI a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X1 a Ha). pose proof KI as (KI1 & _). apply KI1; lia. }
assert (HKI' : forall r : bv 5, reg_in r TOUT_CLOB = false -> getr regsI r = getr regs r).
{ intros r Hr. rewrite (HKI r (tout_tin_clob r Hr)). destruct (tout_clob_cases3 r Hr) as [-> | [-> | Hr']].
- rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS), (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS0). reflexivity.
- rewrite (st_ok_restrict_reg SEGS _ _ _ _ 19%bv HS). cbn [sv_denot]. rewrite H19. reflexivity.
- apply HKr1. cbv [TOUT_KEPT In] in Hr' |- *. tauto. }
assert (I23 : getr regsI 23 = Z_to_bv 64 y) by (rewrite (HKI 23%bv eq_refl); rewrite (HKr1 23%bv ltac:(cbv; tauto)); exact H23).
assert (I22 : getr regsI 22 = Z_to_bv 64 ((top + y) * Wd + left)) by (rewrite (HKI 22%bv eq_refl); rewrite (HKr1 22%bv ltac:(cbv; tauto)); exact H22).
assert (I9 : getr regsI 9 = Z_to_bv 64 sp1) by (rewrite (HKI 9%bv eq_refl); rewrite (HKr1 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 136) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V136a) as V136b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 144) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V144a) as V144b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 160) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V160a) as V160b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 168) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V168a) as V168b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 176) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V176a) as V176b.
clear V136a V144a V160a V168a V176a.
remember (Eimg (Ereg regsI [Z_to_bv 64 h; Z_to_bv 64 w; Z_to_bv 64 (y * w); Z_to_bv 64 Wd])) as Et eqn:HEt. assert (HEIt : img_env VAL A_LIM Et) by (subst Et; apply Eimg_env).
assert (HAEt : env_agree 32 (Ereg regsI [Z_to_bv 64 h; Z_to_bv 64 w; Z_to_bv 64 (y * w); Z_to_bv 64 Wd]) Et) by (rewrite HEt; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEt : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regsI r) by (intros n r Hn; subst Et; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EEt 9%nat 9%bv eq_refl) as T9. rewrite I9 in T9. pose proof (EEt 23%nat 23%bv eq_refl) as T23. rewrite I23 in T23.
pose proof (EEt 22%nat 22%bv eq_refl) as T22. rewrite I22 in T22.
pose proof (EEt 29%nat 29%bv eq_refl) as T29. rewrite H29I in T29.
assert (T32 : ew Et 32 = Z_to_bv 64 h) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 0)).
assert (T33 : ew Et 33 = Z_to_bv 64 w) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 1)).
assert (T34 : ew Et 34 = Z_to_bv 64 (y * w)) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 2)).
assert (T35 : ew Et 35 = Z_to_bv 64 Wd) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 3)).
assert (HSt : st_ok_pi SEGS VAL Et ss_totl (restrict (w_H W) (mkst regsI (Z_to_bv 64 (BASE + 0x2944)) memI (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_totl. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any Et (BASE + 0x2944) _ regsI _ _ (mrestrict (w_H W) memI)).
- subst Et. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, totl_loc; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite T9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HSpresI; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 144 8 _ h); [cbn [sv_denot]; rewrite T32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V144b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 160 8 _ w); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 168 8 _ (y * w)); [cbn [sv_denot]; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite T35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176b]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [totl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite T9, T32, T33, T34, T35, T22, T23, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HEt. pose proof HSt as HSt0. clear HS HS0. rename HSt into HS. try clear SHOK.
shok_auto SHOK (SOff 29 0) Et (mrestrict (w_H W) memI).
pose proof (proj1 HJI) as HARI.
hei_havoc HS; paj_run_tok RUN HS HJI SHOK FLBspan.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite T9; apply unsigned_lit_small; lia
| intros a Ha; unfold totl_loc in Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; rewrite FFS; lia | apply awr_ok_nil]. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) (sp1 + 176) (fun a => pt <= a < pt + w * h) HARI HFr3 HG3
ltac:(unfold ss_totl, totl_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
rewrite T9, unsigned_lit_small in Hw by lia; right; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) HSpresI) as K3.
assert (Wt : forall x, in_wrange Et (ss_mem ss_totl) x -> sp1 + 168 <= x < sp1 + 176).
{ unfold ss_totl, totl_loc; cbn [ss_mem]. intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
rewrite T9, unsigned_lit_small in Hw by lia. lia. }
assert (X3 : forall a, sp1 <= a < sp1 + 168 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X2 a Ha). apply (aview_kept_out Et _ _ _ _ HFr3 a ltac:(lia)). intros Hin. pose proof (Wt a Hin). lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
assert (F33 : ew Ex 33 = Z_to_bv 64 w) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33);
assert (F34 : ew Ex 34 = Z_to_bv 64 (y * w)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T34);
assert (F35 : ew Ex 35 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T35);
assert (F22 : ew Ex 22 = Z_to_bv 64 ((top + y) * Wd + left)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T22);
assert (F23 : ew Ex 23 = Z_to_bv 64 y) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T23);
assert (F32 : ew Ex 32 = Z_to_bv 64 h) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T32);
pose proof (st_ok_pi_region_nth Ex ssx msx 0 ltac:(let rr := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in exact rr) HS ltac:(vm_compute; reflexivity)) as HR9; cbn [ms_mem restrict mkst] in HR9;
lazymatch type of HR9 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 168 8%N (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) (y * w + w) HR9
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(rewrite (denot_add_atoms Ex 33 34 w (y * w) F33 F34) by lia; f_equal; lia)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V168c end;
clear HR9 | st_ok _ ?Ex ?ssx ?msx =>
assert (F33 : ew Ex 33 = Z_to_bv 64 w) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33);
assert (F34 : ew Ex 34 = Z_to_bv 64 (y * w)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T34);
assert (F35 : ew Ex 35 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T35);
assert (F22 : ew Ex 22 = Z_to_bv 64 ((top + y) * Wd + left)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T22);
assert (F23 : ew Ex 23 = Z_to_bv 64 y) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T23);
assert (F32 : ew Ex 32 = Z_to_bv 64 h) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T32);
pose proof (st_ok_region_nth Ex ssx msx 0 ltac:(let rr := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in exact rr) HS ltac:(vm_compute; reflexivity)) as HR9; cbn [ms_mem restrict mkst] in HR9;
lazymatch type of HR9 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 168 8%N (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) (y * w + w) HR9
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(rewrite (denot_add_atoms Ex 33 34 w (y * w) F33 F34) by lia; f_equal; lia)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V168c end;
clear HR9  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V168c.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_ne_U in Hc.
first [ rewrite (U_atom_off _ 23 y 1 F23), (U_atom _ 32 h F32) in Hc by lia
| rewrite (U_addiw1_small _ (SOff 23 0)) in Hc by (rewrite (U_atom _ 23 y F23) by lia; lia); rewrite (U_atom _ 23 y F23), (U_atom _ 32 h F32) in Hc by lia ].
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x2868.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; rewrite FFS; lia | apply awr_ok_nil]. }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) (sp1 + 176) (fun a => pt <= a < pt + w * h) HARb HFrb HGb
ltac:(cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; right; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K3 as (_ & _ & _ & _ & _ & K6); exact K6)) as Kb.
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K2 (acall_kept_trans B _ _ _ _ _ _ _ _ _ K3 Kb)) as K4.
lazymatch type of HFrb with frame_of ?Ef ?rsf _ _ =>
assert (Wb : forall x, in_wrange Ef rsf x -> sp1 + 168 <= x < sp1 + 176) by
(cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; lia) end.
assert (X4 : forall a, sp1 <= a < sp1 + 168 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X3 a Ha). apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)). intros Hin. pose proof (Wb a Hin). lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (19%bv :: TOUT_KEPT) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr4. cbn [ms_regs restrict] in HKr4.
assert (HK4 : forall r : bv 5, reg_in r TOUT_CLOB = false -> getr (ms_regs ms1) r = getr regs r).
{ intros r Hr. transitivity (getr regsI r); [|exact (HKI' r Hr)].
destruct (tout_clob_cases3 r Hr) as [-> | [-> | Hr']]; [rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS), (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HSt0); reflexivity | apply HKr4; cbv; tauto | apply HKr4; cbv [TOUT_KEPT In] in Hr' |- *; tauto]. }
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 136) (w * 2 ^ 48) _ _ HFrb Wb ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 136) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V136b)) as V136c.
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 144) h _ _ HFrb Wb ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 144) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V144b)) as V144c.
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 160) w _ _ HFrb Wb ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 160) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V160b)) as V160c.
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 176) Wd _ _ HFrb Wb ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 176) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V176b)) as V176c.
cbn [ms_mem restrict mkst] in V136c, V144c, V160c, V176c.
assert (V168d : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (sp1 + 168) 8 (y * w + w)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (st_ok_pi_region_nth Ex ssx msx 0 ltac:(let rr := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in exact rr) HS ltac:(vm_compute; reflexivity)) as HR9; cbn [ms_mem restrict mkst] in HR9;
lazymatch type of HR9 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
exact (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 168 8%N (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) (y * w + w) HR9
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(rewrite (denot_add_atoms Ex 33 34 w (y * w)); [f_equal; lia | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T34 | lia | lia | lia])
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) end | st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_region_nth Ex ssx msx 0 ltac:(let rr := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in exact rr) HS ltac:(vm_compute; reflexivity)) as HR9; cbn [ms_mem restrict mkst] in HR9;
lazymatch type of HR9 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
exact (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 168 8%N (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) (y * w + w) HR9
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(rewrite (denot_add_atoms Ex 33 34 w (y * w)); [f_equal; lia | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T34 | lia | lia | lia])
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) end  end. }
prreg HS (29%bv : bv 5) R29. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (G35 : ew Ev 35 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T35);
assert (G22 : ew Ev 22 = Z_to_bv 64 ((top + y) * Wd + left)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T22);
assert (G23 : ew Ev 23 = Z_to_bv 64 y) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T23);
rreg_by HS (22%bv : bv 5) (Z_to_bv 64 ((top + y) * Wd + left + Wd)) (denot_add_atoms Ev 22 35 ((top + y) * Wd + left) Wd G22 G35 ltac:(lia) ltac:(lia) ltac:(lia)) R22;
first [ rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (y + 1)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_atom_off Ev 23 y 1 G23 ltac:(lia) ltac:(lia)))) R23
| rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (y + 1)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (eq_trans (U_addiw1_small Ev (SOff 23 0) ltac:(rewrite (U_atom Ev 23 y G23) by lia; lia)) (f_equal (fun z => z + 1) (U_atom Ev 23 y G23 ltac:(lia)))))) R23 ] | st_ok _ ?Ev _ _ =>
assert (G35 : ew Ev 35 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T35);
assert (G22 : ew Ev 22 = Z_to_bv 64 ((top + y) * Wd + left)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T22);
assert (G23 : ew Ev 23 = Z_to_bv 64 y) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T23);
rreg_by HS (22%bv : bv 5) (Z_to_bv 64 ((top + y) * Wd + left + Wd)) (denot_add_atoms Ev 22 35 ((top + y) * Wd + left) Wd G22 G35 ltac:(lia) ltac:(lia) ltac:(lia)) R22;
first [ rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (y + 1)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_atom_off Ev 23 y 1 G23 ltac:(lia) ltac:(lia)))) R23
| rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (y + 1)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (eq_trans (U_addiw1_small Ev (SOff 23 0) ltac:(rewrite (U_atom Ev 23 y G23) by lia; lia)) (f_equal (fun z => z + 1) (U_atom Ev 23 y G23 ltac:(lia)))))) R23 ]  end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
pose proof (tin_ctx_kept B LAWS W regs (ms_regs msX) memc mdc (ms_mem msX) mdX sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) bimg Nb g cfp bfp tidx
gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ HCTX0 HJI K4 ltac:(lia) ltac:(tctx_regs_of HK4)) as HCTX4 end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (y + 1) W _ _ _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt w h top left Wd bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx);
[ lia | lia | exact HCTX4
| split; [exact Rw|]; split; [exact Rh|]; split; [exact Htop0|]; split; [exact Hleft0|]; split; [exact Hlw|]; split; [exact HWd|]; split; [exact HthW|];
split; [exact V136c|]; split; [exact V144c|]; split; [exact V160c | exact V176c]
| replace ((y + 1) * w) with (y * w + w) by lia; exact V168d
| rewrite R29, ?ew_ewset_other by lia; exact T29
| rewrite R15, ?ew_ewset_other by lia; rewrite (EEt 15%nat 15%bv eq_refl); exact H15I
| rewrite R16, ?ew_ewset_other by lia; rewrite (EEt 16%nat 16%bv eq_refl); exact H16I
| rewrite R17, ?ew_ewset_other by lia; rewrite (EEt 17%nat 17%bv eq_refl); exact H17I
| exact R23
| rewrite R22; f_equal; lia ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & H293 & H153 & H163 & H173 & K5 & X5).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK4 r Hr)|].
split; [exact H293|]. split; [exact H153|]. split; [exact H163|]. split; [exact H173|].
split; [eapply (acall_kept_trans B); [exact K4 | exact K5]|].
intros a Ha. rewrite (X5 a Ha). exact (X4 a Ha).
-
reshok_bx HS 29%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x2968.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; rewrite FFS; lia | apply awr_ok_nil]. }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) (sp1 + 176) (fun a => pt <= a < pt + w * h) HARb HFrb HGb
ltac:(cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; right; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K3 as (_ & _ & _ & _ & _ & K6); exact K6)) as Kb.
lazymatch type of HFrb with frame_of ?Ef ?rsf _ _ =>
assert (Wb : forall x, in_wrange Ef rsf x -> sp1 + 168 <= x < sp1 + 176) by
(cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; lia) end.
assert (X4 : forall a, sp1 <= a < sp1 + 168 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X3 a Ha). apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)). intros Hin. pose proof (Wb a Hin). lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (19%bv :: TOUT_KEPT) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr4. cbn [ms_regs restrict] in HKr4.
prreg HS (29%bv : bv 5) R29. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJI|].
split.
{ intros r Hr. transitivity (getr regsI r); [|exact (HKI' r Hr)].
destruct (tout_clob_cases3 r Hr) as [-> | [-> | Hr']]; [cbn [ms_regs]; rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS), (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HSt0); reflexivity | apply HKr4; cbv; tauto | apply HKr4; cbv [TOUT_KEPT In] in Hr' |- *; tauto]. }
split; [rewrite R29, ?ew_ewset_other by lia; exact T29|].
split; [rewrite R15, ?ew_ewset_other by lia; rewrite (EEt 15%nat 15%bv eq_refl); exact H15I|].
split; [rewrite R16, ?ew_ewset_other by lia; rewrite (EEt 16%nat 16%bv eq_refl); exact H16I|].
split; [rewrite R17, ?ew_ewset_other by lia; rewrite (EEt 17%nat 17%bv eq_refl); exact H17I|].
split; [eapply (acall_kept_trans B); [exact K2 | eapply (acall_kept_trans B); [exact K3 | exact Kb]]|].
exact X4.
Qed.
Lemma fl_tout : forall m, tout_stmt m.
Proof.
induction m as [|m IH]; [|exact (fl_tout_step m IH)].
unfold tout_stmt. intros. exfalso. lia.
Qed.
End d.
End c.
End b.
