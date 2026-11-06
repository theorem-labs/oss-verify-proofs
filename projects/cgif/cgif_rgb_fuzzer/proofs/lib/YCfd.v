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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdv YCe5 YCe9 YCfx YCex YCev YCf8 YCfp YCfa YCfb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma mod32_of_mod64 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.rem_mul_r by lia. rewrite Z.add_mod by lia. rewrite Z.mod_mod by lia. rewrite Z.mul_comm, Z.mod_mul by lia. rewrite Z.add_0_r. apply Z.mod_mod. lia. Qed.


Lemma U_zext32_sh : forall E a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = U E a mod 2 ^ 32.
Proof.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (zcanon 32) with 32. change (Z.land 32 63) with 32. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon, M64. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma U_subw_mod32 : forall E a b, U E (SAluw ALU_SUB a b) mod 2 ^ 32 = (U E a - U E b) mod 2 ^ 32.
Proof.
intros E a b. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
unfold bv_wrap, bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
set (x := U E a). set (y := U E b).
rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
rewrite <- Zminus_mod_idemp_l. rewrite (Z.mod_mod_divide _ (2 ^ 32) (2 ^ 32)) by (exists 1; reflexivity).
rewrite Zminus_mod_idemp_l.
replace (x mod 2 ^ 32 - y mod 2 ^ 32 + 2 ^ 31 - 2 ^ 31) with (x mod 2 ^ 32 - y mod 2 ^ 32) by ring.
symmetry. apply Zminus_mod.
Qed.
Lemma U_and_ffff_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 16 ->
U E (SAlu ALU_AND (SOff n c) (SLit 65535)) = x + c.
Proof.
intros E n x c Hn Rx Rc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n x c Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_dec_zext16 : forall E n x, ew E n = Z_to_bv 64 x -> 1 <= x < 2 ^ 16 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = x - 1.
Proof.
intros E n x Hn Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), !U_SLit by lia. rewrite (zcanon_id 48) by (rewrite M64_val; lia). change (Z.land 48 63) with 48.
change (zcanon (-281474976710656)) with (2 ^ 64 - 2 ^ 48).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 48)) by (rewrite M64_val; change (2 ^ 48) with 281474976710656 in *; lia).
replace (zcanon (x * 2 ^ 48 + (2 ^ 64 - 2 ^ 48))) with ((x - 1) * 2 ^ 48).
2: { unfold zcanon. rewrite M64_val. replace (x * 2 ^ 48 + (2 ^ 64 - 2 ^ 48)) with ((x - 1) * 2 ^ 48 + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. change (2 ^ 48) with 281474976710656 in *. lia. }
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_icpt.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section f.
Variables (W : world trbsegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Let CALL := bcmp_callW B LAWS ABCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
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
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (HFB : FBAND = 8192) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Definition F2_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 21; 25; 26; 27]%bv.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Ltac wscr_windows E9 :=
cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_havoc_old in Hw by lia; rewrite ?ew_ewset_other in Hw by lia;
rewrite ?E9, ?unsigned_lit_small in Hw by lia; unfold wscr; lia |]);
destruct Hr.
Ltac awrW E9 FFS :=
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
Ltac run_wkeptF HFr HG HARx WK WKn E9 :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG ltac:(wscr_windows E9) ltac:(lia) ltac:(lia)
ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn end.
Definition f2_post (top : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 0x88064) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 27 = Z_to_bv 64 Wd /\ getr regs' 25 = Z_to_bv 64 bimg /\ getr regs' 26 = Z_to_bv 64 top /\ getr regs' 18 = Z_to_bv 64 top /\
getr regs' 29 = Z_to_bv 64 SB /\
exists bot, top <= bot < Hd /\ getr regs' 19 = Z_to_bv 64 bot.
Definition f2_regs := sr_set (sr_set (sr_set sr_atoms 20%bv (SLit 65535)) 22%bv (SLit 1)) 24%bv (SLit 1).
Definition f2_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 168 176 168 168 [YQ0b.mkChunk 168 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 216 224 216 216 [YQ0b.mkChunk 216 (CVal 8 (SOff 34 0))] ].
Definition f2_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (34%nat, mkAF SB SB 0); (27%nat, mkAF 1 65535 0); (19%nat, mkAF 1 65534 0); (21%nat, mkAF 0 65534 0);
(35%nat, mkAF 0 4294967295 0); (32%nat, HPTR 0); (25%nat, HPTR 0) ] []
[ (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 32)) (SLit 32), SOff 35 0) ].
Definition ss_f2 : sstate := mkSS 0x88004 f2_regs f2_mem None f2_facts.
Definition f2_stmt (m : nat) : Prop :=
forall (top r s7v : Z) (regsE : bvmap 5 word) memE mdE,
r - top <= Z.of_nat m -> 0 <= top < r -> r < Hd ->
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r0 : bv 5, In r0 WKEPT5 -> getr regsE r0 = getr regs r0) ->
getr regsE 19 = Z_to_bv 64 r -> getr regsE 23 = Z_to_bv 64 s7v -> 0 <= s7v < 2 ^ 64 -> s7v mod 2 ^ 32 = r * Wd ->
getr regsE 20 = Z_to_bv 64 65535 -> getr regsE 22 = Z_to_bv 64 1 -> getr regsE 24 = Z_to_bv 64 1 ->
getr regsE 21 = Z_to_bv 64 top -> getr regsE 25 = Z_to_bv 64 bimg -> getr regsE 27 = Z_to_bv 64 Wd ->
getr regsE 26 = Z_to_bv 64 top -> getr regsE 18 = Z_to_bv 64 top ->
SRr trbsegs W (mkCfg (mkst regsE (Z_to_bv 64 0x88004) memE (seg_rom trbsegs)) mdE) (f2_post top).
Lemma fl_f2l_step : forall m, f2_stmt m -> f2_stmt (Datatypes.S m).
Proof.
intros m IH. unfold f2_stmt.
intros top r s7v regsE memE mdE Hm Htr HrH HJE WK HKE E19r E23r R7 M7 E20r E22r E24r E21r E25r E27r E26r E18r.
wctx_names. wprelude HJE. pose proof HJE as HJE0.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= r * Wd /\ r * Wd + Wd <= Nb) by (rewrite HN; clear - Htr HrH RW RH; nia).
assert (HSpresE : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168E.
remember (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 Hd; Z_to_bv 64 SB; Z_to_bv 64 (r * Wd)]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 Hd; Z_to_bv 64 SB; Z_to_bv 64 (r * Wd)]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr regsE r0) by (intros n r0 Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite E19r in E19. pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regsE _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (r * Wd)) by (subst E; exact (ew_Ereg_extra regsE _ 3)).
assert (HS : st_ok trbsegs E ss_f2 (restrict (w_H W) (mkst regsE (Z_to_bv 64 0x88004) memE (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f2, f2_regs.
apply (rn_st_ok_any E 0x88004 _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite E20r; cbn [sv_denot]; reflexivity]
| intros X; discriminate X | rewrite E22r; cbn [sv_denot]; reflexivity]
| intros X; discriminate X | rewrite E24r; cbn [sv_denot]; reflexivity].
- reflexivity.
- unfold f2_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
+ apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168E]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|]. apply Forall_nil.
- unfold f2_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f2_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E34, E27, E19, E21, E35, E32, E25, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end;
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end].
+ cbn [f2_facts f_alias alias_ok]. split; [|exact I].
rewrite (denot_lit_U E (SAlu ALU_SRL _ _)), U_zext32_sh, (U_atom E 23 s7v E23 R7), M7. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 34 0) E (mrestrict (w_H W) memE).
aj_run_tok trbtbl_lib_ok HS HJE SHOK FLBspan.
1: { unfold f2_mem. awrW E9 FFS. }
run_wkeptF HFr HG HAR WK WK1 E9. clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
1: {
exfalso. rewrite branch_ltu_U in Hc. rewrite (U_add_atoms2 _ 32 35 fimg (r * Wd) E32 E35), (U_atom _ 32 fimg E32) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
pose proof (proj1 HJE) as HAR2.
aj_run_tok trbtbl_lib_ok HS HJE SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR2 WK1 WK2 E9. clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
1: { exfalso. rewrite branch_ltu_U in Hc. rewrite (U_add_atoms2 _ 25 35 bimg (r * Wd) E25 E35), (U_atom _ 25 bimg E25) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
pose proof (proj1 HJE) as HAR3.
aj_run_to_tok trbtbl_lib_ok HS HJE SHOK FLBspan A_bcmp_icpt.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR3 WK2 WK3 E9. clear HF HFr HG.
rreg HS (12%bv : bv 5) Qa2.
rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + r * Wd)) (denot_add_atoms Ev 32 35 fimg (r * Wd) ltac:(evE; exact E32) ltac:(evE; exact E35) ltac:(lia) ltac:(lia) ltac:(lia)) Qa0;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + r * Wd)) (denot_add_atoms Ev 25 35 bimg (r * Wd) ltac:(evE; exact E25) ltac:(evE; exact E35) ltac:(lia) ltac:(lia) ltac:(lia)) Qa1 end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX (r * Wd) Wd (Z_to_bv 64 0x88040) HJE WK3) end.
- lia. - lia. - lia.
- unfold spZ. rewrite Qsp; evE. rewrite (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp; evE. rewrite (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp; evE. rewrite (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- rewrite Qa0; f_equal; lia. - rewrite Qa1; f_equal; lia. - rewrite Qa2; evE. exact E27.
- exact Qra. - apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hz & WK4 & Kc & Lc).
clear Qa0 Qa1 Qa2 Qra Qsp Qgp Qtp.
assert (HSpres2 : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) mem2 a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K 0 (SOff 34 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2 end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil | specialize (HS2 HQ); clear HQ ] end.
1-2: eapply (region_kept_stack_aj trbsegs _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia].
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 34%nat.
pose proof (proj1 HJ2) as HAR4.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR4 WK4 WK5 E9. clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
-
clear Hc. reshok_bx HS 34%nat. pose proof (proj1 HJ2) as HAR5.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan 0x88064.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK5 WK6 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (19%bv : bv 5) R19f. rreg HS (29%bv : bv 5) R29f.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|].
split; [intros r0 Hr0; transitivity (getr regsE r0); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr0 |- *; tauto | apply HKE; exact Hr0]|].
split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|].
split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18r|].
split; [rewrite R29f; evE; exact E34|].
exists r. split; [lia|]. rewrite R19f; evE; exact E19.
-
reshok_bx HS 34%nat. pose proof (proj1 HJ2) as HAR5.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK5 WK6 E9. clear HF HFr HG.
clear Hc. srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HLTU end;
rewrite branch_ltu_U in HLTU; rewrite (U_atom _ 21 top) in HLTU by (first [evE; exact E21 | lia]); rewrite (U_and_ffff_off _ 19 r (-1)) in HLTU by (first [evE; exact E19 | lia]);
[apply Z.ltb_lt in HLTU | apply Z.ltb_ge in HLTU]; reshok_bx HS 34%nat; pose proof (proj1 HJ2) as HAR6.
+
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan 0x88004.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR6 WK6 WK7 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (19%bv : bv 5) R19. rreg HS (20%bv : bv 5) R20. rreg HS (22%bv : bv 5) R22. rreg HS (24%bv : bv 5) R24.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (G23 : ew Ev 23 = Z_to_bv 64 s7v) by (evE; exact E23); assert (G27 : ew Ev 27 = Z_to_bv 64 Wd) by (evE; exact E27);
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (U Ev (SAluw ALU_SUB (SOff 23 0) (SOff 27 0)))) (denot_lit_U Ev (SAluw ALU_SUB (SOff 23 0) (SOff 27 0))) R23;
assert (Mv' : U Ev (SAluw ALU_SUB (SOff 23 0) (SOff 27 0)) mod 2 ^ 32 = (r - 1) * Wd)
by (rewrite U_subw_mod32, (U_atom Ev 23 s7v G23), (U_atom Ev 27 Wd G27) by lia;
rewrite <- Zminus_mod_idemp_l, M7; replace (r * Wd - Wd) with ((r - 1) * Wd) by lia; apply Z.mod_small; clear - Htr HrH RW RH; nia);
pose proof (U_range Ev (SAluw ALU_SUB (SOff 23 0) (SOff 27 0))) as Rv'; rewrite M64_val in Rv' end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (IH top (r - 1)); [ lia | lia | lia | exact HJ2 | exact WK7
| intros r0 Hr0; transitivity (getr regsE r0); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr0 |- *; tauto | apply HKE; exact Hr0]
| rewrite R19; evE; rewrite E19, unsigned_lit_small by lia; f_equal; lia
| exact R23 | exact Rv' | exact Mv'
| exact R20 | exact R22 | exact R24
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r
| rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r | rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18r ].
+
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK FLBspan 0x88064.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR6 WK6 WK7 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (19%bv : bv 5) R19f. rreg HS (29%bv : bv 5) R29f.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK7|].
split; [intros r0 Hr0; transitivity (getr regsE r0); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr0 |- *; tauto | apply HKE; exact Hr0]|].
split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|].
split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18r|].
split; [rewrite R29f; evE; exact E34|].
exists top. split; [lia|]. rewrite R19f; evE; exact E26.
Qed.
Lemma fl_f2l : forall m, f2_stmt m.
Proof. induction m as [|m IH]; [unfold f2_stmt; intros; exfalso; lia | exact (fl_f2l_step m IH)]. Qed.
Definition f2s_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 136 144 136 136 [YQ0b.mkChunk 136 (CVal 8 (SOff 33 0))];
YQ0b.mkRegion (Some 9%nat) 168 176 168 168 [YQ0b.mkChunk 168 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 216 224 216 216 [YQ0b.mkChunk 216 (CVal 8 (SOff 34 0))] ].
Definition f2s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (34%nat, mkAF SB SB 0); (27%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0); (33%nat, mkAF 1 65535 0);
(32%nat, HPTR 0); (25%nat, HPTR 0) ] [] [].
Definition ss_f2s : sstate := mkSS 0x87fac sr_atoms f2s_mem None f2s_facts.
Lemma fl_f2 : forall (top : Z) (regsF : bvmap 5 word) memF mdF,
0 <= top < Hd ->
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memF mdF k -> wkeptF B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 26 = Z_to_bv 64 top -> getr regsF 25 = Z_to_bv 64 bimg -> getr regsF 27 = Z_to_bv 64 Wd ->
SRr trbsegs W (mkCfg (mkst regsF (Z_to_bv 64 0x87fac) memF (seg_rom trbsegs)) mdF) (f2_post top).
Proof.
intros top regsF memF mdF Htp1 HJF WK HKF E26r E25r E27r.
wctx_names. wprelude HJF. pose proof HJF as HJF0.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HSpresF : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memF a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbF.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 136 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V136) as V136F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168F.
remember (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 Hd; Z_to_bv 64 SB]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 Hd; Z_to_bv 64 SB]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr regsF r0) by (intros n r0 Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regsF _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Hd) by (subst E; exact (ew_Ereg_extra regsF _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regsF _ 2)).
assert (HS : st_ok trbsegs E ss_f2s (restrict (w_H W) (mkst regsF (Z_to_bv 64 0x87fac) memF (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f2s.
apply (rn_st_ok_any E 0x87fac _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_Ereg.
- reflexivity.
- unfold f2s_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
+ apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 136 8 _ Hd); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V136F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbF]|]. apply Forall_nil.
- unfold f2s_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f2s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E34, E27, E26, E33, E32, E25, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end;
first [lia | match goal with |- ?g => idtac "FACT-LEFT2" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 34 0) E (mrestrict (w_H W) memF).
aj_run_tok trbtbl_lib_ok HS HJF SHOK FLBspan.
1: { unfold f2s_mem. awrW E9 FFS. }
run_wkeptF HFr HG HAR WK WK1 E9. clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
2: {
exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom _ 26 top) in Hc by (first [evE; exact E26 | lia]). rewrite (U_atom _ 33 Hd) in Hc by (first [evE; exact E33 | lia]).
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc. clear - Hc Htp1. lia. }
clear Hc. reshok_bx HS 34%nat. pose proof (proj1 HJF) as HAR2.
aj_run_tok trbtbl_lib_ok HS HJF SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR2 WK1 WK2 E9. clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HGEU end;
rewrite branch_geu_U in HGEU; rewrite (U_and_ffff_off _ 26 top 0) in HGEU by (first [evE; exact E26 | lia]); rewrite (U_and_ffff_off _ 33 Hd (-1)) in HGEU by (first [evE; exact E33 | lia]);
[apply (proj1 (negb_true_iff _)) in HGEU; apply Z.ltb_ge in HGEU | apply (proj1 (negb_false_iff _)) in HGEU; apply Z.ltb_lt in HGEU];
reshok_bx HS 34%nat; pose proof (proj1 HJF) as HAR3.
+
aj_run_to_tok trbtbl_lib_ok HS HJF SHOK FLBspan 0x88064.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR3 WK2 WK3 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsF _ (25%bv :: 26%bv :: 27%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (18%bv : bv 5) R18. rreg HS (19%bv : bv 5) R19. rreg HS (29%bv : bv 5) R29.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJF|]. split; [exact WK3|].
split; [intros r0 Hr0; transitivity (getr regsF r0); [apply HKr; cbv [WKEPT5 In] in Hr0 |- *; tauto | apply HKF; exact Hr0]|].
split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|].
split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [rewrite R18; evE; exact E26|].
split; [rewrite R29; evE; exact E34|].
exists (Hd - 1). split; [lia|]. rewrite R19; evE; rewrite E33, unsigned_lit_small by lia; f_equal; lia.
+
aj_run_to_tok trbtbl_lib_ok HS HJF SHOK FLBspan 0x88004.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR3 WK2 WK3 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsF _ (25%bv :: 26%bv :: 27%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (18%bv : bv 5) R18. rreg HS (19%bv : bv 5) R19. rreg HS (20%bv : bv 5) R20. rreg HS (22%bv : bv 5) R22. rreg HS (24%bv : bv 5) R24.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (G33 : ew Ev 33 = Z_to_bv 64 Hd) by (evE; exact E33); assert (G27 : ew Ev 27 = Z_to_bv 64 Wd) by (evE; exact E27); assert (G26 : ew Ev 26 = Z_to_bv 64 top) by (evE; exact E26);
assert (U23 : U Ev (SMd M_MUL (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) (SOff 27 0)) = (Hd - 1) * Wd)
by (apply U_mul_small1; [apply (U_dec_zext16 Ev 33 Hd G33); lia | apply (U_atom Ev 27 Wd G27); lia | lia | lia | clear - RW RH; nia]);
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 ((Hd - 1) * Wd)) (denot_of_U2 Ev _ _ U23) R23;
assert (U21 : U Ev (SAlu ALU_AND (SOff 26 0) (SLit 65535)) = top) by (rewrite (U_and_ffff_off Ev 26 top 0 G26) by lia; lia);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 top) (denot_of_U2 Ev _ _ U21) R21 end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (fl_f2l (Z.to_nat (Hd - 1 - top)) top (Hd - 1) ((Hd - 1) * Wd)); [ lia | lia | lia | exact HJF | exact WK3
| intros r0 Hr0; transitivity (getr regsF r0); [apply HKr; cbv [WKEPT5 In] in Hr0 |- *; tauto | apply HKF; exact Hr0]
| rewrite R19; evE; rewrite E33, unsigned_lit_small by lia; f_equal; lia
| exact R23 | clear - RW RH; nia | apply Z.mod_small; clear - RW RH; nia
| exact R20 | exact R22 | exact R24 | exact R21
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r
| rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r | rewrite R18; evE; exact E26 ].
Qed.
End f.
End e.
End d.
