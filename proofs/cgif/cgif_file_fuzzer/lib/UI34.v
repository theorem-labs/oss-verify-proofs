(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o YI0s UI3p UI3n UI3o UI3k
UI1u UI1t YI62.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30 UI3e UI32 UI33.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2v UI3f UI35.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0h YI0v UI2z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfree_post_live_nz : forall (p n : Z) rest Bfin (blc bl2 : list (Z * Z)),
Permutation blc (nz ((p, n) :: rest) ++ Bfin) -> p <> 0 -> rm1 (p, n) blc bl2 -> Permutation bl2 (nz rest ++ Bfin).
Proof using. intros p n rest Bfin blc bl2 HP Hp Hrm. eapply tfree_post_step; [exact HP | right; split; [exact Hp | exact Hrm]]. Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis CBLV : cbl_specV API.
Hypothesis CBBV : cbb_specV API.
Lemma tlzw_epiBV_R :
forall cx STK sp0 FP L A mem md (regs : bvmap 5 word) (mem1 : word -> option byte) (lp : Z) (B0 : list (Z * Z)) (codes : list Z) c0 (bq : rbound),
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_win STK sp0 cx ->
(forall b, In b (tcx_tabs cx) -> wtok' STK sp0 FP (blocks L A) b) ->
getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
0 <= lp -> lp + 1 <= y_cap cx -> y_sp cx + 112 <= y_pR cx -> y_pR cx + 16 <= sp0 ->
Z.of_nat (length codes) = lp + 1 ->
tepi_midV_R API cx STK sp0 FP L A mem md B0 regs mem1 lp codes bq c0 ->
SR ubs0segs c0 (tepi_postV_R API cx STK sp0 FP L A mem md B0 regs mem1 codes
(rb_free (rb_malloc (rb_malloc bq (12 * (lp + 1) / 8 + 3)) (384 * (lp + 1) / 255 + 4)) (12 * (lp + 1) / 8 + 3))).
Proof using CBBV CBLV IMG.
intros cx STK sp0 FP L A mem md regs mem1 lp B0 codes c0 bq HCX HRG HSEP HWIN HWT Htp0 Hlp0 Hlp1 HpRhi HpRhi2 LenC
(L2 & A2 & regs2 & mem2 & md2 & res1 & res2 & -> & HJ & Hid & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & VLD
& MHI & MBL & MG & HB & Htok & Hr1 & Hr2 & VLDK & Hnz1 & Hnz2 & HRq).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HWIN as [W1 W2].
pose proof HJ as (HH & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Hlp27 : lp + 1 <= 134217727) by lia.
assert (Hspm : y_sp cx mod 16 = 0) by exact Hal16.
pose proof (Z.div_mod (12 * (lp + 1)) 8 ltac:(lia)) as Hdm8. pose proof (Z.mod_pos_bound (12 * (lp + 1)) 8 ltac:(lia)) as Hmb8.
remember (12 * (lp + 1) / 8) as q8 eqn:Hq8. remember ((12 * (lp + 1)) mod 8) as r8 eqn:Hr8. clear Hr8. apply hideP_i in Hq8.
pose proof (Z.div_mod (384 * (lp + 1)) 255 ltac:(lia)) as Hdm255. pose proof (Z.mod_pos_bound (384 * (lp + 1)) 255 ltac:(lia)) as Hmb255.
remember (384 * (lp + 1) / 255) as q255 eqn:Hq255. remember ((384 * (lp + 1)) mod 255) as r255 eqn:Hr255. clear Hr255. apply hideP_i in Hq255.
remember (Ereg regs2 [Z_to_bv 64 (y_ld cx)]) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : ew E 2 = Z_to_bv 64 (y_sp cx)) by (rewrite (HE 2%nat 2%bv eq_refl); exact G2).
assert (HE2u : bv_unsigned (ew E 2) = y_sp cx) by (rewrite HE2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (y_g cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE18 : ew E 18 = Z_to_bv 64 (y_pR cx)) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE19 : ew E 19 = Z_to_bv 64 (y_icl cx)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE20 : ew E 20 = Z_to_bv 64 (y_idl cx)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HE32 : ew E 32 = Z_to_bv 64 (y_ld cx)) by (rewrite HE0, (ew_Ereg_extra regs2 _ 0); reflexivity).
assert (Ha2 : ew E 21 = Z_to_bv 64 res2) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE22 : ew E 22 = Z_to_bv 64 (lp + 1)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (Ha1 : ew E 23 = Z_to_bv 64 res1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HS : st_ok ubs0segs E ss_tepib_c (mkst regs2 (Z_to_bv 64 TPC_EPIB) mem2 (seg_rom ubs0segs))).
{ change ss_tepib_c with ss_tepib. unfold ss_tepib. rewrite HE0. apply entry_st_ok; rewrite <- ?HE0.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok, tgld_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE32, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact VLD ].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2u, HE18, HE8, HE22, HE20, HE19, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [lia | assumption]. }
clear HE0.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 TPC_EPIB) mem2 (seg_rom ubs0segs))) in HJ, MHI, MBL, MG.
assert (Gin : In (y_g cx, 72) (blocks L2 A2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; apply in_app_iff; left; cbv; tauto]. }
assert (B0rng : forall b m i, In (b, m) B0 -> 0 <= i < m -> 4096 <= b /\ b + m <= alloc_ceiling).
{ intros b m i Hbm Hi. destruct (heap_blocks _ _ LAWS _ _ _ _ b m i HH ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; apply in_app_iff; right; exact Hbm]) Hi) as (_ & H1 & H2 & _). lia. }
Ltac mem_call cx MHI MBL MG HB Hkeep Hhi mem2 lo_tac :=
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in let MG2 := fresh "MG" in
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m1 a =>
lazymatch type of MBL with forall b m i, In (b, m) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs m1 a)
by (intros a Ha Hna; rewrite (proj1 (Hhi a Ha ltac:(clear - Ha Hna; lo_tac; lia))); exact (MHI a Ha Hna));
assert (MBL2 : forall b m i, In (b, m) Bf -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs m1 (b + i))
by (intros b m i Hb Hi; rewrite (Hkeep b m i ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; apply in_app_iff; right; exact Hb]) Hi);
exact (MBL b m i Hb Hi));
assert (MG2 : forall i, 0 <= i < 48 -> mbyte ubs0segs mem2 (y_g cx + i) = mbyte ubs0segs m1 (y_g cx + i))
by (intros i Hi; rewrite (Hkeep (y_g cx) 72 i ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; apply in_app_iff; left; cbv; tauto]) ltac:(lia));
exact (MG i Hi))
end end;
try (lazymatch goal with VK : garr8 _ _ ?bb ?ll, Hwb : wtok' _ _ _ _ (?bb, ?nn), LenK : Z.of_nat (length ?ll) = _ |- _ =>
let V2 := fresh "VK" in
assert (V2 : garr8 ubs0segs mem2 bb ll)
by (eapply garr8_frame; [exact VK|]; intros a Ha; rewrite LenK in Ha;
replace a with (bb + (a - bb)) by lia;
apply (Hkeep bb nn (a - bb));
[ eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; apply (proj2 (In_nz _ _)); split; [left; reflexivity | cbn [fst]; assumption]] | lia ]);
clear VK; rename V2 into VGK end);
clear MHI MBL MG Hkeep; rename MHI2 into MHI; rename MBL2 into MBL; rename MG2 into MG.
Ltac fold_ro cx MHI MBL MG :=
lazymatch goal with HF : frame_of _ _ ?m ?m' |- _ =>
let Hro := fresh "Hro" in
pose proof (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hro; clear HF;
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in let MG2 := fresh "MG" in
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m0 a =>
lazymatch type of MBL with forall b mm i, In (b, mm) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) ->
mbyte ubs0segs m' a = mbyte ubs0segs m0 a)
by (intros a Ha Hna; rewrite (tmbyte_eq_of1 _ _ a (Hro _)); exact (MHI a Ha Hna));
assert (MBL2 : forall b mm i, In (b, mm) Bf -> 0 <= i < mm -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m0 (b + i))
by (intros b mm i Hb Hi; rewrite (tmbyte_eq_of1 _ _ (b + i) (Hro _)); exact (MBL b mm i Hb Hi));
assert (MG2 : forall i, 0 <= i < 48 -> mbyte ubs0segs m' (y_g cx + i) = mbyte ubs0segs m0 (y_g cx + i))
by (intros i Hi; rewrite (tmbyte_eq_of1 _ _ (y_g cx + i) (Hro _)); exact (MG i Hi));
try (lazymatch goal with VK : arr16 _ _ (y_ld cx) ?ll |- _ =>
let V2 := fresh "VK" in
assert (V2 : arr16 ubs0segs m' (y_ld cx) ll) by (eapply arr16_frame; [exact VK|]; intros a Ha; exact (tmbyte_eq_of1 _ _ a (Hro _)));
clear VK; rename V2 into VLDK end);
try (lazymatch goal with VK : garr8 _ _ ?bb ?ll |- _ =>
let V2 := fresh "VK" in
assert (V2 : garr8 ubs0segs m' bb ll) by (eapply garr8_frame; [exact VK|]; intros a Ha; exact (tmbyte_eq_of1 _ _ a (Hro _)));
clear VK; rename V2 into VGK end);
clear MHI MBL MG Hro; rename MHI2 into MHI; rename MBL2 into MBL; rename MG2 into MG
end end end.
Ltac res_fact' HS k Hatom R :=
add_fact' HS k (mkAF 4096 CEIL_MAX 4); [| ew_havoc; rewrite Hatom, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
Ltac do_free cx HS HJ Hid nsz k MHI MBL MG HB Htok HE2u Hspm Htp0 HE Hceil G4 HRq Hnz :=
let F10 := fresh "F10" in let F2 := fresh "F2" in let F4 := fresh "F4" in let F1 := fresh "F1" in
(jreg HS (10%bv:reg) as F10); (jreg HS (2%bv:reg) as F2); (jreg HS (4%bv:reg) as F4); (jreg HS (1%bv:reg) as F1);
cbn [ms_regs mkst] in F10, F2, F4, F1;
eapply SR_bind;
[ eapply (jfree_tok_res API IMG) with (spc := _) (n := nsz);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid
| eapply (ttmp_free_live API _ _ _ _ _ nsz); [exact (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) | exact HB | exact Htok | lia | exact Hceil | exact Hnz]
| exact HRq
| cbn [ms_regs mkst]; rewrite F10; first [reflexivity | assumption | symmetry; assumption]
| cbn [ms_regs mkst]; rewrite F2, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2u; reflexivity | lia | exact Hspm | lia | lia
| cbn [ms_regs mkst]; rewrite F4, (HE 4%nat (4%bv:reg) eq_refl), G4; exact Htp0
| cbn [ms_regs mkst]; exact F1 | apply ret_ok_even; vm_compute; reflexivity ]
| ];
clear F10 F2 F4 F1;
let L2 := fresh "L" in let A2 := fresh "A" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in
let HJ2 := fresh "HJ" in let Hid2 := fresh "Hid" in let HP2 := fresh "HP" in let Hres := fresh "Hfres" in
let Hkeep := fresh "Hkeep" in let Hhi := fresh "Hhi" in let HRq2 := fresh "HRq" in
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & Hid2 & HP2 & Hres & Hkeep & Hhi & HRq2);
clear HJ Hid HRq; change (ms_segs ubs0_msyms) with ubs0segs in Hkeep, Hhi;
let HB2 := fresh "HB" in
pose proof (tfree_post_live_nz _ _ _ _ _ _ HB Hnz Hres) as HB2;
let Htok2 := fresh "Htok" in
pose proof (tnz_tl _ _ _ Htok) as Htok2; cbv beta in Htok2;
clear HB Htok Hres; rename HB2 into HB; rename Htok2 into Htok;
mem_call cx MHI MBL MG HB Hkeep Hhi mem2 ltac:(unfold ALLOC_STACK);
let HS2 := fresh "HS" in
jafter_call_keep HS k regs2 mem2 HP2 (@nil nat) HS2;
specialize (HS2 ltac:(constructor)); clear HS Hhi HP2; rename HS2 into HS;
rename HJ2 into HJ; rename Hid2 into Hid; rename HRq2 into HRq.
Ltac pin_from HS rr Hatom :=
let P := fresh "P" in
(jreg HS rr as P); cbn [ms_regs mkst] in P; rewrite Hatom in P; pin_reg' HS rr 0 P; clear P.
Ltac ealloc_tail cx HS HJ Hid n1 n2 MHI MBL MG HB Htok HE2u Hspm Htp0 HE Hceil G4 :=
apply nz_swap2 in HB;
let Ht := fresh "Htok" in pose proof (nz_swap2_in _ _ _ Htok) as Ht; cbv beta in Ht; clear Htok; rename Ht into Htok;
do_free cx HS HJ Hid n1 33%nat MHI MBL MG HB Htok HE2u Hspm Htp0 HE Hceil G4;
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free; [wr_ok_tac|]; fold_ro cx MHI MBL MG;
do_free cx HS HJ Hid n2 49%nat MHI MBL MG HB Htok HE2u Hspm Htp0 HE Hceil G4.
Ltac post_fail HS HJ Hid MHI MBL MG HB HE HE2 HE8 G9 G3 G4 :=
apply SR_ret; unfold tepi_postV;
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
lazymatch goal with |- context [mkst ?rg _ ?mm _] =>
exists Lf, Af, rg, mm, mdf, 2 end end;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hid|];
let Q := fresh "Q" in
let greg rr := (jreg HS rr as Q); cbn [ms_regs mkst] in Q; rewrite Q; clear Q;
let n := eval cbv in (Z.to_nat (bv_unsigned rr)) in
first [exact HE2 | exact HE8 | reflexivity | rewrite (HE n rr eq_refl); first [reflexivity | exact G9 | exact G3 | exact G4] ] in
split; [greg (2%bv:reg)|]; split; [greg (3%bv:reg)|]; split; [greg (4%bv:reg)|];
split; [greg (8%bv:reg)|]; split; [greg (9%bv:reg)|];
split; [intros a Ha Hna Hnp; exact (MHI a Ha Hna)|];
split; [exact MBL|]; split; [exact MG|];
right; split; [reflexivity|]; split; [exact HB|];
intros a Ha; apply MHI; lia.
specialize (Hr1 Hnz1). res_fact' HS 23%nat Ha1 Hr1.
specialize (Hr2 Hnz2). res_fact' HS 21%nat Ha2 Hr2.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_create_byte_list; [wr_ok_tac|]. fold_ro cx MHI MBL MG.
assert (Hnzid : nz [(res2, q255 + 4); (res1, q8 + 3)] = [(res2, q255 + 4); (res1, q8 + 3)]).
{ apply tnz_id. intros b Hb. cbv [In] in Hb. destruct Hb as [<-|[<-|[]]]; cbn [fst]; assumption. }
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lx ?Ax _ _ =>
assert (HBl : Permutation (blocks Lx Ax)
((res1, q8 + 3) :: (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ::
((res2, q255 + 4) :: [(y_ti cx, 2 * y_idl cx * y_idl cx); (y_lm cx, 8192); (y_lc cx, 4096); (y_li cx, 8192); (y_tm cx, 4098 * y_idl cx); (y_g cx, 72)] ++ B0))) end.
{ eapply Permutation_trans; [exact HB|]. rewrite Hnzid. unfold tcx_tabs, y_tisz, y_tmsz, y_cap, cap. apply tperm_cbl. }
lazymatch goal with |- SR _ (mkCfg ?msq ?mdq) _ =>
jreg HS (10%bv:reg) as C10; jreg HS (11%bv:reg) as C11; jreg HS (12%bv:reg) as C12; jreg HS (13%bv:reg) as C13;
jreg HS (14%bv:reg) as C14; jreg HS (1%bv:reg) as C1; jreg HS (2%bv:reg) as C2; jreg HS (4%bv:reg) as C4 end.
cbn [ms_regs mkst] in C10, C11, C12, C13, C14, C1, C2, C4.
lazymatch goal with |- SR _ (mkCfg ?msq _) _ =>
assert (Hspc : spZ (ms_regs msq) = y_sp cx) by (unfold spZ; cbn [ms_regs mkst]; rewrite C2; exact HE2u) end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lx ?Ax _ _ =>
eapply (CBLV Lx Ax _ _ _ res1 (q8 + 3) (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (lp + 1) (y_idl cx) (y_icl cx) _ codes) end.
- eapply fn_pre_of_journal; [exact HJ | | | | | |].
+ cbn [ms_regs mkst]. rewrite C1. apply ret_ok_even. vm_compute. reflexivity.
+ rewrite Hspc. exact Hspm.
+ unfold CBL_STK_U. lia.
+ rewrite Hspc. unfold CBL_STK_U. lia.
+ rewrite Hspc. lia.
+ cbn [ms_regs mkst]. rewrite C4, (HE 4%nat (4%bv:reg) eq_refl), G4. exact Htp0.
- cbn [ms_regs mkst]. rewrite C10. exact Ha1.
- cbn [ms_regs mkst]. rewrite C11. exact HE22.
- cbn [ms_regs mkst]. rewrite C12. exact HE32.
- cbn [ms_regs mkst]. rewrite C13. exact HE20.
- cbn [ms_regs mkst]. rewrite C14. exact HE19.
- lia.
- lia.
- lia.
- rewrite (hideP_e _ Hq8). lia.
- lia.
- lia.
- exact HBl.
- exact VLDK.
- exact LenC. }
cbv beta. intros c' (regs9 & mem9 & ret & -> & HJc & HPc & Hret & Hret0 & Hret1 & VGK & LenBL). cbn [ms_regs ms_mem mkst] in HJc, HPc.
clear VLDK.
rewrite C1. clear C1 C10 C11 C12 C13 C14 C2 C4.
Ltac after_callee cx HS HJ HJc HPc Hspc p n Hw HBfirst inRest inRestG k MHI MBL MG HE2u Hceil :=
let Hsep := fresh "Hsep" in
assert (Hsep : forall b m, In (b, m) _ -> p + n <= b \/ b + m <= p)
by (let b := fresh "b" in let m := fresh "m" in let Hbm := fresh "Hbm" in
intros b m Hbm;
pose proof (heap_sep_perm _ _ LAWS _ _ _ _ (p, n) _ (b, m) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HBfirst
ltac:(inRest Hbm)) as Hs;
cbn [fst snd] in Hs; exact Hs);
let HsepG := fresh "HsepG" in
assert (HsepG : p + n <= y_g cx \/ y_g cx + 72 <= p)
by (pose proof (heap_sep_perm _ _ LAWS _ _ _ _ (p, n) _ (y_g cx, 72) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HBfirst
ltac:(inRestG)) as Hs;
cbn [fst snd] in Hs; exact Hs);
let Rng := fresh "Rng" in
pose proof (heap_blocks_range _ _ LAWS _ _ _ _ p n (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) ltac:(eapply blocks_perm_in; [exact HBfirst | left; reflexivity]) ltac:(lia)) as Rng;
let Ging := fresh "Ging" in
pose proof (blocks_perm_in _ _ _ _ (y_g cx, 72) HBfirst ltac:(right; inRestG)) as Ging;
let HJ2 := fresh "HJ" in
lazymatch type of HJc with journal _ _ _ _ _ _ _ _ _ ?Lx ?Ax ?m9 ?mdx =>
lazymatch type of HJ with journal _ _ ?STK ?sp0 ?FP ?L ?A ?mem ?md _ _ _ _ =>
assert (HJ2 : journal ubs0_msyms MR STK sp0 FP L A mem md Lx Ax m9 mdx)
by (eapply (journal_sub_gen _ _ LAWS); [exact HJ | exact HJc | rewrite Hspc; unfold CBL_STK_U, CBB_STK; lia | rewrite Hspc; lia
| eapply (sub_cond_of_wtok _ _ _ _ _ p n Hw); [eapply blocks_perm_in; [exact HBfirst | left; reflexivity] | lia | exact Hceil] ])
end end;
let Hhi := fresh "Hhi" in
pose proof (journal_high_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as Hhi; rewrite Hspc in Hhi;
let Hbk := fresh "Hbk" in
pose proof (journal_blocks_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as Hbk;
change (ms_segs ubs0_msyms) with ubs0segs in Hhi, Hbk;
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in let MG2 := fresh "MG" in
lazymatch type of MHI with forall a, _ -> _ -> mbyte _ ?mc a = mbyte _ ?m1 a =>
lazymatch type of MBL with forall b m i, In (b, m) ?Bf -> _ =>
lazymatch type of HJc with journal _ _ _ _ _ _ _ _ _ _ _ ?m9 _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) ->
mbyte ubs0segs m9 a = mbyte ubs0segs m1 a)
by (intros a Ha Hna; rewrite (proj1 (Hhi a Ha ltac:(clear - Ha Hna; unfold CBL_STK_U, CBB_STK; lia))); exact (MHI a Ha Hna));
assert (MBL2 : forall b m i, In (b, m) Bf -> 0 <= i < m -> mbyte ubs0segs m9 (b + i) = mbyte ubs0segs m1 (b + i))
by (intros b m i Hb Hi;
rewrite (Hbk b m i ltac:(eapply blocks_perm_in; [exact HBfirst | right; inRest Hb])
ltac:(eapply blocks_perm_in; [exact HBfirst | right; inRest Hb]) Hi
ltac:(intros Hf; apply inFP_cons in Hf as [Hf|Hf]; [pose proof (Hsep b m Hb); lia | exact (inFP_nil _ Hf)]));
exact (MBL b m i Hb Hi));
assert (MG2 : forall i, 0 <= i < 48 -> mbyte ubs0segs m9 (y_g cx + i) = mbyte ubs0segs m1 (y_g cx + i))
by (intros i Hi;
rewrite (Hbk (y_g cx) 72 i Ging Ging ltac:(lia)
ltac:(intros Hf; apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil _ Hf)]));
exact (MG i Hi))
end end end;
clear MHI MBL MG Hbk; rename MHI2 into MHI; rename MBL2 into MBL; rename MG2 into MG;
let HS2 := fresh "HS" in
lazymatch type of HJc with journal _ _ _ _ _ _ _ _ _ _ _ ?m9 _ =>
lazymatch type of HPc with regs_preserved _ ?regs9 =>
jafter_call_keep HS k regs9 m9 HPc (@nil nat) HS2 end end;
specialize (HS2 ltac:(constructor)); clear HS Hhi HPc HJc; rename HS2 into HS;
clear HJ; rename HJ2 into HJ.
assert (Hw1 : wtok' STK sp0 FP (blocks L A) (res1, q8 + 3)) by (apply Htok; rewrite Hnzid; right; left; reflexivity).
assert (Hw2 : wtok' STK sp0 FP (blocks L A) (res2, q255 + 4)) by (apply Htok; rewrite Hnzid; left; reflexivity).
after_callee cx HS HJ HJc HPc Hspc res1 (q8 + 3) Hw1 HBl
ltac:(fun Hbm => do 8 right; exact Hbm) ltac:(do 7 right; left; reflexivity) 33%nat MHI MBL MG HE2u Hceil.
jreg HS (10%bv:reg) as Hra1. cbn [ms_regs mkst] in Hra1. rewrite Hret in Hra1. symmetry in Hra1.
add_fact' HS 37%nat (mkAF 0 (2 ^ 28) 0); [| rewrite Hra1, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_create_byte_list_block; [wr_ok_tac|]. fold_ro cx MHI MBL MG.
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lx ?Ax _ _ =>
assert (HBb : Permutation (blocks Lx Ax) ((res1, q8 + 3) :: (res2, q255 + 4) :: (tcx_tabs cx ++ B0))) end.
{ eapply Permutation_trans; [exact HB|]. rewrite Hnzid. apply perm_cbb. }
jreg HS (10%bv:reg) as C10; jreg HS (11%bv:reg) as C11; jreg HS (12%bv:reg) as C12;
jreg HS (1%bv:reg) as C1; jreg HS (2%bv:reg) as C2; jreg HS (4%bv:reg) as C4.
cbn [ms_regs mkst] in C10, C11, C12, C1, C2, C4.
clear Hspc.
lazymatch goal with |- SR _ (mkCfg ?msq _) _ =>
assert (Hspc : spZ (ms_regs msq) = y_sp cx) by (unfold spZ; cbn [ms_regs mkst]; rewrite C2; exact HE2u) end.
pose proof (cbb_len_bounds (ret + 1) ltac:(lia)) as Hcbb1.
pose proof (blb_size_ok (lp + 1) (ret + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcbb2.
rewrite <- (hideP_e _ Hq255) in Hcbb2.
remember ((ret + 1) / 255) as d255 eqn:Hd255. clear Hd255.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lx ?Ax _ _ =>
eapply (CBBV Lx Ax _ _ _ res1 (q8 + 3) res2 (q255 + 4) (ret + 1) _ (create_byte_list (y_idl cx) (y_icl cx) codes)) end.
- eapply fn_pre_of_journal; [exact HJ | | | | | |].
+ cbn [ms_regs mkst]. rewrite C1. apply ret_ok_even. vm_compute. reflexivity.
+ rewrite Hspc. exact Hspm.
+ unfold CBB_STK. lia.
+ rewrite Hspc. unfold CBB_STK. lia.
+ rewrite Hspc. lia.
+ cbn [ms_regs mkst]. rewrite C4, (HE 4%nat (4%bv:reg) eq_refl), G4. exact Htp0.
- cbn [ms_regs mkst]. rewrite C10. exact Ha1.
- cbn [ms_regs mkst]. rewrite C11. exact Ha2.
- cbn [ms_regs mkst]. rewrite C12, Hra1, unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- lia.
- lia.
- exact HBb.
- exact VGK.
- exact LenBL. }
cbv beta. intros c' (regs10 & mem10 & -> & HJc & HPc & Hcbb & VOUT & LenOUT). cbn [ms_regs ms_mem mkst] in HJc, HPc.
clear VGK. rename VOUT into VGK.
rewrite C1. clear C1 C10 C11 C12 C2 C4.
pose proof HB as HBr. rewrite Hnzid in HBr. cbn [app] in HBr.
after_callee cx HS HJ HJc HPc Hspc res2 (q255 + 4) Hw2 HBr
ltac:(fun Hbm => right; apply in_app_iff; right; exact Hbm) ltac:(right; apply in_app_iff; left; cbv; tauto) 49%nat MHI MBL MG HE2u Hceil.
jreg HS (10%bv:reg) as Hrb. cbn [ms_regs mkst] in Hrb. rewrite Hcbb in Hrb. symmetry in Hrb.
add_fact' HS 53%nat (mkAF 0 (2 ^ 40) 0); [| rewrite Hrb, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free; [wr_ok_tac|]. fold_ro cx MHI MBL MG.
apply nz_swap2 in HB.
pose proof (nz_swap2_in _ _ _ Htok) as Htok'; cbv beta in Htok'; clear Htok; rename Htok' into Htok.
do_free cx HS HJ Hid (q8 + 3) 65%nat MHI MBL MG HB Htok HE2u Hspm Htp0 HE Hceil G4 HRq Hnz1.
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_add_region' segs E1 ss1 ms1 tpresult_region HS ltac:(vm_compute; reflexivity)) as HS2 end.
match type of HS2 with ?P -> ?Q -> _ => assert (HRo : P); [| assert (HRd : Q); [| specialize (HS2 HRo HRd); clear HRo HRd HS]] end.
{ unfold region_ok, tpresult_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst].
ew_havoc. rewrite HE18, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
{ cbn [all_disjoint ss_mem]. exact I. }
lazymatch type of HS2 with st_ok _ _ ?ss2 _ => let v := eval vm_compute in ss2 in change ss2 with v in HS2 end.
rename HS2 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_CLEAN.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | ew_havoc; rewrite HE18; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. unfold tepi_postV_R.
rewrite <- ?(hideP_e _ Hq8), <- ?(hideP_e _ Hq255).
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
lazymatch goal with |- context [mkst (ms_regs ?msf) _ (ms_mem _) _] =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf, 0 end end.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hid|].
Ltac gregf HS rr Hx :=
let Q := fresh "Q" in
(jreg HS rr as Q); cbn [ms_regs mkst] in Q; rewrite Q; clear Q; first [exact Hx | reflexivity | rewrite Hx; reflexivity | rewrite Hx].
split; [gregf HS (2%bv:reg) HE2|]. split; [gregf HS (3%bv:reg) (HE 3%nat (3%bv:reg) eq_refl); exact G3|]. split; [gregf HS (4%bv:reg) (HE 4%nat (4%bv:reg) eq_refl); exact G4|].
split; [gregf HS (8%bv:reg) HE8|]. split; [gregf HS (9%bv:reg) HE2|].
cbn [ms_mem mkst].
lazymatch goal with HF : frame_of ?E1 ?rs ?m ?m' |- _ =>
assert (Hlast : forall a, 0 <= a < 2 ^ 64 -> ~ (y_pR cx <= a < y_pR cx + 12) -> mbyte ubs0segs m' a = mbyte ubs0segs m a)
by (intros a Ha Hna; apply tmbyte_eq_of1; apply HF; rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2u, ?HE18, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0) end.
split. { intros a Ha Hna Hnp. rewrite (Hlast a ltac:(lia) Hnp). exact (MHI a Ha Hna). }
split. { intros b m i Hb Hi. pose proof (B0rng b m i Hb Hi). rewrite (Hlast (b + i) ltac:(lia) ltac:(lia)). exact (MBL b m i Hb Hi). }
split. { intros i Hi. rewrite (Hlast (y_g cx + i) ltac:(lia) ltac:(lia)). exact (MG i Hi). }
split; [| exact HRq].
split; [reflexivity|]. exists res2, (q255 + 4), (cbb_len (ret + 1)).
split. { rewrite nz_cons_nz in HB by exact Hnz2. exact HB. }
split; [exact Hw2|]. split; [exact Hnz2|].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
pose proof (tst_ok_region_nth E1 ss1 ms1 0%nat _ HS eq_refl) as HR0 end.
cbn [ms_mem mkst] in HR0.
split.
{ apply val_mem_word_mem. replace (y_pR cx) with (bv_unsigned (ew E 18) + 0) by (rewrite HE18, unsigned_lit_small by lia; lia).
change 8%nat with (N.to_nat 8).
eapply (tval_mem_of_chunk _ _ _ 18%nat _ 0 8 (SOff 21 0) res2 HR0); [reflexivity | cbv; tauto | ew_havoc; reflexivity | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia].
cbn [sv_denot]. ew_havoc. rewrite Ha2, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
split.
{ replace (y_pR cx + 8) with (bv_unsigned (ew E 18) + 8) by (rewrite HE18, unsigned_lit_small by lia; lia).
change 4%nat with (N.to_nat 4).
eapply (tval_mem_of_chunk _ _ _ 18%nat _ 8 4 (SOff 53 1) (cbb_len (ret + 1)) HR0); [reflexivity | cbv; tauto | ew_havoc; reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. ew_havoc. rewrite Hrb, unsigned_lit_small by lia. f_equal. lia. }
split; [lia|].
split. { assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
unfold raster_of. cbv zeta.
split; [| split; [symmetry; exact LenOUT | rewrite LenC, <- (hideP_e _ Hq255); reflexivity]].
eapply garr8_frame; [exact VGK|]. intros a Ha. rewrite LenOUT in Ha. apply Hlast; lia.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
