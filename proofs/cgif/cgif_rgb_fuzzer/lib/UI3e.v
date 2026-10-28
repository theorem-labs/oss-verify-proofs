(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i YI08 UI3d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition ss_free_cht : sstate :=
mkSS ubs2_A_free_col_hash_table sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 CHT_SIZE 0 0 (obj_chunks_from LAY_Cht 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FREECHT_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - CHT_SIZE) 4) ] [] []).
Theorem ubs2_free_cht : free_cht_spec API.
Proof.
intros L A regs mem md c f h u p x cnt ts nf nh nu np nx rest HPRE Ha0 Hobj HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREECHT_STK = 8208) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCSv : CHT_SIZE = 48) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hcin : In (c, CHT_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md c CHT_SIZE HH Hcin ltac:(lia)) as (Hc0 & Hc1 & Hc16).
set (vals := [f; h; u; p; x; cnt; ts]).
set (E := Ereg regs (map (Z_to_bv 64) vals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HE32 : ew E 32 = Z_to_bv 64 f) by (apply (HV 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 h) by (apply (HV 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 u) by (apply (HV 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 p) by (apply (HV 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 x) by (apply (HV 4%nat); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = c) by (rewrite (HE 10%nat 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs2segs E ss_free_cht (mkst regs (Z_to_bv 64 ubs2_A_free_col_hash_table) mem (seg_rom ubs2segs))).
{ unfold ss_free_cht. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ mem 2 (spZ regs)); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ eapply (region_ok_obj ubs2segs _ mem 10 c); [exact HU10 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR FREECHT_STK
((c, c + CHT_SIZE) :: optfp f nf ++ optfp h nh ++ optfp u nu ++ optfp p np ++ optfp x nx) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_free_col_hash_table) mem (seg_rom ubs2segs))) in HJ.
assert (Hspm : (spZ regs - 16) mod 16 = 0) by (replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
jreg HS (10%bv:reg) as Hr10. rewrite HE32 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (spZ regs + -16) with (spZ regs - 16) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API))
with (p := f) (n := nf) (rest := (c, CHT_SIZE) :: optb h nh ++ optb u nu ++ optb p np ++ optb x nx ++ rest) (spc := spZ regs - 16);
[ exact HS | reflexivity | reflexivity | exact HJ | eapply Permutation_trans; [exact HB | apply Permutation_middle]
| exact Hr10 | exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hf0 _ i Hi. exists (f, f + nf). split; [| cbn; lia].
right. apply in_app_iff; left. unfold optfp. rewrite (proj2 (Z.eqb_neq _ _) Hf0). left. reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJn & HP2 & HB2 & Hkeep2 & Hhi2). clear HJ. rename HJn into HJ.
assert (Hc2 : In (c, CHT_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call HS 39%nat regs2 mem2 HP2 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi2 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hc2 | exact Hkeep2 | lia | lia | lia]. }
clear HS Hhi2 Hkeep2 Hr10 Hr2 Hr4 Hr1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
jreg HS (10%bv:reg) as Hr10. rewrite HE33 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (spZ regs + -16) with (spZ regs - 16) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API))
with (p := h) (n := nh) (rest := (c, CHT_SIZE) :: optb u nu ++ optb p np ++ optb x nx ++ rest) (spc := spZ regs - 16);
[ exact HS | reflexivity | reflexivity | exact HJ | eapply Permutation_trans; [exact HB2 | apply Permutation_middle]
| exact Hr10 | exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hf0 _ i Hi. exists (h, h + nh). split; [| cbn; lia].
right. apply in_app_iff; right. apply in_app_iff; left. unfold optfp. rewrite (proj2 (Z.eqb_neq _ _) Hf0). left. reflexivity. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJn & HP3 & HB3 & Hkeep3 & Hhi3). clear HJ. rename HJn into HJ.
assert (Hc3 : In (c, CHT_SIZE) (blocks L3 A3)) by (eapply blocks_perm_in; [exact HB3 | left; reflexivity]).
jafter_call HS 55%nat regs3 mem3 HP3 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi3 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hc3 | exact Hkeep3 | lia | lia | lia]. }
clear HS Hhi3 Hkeep3 Hr10 Hr2 Hr4 Hr1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
jreg HS (10%bv:reg) as Hr10. rewrite HE34 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (spZ regs + -16) with (spZ regs - 16) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API))
with (p := u) (n := nu) (rest := (c, CHT_SIZE) :: optb p np ++ optb x nx ++ rest) (spc := spZ regs - 16);
[ exact HS | reflexivity | reflexivity | exact HJ | eapply Permutation_trans; [exact HB3 | apply Permutation_middle]
| exact Hr10 | exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hf0 _ i Hi. exists (u, u + nu). split; [| cbn; lia].
right. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left. unfold optfp. rewrite (proj2 (Z.eqb_neq _ _) Hf0). left. reflexivity. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJn & HP4 & HB4 & Hkeep4 & Hhi4). clear HJ. rename HJn into HJ.
assert (Hc4 : In (c, CHT_SIZE) (blocks L4 A4)) by (eapply blocks_perm_in; [exact HB4 | left; reflexivity]).
jafter_call HS 71%nat regs4 mem4 HP4 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi4 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hc4 | exact Hkeep4 | lia | lia | lia]. }
clear HS Hhi4 Hkeep4 Hr10 Hr2 Hr4 Hr1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
jreg HS (10%bv:reg) as Hr10. rewrite HE35 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (spZ regs + -16) with (spZ regs - 16) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API))
with (p := p) (n := np) (rest := (c, CHT_SIZE) :: optb x nx ++ rest) (spc := spZ regs - 16);
[ exact HS | reflexivity | reflexivity | exact HJ | eapply Permutation_trans; [exact HB4 | apply Permutation_middle]
| exact Hr10 | exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hf0 _ i Hi. exists (p, p + np). split; [| cbn; lia].
right. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left. unfold optfp. rewrite (proj2 (Z.eqb_neq _ _) Hf0). left. reflexivity. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJn & HP5 & HB5 & Hkeep5 & Hhi5). clear HJ. rename HJn into HJ.
assert (Hc5 : In (c, CHT_SIZE) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5 | left; reflexivity]).
jafter_call HS 87%nat regs5 mem5 HP5 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi5 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hc5 | exact Hkeep5 | lia | lia | lia]. }
clear HS Hhi5 Hkeep5 Hr10 Hr2 Hr4 Hr1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
jreg HS (10%bv:reg) as Hr10. rewrite HE36 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (spZ regs + -16) with (spZ regs - 16) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API))
with (p := x) (n := nx) (rest := (c, CHT_SIZE) :: rest) (spc := spZ regs - 16);
[ exact HS | reflexivity | reflexivity | exact HJ | eapply Permutation_trans; [exact HB5 | apply Permutation_middle]
| exact Hr10 | exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hf0 _ i Hi. exists (x, x + nx). split; [| cbn; lia].
right. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; right. unfold optfp. rewrite (proj2 (Z.eqb_neq _ _) Hf0). left. reflexivity. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJn & HP6 & HB6 & Hkeep6 & Hhi6). clear HJ. rename HJn into HJ.
assert (Hc6 : In (c, CHT_SIZE) (blocks L6 A6)) by (eapply blocks_perm_in; [exact HB6 | left; reflexivity]).
jafter_call HS 103%nat regs6 mem6 HP6 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi6 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hc6 | exact Hkeep6 | lia | lia | lia]. }
clear HS Hhi6 Hkeep6 Hr10 Hr2 Hr4 Hr1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 103 _ _ _ ltac:(lia)
(env_agree_havoc_ge 32 87 _ _ _ ltac:(lia)
(env_agree_havoc_ge 32 71 _ _ _ ltac:(lia)
(env_agree_havoc_ge 32 55 _ _ _ ltac:(lia)
(env_agree_havoc_ge 32 39 _ _ _ ltac:(lia) (env_agree_refl _ _)))))) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 10)), HU10 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hc6 | exact Hq10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; reflexivity | exact HU2 | reflexivity | lia | lia
| exact Hq4 | ew_havoc; rewrite (HE 4%nat 4%bv eq_refl); exact Htp | exact Hq1 | rewrite (HE 1%nat 1%bv eq_refl); exact Hra
| intros _ i Hi; exists (c, c + CHT_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hrm7 & Hkeep7 & Hhi7).
exists L7, A7, regs7, mem7, md7. rewrite (HE 1%nat 1%bv eq_refl). split; [reflexivity|]. split; [exact HJ7|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP7]|].
eapply perm_after_rm1; [exact HB6 | exact Hrm7].
Qed.
End S.
End b.
