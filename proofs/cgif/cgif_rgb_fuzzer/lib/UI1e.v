(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ubs2_errno_low : errno_addr ubs2_msyms + 4 <= alloc_ceiling.
Proof.
pose proof (proj1 alloc_ceiling_val). enough (errno_addr ubs2_msyms + 4 <= CEIL_MIN) by lia.
vm_compute. intros H'. discriminate H'. Qed.

Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition FREECGIF_STK : Z := 16 + ALLOC_STACK.
Definition gpals_of (attr pal palsz : Z) : list (Z * Z) :=
if Z.land attr 4 =? 0 then [(pal, palsz)] else [].
Definition fp_freeCGIF (g attr pal palsz : Z) : list (Z * Z) :=
(g, g + CGIF_SIZE) :: (if Z.land attr 4 =? 0 then [(pal, pal + palsz)] else []).
Definition ss_freeCGIF : sstate :=
mkSS ubs2_A_freeCGIF sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 (obj_chunks_from LAY_CGIF 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FREECGIF_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4) ] [] []).
Theorem ubs2_freeCGIF :
forall L A regs mem md g vals attr pal palsz rest,
fn_pre ubs2_msyms MR FREECGIF_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 g ->
obj_at ubs2segs mem g LAY_CGIF vals ->
nth_error vals CG_attr = Some attr -> nth_error vals CG_pal = Some pal ->
Permutation (blocks L A) ((g, CGIF_SIZE) :: gpals_of attr pal palsz ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_freeCGIF) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR FREECGIF_STK (spZ regs) (fp_freeCGIF g attr pal palsz) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Proof.
intros L A regs mem md g vals attr pal palsz rest HPRE Ha0 Hobj Hattr Hpal HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREECGIF_STK = 8208) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hgin : In (g, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_nth ubs2segs mem g LAY_CGIF vals 5 _ _ Hobj eq_refl Hattr) as [_ Hattr_r]. cbn [snd] in Hattr_r.
pose proof (obj_at_nth ubs2segs mem g LAY_CGIF vals 3 _ _ Hobj eq_refl Hpal) as [_ Hpal_r]. cbn [snd] in Hpal_r.
assert (HS : st_ok ubs2segs (Ereg regs (map (Z_to_bv 64) vals ++ [])) ss_freeCGIF
(mkst regs (Z_to_bv 64 ubs2_A_freeCGIF) mem (seg_rom ubs2segs))).
{ apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj ubs2segs _ mem 10 g); [ | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). rewrite Ha0. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite Ha0, unsigned_lit_small by lia. unfold spZ in *. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite Ha0, unsigned_lit_small by lia. unfold spZ in *.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR FREECGIF_STK (fp_freeCGIF g attr pal palsz) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_freeCGIF) mem (seg_rom ubs2segs))) in HJ.
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 2 = getr regs 2)
by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 1 = getr regs 1)
by (apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE4 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 4 = getr regs 4)
by (apply (ew_Ereg_nat regs _ 4 4%bv); vm_compute; reflexivity).
assert (HE10 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 10 = Z_to_bv 64 g).
{ rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). exact Ha0. }
assert (HE37 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 37 = Z_to_bv 64 attr) by (apply (Ereg_vals regs vals [] 5); exact Hattr).
assert (HE35 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 35 = Z_to_bv 64 pal) by (apply (Ereg_vals regs vals [] 3); exact Hpal).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
jrun LAWS ubs2tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jbranch ubs2tbl HS.
-
rewrite branch_ne_U, U_and_lit, U_zext, (U_atom _ 37 attr HE37), U_lit in Hc by lia.
change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_4 in Hc by lia.
assert (Hattr4 : Z.land attr 4 <> 0) by (intros E0; rewrite E0 in Hc; discriminate).
assert (Hpals : gpals_of attr pal palsz = []).
{ unfold gpals_of. destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity]. }
rewrite Hpals in HB. cbn [app] in HB.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. rewrite HE10 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hgin | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | rewrite HE4; exact Htp | exact Hr1 | rewrite HE1; exact Hra
| intros _ i Hi; exists (g, g + CGIF_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2).
exists L2, A2, regs2, mem2, md2. rewrite HE1. split; [reflexivity|]. split; [exact HJ2|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP2]|].
eapply perm_after_rm1; [exact HB | exact Hrm].
-
rewrite branch_ne_U, U_and_lit, U_zext, (U_atom _ 37 attr HE37), U_lit in Hc by lia.
change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_4 in Hc by lia.
assert (Hattr4 : Z.land attr 4 = 0) by (destruct (Z.eqb_spec (Z.land attr 4) 0); [assumption | discriminate]).
assert (Hpals : gpals_of attr pal palsz = [(pal, palsz)]) by (unfold gpals_of; rewrite Hattr4; reflexivity).
rewrite Hpals in HB. cbn [app] in HB.
assert (Hpalin : In (pal, palsz) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
pose proof (heap_sep_perm ubs2_msyms MR LAWS L A mem md (g, CGIF_SIZE) _ (pal, palsz) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. rewrite HE35 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hpalin | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | rewrite HE4; exact Htp | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros _ i Hi; exists (pal, pal + palsz); split; [right; rewrite Hattr4; left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2). clear HJ.
assert (HB2 : Permutation (blocks L2 A2) ((g, CGIF_SIZE) :: rest)).
{ eapply perm_after_rm1; [|exact Hrm]. eapply Permutation_trans; [exact HB|]. apply perm_swap. }
assert (Hg2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call HS 49%nat regs2 mem2 HP2 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [rewrite HE10; apply unsigned_lit_small; lia | exact Hg2 | exact Hkeep | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 49 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. rewrite HE10 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hg2 | exact Hq10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hq4 | ew_havoc; rewrite HE4; exact Htp | exact Hq1 | rewrite HE1; exact Hra
| intros _ i Hi; exists (g, g + CGIF_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3).
exists L3, A3, regs3, mem3, md3. rewrite HE1. split; [reflexivity|]. split; [exact HJ3|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP3]|].
eapply perm_after_rm1; [exact HB2 | exact Hrm3].
Qed.
Definition FREEFRAME_STK : Z := 16 + ALLOC_STACK.
Definition pals_of (attr lpal lpalsz : Z) : list (Z * Z) :=
if Z.land attr 1 =? 0 then [] else [(lpal, lpalsz)].
Definition fp_freeFrame (f img imgsz attr lpal lpalsz : Z) : list (Z * Z) :=
(f, f + FRAME_SIZE) :: (img, img + imgsz) :: (if Z.land attr 1 =? 0 then [] else [(lpal, lpal + lpalsz)]).
Definition ss_freeFrame : sstate :=
mkSS ubs2_A_freeFrame sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 FRAME_SIZE 0 0 (obj_chunks_from LAY_Frame 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FREEFRAME_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - FRAME_SIZE) 4) ] [] []).
Theorem ubs2_freeFrame :
forall L A regs mem md f fvals img imgsz attr lpal lpalsz rest,
fn_pre ubs2_msyms MR FREEFRAME_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 f ->
obj_at ubs2segs mem f LAY_Frame fvals ->
nth_error fvals FR_img = Some img -> nth_error fvals FR_attr = Some attr -> nth_error fvals FR_lpal = Some lpal ->
Permutation (blocks L A) ((f, FRAME_SIZE) :: (img, imgsz) :: pals_of attr lpal lpalsz ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_freeFrame) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR FREEFRAME_STK (spZ regs) (fp_freeFrame f img imgsz attr lpal lpalsz) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Proof.
intros L A regs mem md f fvals img imgsz attr lpal lpalsz rest HPRE Ha0 Hobj Himg Hattr Hlpal HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREEFRAME_STK = 8208) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFSv : FRAME_SIZE = 40) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hfin : In (f, FRAME_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md f FRAME_SIZE HH Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
pose proof (obj_at_nth ubs2segs mem f LAY_Frame fvals 1 _ _ Hobj eq_refl Himg) as [_ Himg_r]. cbn [snd] in Himg_r.
pose proof (obj_at_nth ubs2segs mem f LAY_Frame fvals 2 _ _ Hobj eq_refl Hattr) as [_ Hattr_r]. cbn [snd] in Hattr_r.
pose proof (obj_at_nth ubs2segs mem f LAY_Frame fvals 0 _ _ Hobj eq_refl Hlpal) as [_ Hlpal_r]. cbn [snd] in Hlpal_r.
assert (HS : st_ok ubs2segs (Ereg regs (map (Z_to_bv 64) fvals ++ [])) ss_freeFrame
(mkst regs (Z_to_bv 64 ubs2_A_freeFrame) mem (seg_rom ubs2segs))).
{ apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj ubs2segs _ mem 10 f); [ | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). rewrite Ha0. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite Ha0, unsigned_lit_small by lia. unfold spZ in *. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite Ha0, unsigned_lit_small by lia. unfold spZ in *.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR FREEFRAME_STK (fp_freeFrame f img imgsz attr lpal lpalsz) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_freeFrame) mem (seg_rom ubs2segs))) in HJ.
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) fvals ++ [])) 2 = getr regs 2)
by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew (Ereg regs (map (Z_to_bv 64) fvals ++ [])) 1 = getr regs 1)
by (apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE4 : ew (Ereg regs (map (Z_to_bv 64) fvals ++ [])) 4 = getr regs 4)
by (apply (ew_Ereg_nat regs _ 4 4%bv); vm_compute; reflexivity).
assert (HE10 : ew (Ereg regs (map (Z_to_bv 64) fvals ++ [])) 10 = Z_to_bv 64 f).
{ rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). exact Ha0. }
assert (HE32 : ew (Ereg regs (map (Z_to_bv 64) fvals ++ [])) 32 = Z_to_bv 64 lpal) by (apply (Ereg_vals regs fvals [] 0); exact Hlpal).
assert (HE33 : ew (Ereg regs (map (Z_to_bv 64) fvals ++ [])) 33 = Z_to_bv 64 img) by (apply (Ereg_vals regs fvals [] 1); exact Himg).
assert (HE34 : ew (Ereg regs (map (Z_to_bv 64) fvals ++ [])) 34 = Z_to_bv 64 attr) by (apply (Ereg_vals regs fvals [] 2); exact Hattr).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. rewrite HE33 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
assert (Himg_in : In (img, imgsz) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ | exact Himg_in | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | rewrite HE4; exact Htp | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros _ i Hi; exists (img, img + imgsz); split; [right; left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm2 & Hkeep2 & Hhi2). clear HJ.
assert (HB2 : Permutation (blocks L2 A2) ((f, FRAME_SIZE) :: pals_of attr lpal lpalsz ++ rest)).
{ eapply perm_after_rm1; [|exact Hrm2]. eapply Permutation_trans; [exact HB|]. apply perm_swap. }
assert (Hf2 : In (f, FRAME_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call HS 41%nat regs2 mem2 HP2 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [rewrite HE10; apply unsigned_lit_small; lia | exact Hf2 | exact Hkeep2 | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ2.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
jbranch ubs2tbl HS.
-
rewrite branch_eq_U, U_and_lit, U_zext in Hc by lia.
rewrite (U_atom _ 34 attr) in Hc; [| ew_havoc; exact HE34 | lia].
rewrite U_lit in Hc by lia. change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_1 in Hc by lia.
assert (Hattr1 : Z.land attr 1 = 0) by (destruct (Z.eqb_spec (Z.land attr 1) 0); [assumption | discriminate]).
assert (Hpals : pals_of attr lpal lpalsz = []) by (unfold pals_of; rewrite Hattr1; reflexivity).
rewrite Hpals in HB2. cbn [app] in HB2.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 41 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. rewrite HE10 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hf2 | exact Hq10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hq4 | ew_havoc; rewrite HE4; exact Htp | exact Hq1 | rewrite HE1; exact Hra
| intros _ i Hi; exists (f, f + FRAME_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3).
exists L3, A3, regs3, mem3, md3. rewrite HE1. split; [reflexivity|]. split; [exact HJ3|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP3]|].
eapply perm_after_rm1; [exact HB2 | exact Hrm3].
-
rewrite branch_eq_U, U_and_lit, U_zext in Hc by lia.
rewrite (U_atom _ 34 attr) in Hc; [| ew_havoc; exact HE34 | lia].
rewrite U_lit in Hc by lia. change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_1 in Hc by lia.
assert (Hattr1 : Z.land attr 1 <> 0) by (destruct (Z.eqb_spec (Z.land attr 1) 0); [discriminate | assumption]).
assert (Hpals : pals_of attr lpal lpalsz = [(lpal, lpalsz)]).
{ unfold pals_of. destruct (Z.eqb_spec (Z.land attr 1) 0); [contradiction | reflexivity]. }
rewrite Hpals in HB2. cbn [app] in HB2.
assert (Hlp2 : In (lpal, lpalsz) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | right; left; reflexivity]).
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hq10. rewrite HE32 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hlp2 | exact Hq10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hq4 | ew_havoc; rewrite HE4; exact Htp | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity
| intros _ i Hi; exists (lpal, lpal + lpalsz); split; [right; right; unfold fp_freeFrame; destruct (Z.eqb_spec (Z.land attr 1) 0); [contradiction | left; reflexivity] | cbn; lia] ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3). clear HJ2.
assert (HB3 : Permutation (blocks L3 A3) ((f, FRAME_SIZE) :: rest)).
{ eapply perm_after_rm1; [|exact Hrm3]. eapply Permutation_trans; [exact HB2|]. apply perm_swap. }
assert (Hf3 : In (f, FRAME_SIZE) (blocks L3 A3)) by (eapply blocks_perm_in; [exact HB3 | left; reflexivity]).
jafter_call HS 57%nat regs3 mem3 HP3 HS3.
match type of HS3 with ?P -> _ => assert (HK3 : P); [|specialize (HS3 HK3)] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; rewrite HE2; exact Hspw | exact Hhi3 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [ew_havoc; rewrite HE10; apply unsigned_lit_small; lia | exact Hf3 | exact Hkeep3 | lia | lia | lia]. }
pose proof HP2 as HP2'. clear HS. rename HS3 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 57 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 41 _ _ _ ltac:(lia) (env_agree_refl _ _)))
ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hz10. rewrite HE10 in Hz10.
jreg HS (4%bv:reg) as Hz4. jreg HS (1%bv:reg) as Hz1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Hf3 | exact Hz10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hz4 | ew_havoc; rewrite HE4; exact Htp | exact Hz1 | rewrite HE1; exact Hra
| intros _ i Hi; exists (f, f + FRAME_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hrm4 & Hkeep4 & Hhi4).
exists L4, A4, regs4, mem4, md4. rewrite HE1. split; [reflexivity|]. split; [exact HJ4|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP4]|].
eapply perm_after_rm1; [exact HB3 | exact Hrm4].
Qed.


Definition ss_freeFrame_null : sstate :=
mkSS ubs2_A_freeFrame (sr_set sr_atoms 10%bv (SLit 0))
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FREEFRAME_STK) (2^63) 4) ] [] []).
Theorem ubs2_freeFrame_null : forall L A regs mem md,
fn_pre ubs2_msyms MR FREEFRAME_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 0 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_freeFrame) mem (seg_rom ubs2segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md /\
journal ubs2_msyms MR FREEFRAME_STK (spZ regs) [] L A mem md L A mem' md /\
regs_preserved regs regs').
Proof.
intros L A regs mem md HPRE Ha0.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREEFRAME_STK = 8208) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (HS : st_ok ubs2segs (Ereg regs []) ss_freeFrame_null
(mkst regs (Z_to_bv 64 ubs2_A_freeFrame) mem (seg_rom ubs2segs))).
{ apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | exact Ha0].
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack ubs2segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
unfold spZ in *. change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR FREEFRAME_STK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_freeFrame) mem (seg_rom ubs2segs))) in HJ.
assert (HE2 : ew (Ereg regs []) 2 = getr regs 2) by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
jrun LAWS ubs2tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hr1. rewrite (ew_Ereg_nat regs _ 1 1%bv) in Hr1 by (vm_compute; reflexivity).
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end.
rewrite Hr1, Hra. split; [reflexivity|]. split; [exact HJ | exact HPR].
Qed.
Definition CGIF_WRITECB_STK : Z := 16.
Definition lits_CGIF : list (option Z) :=
[None; None; None; None; None; None; None; None; None; None; None; Some ubs2_A_writecb; None; None; Some 0].
Definition ss_cgif_writecb : sstate :=
mkSS ubs2_A_cgif_writecb sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 32 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + CGIF_WRITECB_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4) ] [] []).
Lemma lits_CGIF_ok : forall (vals : list Z),
nth_error vals CG_wfn = Some ubs2_A_writecb -> nth_error vals CG_file = Some 0 ->
forall j z, nth_error lits_CGIF j = Some (Some z) -> nth_error vals j = Some z.
Proof.
intros vals Hw Hf j z Hj.
do 15 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; assumption] |]).
destruct j; discriminate Hj.
Qed.

Definition RAWCLOSE_STK : Z := 32 + ALLOC_STACK.
Definition lits_Raw : list (option Z) := [Some ubs2_A_cgif_writecb].
Definition ss_cgif_raw_close : sstate :=
mkSS ubs2_A_cgif_raw_close sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 RAW_SIZE 0 0 (obj_chunks_gen LAY_Raw 32 lits_Raw);
YQ0b.mkRegion (Some 33%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 41 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RAWCLOSE_STK) (2^63) 4);
(10%nat, mkAF 4096 (CEIL_MAX - RAW_SIZE) 4);
(33%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4) ] [] []).
Lemma lits_Raw_ok : forall (vals : list Z),
nth_error vals RW_wfn = Some ubs2_A_cgif_writecb ->
forall j z, nth_error lits_Raw j = Some (Some z) -> nth_error vals j = Some z.
Proof.
intros vals Hw j z Hj. destruct j as [|j]; [cbn in Hj; injection Hj as <-; assumption|]. destruct j; discriminate Hj.
Qed.
Theorem ubs2_cgif_raw_close : forall L A regs mem md raw rvals g gvals rest,
fn_pre ubs2_msyms MR RAWCLOSE_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 raw ->
obj_at ubs2segs mem raw LAY_Raw rvals ->
nth_error rvals RW_wfn = Some ubs2_A_cgif_writecb -> nth_error rvals RW_ctx = Some g ->
obj_at ubs2segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some ubs2_A_writecb -> nth_error gvals CG_file = Some 0 ->
Permutation (blocks L A) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_raw_close) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR RAWCLOSE_STK (spZ regs) [(raw, raw + RAW_SIZE)] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') ((g, CGIF_SIZE) :: rest)).
Proof.
intros L A regs mem md raw rvals g gvals rest HPRE Ha0 Hraw Hrwfn Hrctx Hg Hgwfn Hgfile HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RAWCLOSE_STK = 8224) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hrawin : In (raw, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hgin : In (g, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md raw RAW_SIZE HH Hrawin ltac:(lia)) as (Hrw0 & Hrw1 & Hrw16).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (heap_sep_perm ubs2_msyms MR LAWS L A mem md (raw, RAW_SIZE) _ (g, CGIF_SIZE) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
pose proof (obj_at_nth ubs2segs mem raw LAY_Raw rvals 1 _ _ Hraw eq_refl Hrctx) as [_ Hctx_r]. cbn [snd] in Hctx_r.
assert (HS : st_ok ubs2segs (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) ss_cgif_raw_close
(mkst regs (Z_to_bv 64 ubs2_A_cgif_raw_close) mem (seg_rom ubs2segs))).
{ pose proof (obj_at_length _ _ _ _ _ Hraw) as Hlen. cbn in Hlen.
apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs2segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj_gen ubs2segs _ mem 10 raw); [ | lia | lia | exact Hraw | reflexivity | | apply (lits_Raw_ok rvals Hrwfn) | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). rewrite Ha0. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
+ eapply (region_ok_obj_gen ubs2segs _ mem 33 g); [ | lia | lia | exact Hg | reflexivity | | apply (lits_CGIF_ok gvals Hgwfn Hgfile) | intros i Hi; lia].
* rewrite (Ereg_vals regs rvals _ 1 g Hrctx). apply unsigned_lit_small. lia.
* intros j v Hj. replace (41 + j)%nat with (32 + (length rvals + j))%nat by (rewrite Hlen; reflexivity).
apply Ereg_more. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite (Ereg_vals regs rvals _ 1 g Hrctx).
rewrite Ha0, !unsigned_lit_small by lia. unfold spZ in *. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite (Ereg_vals regs rvals _ 1 g Hrctx).
rewrite Ha0, !unsigned_lit_small by lia. unfold spZ in *.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR RAWCLOSE_STK [(raw, raw + RAW_SIZE)] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_cgif_raw_close) mem (seg_rom ubs2segs))) in HJ.
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 2 = getr regs 2)
by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 1 = getr regs 1)
by (apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE4 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 4 = getr regs 4)
by (apply (ew_Ereg_nat regs _ 4 4%bv); vm_compute; reflexivity).
assert (HE10 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 10 = Z_to_bv 64 raw).
{ rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). exact Ha0. }
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. rewrite HE10 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hrawin | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | rewrite HE4; exact Htp | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros _ i Hi; exists (raw, raw + RAW_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm2 & Hkeep2 & Hhi2). clear HJ.
jafter_call2 HS 58%nat regs2 mem2 HP2 (-32) (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ2.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 58 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hq1.
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists L2, A2, (ms_regs msx), (ms_mem msx), md2 end.
rewrite Hq1, HE1, Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HPR|].
eapply perm_after_rm1; [exact HB | exact Hrm2].
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
