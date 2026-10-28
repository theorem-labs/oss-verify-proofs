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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_errno_low : errno_addr ubs0_msyms + 4 <= alloc_ceiling.
Proof using.
pose proof (proj1 alloc_ceiling_val). enough (errno_addr ubs0_msyms + 4 <= CEIL_MIN) by lia.
vm_compute. intros H'. discriminate H'. Qed.
Lemma ubs0_img_low : forall a, in_img ubs0_msyms a -> a < alloc_ceiling.
Proof using.
intros a [_ (s & Hin & Hr)]. pose proof (proj1 alloc_ceiling_val) as Hac. enough (a < CEIL_MIN) by lia.
assert (H : In (bv_unsigned (fst s), bv_unsigned (snd s)) (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved (ms_segs ubs0_msyms)))).
{ apply in_map_iff. exists s. auto. }
match type of H with In _ ?l => let l' := eval vm_compute in l in change l with l' in H end.
cbv [In] in H.
repeat (destruct H as [H|H]; [injection H as E1 E2; rewrite <- E1, <- E2 in Hr; lia|]). destruct H.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Definition FREECGIF_STK : Z := 16 + ALLOC_STACK.
Definition gpals_of (attr pal palsz : Z) : list (Z * Z) :=
if Z.land attr 4 =? 0 then [(pal, palsz)] else [].
Definition fp_freeCGIF (g attr pal palsz : Z) : list (Z * Z) :=
(g, g + CGIF_SIZE) :: (if Z.land attr 4 =? 0 then [(pal, pal + palsz)] else []).
Definition ss_freeCGIF : sstate :=
mkSS ubs0_A_freeCGIF sr_atoms
[ YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 (obj_chunks_from LAY_CGIF 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FREECGIF_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4) ] [] []).
Theorem ubs0_freeCGIF :
forall L A regs mem md g vals attr pal palsz rest,
fn_pre ubs0_msyms MR FREECGIF_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 g ->
obj_at ubs0segs mem g LAY_CGIF vals ->
nth_error vals CG_attr = Some attr -> nth_error vals CG_pal = Some pal ->
Permutation (blocks L A) ((g, CGIF_SIZE) :: gpals_of attr pal palsz ++ rest) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_freeCGIF) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR FREECGIF_STK (spZ regs) (fp_freeCGIF g attr pal palsz) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Proof using IMG LAWS.
intros L A regs mem md g vals attr pal palsz rest HPRE Ha0 Hobj Hattr Hpal HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREECGIF_STK = 8208) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hgin : In (g, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_nth ubs0segs mem g LAY_CGIF vals 5 _ _ Hobj eq_refl Hattr) as [_ Hattr_r]. cbn [snd] in Hattr_r.
pose proof (obj_at_nth ubs0segs mem g LAY_CGIF vals 3 _ _ Hobj eq_refl Hpal) as [_ Hpal_r]. cbn [snd] in Hpal_r.
assert (HS : st_ok ubs0segs (Ereg regs (map (Z_to_bv 64) vals ++ [])) ss_freeCGIF
(mkst regs (Z_to_bv 64 ubs0_A_freeCGIF) mem (seg_rom ubs0segs))).
{ apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj ubs0segs _ mem 10 g); [ | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
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
pose proof (journal_init ubs0_msyms MR FREECGIF_STK (fp_freeCGIF g attr pal palsz) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_freeCGIF) mem (seg_rom ubs0segs))) in HJ.
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
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jbranch ubs0tbl HS.
-
rewrite branch_ne_U, U_and_lit, U_zext, (U_atom _ 37 attr HE37), U_lit in Hc by lia.
change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_4 in Hc by lia.
assert (Hattr4 : Z.land attr 4 <> 0) by (intros E0; rewrite E0 in Hc; discriminate).
assert (Hpals : gpals_of attr pal palsz = []).
{ unfold gpals_of. destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity]. }
rewrite Hpals in HB. cbn [app] in HB.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. rewrite HE10 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
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
pose proof (heap_sep_perm ubs0_msyms MR LAWS L A mem md (g, CGIF_SIZE) _ (pal, palsz) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. rewrite HE35 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
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
- eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 10); [rewrite HE10; apply unsigned_lit_small; lia | exact Hg2 | exact Hkeep | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 49 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. rewrite HE10 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
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
mkSS ubs0_A_freeFrame sr_atoms
[ YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 FRAME_SIZE 0 0 (obj_chunks_from LAY_Frame 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FREEFRAME_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - FRAME_SIZE) 4) ] [] []).
Theorem ubs0_freeFrame :
forall L A regs mem md f fvals img imgsz attr lpal lpalsz rest,
fn_pre ubs0_msyms MR FREEFRAME_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 f ->
obj_at ubs0segs mem f LAY_Frame fvals ->
nth_error fvals FR_img = Some img -> nth_error fvals FR_attr = Some attr -> nth_error fvals FR_lpal = Some lpal ->
Permutation (blocks L A) ((f, FRAME_SIZE) :: (img, imgsz) :: pals_of attr lpal lpalsz ++ rest) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_freeFrame) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR FREEFRAME_STK (spZ regs) (fp_freeFrame f img imgsz attr lpal lpalsz) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Proof using IMG LAWS.
intros L A regs mem md f fvals img imgsz attr lpal lpalsz rest HPRE Ha0 Hobj Himg Hattr Hlpal HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREEFRAME_STK = 8208) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFSv : FRAME_SIZE = 40) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hfin : In (f, FRAME_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md f FRAME_SIZE HH Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
pose proof (obj_at_nth ubs0segs mem f LAY_Frame fvals 1 _ _ Hobj eq_refl Himg) as [_ Himg_r]. cbn [snd] in Himg_r.
pose proof (obj_at_nth ubs0segs mem f LAY_Frame fvals 2 _ _ Hobj eq_refl Hattr) as [_ Hattr_r]. cbn [snd] in Hattr_r.
pose proof (obj_at_nth ubs0segs mem f LAY_Frame fvals 0 _ _ Hobj eq_refl Hlpal) as [_ Hlpal_r]. cbn [snd] in Hlpal_r.
assert (HS : st_ok ubs0segs (Ereg regs (map (Z_to_bv 64) fvals ++ [])) ss_freeFrame
(mkst regs (Z_to_bv 64 ubs0_A_freeFrame) mem (seg_rom ubs0segs))).
{ apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj ubs0segs _ mem 10 f); [ | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
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
pose proof (journal_init ubs0_msyms MR FREEFRAME_STK (fp_freeFrame f img imgsz attr lpal lpalsz) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_freeFrame) mem (seg_rom ubs0segs))) in HJ.
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
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. rewrite HE33 in Hr10.
jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
assert (Himg_in : In (img, imgsz) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
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
- eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 10); [rewrite HE10; apply unsigned_lit_small; lia | exact Hf2 | exact Hkeep2 | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
jbranch ubs0tbl HS.
-
rewrite branch_eq_U, U_and_lit, U_zext in Hc by lia.
rewrite (U_atom _ 34 attr) in Hc; [| ew_havoc; exact HE34 | lia].
rewrite U_lit in Hc by lia. change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_1 in Hc by lia.
assert (Hattr1 : Z.land attr 1 = 0) by (destruct (Z.eqb_spec (Z.land attr 1) 0); [assumption | discriminate]).
assert (Hpals : pals_of attr lpal lpalsz = []) by (unfold pals_of; rewrite Hattr1; reflexivity).
rewrite Hpals in HB2. cbn [app] in HB2.
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 41 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. rewrite HE10 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
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
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hq10. rewrite HE32 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
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
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havoc; rewrite HE2; exact Hspw | exact Hhi3 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 10); [ew_havoc; rewrite HE10; apply unsigned_lit_small; lia | exact Hf3 | exact Hkeep3 | lia | lia | lia]. }
pose proof HP2 as HP2'. clear HS. rename HS3 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 57 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 41 _ _ _ ltac:(lia) (env_agree_refl _ _)))
ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hz10. rewrite HE10 in Hz10.
jreg HS (4%bv:reg) as Hz4. jreg HS (1%bv:reg) as Hz1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Hf3 | exact Hz10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hz4 | ew_havoc; rewrite HE4; exact Htp | exact Hz1 | rewrite HE1; exact Hra
| intros _ i Hi; exists (f, f + FRAME_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hrm4 & Hkeep4 & Hhi4).
exists L4, A4, regs4, mem4, md4. rewrite HE1. split; [reflexivity|]. split; [exact HJ4|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP4]|].
eapply perm_after_rm1; [exact HB3 | exact Hrm4].
Qed.
Lemma fetch_tbl : forall pc w, clookup ubs0tbl pc = Some w ->
fetch_word ubs0segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Proof using. intros pc w H. apply ubs0tbl_ok. exact H. Qed.
Definition ss_freeFrame_null : sstate :=
mkSS ubs0_A_freeFrame (sr_set sr_atoms 10%bv (SLit 0))
[ YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FREEFRAME_STK) (2^63) 4) ] [] []).
Theorem ubs0_freeFrame_null : forall L A regs mem md,
fn_pre ubs0_msyms MR FREEFRAME_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 0 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_freeFrame) mem (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR FREEFRAME_STK (spZ regs) [] L A mem md L A mem' md /\
regs_preserved regs regs').
Proof using IMG LAWS.
intros L A regs mem md HPRE Ha0.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREEFRAME_STK = 8208) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (HS : st_ok ubs0segs (Ereg regs []) ss_freeFrame_null
(mkst regs (Z_to_bv 64 ubs0_A_freeFrame) mem (seg_rom ubs0segs))).
{ apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | exact Ha0].
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
unfold spZ in *. change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs0_msyms MR FREEFRAME_STK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_freeFrame) mem (seg_rom ubs0segs))) in HJ.
assert (HE2 : ew (Ereg regs []) 2 = getr regs 2) by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hr1. rewrite (ew_Ereg_nat regs _ 1 1%bv) in Hr1 by (vm_compute; reflexivity).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end.
rewrite Hr1, Hra. split; [reflexivity|]. split; [exact HJ | exact HPR].
Qed.
Definition CGIF_WRITECB_STK : Z := WRITECB_STK.
Definition lits_CGIF : list (option Z) :=
[None; None; None; None; None; None; None; None; None; None; None; Some 0; None; None; None].
Definition ss_cgif_writecb : sstate :=
mkSS ubs0_A_cgif_writecb sr_atoms
[ YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 32 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + CGIF_WRITECB_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(46%nat, mkAF 4096 (CEIL_MAX - FILE_BLOCK) 4) ] [] []).
Lemma lits_CGIF_ok : forall (vals : list Z) {f : Z},
nth_error vals CG_wfn = Some 0 -> nth_error vals CG_file = Some f ->
forall j z, nth_error lits_CGIF j = Some (Some z) -> nth_error vals j = Some z.
Proof using.
intros vals f Hw _ j z Hj.
do 15 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; assumption] |]).
destruct j; discriminate Hj.
Qed.
Theorem ubs0_cgif_writecb : writecb_spec ubs0_msyms MR ubs0_A_cgif_writecb.
Proof using FWRITE IMG LAWS.
unfold writecb_spec. change WRITECB_STK with CGIF_WRITECB_STK.
intros L A regs mem md g gvals src n f S bs HPRE Hsp47 Ha0 Ha1 Ha2 Hobj Hwfn Hfile Hgin Hfin HSK HG Hn Hsrc0 Hsrc63 Hsf Hss Hroom Hn30.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : CGIF_WRITECB_STK = 528) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HFWv : FWRITE_STK = 512) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md f FILE_BLOCK HH Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
assert (HE46 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 46 = Z_to_bv 64 f) by (apply (Ereg_vals regs gvals [] 14 f Hfile)).
assert (HS : st_ok ubs0segs (Ereg regs (map (Z_to_bv 64) gvals ++ [])) ss_cgif_writecb
(mkst regs (Z_to_bv 64 ubs0_A_cgif_writecb) mem (seg_rom ubs0segs))).
{ apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj_gen ubs0segs _ mem 10 g); [ | lia | lia | exact Hobj | reflexivity | | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). rewrite Ha0. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite Ha0, unsigned_lit_small by lia. unfold spZ in *. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite HE46.
rewrite Ha0, !unsigned_lit_small by lia. unfold spZ in *.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs0_msyms MR CGIF_WRITECB_STK (sink_fp f) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_cgif_writecb) mem (seg_rom ubs0segs))) in HJ.
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 2 = getr regs 2)
by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_fwrite.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hm10. jreg HS (11%bv:reg) as Hm11. jreg HS (12%bv:reg) as Hm12. jreg HS (13%bv:reg) as Hm13.
jreg HS (2%bv:reg) as Hm2. jreg HS (4%bv:reg) as Hm4. jreg HS (1%bv:reg) as Hm1.
assert (HE11 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 11 = getr regs 11) by (apply (ew_Ereg_nat regs _ 11 11%bv); vm_compute; reflexivity).
assert (HE12 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 12 = getr regs 12) by (apply (ew_Ereg_nat regs _ 12 12%bv); vm_compute; reflexivity).
assert (HE4 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 4 = getr regs 4) by (apply (ew_Ereg_nat regs _ 4 4%bv); vm_compute; reflexivity).
assert (HE1 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 1 = getr regs 1) by (apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
rewrite HE11, Ha1 in Hm10. rewrite HE12, Ha2 in Hm12. rewrite HE46 in Hm13. rewrite HE2, Hspw in Hm2. rewrite HE4, Htp in Hm4.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = spZ regs - 16) by (unfold spZ at 1; rewrite Hm2; apply unsigned_lit_small; lia) end.
cbn [ms_mem mkst] in HF, HJ.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem a).
{ intros a Ha Hns. apply (mbyte_eq_of ubs0_msyms). apply HF. rewrite unsigned_lit_small by lia.
intros (r & [<- | [<- | []]] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr.
- rewrite HE2, Hspw in Hr. lia.
- lia. }
assert (HSKc : sink_at ubs0_msyms (ms_mem ms) md f S).
{ apply (sink_at_frame ubs0_msyms mem (ms_mem ms) md f S); [|exact HSK].
intros a [Ha | Ha]; apply K1; try lia.
- pose proof (ubs0_env_addr_range a Ha). lia.
- pose proof (ubs0_env_addr_range a Ha). lia. }
assert (HGc : garr8 ubs0segs (ms_mem ms) src bs).
{ eapply garr8_frame; [exact HG|]. intros a Ha. apply K1; lia. }
assert (Hspm : (spZ regs - 16) mod 16 = 0) by (replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
eapply SR_bind with (R := fun c' => exists regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs0_A_cgif_writecb + 0x38)) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR CGIF_WRITECB_STK (spZ regs) (sink_fp f) L A mem md L A mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = Z_to_bv 64 n /\
sink_at ubs0_msyms mem2 md2 f (S ++ bs) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spZ regs - 16 - FWRITE_STK <= x < spZ regs - 16) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x))).
{ eapply SR_mono.
{ eapply (jcall ubs0_msyms MR) with (STK1 := FWRITE_STK) (FP1 := sink_fp f)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) =>
L2 = L /\ A2 = A /\ getr regs2 10 = Z_to_bv 64 n /\ sink_at ubs0_msyms mem2 md2 f (S ++ bs));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | lia | rewrite Hsp; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FWRITE L A _ _ md src n f S bs HPRE1); [rewrite Hsp; lia | exact Hm10 | exact Hm11 | exact Hm12 | exact Hm13 | exact Hfin | exact HSKc | exact HGc | exact Hn | exact Hsrc0 | exact Hsrc63 | exact Hsf | rewrite Hsp; lia | exact Hroom | exact Hn30]. }
cbv beta. intros c' (regs2 & mem2 & md2 & -> & HJc & HP & Hr10 & HSK2).
exists L, A, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
repeat (split; [reflexivity|]). split; [exact Hr10 | exact HSK2].
- intros a Ha. split; [exact Ha|]. destruct Ha as (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (-> & -> & Hr10 & HSK2)).
exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hr10|]. split; [exact HSK2|].
pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2. }
cbv beta. intros c' (regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hr10 & HSK2 & Hhi2). clear HJ.
jafter_call_keep HS 49%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq53. cbn [ms_regs mkst] in Hq53. rewrite Hr10 in Hq53. symmetry in Hq53.
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hq10. jreg HS (1%bv:reg) as Hq1.
rewrite Hq53 in Hq10.
rewrite ew_havoc_old in Hq10 by (cbv; lia). rewrite HE12, Ha2 in Hq10.
assert (Hx0 : alu64 ALU_XOR (Z_to_bv 64 n) (Z_to_bv 64 n) = Z_to_bv 64 0).
{ apply bv_eq. cbn [alu64 alu]. rewrite bv_xor_unsigned, Z.lxor_nilpotent. reflexivity. }
rewrite Hx0 in Hq10.
assert (Hc0 : alu64 ALU_ADD (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 1)) (Z_to_bv 64 (-1)) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
rewrite Hc0 in Hq10.
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 49 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), md2 end.
rewrite Hq1, HE1, Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HPR|]. split; [exact Hq10|].
cbn [ms_mem mkst] in HF0.
apply (sink_at_frame ubs0_msyms mem2 (ms_mem ms0) md2 f (S ++ bs)); [|exact HSK2].
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem2 a).
{ intros a Ha Hns. apply (mbyte_eq_of ubs0_msyms). apply HF0. rewrite unsigned_lit_small by lia.
intros (r & [<- | []] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr.
rewrite ew_havoc_old in Hr by (cbv; lia). rewrite HE2, Hspw in Hr. lia. }
intros a [Ha | Ha]; apply K2; try lia.
- pose proof (ubs0_env_addr_range a Ha). lia.
- pose proof (ubs0_env_addr_range a Ha). lia.
Qed.
Definition RAWCLOSE_STK : Z := 32 + ALLOC_STACK.
Definition lits_Raw : list (option Z) := [Some ubs0_A_cgif_writecb].
Definition ss_cgif_raw_close : sstate :=
mkSS ubs0_A_cgif_raw_close sr_atoms
[ YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 RAW_SIZE 0 0 (obj_chunks_gen LAY_Raw 32 lits_Raw);
YP09.mkRegion (Some 33%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 41 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RAWCLOSE_STK) (2^63) 4);
(10%nat, mkAF 4096 (CEIL_MAX - RAW_SIZE) 4);
(33%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4) ] [] []).
Lemma lits_Raw_ok : forall (vals : list Z),
nth_error vals RW_wfn = Some ubs0_A_cgif_writecb ->
forall j z, nth_error lits_Raw j = Some (Some z) -> nth_error vals j = Some z.
Proof using.
intros vals Hw j z Hj. destruct j as [|j]; [cbn in Hj; injection Hj as <-; assumption|]. destruct j; discriminate Hj.
Qed.
Theorem ubs0_cgif_raw_close : forall L A regs mem md raw rvals g gvals rest (f : Z) (S : list Z),
fn_pre ubs0_msyms MR RAWCLOSE_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 raw ->
obj_at ubs0segs mem raw LAY_Raw rvals ->
nth_error rvals RW_wfn = Some ubs0_A_cgif_writecb -> nth_error rvals RW_ctx = Some g ->
obj_at ubs0segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
Permutation (blocks L A) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: rest) ->
In (f, FILE_BLOCK) rest -> sink_at ubs0_msyms mem md f S -> Z.of_nat (length S) + 1 <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_close) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWCLOSE_STK (spZ regs) ((raw, raw + RAW_SIZE) :: sink_fp f) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') ((g, CGIF_SIZE) :: rest) /\
sink_at ubs0_msyms mem' md' f (S ++ sink_trailer_Z)).
Proof using FWRITE IMG LAWS.
intros L A regs mem md raw rvals g gvals rest f S HPRE Ha0 Hraw Hrwfn Hrctx Hg Hgwfn Hgfile HB Hfrest HSK Hroom Hsp47.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RAWCLOSE_STK = 8224) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hrawin : In (raw, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hgin : In (g, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md raw RAW_SIZE HH Hrawin ltac:(lia)) as (Hrw0 & Hrw1 & Hrw16).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (heap_sep_perm ubs0_msyms MR LAWS L A mem md (raw, RAW_SIZE) _ (g, CGIF_SIZE) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
pose proof (obj_at_nth ubs0segs mem raw LAY_Raw rvals 1 _ _ Hraw eq_refl Hrctx) as [_ Hctx_r]. cbn [snd] in Hctx_r.
assert (HS : st_ok ubs0segs (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) ss_cgif_raw_close
(mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_close) mem (seg_rom ubs0segs))).
{ pose proof (obj_at_length _ _ _ _ _ Hraw) as Hlen. cbn in Hlen.
apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj_gen ubs0segs _ mem 10 raw); [ | lia | lia | exact Hraw | reflexivity | | apply (lits_Raw_ok rvals Hrwfn) | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). rewrite Ha0. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
+ eapply (region_ok_obj_gen ubs0segs _ mem 33 g); [ | lia | lia | exact Hg | reflexivity | | apply (lits_CGIF_ok gvals Hgwfn Hgfile) | intros i Hi; lia].
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
pose proof (journal_init ubs0_msyms MR RAWCLOSE_STK ((raw, raw + RAW_SIZE) :: sink_fp f) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_close) mem (seg_rom ubs0segs))) in HJ.
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 2 = getr regs 2)
by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 1 = getr regs 1)
by (apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE4 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 4 = getr regs 4)
by (apply (ew_Ereg_nat regs _ 4 4%bv); vm_compute; reflexivity).
assert (HE10 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 10 = Z_to_bv 64 raw).
{ rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). exact Ha0. }
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Hfin : In (f, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; exact Hfrest]).
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HCWv : CGIF_WRITECB_STK = 528) by reflexivity.
assert (HWSv : WRITECB_STK = 528) by reflexivity.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md f FILE_BLOCK HH Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hm10. jreg HS (11%bv:reg) as Hm11. jreg HS (12%bv:reg) as Hm12.
jreg HS (2%bv:reg) as Hm2. jreg HS (4%bv:reg) as Hm4. jreg HS (1%bv:reg) as Hm1.
assert (HE33 : ew (Ereg regs (map (Z_to_bv 64) rvals ++ map (Z_to_bv 64) gvals)) 33 = Z_to_bv 64 g) by (apply (Ereg_vals regs rvals _ 1 g Hrctx)).
rewrite HE33 in Hm10. rewrite HE2, Hspw in Hm2. rewrite HE4, Htp in Hm4.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = spZ regs - 32) by (unfold spZ at 1; rewrite Hm2; apply unsigned_lit_small; lia) end.
cbn [ms_mem mkst] in HF, HJ.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem a).
{ intros a Ha Hns. apply (mbyte_eq_of ubs0_msyms). apply HF. rewrite unsigned_lit_small by lia.
intros (r & [<- | [<- | [<- | []]]] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr.
- rewrite HE2, Hspw in Hr. lia.
- lia.
- lia. }
assert (HSKc : sink_at ubs0_msyms (ms_mem ms) md f S).
{ apply (sink_at_frame ubs0_msyms mem (ms_mem ms) md f S); [|exact HSK].
intros a [Ha | Ha]; apply K1; try lia.
- pose proof (ubs0_env_addr_range a Ha). lia.
- pose proof (ubs0_env_addr_range a Ha). lia. }
assert (HGt : garr8 ubs0segs (ms_mem ms) sk_trailer_addr sink_trailer_Z).
{ exact (sink_at_trailer ubs0_msyms _ _ _ _ HSKc). }
assert (Hgc : obj_at ubs0segs (ms_mem ms) g LAY_CGIF gvals).
{ eapply (obj_at_transport_range ubs0segs mem); [exact Hg | exact (proj1 LAY_CGIF_ok) |]. intros i Hi. apply K1; lia. }
assert (Htr_img : in_img ubs0_msyms sk_trailer_addr).
{ apply (skl_env ubs0_msyms sk_trailer_addr). unfold env_addr. right. right. right. right. right. lia. }
assert (Hsf : sk_trailer_addr + 1 <= f \/ f + FILE_BLOCK <= sk_trailer_addr).
{ destruct (Z_lt_le_dec sk_trailer_addr f) as [H1|H1]; [left; lia|]. destruct (Z_lt_le_dec sk_trailer_addr (f + FILE_BLOCK)) as [H2|H2]; [|right; lia].
exfalso. apply blocks_In in Hfin as (q & Hq & Hqin).
assert (Hrg : 0 <= sk_trailer_addr - f < FILE_BLOCK) by lia.
apply (il_blocks IMG L A mem md q FILE_BLOCK (sk_trailer_addr - f) (proj1 HH) Hqin Hrg). rewrite Hq.
replace (f + (sk_trailer_addr - f)) with sk_trailer_addr by lia. exact Htr_img. }
assert (Htrv : sk_trailer_addr = 66321) by reflexivity.
assert (Hspm : (spZ regs - 32) mod 16 = 0) by (replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
eapply SR_bind with (R := fun c' => exists regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs0_A_cgif_raw_close + 0x3c)) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWCLOSE_STK (spZ regs) ((raw, raw + RAW_SIZE) :: sink_fp f) L A mem md L A mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = Z_to_bv 64 0 /\
sink_at ubs0_msyms mem2 md2 f (S ++ sink_trailer_Z) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spZ regs - 32 - CGIF_WRITECB_STK <= x < spZ regs - 32) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
(forall a n i, In (a, n) (blocks L A) -> 0 <= i < n -> ~ inFP (sink_fp f) (a + i) ->
mbyte ubs0segs mem2 (a + i) = mbyte ubs0segs (ms_mem ms) (a + i))).
{ eapply SR_mono.
{ eapply (jcall ubs0_msyms MR) with (STK1 := CGIF_WRITECB_STK) (FP1 := sink_fp f)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) =>
L2 = L /\ A2 = A /\ getr regs2 10 = Z_to_bv 64 0 /\ sink_at ubs0_msyms mem2 md2 f (S ++ sink_trailer_Z));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | lia | rewrite Hsp; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (ubs0_cgif_writecb L A _ _ md g gvals sk_trailer_addr 1 f S sink_trailer_Z HPRE1);
[ rewrite Hsp; lia | exact Hm10 | exact Hm11 | exact Hm12 | exact Hgc | exact Hgwfn | exact Hgfile | exact Hgin | exact Hfin | exact HSKc | exact HGt
| reflexivity | lia | lia | exact Hsf | rewrite Hsp; lia | exact Hroom | lia ]. }
cbv beta. intros c' (regs2 & mem2 & md2 & -> & HJc & HP & Hr10 & HSK2).
exists L, A, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
repeat (split; [reflexivity|]). split; [exact Hr10 | exact HSK2].
- intros a Ha. split; [apply inFP_cons; right; exact Ha|]. destruct Ha as (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (-> & -> & Hr10 & HSK2)).
exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hr10|]. split; [exact HSK2|].
split.
- pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2.
- intros a n i Hin Hi Hnf. pose proof HJc2 as (_ & _ & _ & Hblk2 & _). exact (Hblk2 a n i Hin Hin Hi Hnf). }
cbv beta. intros c' (regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hr10c & HSK2 & Hhi2 & Hblk2). clear HJ.
jafter_call2 HS 58%nat regs2 mem2 HP2 (-32) [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 10 _ _ _ _ _ raw); [rewrite HE10; apply unsigned_lit_small; lia | | lia].
intros a Ha. replace a with (raw + (a - raw)) by lia. apply (Hblk2 raw RAW_SIZE (a - raw) Hrawin); [lia|].
replace (raw + (a - raw)) with a by lia.
intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; [lia|].
pose proof (heap_sep_in2 ubs0_msyms MR LAWS L A mem md (raw, RAW_SIZE) (f, FILE_BLOCK) HH Hrawin Hfin) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E; injection E as E1 E2; lia | lia | lia]. }
clear HS. rename HS2 into HS.
pin_reg' HS (10%bv:reg) 0 Hr10c.
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. jreg HS (4%bv:reg) as Hr4. jreg HS (1%bv:reg) as Hr1.
rewrite HE10 in Hr10.
cbn [ms_mem mkst] in HF0.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem2 a).
{ intros a Ha Hns. apply (mbyte_eq_of ubs0_msyms). apply HF0. rewrite unsigned_lit_small by lia.
intros (r & [<- | [<- | []]] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr.
- rewrite ew_havoc_old in Hr by (cbv; lia). rewrite HE2, Hspw in Hr. lia.
- lia. }
assert (HSKf : sink_at ubs0_msyms (ms_mem ms0) md2 f (S ++ sink_trailer_Z)).
{ apply (sink_at_frame ubs0_msyms mem2 (ms_mem ms0) md2 f _); [|exact HSK2].
intros a [Ha | Ha]; apply K2; try lia.
- pose proof (ubs0_env_addr_range a Ha). lia.
- pose proof (ubs0_env_addr_range a Ha). lia. }
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(raw, raw + RAW_SIZE)] HJ2) as HJl.
eapply SR_bind.
{ eapply (jfree _ _ LAWS ubs0_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJl | exact Hrawin | exact Hr10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; exact HE2 | exact Hspw | reflexivity | lia | lia
| exact Hr4 | rewrite HE4; exact Htp | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros _ i Hi; exists (raw, raw + RAW_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJl3 & HP3 & Hrm3 & Hkeep3 & Hhi3).
assert (HJ3 : journal ubs0_msyms MR RAWCLOSE_STK (spZ regs) ((raw, raw + RAW_SIZE) :: sink_fp f) L A mem md L3 A3 mem3 md3).
{ eapply (journal_sub ubs0_msyms MR); [exact HJ2 | exact HJl3 | lia | lia |].
intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. split; [apply inFP_cons; left; exact Hr | lia]. }
assert (HK3 : sink_at ubs0_msyms mem3 md3 f (S ++ sink_trailer_Z) /\ In (f, FILE_BLOCK) (blocks L3 A3)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJl3 | | exact Hfin | | exact HSKf].
- intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
- intros a Ha (r & [<- | []] & Hr). cbn [fst snd] in Hr.
pose proof (heap_sep_in2 ubs0_msyms MR LAWS L A mem md (raw, RAW_SIZE) (f, FILE_BLOCK) HH Hrawin Hfin) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E; injection E as E1 E2; lia | lia | lia]. }
destruct HK3 as [HSK3 Hflive3].
clear HJ2 HJl HJl3.
jafter_call2 HS 74%nat regs3 mem3 HP3 (-32) (@nil nat) HS3.
match type of HS3 with ?P -> _ => assert (HK : P); [|specialize (HS3 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havoc; rewrite HE2; exact Hspw | exact Hhi3 | lia | lia | lia | lia | lia]. }
clear HS. rename HS3 into HS.
jrun LAWS ubs0tbl_ok HS HJ3.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 74 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 58 _ _ _ ltac:(lia) (env_agree_refl _ _))) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (1%bv:reg) as Hq1.
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists L3, A3, (ms_regs msx), (ms_mem msx), md3 end.
rewrite Hq1, HE1, Hra. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HPR|].
split; [eapply perm_after_rm1; [exact HB | exact Hrm3]|].
cbn [ms_mem mkst] in HF1.
apply (sink_at_frame ubs0_msyms mem3 _ md3 f _); [|exact HSK3].
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem3 a).
{ intros a Ha Hns. apply (mbyte_eq_of ubs0_msyms). apply HF1. rewrite unsigned_lit_small by lia.
intros (r & [<- | []] & Hr); cbn [r_base r_wlo r_whi base_val] in Hr.
rewrite !ew_havoc_old in Hr by (cbv; lia). rewrite HE2, Hspw in Hr. lia. }
intros a [Ha | Ha]; apply K3; try lia.
- pose proof (ubs0_env_addr_range a Ha). lia.
- pose proof (ubs0_env_addr_range a Ha). lia.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
