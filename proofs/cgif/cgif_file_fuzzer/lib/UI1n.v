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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UI4l UI21 UI2m UI5o UI5l YI6b UI5n UI20 UI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b UI1o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_ret : sstate :=
mkSS AF_RET sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 64) (2^63 - 64) 4) ] [] []).
Definition ss_retc : sstate :=
mkSS AF_RETC sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ;
YP09.mkRegion (Some 8%nat) 88 92 88 92 [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 64) (2^63 - 64) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4) ] [] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma af_ret :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z)) (GPAL : list Z) (gs gsF : YO07.gif_st) (bF : rbound),
let sp0 := spZ regs0 in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> (forall a, inFP FP a -> inFP (cgif_fp g s0 N) a) ->
cgif_rel memc mdc s N GPAL gsF -> Z.of_nat (length (concat (YO07.s_out gsF))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N -> res_ok Ac bF ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_RET) memc (seg_rom ubs0segs)) mdc) (af_postX API regs0 g N s0 CB rest GPAL gs gsF bF L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP GPAL gs gsF bF sp0 HJ Hid Hra0 Hal16 Hat Hwf Hgeom HB HSV G2 HUT Xgen Xfile HFPX XREL XLEN XRq.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (E := Ereg regs1 (map (Z_to_bv 64) (af_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E ss_ret (mkst regs1 (Z_to_bv 64 AF_RET) memc (seg_rom ubs0segs))).
{ unfold ss_ret. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV HK (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16.
repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_RET) memc (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold af_postX.
lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), mdc, s end.
assert (HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error AF_SAVED j = Some r -> ew E n = getr regs0 r).
{ intros n j r -> Hr. rewrite (HK j _ (af_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. }
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, (HKr 32%nat 0%nat 1%bv eq_refl eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split.
{ cbn [ms_mem mkst]. eapply (journal_fp_weaken API); [exact HFPX | exact HJ]. }
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 64 + 64) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite (HKr 33%nat 1%nat 8%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 34%nat 2%nat 9%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 35%nat 3%nat 18%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 36%nat 4%nat 19%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 37%nat 5%nat 20%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 38%nat 6%nat 21%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 39%nat 7%nat 22%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27). }
split; [exact Hid|].
pose proof Hgeom as (GW & GH & GA & GR & _).
split.
{ cbn [ms_mem mkst]. lazymatch goal with |- cgif_at ?m' g s =>
eapply (cgif_at_low0 _ memc m' g s N Lc Ac memc mdc (CB ++ rest) HH0 HB Hat) end.
intros a Ha. cbn [ms_mem mkst] in HF. unfold mbyte.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
split; [exact Hwf|]. do 4 (split; [assumption|]). split; [exact Xfile|]. split; [exact HB|].
pose proof Hgeom as (_ & _ & _ & _ & GP & GN). split; [exact Xgen|]. split; [exact GN|]. split; [exact GP|].
split; [| split; [exact XLEN | exact XRq]].
cbn [ms_mem mkst]. cbn [ms_mem mkst] in HF. apply (cgif_rel_kept_all memc _ mdc s N GPAL gsF Hwf); [| exact XREL].
intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
Qed.
Lemma af_ret_cur :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z)) (GPAL : list Z) (gs gsF : YO07.gif_st) (bF : rbound),
let sp0 := spZ regs0 in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> (forall a, inFP FP a -> inFP (cgif_fp g s0 N) a) ->
rc_int (bv_unsigned (getr regs1 18) mod 2 ^ 32) = YO07.s_cur gsF -> cgif_occ s gsF ->
sink_at ubs0_msyms memc mdc (cg_file s) (concat (YO07.s_out gsF)) -> In (cg_file s, FILE_BLOCK) rest ->
(cgif_live gsF -> af_live memc s N GPAL gsF) ->
Z.of_nat (length (concat (YO07.s_out gsF))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N -> res_ok Ac bF ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_RETC) memc (seg_rom ubs0segs)) mdc) (af_postX API regs0 g N s0 CB rest GPAL gs gsF bF L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP GPAL gs gsF bF sp0 HJ Hid Hra0 Hal16 HFPg Hat Hwf Hgeom HB HSV G2 G8 HUT Xgen Xfile HFPX XCUR XOCC XSINK XFIN XLIVE XLEN XRq.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N (CB ++ rest) HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
set (E := Ereg regs1 (map (Z_to_bv 64) (af_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E ss_retc (mkst regs1 (Z_to_bv 64 AF_RETC) memc (seg_rom ubs0segs))).
{ unfold ss_retc. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV HK (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8. change (2 ^ 4) with 16.
repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_RETC) memc (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_block with (m := CGIF_SIZE);
[ reflexivity | exact HU8 | exact Hgin | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | apply wr_ok_nil ]. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold af_postX.
set (c := U E (SOff 18 0) mod 2 ^ 32).
assert (Hc18 : c = bv_unsigned (getr regs1 18) mod 2 ^ 32) by (subst c; unfold U; cbn [sv_denot]; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity).
lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), mdc, (set_cur s c) end.
assert (HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error AF_SAVED j = Some r -> ew E n = getr regs0 r).
{ intros n j r -> Hr. rewrite (HK j _ (af_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. }
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, (HKr 32%nat 0%nat 1%bv eq_refl eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split.
{ cbn [ms_mem mkst]. eapply (journal_fp_weaken API); [exact HFPX | exact HJ]. }
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 64 + 64) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite (HKr 33%nat 1%nat 8%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 34%nat 2%nat 9%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 35%nat 3%nat 18%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 36%nat 4%nat 19%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 37%nat 5%nat 20%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 38%nat 6%nat 21%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 39%nat 7%nat 22%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27). }
split; [exact Hid|].
pose proof Hgeom as (GW & GH & GA & GR & _).
split.
{ cbn [ms_mem mkst]. cbn [ms_mem mkst] in HF.
apply (cgif_at_set_cur memc _ g s c Hat).
- intros i Hi Hni. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
- intros i Hi. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
- intros f i Hin Hi. destruct (Hfgeom f Hin) as (F0 & F1 & F2). mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
- replace (g + 88) with (bv_unsigned (ew E 8) + 88) by (rewrite HU8; reflexivity).
eapply (st_chunk_lowv _ _ _ 1%nat _ 8%nat 88 4%N (SOff 18 0) _ 4%nat (2 ^ 32) HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity | reflexivity].
- pose proof (Z.mod_pos_bound (U E (SOff 18 0)) (2 ^ 32) ltac:(lia)). subst c. lia. }
split; [apply set_cur_wf; exact Hwf|]. do 4 (split; [assumption|]). split; [exact Xfile|]. split; [exact HB|].
pose proof Hgeom as (_ & _ & _ & _ & GP & GN). split; [exact Xgen|]. split; [exact GN|]. split; [exact GP|].
split; [| split; [exact XLEN | exact XRq]].
cbn [ms_mem mkst]. cbn [ms_mem mkst] in HF.
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a Hr Ha. mb_frame_with HF ltac:(exact Hr) ltac:(rewrite ?HU2, ?HU8; clear - Ha; lia). reflexivity. }
assert (HfLA : In (cg_file s, FILE_BLOCK) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; right; exact XFIN).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 HfLA) as [Rf0 Rf1].
assert (KV : forall a n k, In (a, n) (af_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs (ms_mem ms) (a + k) = mbyte ubs0segs memc (a + k)).
{ intros a n k Hin Hk. pose proof (af_vblocks_sub0 s N _ Hin) as Hin0.
assert (Hin' : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; right; right; exact Hin0).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a n HH0 Hin') as [R0 R1].
assert (HBc : Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: ((cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s)) ++ CB ++ rest)) by exact HB.
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (a, n) HH0 HBc ltac:(apply in_app_iff; left; right; exact Hin0)) as Y. cbn [fst snd] in Y.
apply KO; [clear - R0 R1 Hk Hac; lia | clear - Y Hk HGSv; lia]. }
apply (proj2 (cgif_rel_split _ _ _ _ _ _)). split; [| split].
- split; [cbn [set_cur cg_cur]; rewrite Hc18; exact XCUR | apply (proj2 (cgif_occ_set_cur _ _ _)); exact XOCC].
- cbn [set_cur cg_file]. apply (sink_at_frame ubs0_msyms memc _ mdc); [| exact XSINK].
pose proof (fl_file_sep API Lc Ac memc mdc g s N [] (CB ++ rest) g CGIF_SIZE HH0 HB ltac:(apply in_app_iff; right; exact XFIN) ltac:(left; reflexivity)) as Xs.
intros a Ha. destruct Ha as [Ha|Ha].
+ apply KO; [clear - Ha Rf0 Rf1 Hac; lia | clear - Ha Xs HGSv; lia].
+ pose proof (ubs0_env_addr_range a Ha) as Xr. pose proof (af_env_blk API IMG Lc Ac memc mdc g CGIF_SIZE a HH0 Hgin Ha) as Xe. apply KO; [clear - Xr; lia | clear - Xe HGSv; lia].
- intros Hl. apply (proj2 (af_live_set_cur _ _ _ _ _ _)). apply (af_live_kept memc _ s N GPAL gsF Hwf); [exact KV | exact (XLIVE Hl)].
Qed.
Definition ss_same (ih : Z) : sstate :=
mkSS AF_SAME (sr_set sr_atoms 20%bv (SLit ih))
[ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ;
af_Rg_part (8 * ih) (8 * ih + 8) 0 0 None None None None ;
YP09.mkRegion (Some (Z.to_nat (51 + ih))) 24 26 24 26 [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 64) (2^63 - 64) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(Z.to_nat (51 + ih), mkAF 4096 (CEIL_MAX - 40) 4) ] [] []).
Lemma af_same :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z)) (ih : nat) (fh : frame_st)
(GPAL : list Z) (gs : YO07.gif_st) (hd : YO07.frame) (fd : Z) (bF : rbound),
let sp0 := spZ regs0 in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
nth_error (cg_frames s) ih = Some (Some fh) ->
(forall a, fr_ptr fh <= a < fr_ptr fh + FRAME_SIZE -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 20 = Z_to_bv 64 (Z.of_nat ih) ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> (forall a, inFP FP a -> inFP (cgif_fp g s0 N) a) ->
rc_int (cg_cur s) = YO07.s_cur gs -> cgif_occ s gs ->
sink_at ubs0_msyms memc mdc (cg_file s) (concat (YO07.s_out gs)) -> In (cg_file s, FILE_BLOCK) rest ->
af_live memc s N GPAL gs -> (ih < 3)%nat -> qslot gs ih = Some hd ->
bv_unsigned (getr regs1 21) mod 2 ^ 16 = fd -> res_ok Ac bF ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_SAME) memc (seg_rom ubs0segs)) mdc)
(af_postX API regs0 g N s0 CB rest GPAL gs (YO07.q_set gs (Z.of_nat ih) (Some (YO07.set_delay hd fd))) bF L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP ih fh GPAL gs hd fd bF sp0 HJ Hid Hra0 Hal16 Hat Hwf Hgeom Hih HFPf HB HSV G2 G8 G20 HUT
Xgen Xfile HFPX XCUR XOCC XSINK XFIN XLIVE Hih3 Xhd Xfd XRq.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hfin : In (Some fh) (cg_frames s)) by (eapply nth_error_In; exact Hih).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N (CB ++ rest) HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom fh Hfin) as (Hf0 & Hf1 & Hfg).
pose proof (af_raw_frame_sep0 API Lc Ac memc mdc g s N (CB ++ rest) fh HH0 HB Hfin) as Hfr_raw.
destruct (af_frame_geom0 API Lc Ac memc mdc g s N (CB ++ rest) fh HH0 HB Hfin) as (Hfblk & _ & _).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE HH0 Hfblk ltac:(lia)) as (_ & _ & Hf16).
pose proof Hat as (Hobj & Hraw & Hfrs).
set (E := af_E regs1 regs0 [0; 0; 0; 0; 0; 0; 0] s []).
pose proof (af_HE regs1 regs0 0 0 0 0 0 0 0 s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 0 0 0 0 0 0 0 s [] : forall n j v, _ -> _ -> ew E n = _) as HK0.
pose proof (af_HX regs1 regs0 0 0 0 0 0 0 0 s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HK : forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; exact (HK0 _ j v eq_refl Hj)).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HUd : U E (SOff 21 0) mod 2 ^ 16 = fd).
{ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, (HE 21%nat 21%bv eq_refl), Z_to_bv_bv_unsigned. exact Xfd. }
assert (GO : forall ss ms', st_ok ubs0segs E ss ms' -> ss_pc ss = AF_RET -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (fr_ptr fh + 24 <= a < fr_ptr fh + 26) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
field_ok ubs0segs (ms_mem ms') (fr_ptr fh) (24, 2%N) fd ->
SR ubs0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 CB rest GPAL gs (YO07.q_set gs (Z.of_nat ih) (Some (YO07.set_delay hd fd))) bF L A mem md)).
{ intros ss ms' HS' Hpc Hrv Q2 Q3 Q4 Q23 Q24 Q25 Q26 Q27 HJ' KO Hfd.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
set (fh' := set_fr_delay fh fd).
assert (Hnew : obj_at ubs0segs (ms_mem ms') (fr_ptr fh') LAY_Frame (frame_vals fh')).
{ subst fh'. cbn [fr_ptr set_fr_delay].
eapply (obj_at_upd ubs0segs memc (ms_mem ms') (fr_ptr fh) LAY_Frame FRAME_SIZE (frame_vals fh) _ [4%nat] [(24, 26)] (Hfrs fh Hfin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros i Hi Hw. apply KO; [lia|]. cbn in Hw. destruct (Z.leb_spec 24 i); destruct (Z.ltb_spec i 26); cbn in Hw; try discriminate; lia.
- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-. exact Hfd.
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity. }
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_ret L A mem md regs0 rg Lc Ac mm mdc g N s0 (upd_frame s ih fh') CB rest FP GPAL gs (YO07.q_set gs (Z.of_nat ih) (Some (YO07.set_delay hd fd))) bF) end;
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | | | apply same_geom_upd_frame; exact Hgeom | | | | | exact Xgen | exact Xfile | exact HFPX | | | exact XRq ].
-
split; [|split].
-- rewrite (cgif_vals_upd_frame s ih fh fh' Hih eq_refl).
eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros i Hi. apply KO; lia.
-- cbn [upd_frame set_frames cg_raw].
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros i Hi. apply KO; lia.
-- apply (frames_at_upd memc (ms_mem ms') s ih (Some fh) fh' Hfrs Hih Hnew).
intros j x Hj Hne k Hk.
pose proof (af_frames_sep0 API Lc Ac memc mdc g s N (CB ++ rest) ih j fh x HH0 HB Hih Hj ltac:(lia)) as Hsep.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & _).
apply KO; lia.
- apply (cgif_wf_upd_frame s N ih fh fh' Hwf Hih). pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf).
apply (frame_wf_fields (cg_attr s) fh fh' (Hfwf fh Hfin)); reflexivity.
- rewrite (cgif_blocks_upd_frame0 g s N ih fh fh' Hih eq_refl). exact HB.
- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KO; lia.
- apply (RG _ _ _ Q2). rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- split; [|split; [|split; [|split; [|split; [|split]]]]].
-- apply (RG _ _ _ Q3). rewrite (HE 3%nat 3%bv eq_refl). exact G3.
-- apply (RG _ _ _ Q4). rewrite (HE 4%nat 4%bv eq_refl). exact G4.
-- apply (RG _ _ _ Q23). rewrite (HE 23%nat 23%bv eq_refl). exact G23.
-- apply (RG _ _ _ Q24). rewrite (HE 24%nat 24%bv eq_refl). exact G24.
-- apply (RG _ _ _ Q25). rewrite (HE 25%nat 25%bv eq_refl). exact G25.
-- apply (RG _ _ _ Q26). rewrite (HE 26%nat 26%bv eq_refl). exact G26.
-- apply (RG _ _ _ Q27). rewrite (HE 27%nat 27%bv eq_refl). exact G27.
-
pose proof Hwf as (Hlen & _).
assert (HfLA : In (cg_file s, FILE_BLOCK) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; right; exact XFIN).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 HfLA) as [Rf0 Rf1].
assert (KV : forall a n k, In (a, n) (af_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs (ms_mem ms') (a + k) = mbyte ubs0segs memc (a + k)).
{ intros a n k Hin Hk. pose proof (af_frame_vsep0 API Lc Ac memc mdc g s N (CB ++ rest) ih fh a n HH0 HB Hih Hin) as Y.
assert (Hin' : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; right; right; exact (af_vblocks_sub0 s N _ Hin)).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a n HH0 Hin') as [R0 R1].
apply KO; [clear - R0 R1 Hk Hac; lia | clear - Y Hk HFSv; lia]. }
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as (XH & XS).
pose proof (XS ih Hih3 I) as Xfh. rewrite (nth_error_nth _ _ None Hih), Xhd in Xfh. cbn [oframe_relb] in Xfh.
apply (proj2 (cgif_rel_split _ _ _ _ _ _)). split; [| split].
-- split; [cbn [upd_frame set_frames cg_cur]; rewrite (proj1 (q_set_fields _ _ _)); exact XCUR | apply (cgif_occ_upd s gs ih fh' _ Hih3 Hlen XOCC)].
-- cbn [upd_frame set_frames cg_file]. rewrite (proj1 (proj2 (proj2 (q_set_fields _ _ _)))).
apply (sink_at_frame ubs0_msyms memc _ mdc); [| exact XSINK].
pose proof (fl_file_sep API Lc Ac memc mdc g s N [] (CB ++ rest) (fr_ptr fh) FRAME_SIZE HH0 HB ltac:(apply in_app_iff; right; exact XFIN)
ltac:(unfold cgif_blocks0; right; right; apply in_app_iff; right; apply af_frames_blocks_ptr_in; exact Hfin)) as Xs.
intros a Ha. destruct Ha as [Ha|Ha].
++ apply KO; [clear - Ha Rf0 Rf1 Hac; lia | clear - Ha Xs HFSv; lia].
++ pose proof (ubs0_env_addr_range a Ha) as Xr. pose proof (af_env_blk API IMG Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE a HH0 Hfblk Ha) as Xe. apply KO; [clear - Xr; lia | clear - Xe HFSv; lia].
-- intros _. apply (proj2 (af_live_iff _ _ _ _ _)). split; [apply af_hdr_upd; apply (af_hdr_kept memc); [| exact XH]|].
{ intros Hz k Hk. apply (KV (cg_pal s) (3 * cg_ngp s) k); [| exact Hk]. rewrite af_vblocks_eq. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity. }
apply (af_slots_upd _ s N gs ih fh' _ (fun _ => True) Hih3 Hlen).
++ apply (af_slots_kept memc); [| eapply af_slots_mono; [| exact XS]; intros; exact I].
intros k f Hk _ Hn a n j Hin Hj. apply (KV a n j); [| exact Hj]. rewrite af_vblocks_eq. apply in_app_iff. right.
apply in_flat_map. exists (Some f). split; [rewrite <- Hn; apply nth_In; rewrite Hlen; exact Hk | exact Hin].
++ intros _.
destruct Xfh as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl).
subst fh'. unfold frame_relb, set_fr_delay, YO07.set_delay.
cbn [fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal YO07.f_attr YO07.f_gen YO07.f_delay YO07.f_nlp YO07.f_ctrans YO07.f_disp YO07.f_trans YO07.f_img YO07.f_lpal].
split; [exact A1|]. split; [exact A2|]. split; [reflexivity|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [| split; [exact Hil|]].
** eapply garr8_frame; [exact Hi|]. intros a Ha. replace a with (fr_img fh + (a - fr_img fh)) by lia. apply (KV (fr_img fh) N (a - fr_img fh)); [| lia].
rewrite af_vblocks_eq. apply in_app_iff. right. apply in_flat_map. exists (Some fh). split; [exact Hfin | left; reflexivity].
** intros H1. destruct (Hl H1) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (fr_lpal fh + (a - fr_lpal fh)) by lia. apply (KV (fr_lpal fh) (3 * fr_nlp fh) (a - fr_lpal fh)); [| lia].
rewrite af_vblocks_eq. apply in_app_iff. right. apply in_flat_map. exists (Some fh). split; [exact Hfin|]. cbn [af_fvb]. right.
destruct (Z.eqb_spec (Z.land (fr_attr fh) 1) 0); [exfalso; exact (H1 ltac:(assumption)) | left; reflexivity].
-
rewrite (proj1 (proj2 (proj2 (q_set_fields _ _ _)))). pose proof Hwf as (_ & HW1 & HH1 & HN & _).
assert (HN0 : 0 <= N) by (rewrite HN; apply Z.mul_nonneg_nonneg; lia). unfold FRAME_OUT. clear - HN0. lia. }
assert (Hcv : nth_error (cgif_vals s) ih = Some (fr_ptr fh)).
{ assert (Hn : nth ih (cg_frames s) None = Some fh) by (apply nth_error_nth; exact Hih).
destruct ih as [|[|[|ih']]]; [ | | | exfalso; lia]; cbn [cgif_vals nth_error]; rewrite Hn; reflexivity. }
assert (HUf : forall n, n = (51 + ih)%nat -> bv_unsigned (ew E n) = fr_ptr fh).
{ intros n ->. rewrite (HX (51 + ih)%nat ih (fr_ptr fh) eq_refl Hcv). apply unsigned_lit_small. lia. }
assert (HUz : bv_unsigned (ew E (Z.to_nat (51 + Z.of_nat ih))) = fr_ptr fh) by (apply HUf; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV HK (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
assert (HR1 : region_ok ubs0segs E memc (af_Rg_part (8 * Z.of_nat ih) (8 * Z.of_nat ih + 8) 0 0 None None None None)).
{ apply (af_Rg_part_ok regs1 regs0 0 0 0 0 0 0 0 s [] memc g None None None None);
[exact HU8 | lia | lia | exact Hobj | exact I | exact I | exact I | exact I | lia | lia | intros i Hi; lia]. }
assert (HR2 : region_ok ubs0segs E memc (YP09.mkRegion (Some (Z.to_nat (51 + Z.of_nat ih))) 24 26 24 26 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HUz.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE o HH0 Hfblk ltac:(lia))). }
assert (HPD : pairwise_disjoint E (ss_mem (ss_same (Z.of_nat ih)))).
{ cbn [ss_mem ss_same pairwise_disjoint all_disjoint]. unfold af_Rg_part, extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HUz. clear - Hfg Hf1 Hg1 Hceil Hih3 HASv HGSv HFSv Hac Hstk0. repeat split; lia. }
assert (HFA : atoms_ok E [ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 64) (2^63 - 64) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(Z.to_nat (51 + Z.of_nat ih), mkAF 4096 (CEIL_MAX - 40) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HUz. change (2 ^ 4) with 16.
repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HRG : regs_ok E (sr_set sr_atoms 20%bv (SLit (Z.of_nat ih))) regs1).
{ apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; exact G20]. }
assert (HWF : regions_wf (ss_mem (ss_same (Z.of_nat ih))) = true).
{ destruct ih as [|[|[|ih']]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia]. }
assert (HS : st_ok ubs0segs E (ss_same (Z.of_nat ih)) (mkst regs1 (Z_to_bv 64 AF_SAME) memc (seg_rom ubs0segs))).
{ unfold ss_same. apply entry_st_ok_full; [exact HRG | exact HWF | constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]] | exact HPD | split; [exact HFA | split; exact I]]. }
clear HR0 HR1 HR2 HPD HFA HRG HWF.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_SAME) memc (seg_rom ubs0segs))) in HJ.
destruct ih as [|[|[|ih']]]; [ | | | exfalso; lia ];
(pose proof (HUf _ eq_refl) as HUf'; cbn [Nat.add] in HUf';
jrun_to LAWS ubs0tbl_ok HS HJ AF_RET;
[ apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|];
eapply wr_ok_cons_block with (m := FRAME_SIZE);
[ reflexivity | exact HUf' | exact Hfblk | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPf; lia | apply wr_ok_nil ]
| cbn [ms_mem mkst] in HF;
eapply (GO _ _ HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact HJ
| intros a Hr Ha; mb_frame_with HF ltac:(exact Hr) ltac:(rewrite ?HU2, ?HU8, ?HUf'; clear - Ha; lia); reflexivity
| rewrite <- HUd; eapply (st_field_low ubs0segs _ _ _ 2%nat _ _ _ 24 2%N (SOff 21 0) _ HS); [reflexivity | reflexivity | cbv; auto 10 | exact HUf' | cbn; lia | reflexivity] ] ]).
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
