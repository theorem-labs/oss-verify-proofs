(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI39 YI1i YI20 YI59 YI56 YI0x YI57
YI1h YI1g YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_ret : sstate :=
mkSS AF_RET sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 96 0 0 (af_stk_chunks 32) ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 96) (2^63 - 96) 4) ] [] []).
Definition ss_retc : sstate :=
mkSS AF_RETC sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 96 0 0 (af_stk_chunks 32) ;
YQ0b.mkRegion (Some 8%nat) 88 92 88 92 [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 96) (2^63 - 96) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4) ] [] []).
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Lemma af_ret :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z)),
let sp0 := spZ regs0 in
journal src2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 96) ->
af_untouched regs0 regs1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_RET) memc (seg_rom src2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP sp0 HJ Hid Hra0 Hal16 Hat Hwf Hgeom HB HSV G2 HUT.
pose proof HUT as (G3 & G4 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (E := Ereg regs1 (map (Z_to_bv 64) (af_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E ss_ret (mkst regs1 (Z_to_bv 64 AF_RET) memc (seg_rom src2segs))).
{ unfold ss_ret. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV HK (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16.
repeat split; try lia.
replace (sp0 - 96) with (sp0 + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_RET) memc (seg_rom src2segs))) in HJ.
jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold af_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), mdc, s end.
assert (HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error AF_SAVED j = Some r -> ew E n = getr regs0 r).
{ intros n j r -> Hr. rewrite (HK j _ (af_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. }
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg src2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, (HKr 32%nat 0%nat 1%bv eq_refl eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split.
{ cbn [ms_mem mkst]. exact HJ. }
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 96 + 96) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite (HKr 33%nat 1%nat 8%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 34%nat 2%nat 9%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 35%nat 3%nat 18%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 36%nat 4%nat 19%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 37%nat 5%nat 20%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 38%nat 6%nat 21%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 39%nat 7%nat 22%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 40%nat 8%nat 23%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 41%nat 9%nat 24%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 42%nat 10%nat 25%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27). }
split; [exact Hid|].
pose proof Hgeom as (GW & GH & GA & GR & _).
split.
{ cbn [ms_mem mkst]. lazymatch goal with |- cgif_at ?m' g s =>
eapply (cgif_at_low _ memc m' g s N Lc Ac memc mdc (CB ++ rest) HH0 HB Hat) end.
intros a Ha. cbn [ms_mem mkst] in HF. unfold mbyte.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
split; [exact Hwf|]. do 4 (split; [assumption|]). exact HB.
Qed.
Lemma af_ret_cur :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z)),
let sp0 := spZ regs0 in
journal src2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 96) -> getr regs1 8 = Z_to_bv 64 g ->
af_untouched regs0 regs1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_RETC) memc (seg_rom src2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP sp0 HJ Hid Hra0 Hal16 HFPg Hat Hwf Hgeom HB HSV G2 G8 HUT.
pose proof HUT as (G3 & G4 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (af_cgif_geom API Lc Ac memc mdc g s N (CB ++ rest) HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
set (E := Ereg regs1 (map (Z_to_bv 64) (af_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E ss_retc (mkst regs1 (Z_to_bv 64 AF_RETC) memc (seg_rom src2segs))).
{ unfold ss_retc. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV HK (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8. change (2 ^ 4) with 16.
repeat split; try lia.
replace (sp0 - 96) with (sp0 + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_RETC) memc (seg_rom src2segs))) in HJ.
jrun LAWS src2tbl_ok HS HJ.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_block with (m := CGIF_SIZE);
[ reflexivity | exact HU8 | exact Hgin | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | apply wr_ok_nil ]. }
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold af_post.
set (c := U E (SOff 19 0) mod 2 ^ 32).
lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), mdc, (set_cur s c) end.
assert (HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error AF_SAVED j = Some r -> ew E n = getr regs0 r).
{ intros n j r -> Hr. rewrite (HK j _ (af_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. }
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg src2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, (HKr 32%nat 0%nat 1%bv eq_refl eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split.
{ cbn [ms_mem mkst]. exact HJ. }
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 96 + 96) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite (HKr 33%nat 1%nat 8%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 34%nat 2%nat 9%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 35%nat 3%nat 18%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 36%nat 4%nat 19%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 37%nat 5%nat 20%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 38%nat 6%nat 21%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 39%nat 7%nat 22%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 40%nat 8%nat 23%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 41%nat 9%nat 24%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 42%nat 10%nat 25%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
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
eapply (st_chunk_lowv _ _ _ 1%nat _ 8%nat 88 4%N (SOff 19 0) _ 4%nat (2 ^ 32) HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity | reflexivity].
- pose proof (Z.mod_pos_bound (U E (SOff 19 0)) (2 ^ 32) ltac:(lia)). subst c. lia. }
split; [apply set_cur_wf; exact Hwf|]. do 4 (split; [assumption|]). rewrite set_cur_blocks. exact HB.
Qed.
Definition ss_same : sstate :=
mkSS AF_SAME sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 96 0 0 (af_stk_chunks 32) ;
YQ0b.mkRegion (Some 18%nat) 24 26 24 26 [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 96) (2^63 - 96) 4) ] [] []).
Lemma af_same :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z)) (ih : nat) (fh : frame_st),
let sp0 := spZ regs0 in
journal src2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
nth_error (cg_frames s) ih = Some (Some fh) ->
(forall a, fr_ptr fh <= a < fr_ptr fh + FRAME_SIZE -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 96) -> getr regs1 18 = Z_to_bv 64 (fr_ptr fh) ->
af_untouched regs0 regs1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_SAME) memc (seg_rom src2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP ih fh sp0 HJ Hid Hra0 Hal16 Hat Hwf Hgeom Hih HFPf HB HSV G2 G18 HUT.
pose proof HUT as (G3 & G4 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hfin : In (Some fh) (cg_frames s)) by (eapply nth_error_In; exact Hih).
destruct (af_cgif_geom API Lc Ac memc mdc g s N (CB ++ rest) HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom fh Hfin) as (Hf0 & Hf1 & Hfg).
pose proof (af_raw_frame_sep API Lc Ac memc mdc g s N (CB ++ rest) fh HH0 HB Hfin) as Hfr_raw.
destruct (af_frame_geom API Lc Ac memc mdc g s N (CB ++ rest) fh HH0 HB Hfin) as (Hfblk & _ & _).
pose proof Hat as (Hobj & Hraw & Hfrs).
set (E := Ereg regs1 (map (Z_to_bv 64) (af_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr fh) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E ss_same (mkst regs1 (Z_to_bv 64 AF_SAME) memc (seg_rom src2segs))).
{ unfold ss_same. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV HK (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE o HH0 Hfblk ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16.
repeat split; try lia.
replace (sp0 - 96) with (sp0 + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_SAME) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ AF_RET.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_block with (m := FRAME_SIZE);
[ reflexivity | exact HU18 | exact Hfblk | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPf; lia | apply wr_ok_nil ]. }
cbn [ms_mem mkst] in HF.
set (d' := U E (SOff 22 0) mod 2 ^ 16).
set (fh' := set_fr_delay fh d').
assert (Hnew : obj_at src2segs (ms_mem ms) (fr_ptr fh') LAY_Frame (frame_vals fh')).
{ subst fh'. cbn [fr_ptr set_fr_delay].
eapply (obj_at_upd src2segs memc (ms_mem ms) (fr_ptr fh) LAY_Frame FRAME_SIZE (frame_vals fh) _ [4%nat] [(24, 26)] (Hfrs fh Hfin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros i Hi Hw. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU18; cbn in Hw; first [lia | destruct (Z.leb_spec 24 i); destruct (Z.ltb_spec i 26); cbn in Hw; try discriminate; lia]). reflexivity.
- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
rewrite <- HU18. eapply (st_field_low src2segs _ _ _ 1%nat _ 18%nat _ 24 2%N (SOff 22 0) _ HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity].
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_same].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_ret L A mem md regs0 rg Lc Ac mm mdc g N s0 (upd_frame s ih fh') CB rest FP) end;
[ exact HJ | exact Hid | exact Hra0 | exact Hal16 | | | apply same_geom_upd_frame; exact Hgeom | | | | ].
-
split; [|split].
+ rewrite (cgif_vals_upd_frame s ih fh fh' Hih eq_refl).
eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros i Hi. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU18; lia). reflexivity.
+ cbn [upd_frame set_frames cg_raw].
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros i Hi. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU18; lia). reflexivity.
+ apply (frames_at_upd memc (ms_mem ms) s ih (Some fh) fh' Hfrs Hih Hnew).
intros j x Hj Hne k Hk.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) ih j fh x HH0 HB Hih Hj ltac:(lia)) as Hsep.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & _).
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU18; lia). reflexivity.
- apply (cgif_wf_upd_frame s N ih fh fh' Hwf Hih). pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf).
apply (frame_wf_fields (cg_attr s) fh fh' (Hfwf fh Hfin)); reflexivity.
- rewrite (cgif_blocks_upd_frame g s N ih fh fh' Hih eq_refl). exact HB.
- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU18; lia). reflexivity.
- reg_nowF HS ltac:(rewrite HU2; reflexivity).
- split; [|split; [|split]].
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
