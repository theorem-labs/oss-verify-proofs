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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m
YI00 YI02 YI01 YI03 YI04 YI5a UI1e UI2m UI26 UI2r
UI2s UI36 UI38 UI34 UI2y.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma ra_t2_lct456 :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) -> c_slct cx <> 0 -> c_slct cx <= 2 ^ p -> (p = 4 \/ p = 5 \/ p = 6) ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (bb, Lbb) ->
word_mem ubs2segs mem2 (c_sp cx + 8) bb -> val_mem ubs2segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs2_msyms 12 regs0 mem2 (spZ regs0) ->
SR ubs2segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) md2)
(at_T3 API cx L A mem md regs0).
Proof.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M Hcx HO HJ Hid HB HR G23 G24 G22 Hnz Hsk Hpc HB2 Hwt W32 W40 HM Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hbbin : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 bb Lbb HH2 Hbbin ltac:(lia)) as (Hbb0 & Hbb1 & _).
set (M' := M mod 2 ^ 32).
pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)) as HM'. fold M' in HM'.
assert (W40' : val_mem ubs2segs mem2 (c_sp cx + 16) 4 M') by (subst M'; change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)); apply (proj1 (val_mem_mod _ _ _ _)); exact W40).
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [bb; M'])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs2 cx (c_rcur cx) [bb; M']) as HX. pose proof (E_rv regs2 cx (c_rcur cx) [bb; M']) as HY. rewrite <- HE0 in HX, HY.
pose proof (E_morev regs2 cx (c_rcur cx) [bb; M'] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (CASE : forall pl K : Z, p = pl -> K = 2 ^ pl -> 1 <= c_slct cx <= K -> K <= 256 ->
(forall E0, st_ok ubs2segs E0 (ssT2l pl K) (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) -> E0 = E ->
SR ubs2segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) md2) (at_T3 API cx L A mem md regs0)) ->
SR ubs2segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) md2) (at_T3 API cx L A mem md regs0)).
{ intros pl K Hpl HK Hsk2 HK2 RUN. apply (RUN E); [|reflexivity]. subst E. unfold ssT2l.
apply (ra_st_ok cx (c_rcur cx) regs2 [bb; M'] mem2 PC_T2 _ false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite G24, Hpl; reflexivity]
| intros X; discriminate X | cbn [sv_denot]; rewrite G22, HE9, unsigned_lit_small by lia; reflexivity].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE23, HE40, HE70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs))) in HJ.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs))) in HJ.
destruct Hpc as [Hp | [Hp | Hp]]; rewrite Hp in Hsk; cbn in Hsk.
- lct_run API IMG LAWS 4 16 CASE HJ Hid HE HE0 HE2 HE8 HE40 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS regs2 cx R2 R8 R4 R3 R27 Htpv Hcx Hspal Hg0 Hg1 Hg16 Hfile Hwfn Hsp063.
- lct_run API IMG LAWS 5 32 CASE HJ Hid HE HE0 HE2 HE8 HE40 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS regs2 cx R2 R8 R4 R3 R27 Htpv Hcx Hspal Hg0 Hg1 Hg16 Hfile Hwfn Hsp063.
- lct_run API IMG LAWS 6 64 CASE HJ Hid HE HE0 HE2 HE8 HE40 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS regs2 cx R2 R8 R4 R3 R27 Htpv Hcx Hspal Hg0 Hg1 Hg16 Hfile Hwfn Hsp063.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
