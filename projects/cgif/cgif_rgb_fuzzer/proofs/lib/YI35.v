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
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3m
YI00 YI02 YI01 YI03 YI04 YI1e YI2m YI26 YI2r
YI2s YI37.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ssC0 : sstate :=
ra_ss PC_C (sr_set sr_atoms 10%bv (SLit 0)) [] false
[(18%nat, mkAF 3 9 0); (23%nat, mkAF 4 256 0); (11%nat, mkAF 1 65535 0); (13%nat, mkAF 1 65535 0)] [] [].
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Definition at_OK (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (p : Z) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (bb Lbb M : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 PC_OK) mem2 (seg_rom src2segs)) md2 /\
journal src2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
ra_regs regs2 cx /\ getr regs2 21 = Z_to_bv 64 (c_slct cx) /\ getr regs2 22 = Z_to_bv 64 p /\
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (bb, Lbb) /\
word_mem src2segs mem2 (c_sp cx + 8) bb /\ val_mem src2segs mem2 (c_sp cx + 16) 4 M /\ 1 <= M <= Lbb /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN src2_msyms 10 regs0 mem2 (spZ regs0).
Lemma rodata_ok_of_heap : forall L1 A1 m1 md1, heap_ok MR L1 A1 m1 md1 -> lzw_rodata_ok m1.
Proof.
intros L1 A1 m1 md1 HH i Hi. apply (il_rodata IMG L1 A1 m1 md1 _ (proj1 HH)).
change (ms_debruijn src2_msyms) with src2_D_debruijn32. unfold src2_D_debruijn32, src2_D_const_u64_0x0101010101010102. lia.
Qed.
Lemma ra_plain : lzw_spec API ->
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (p icl idl : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal src2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> Permutation (blocks L1 A1) (blocks L A) -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs1 cx -> getr regs1 21 = Z_to_bv 64 (c_slct cx) ->
getr regs1 10 = Z_to_bv 64 0 -> getr regs1 22 = Z_to_bv 64 p ->
getr regs1 18 = Z_to_bv 64 icl -> getr regs1 23 = Z_to_bv 64 idl -> 3 <= icl <= 9 -> 4 <= idl <= 256 ->
getr regs1 11 = Z_to_bv 64 (c_w cx) -> getr regs1 13 = Z_to_bv 64 (c_h cx) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN src2_msyms 10 regs0 mem1 (spZ regs0) ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom src2segs)) md1)
(fun c' => ra_post API cx L A mem md regs0 c' \/ at_OK cx L A mem md regs0 p c').
Proof.
intros LZW cx L A mem md L1 A1 md1 regs0 regs1 mem1 p icl idl Hcx HO HJ Hid HB1 HB HR G21 G10 G22 G18 G23 Hicl Hidl G11 G13 Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HLSv : YI2m.LZW_STK = 8400) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R25 & R26 & R27).
pose proof HJ as (HH1 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hgin : In (c_g cx, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
assert (Himgin : In (c_img cx, c_Nimg cx) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]).
assert (Hrawin1 : In (c_raw cx, 48) (blocks L1 A1)) by (rewrite <- HRSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Hrawin]).
assert (Hgin1 : In (c_g cx, 96) (blocks L1 A1)) by (rewrite <- HGSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Hgin]).
assert (Himgin1 : In (c_img cx, c_Nimg cx) (blocks L1 A1)) by (eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Himgin]).
assert (HnP1 : 1 <= c_w cx * c_h cx) by nia.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. pose proof (E_rv regs1 cx (c_rcur cx) []) as HY. rewrite <- HE0 in HX, HY.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE21 : ew E 21 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE22 : ew E 22 = Z_to_bv 64 p) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE18 : ew E 18 = Z_to_bv 64 icl) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE23 : ew E 23 = Z_to_bv 64 idl) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE11 : ew E 11 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE13 : ew E 13 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 13%nat 13%bv eq_refl); exact G13).
assert (HE33 : ew E 33 = Z_to_bv 64 (c_img cx)) by (apply (HX 1%nat); reflexivity).
pose proof (bv_unsigned_in_range 64 (getr regs0 3)) as Rgp. change (bv_modulus 64) with (2 ^ 64) in Rgp.
assert (HS : st_ok src2segs E ssC0 (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom src2segs))).
{ subst E. unfold ssC0.
apply (ra_st_ok cx (c_rcur cx) regs1 [] mem1 PC_C _ false [] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact G10].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE18, HE23, HE11, HE13, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_LZW_GenerateStream; [eapply ra_wr_ok; [exact HE2 | lia | lia | left; cbn; lia]|].
jreg HS (10%bv:reg) as A10. cbn [sv_denot] in A10. rewrite HE2 in A10.
pose proof (st_ok_reg _ _ _ _ (11%bv:reg) HS) as A11. eval_sr_get_in A11. rewrite denot_lit_U in A11.
rewrite (U_mulw_small _ _ _ (c_h cx) (c_w cx) (U_atom _ 13 _ HE13 ltac:(lia)) (U_atom _ 11 _ HE11 ltac:(lia))) in A11 by lia.
replace (c_h cx * c_w cx) with (c_nP cx) in A11 by (unfold c_nP; lia).
jreg HS (12%bv:reg) as A12. rewrite HE33 in A12.
jreg HS (13%bv:reg) as A13. rewrite HE23 in A13.
jreg HS (14%bv:reg) as A14. rewrite HE18 in A14.
jreg HS (1%bv:reg) as Ara. jreg HS (2%bv:reg) as Asp. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in Asp.
jreg HS (4%bv:reg) as A4. rewrite (HE 4%nat 4%bv eq_refl), R4, Htpv in A4.
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [3; 8; 9; 21; 22; 25; 26; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ : forall a, ~ (c_sp cx - 16 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte src2segs (ms_mem ms) a = mbyte src2segs mem1 a).
{ intros a Hna Ha. mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (Hobjs' : objs_at (ms_mem ms) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ; lia. }
assert (HFS' : frame_savedN src2_msyms 10 regs0 (ms_mem ms) (spZ regs0)).
{ eapply (frame_savedN_kept src2_msyms 10); [lia | exact HFS|]. intros a Ha. apply MEQ; lia. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
assert (Hsp_l : spZ (ms_regs ms) = c_sp cx) by (unfold spZ; rewrite Asp; apply unsigned_lit_small; lia).
eapply SR_bind.
{ unfold lzw_spec in LZW.
eapply (LZW RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 (ms_mem ms) md1 (ms_regs ms)
(c_sp cx + 8) (c_nP cx) (c_img cx) idl icl (c_img cx) (c_Nimg cx));
rewrite ?Hsp_l; try first [exact HJ | exact Hid | exact A10 | exact A11 | exact A12 | exact A13 | exact A14 | exact A4 | exact Himgin1].
- rewrite Ara. apply ret_ok_even. vm_compute. reflexivity.
- exact Hspal.
- lia.
- lia.
- lia.
- replace (c_sp cx + 8) with (c_sp cx + 1 * 8) by lia. rewrite Z.mod_add by lia.
rewrite (Znumtheory.Zmod_div_mod 8 16 (c_sp cx)); [rewrite Hspal; reflexivity | lia | lia | exists 2; reflexivity].
- unfold c_nP. lia.
- lia.
- lia.
- lia.
- unfold c_nP. lia.
- eapply rodata_ok_of_heap. exact (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & MHI & MBL & Hcase).
rewrite Hsp_l in MHI. rewrite Ara.
jafter_call_keep HS 69%nat regs2 mem2 HP2 [1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKr : P); [|specialize (HS2 HKr); clear HKr] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_pointwise src2segs _ _ _ 9); [rewrite HE9; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. apply MHI; lia.
- eapply (region_kept_block_ro src2segs _ _ _ 8); [rewrite HE8; apply unsigned_lit_small; lia | exact Hrawin1 | exact MBL | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro src2segs _ _ _ 44); [rewrite HE44; apply unsigned_lit_small; lia | exact Hgin1 | exact MBL | cbn; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (Hobjs2 : objs_at mem2 cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs' | | |]; intros i Hi.
- apply MHI; lia.
- apply (MBL _ _ i Hrawin1). lia.
- apply (MBL _ _ i Hgin1). lia. }
assert (HFS2 : frame_savedN src2_msyms 10 regs0 mem2 (spZ regs0)).
{ eapply (frame_savedN_kept src2_msyms 10); [lia | exact HFS'|]. intros a Ha. apply MHI; lia. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (RA0 + 0x178)) mem2 (seg_rom src2segs))) in HJ2.
destruct Hcase as [(-> & bb & Lbb & M & HB2 & Hw & W1 & W2 & HM) | (Hres & HB2 & HpR)].
-
pin_reg' HS (10%bv:reg) 0 Hres10.
jrun_to LAWS src2tbl_ok HS HJ2 PC_OK.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. right.
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 9; 21; 22; 25; 26; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HK3.
cbn [ms_regs mkst] in HK3.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs mem2 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
exists L2, A2, (ms_regs ms0), (ms_mem ms0), md2, bb, Lbb, M.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split. { unfold ra_regs. rewrite !HK3 by (cbv; tauto). exact HR. }
split; [rewrite HK3 by (cbv; tauto); exact G21|].
split; [rewrite HK3 by (cbv; tauto); exact G22|].
split. { eapply Permutation_trans; [exact HB2|]. apply perm_skip. exact HB1. }
split; [exact Hw|].
split. { intros k Hk. rewrite MEQ3 by lia. apply W1. exact Hk. }
split. { intros k Hk. rewrite MEQ3 by lia. replace (c_sp cx + 16) with (c_sp cx + 8 + 8) by lia. apply W2. exact Hk. }
split; [exact HM|].
split. { eapply objs_at_kept; [exact Hobjs2 | | |]; intros i Hi; apply MEQ3; lia. }
eapply (frame_savedN_kept src2_msyms 10); [lia | exact HFS2|]. intros a Ha. apply MEQ3; lia.
-
jreg HS (10%bv:reg) as P10. cbn [ms_regs mkst] in P10. rewrite Hres10 in P10. symmetry in P10.
add_fact' HS 73%nat (mkAF 2 5 0). 2:{ rewrite P10, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
jrun_to LAWS src2tbl_ok HS HJ2 PC_ST.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 25; 26; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HK3.
cbn [ms_regs mkst] in HK3.
jreg HS (18%bv:reg) as Q18. cbn [ms_regs mkst] in Q18.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs mem2 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono; [| cbv beta; intros c' Hc'; left; exact Hc'].
eapply (ra_st API IMG cx L A mem md L2 A2 md2 regs0 (ms_regs ms0) (ms_mem ms0) (c_rcur cx));
[ exact (proj1 Hcx) | exact HO | exact HJ2 | exact Hid2 | | exact Hrawin | | | | | | | | | | exact Q18 ]; cbn [ms_regs ms_mem].
+ eapply Permutation_trans; [exact HB2 | exact HB1].
+ eapply obj_at_transport_range; [exact (proj1 (proj2 Hobjs2)) | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply MEQ3. lia.
+ eapply (frame_savedN_kept src2_msyms 10); [lia | exact HFS2|]. intros a Ha. apply MEQ3; lia.
+ rewrite HK3 by (cbv; tauto). exact R2.
+ rewrite HK3 by (cbv; tauto). rewrite R3, Hgp0. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R4, Htp0. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R25, H25o. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R26, H26o. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R27, H27o. reflexivity.
+ rewrite HK3 by (cbv; tauto). exact R8.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
