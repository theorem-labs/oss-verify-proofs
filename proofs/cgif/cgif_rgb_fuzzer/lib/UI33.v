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
YI00 YI02 YI01 YI03 YI04 UI1e UI2m UI26 UI2r
UI2s UI36.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ssB (lct : bool) : sstate :=
ra_ss PC_B (sr_set sr_atoms 11%bv (if lct then SOff 9%nat 30 else SOff 8%nat 32)) [] false
[(40%nat, mkAF 0 256 0); (19%nat, mkAF 0 (2^32-1) 0)] [] [].
Definition ssIC (fs : list (nat * afact)) : sstate := ra_ss PC_IC sr_atoms [] false fs [] [].
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition at_IC (cx : ra_cx) L A mem md L1 A1 md1 (regs0 : bvmap 5 word) (p : Z) (c' : config) : Prop :=
exists regs1 mem1 (ne : Z),
c' = mkCfg (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs2segs)) md1 /\
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 /\
ra_regs regs1 cx /\ getr regs1 23 = Z_to_bv 64 (c_slct cx) /\ getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs1 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2) /\ getr regs1 24 = Z_to_bv 64 p /\
getr regs1 11 = Z_to_bv 64 ne /\ 0 <= ne <= 256 /\
objs_at mem1 cx (c_rcur cx) /\ frame_savedN ubs2_msyms 12 regs0 mem1 (spZ regs0).
Definition at_C (cx : ra_cx) L A mem md L1 A1 md1 (regs0 : bvmap 5 word) (p : Z) (c' : config) : Prop :=
exists regs1 mem1 (icl idl : Z),
c' = mkCfg (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs2segs)) md1 /\
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 /\
ra_regs regs1 cx /\ getr regs1 23 = Z_to_bv 64 (c_slct cx) /\ getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs1 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2) /\ getr regs1 24 = Z_to_bv 64 p /\
getr regs1 18 = Z_to_bv 64 icl /\ getr regs1 25 = Z_to_bv 64 idl /\ 3 <= icl <= 9 /\ 4 <= idl <= 256 /\
getr regs1 13 = Z_to_bv 64 (c_w cx) /\ getr regs1 14 = Z_to_bv 64 (c_h cx) /\
objs_at mem1 cx (c_rcur cx) /\ frame_savedN ubs2_msyms 12 regs0 mem1 (spZ regs0).
Lemma ra_neff :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (p : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
ra_regs regs1 cx -> getr regs1 19 = Z_to_bv 64 (c_fattr cx) -> getr regs1 23 = Z_to_bv 64 (c_slct cx) ->
getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) -> getr regs1 24 = Z_to_bv 64 p ->
getr regs1 11 = Z_to_bv 64 (if c_slct cx =? 0 then c_raw cx + 32 else c_cfp cx + 30) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs2_msyms 12 regs0 mem1 (spZ regs0) ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom ubs2segs)) md1)
(at_IC cx L A mem md L1 A1 md1 regs0 p).
Proof.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 p Hcx HO HJ HR G19 G23 G22 G24 G11 Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hstw. cbn beta in Hstw.
pose proof (Z_land_upper (c_fattr cx) 2 ltac:(lia)) as Hil1.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. pose proof (E_rv regs1 cx (c_rcur cx) []) as HY. rewrite <- HE0 in HX, HY.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE19 : ew E 19 = Z_to_bv 64 (c_fattr cx)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE22 : ew E 22 = Z_to_bv 64 (c_cfp cx + 30)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE24 : ew E 24 = Z_to_bv 64 p) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE42 : ew E 42 = Z_to_bv 64 (c_tidx cx)) by (apply (HX 10%nat); reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 (c_sgct cx)) by (apply (HY 6%nat); reflexivity).
assert (MKS : forall lct : bool, (if lct then c_slct cx <> 0 else c_slct cx = 0) ->
st_ok ubs2segs E (ssB lct) (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom ubs2segs))).
{ intros lct Hlct. subst E. unfold ssB.
apply (ra_st_ok cx (c_rcur cx) regs1 [] mem1 PC_B _ false [] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
cbn [sv_denot]. rewrite G11. destruct lct; cbn [sv_denot]; [rewrite HE9 | rewrite HE8]; rewrite unsigned_lit_small by lia;
destruct (Z.eqb_spec (c_slct cx) 0); first [reflexivity | lia].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE40, HE19, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom ubs2segs))) in HJ.
Ltac wr HE2 := eapply ra_wr_ok; [ew_havoc; exact HE2 | lia | lia | left; cbn; lia].
Ltac finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS ne netac :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch goal with |- at_IC _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx), ne end;
split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ|];
split; [ split; [| split; [| split; [|split; [|split]]]];
[ let Q := fresh "Q" in (jreg HS (2%bv:reg) as Q); rewrite Q, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity
| let Q := fresh "Q" in (jreg HS (8%bv:reg) as Q); rewrite Q; exact HE8
| let Q := fresh "Q" in (jreg HS (9%bv:reg) as Q); rewrite Q; exact HE9
| let Q := fresh "Q" in (jreg HS (4%bv:reg) as Q); rewrite Q, (HE 4%nat 4%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (3%bv:reg) as Q); rewrite Q, (HE 3%nat 3%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (27%bv:reg) as Q); rewrite Q, (HE 27%nat 27%bv eq_refl); assumption ] |];
split; [let Q := fresh "Q" in (jreg HS (23%bv:reg) as Q); rewrite Q; exact HE23|];
split; [let Q := fresh "Q" in (jreg HS (22%bv:reg) as Q); rewrite Q; exact HE22|];
split; [let Q := fresh "Q" in
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_reg segs E1 ss1 ms1 (10%bv:reg) HS) as Q; eval_sr_get_in Q;
rewrite denot_lit_U in Q; cbn [ms_regs mkst] in Q; rewrite Q; f_equal;
rewrite U_and_lit by lia; rewrite (U_atom _ 19 _ HE19) by lia; reflexivity end|];
split; [let Q := fresh "Q" in (jreg HS (24%bv:reg) as Q); rewrite Q; exact HE24|];
split; [let Q := fresh "Q" in (jreg HS (11%bv:reg) as Q); rewrite Q; cbn [sv_denot]; netac |];
split; [lia|];
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
| eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H) ].
Ltac tests HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 HE42 Hobjs HFS cx ne0 HEne0 :=
jrun_to LAWS ubs2tbl_ok HS HJ PC_IC; [wr HE2|];
jbranch ubs2tbl HS;
[ jrun_to LAWS ubs2tbl_ok HS HJ PC_IC; [wr HE2|]; finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS ne0 ltac:(rewrite HEne0; reflexivity)
| jrun_to LAWS ubs2tbl_ok HS HJ PC_IC; [wr HE2|];
jbranch ubs2tbl HS;
[ jrun_to LAWS ubs2tbl_ok HS HJ PC_IC; [wr HE2|]; finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS ne0 ltac:(rewrite HEne0; reflexivity)
| jrun_to LAWS ubs2tbl_ok HS HJ PC_IC; [wr HE2|];
jbranch ubs2tbl HS;
[ jrun_to LAWS ubs2tbl_ok HS HJ PC_IC; [wr HE2|]; finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS ne0 ltac:(rewrite HEne0; reflexivity)
| jrun_to LAWS ubs2tbl_ok HS HJ PC_IC; [wr HE2|];
finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS (c_tidx cx + 1) ltac:(rewrite HE42, unsigned_lit_small by lia; reflexivity) ] ] ].
destruct (Z.eq_dec (c_slct cx) 0) as [Hz | Hnz].
- pose proof (MKS false Hz) as HS. clear MKS.
tests HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 HE42 Hobjs HFS cx (c_sgct cx) HE49.
- pose proof (MKS true Hnz) as HS. clear MKS.
tests HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 HE42 Hobjs HFS cx (c_slct cx) HE40.
Qed.
Lemma ra_icl :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (p ne : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
ra_regs regs1 cx -> getr regs1 23 = Z_to_bv 64 (c_slct cx) -> getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) ->
getr regs1 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2) -> getr regs1 24 = Z_to_bv 64 p ->
getr regs1 11 = Z_to_bv 64 ne -> 0 <= ne <= 256 ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs2_msyms 12 regs0 mem1 (spZ regs0) ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs2segs)) md1)
(at_C cx L A mem md L1 A1 md1 regs0 p).
Proof.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 p ne Hcx HO HJ HR G23 G22 G10 G24 G11 Hne Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hstw. cbn beta in Hstw.
pose proof (Z_land_upper (c_fattr cx) 2 ltac:(lia)) as Hil1.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. rewrite <- HE0 in HX.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE10 : ew E 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE22 : ew E 22 = Z_to_bv 64 (c_cfp cx + 30)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE24 : ew E 24 = Z_to_bv 64 p) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE11 : ew E 11 = Z_to_bv 64 ne) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (c_h cx)) by (apply (HX 4%nat); reflexivity).
assert (MKS : forall lo hi, lo <= ne <= hi ->
st_ok ubs2segs E (ssIC [(11%nat, mkAF lo hi 0)]) (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs2segs))).
{ intros lo hi Hlh. subst E. unfold ssIC.
apply (ra_st_ok cx (c_rcur cx) regs1 [] mem1 PC_IC sr_atoms false [] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE11, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs2segs))) in HJ.
Ltac finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS icl idl :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch goal with |- at_C _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx), icl, idl end;
split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ|];
split; [ split; [| split; [| split; [|split; [|split]]]];
[ let Q := fresh "Q" in (jreg HS (2%bv:reg) as Q); rewrite Q, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity
| let Q := fresh "Q" in (jreg HS (8%bv:reg) as Q); rewrite Q; exact HE8
| let Q := fresh "Q" in (jreg HS (9%bv:reg) as Q); rewrite Q; exact HE9
| let Q := fresh "Q" in (jreg HS (4%bv:reg) as Q); rewrite Q, (HE 4%nat 4%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (3%bv:reg) as Q); rewrite Q, (HE 3%nat 3%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (27%bv:reg) as Q); rewrite Q, (HE 27%nat 27%bv eq_refl); assumption ] |];
split; [let Q := fresh "Q" in (jreg HS (23%bv:reg) as Q); rewrite Q; exact HE23|];
split; [let Q := fresh "Q" in (jreg HS (22%bv:reg) as Q); rewrite Q; exact HE22|];
split; [let Q := fresh "Q" in (jreg HS (10%bv:reg) as Q); rewrite Q; exact HE10|];
split; [let Q := fresh "Q" in (jreg HS (24%bv:reg) as Q); rewrite Q; exact HE24|];
split; [let Q := fresh "Q" in (jreg HS (18%bv:reg) as Q); rewrite Q; reflexivity|];
split; [let Q := fresh "Q" in (jreg HS (25%bv:reg) as Q); rewrite Q; reflexivity|];
split; [lia|]; split; [lia|];
split; [let Q := fresh "Q" in (jreg HS (13%bv:reg) as Q); rewrite Q; exact HE35|];
split; [let Q := fresh "Q" in (jreg HS (14%bv:reg) as Q); rewrite Q; exact HE36|];
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
| eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H) ].
assert (Hcases : (0 <= ne <= 1) \/ ne = 2 \/ (3 <= ne <= 4) \/ (5 <= ne <= 8) \/ (9 <= ne <= 16) \/
(17 <= ne <= 32) \/ (33 <= ne <= 64) \/ (65 <= ne <= 128) \/ (129 <= ne <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]].
- pose proof (MKS 0 1 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 3 4.
- pose proof (MKS 2 2 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 3 4.
- pose proof (MKS 3 4 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 3 4.
- pose proof (MKS 5 8 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 4 8.
- pose proof (MKS 9 16 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 5 16.
- pose proof (MKS 17 32 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 6 32.
- pose proof (MKS 33 64 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 7 64.
- pose proof (MKS 65 128 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 8 128.
- pose proof (MKS 129 256 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS 9 256.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
