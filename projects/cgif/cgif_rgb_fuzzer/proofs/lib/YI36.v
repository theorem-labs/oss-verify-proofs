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
YI2s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition pow2_ok (s p : Z) : Prop := (s = 0 -> p = 0) /\ (s <> 0 -> 1 <= p <= 8 /\ s <= 2 ^ p).
Definition ssA (fs : list (nat * afact)) : sstate := ra_ss PC_A sr_atoms [] false fs [] [].
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Definition at_B (cx : ra_cx) L A mem md L1 A1 md1 (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists regs1 mem1 (p : Z),
c' = mkCfg (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom src2segs)) md1 /\
journal src2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 /\
ra_regs regs1 cx /\ getr regs1 11 = Z_to_bv 64 (c_fattr cx) /\ getr regs1 21 = Z_to_bv 64 (c_slct cx) /\
getr regs1 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2) /\
getr regs1 22 = Z_to_bv 64 p /\ pow2_ok (c_slct cx) p /\
getr regs1 12 = Z_to_bv 64 (if c_slct cx =? 0 then c_raw cx + 32 else c_cfp cx + 30) /\
objs_at mem1 cx (c_rcur cx) /\ frame_savedN src2_msyms 10 regs0 mem1 (spZ regs0).
Lemma ra_pow2 :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte),
rcx_ok cx -> ra_origin cx regs0 ->
journal src2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
ra_regs regs1 cx -> getr regs1 11 = Z_to_bv 64 (c_fattr cx) -> getr regs1 21 = Z_to_bv 64 (c_slct cx) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN src2_msyms 10 regs0 mem1 (spZ regs0) ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom src2segs)) md1)
(at_B cx L A mem md L1 A1 md1 regs0).
Proof.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 Hcx HO HJ HR G11 G21 Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R25 & R26 & R27).
pose proof (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hstw. cbn beta in Hstw.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. rewrite <- HE0 in HX.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE11 : ew E 11 = Z_to_bv 64 (c_fattr cx)) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE21 : ew E 21 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE34 : ew E 34 = Z_to_bv 64 (c_fattr cx)) by (apply (HX 2%nat); reflexivity).
assert (MKS : forall lo hi, lo <= c_slct cx <= hi ->
st_ok src2segs E (ssA [(21%nat, mkAF lo hi 0); (11%nat, mkAF 0 (2^32-1) 0)]) (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom src2segs))).
{ intros lo hi Hlh. subst E. unfold ssA.
apply (ra_st_ok cx (c_rcur cx) regs1 [] mem1 PC_A sr_atoms false [] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE21, HE11, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom src2segs))) in HJ.
Ltac wr HE2 := eapply ra_wr_ok; [exact HE2 | lia | lia | left; cbn; lia].
Ltac finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk p :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch goal with |- at_B _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx), p end;
split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ|];
split; [ split; [| split; [| split; [|split; [|split; [|split; [|split]]]]]];
[ let Q := fresh "Q" in (jreg HS (2%bv:reg) as Q); rewrite Q, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity
| let Q := fresh "Q" in (jreg HS (8%bv:reg) as Q); rewrite Q; exact HE8
| let Q := fresh "Q" in (jreg HS (9%bv:reg) as Q); rewrite Q; exact HE9
| let Q := fresh "Q" in (jreg HS (4%bv:reg) as Q); rewrite Q, (HE 4%nat 4%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (3%bv:reg) as Q); rewrite Q, (HE 3%nat 3%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (25%bv:reg) as Q); rewrite Q, (HE 25%nat 25%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (26%bv:reg) as Q); rewrite Q, (HE 26%nat 26%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (27%bv:reg) as Q); rewrite Q, (HE 27%nat 27%bv eq_refl); assumption ] |];
split; [let Q := fresh "Q" in (jreg HS (11%bv:reg) as Q); rewrite Q; exact HE11|];
split; [let Q := fresh "Q" in (jreg HS (21%bv:reg) as Q); rewrite Q; first [exact HE21 | rewrite Hk; reflexivity]|];
split; [let Q := fresh "Q" in
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_reg segs E1 ss1 ms1 (10%bv:reg) HS) as Q; eval_sr_get_in Q;
rewrite denot_lit_U in Q; cbn [ms_regs mkst] in Q; rewrite Q; f_equal;
rewrite U_and_lit by lia; first [rewrite (U_atom _ 11 _ HE11) by lia | rewrite (U_atom _ 34 _ HE34) by lia]; reflexivity end|];
split; [let Q := fresh "Q" in (jreg HS (22%bv:reg) as Q); rewrite Q; reflexivity|];
split; [split; intros; [lia | split; [lia | cbn; lia]]|];
split; [let Q := fresh "Q" in (jreg HS (12%bv:reg) as Q); rewrite Q; cbn [sv_denot]; rewrite ?HE8, ?HE9, ?unsigned_lit_small by lia;
lazymatch goal with |- _ = Z_to_bv 64 (if ?s =? 0 then _ else _) => destruct (Z.eqb_spec s 0); [first [reflexivity | lia] | first [reflexivity | lia]] end|];
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
| eapply (frame_savedN_kept src2_msyms 10); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H) ].
assert (Hcases : c_slct cx = 0 \/ c_slct cx = 1 \/ c_slct cx = 2 \/ (3 <= c_slct cx <= 4) \/ (5 <= c_slct cx <= 8) \/ (9 <= c_slct cx <= 16) \/
(17 <= c_slct cx <= 32) \/ (33 <= c_slct cx <= 64) \/ (65 <= c_slct cx <= 128) \/ (129 <= c_slct cx <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]]].
-
pose proof (MKS 0 0 ltac:(lia)) as HS. clear MKS.
assert (G21' : getr regs1 21 = Z_to_bv 64 0) by (rewrite G21, Hk; reflexivity). pin_reg' HS (21%bv:reg) 0 G21'.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 0.
- pose proof (MKS 1 1 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 1.
- pose proof (MKS 2 2 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 1.
- pose proof (MKS 3 4 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 2.
- pose proof (MKS 5 8 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 3.
- pose proof (MKS 9 16 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 4.
- pose proof (MKS 17 32 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 5.
- pose proof (MKS 33 64 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 6.
- pose proof (MKS 65 128 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 7.
- pose proof (MKS 129 256 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS src2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE11 HE21 HE34 Hobjs HFS Htpv F2 Hk 8.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
