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
YI00 YI02 YI01 YI03 YI04 YI5a YI1e YI2m YI26 YI2r
YI2s YI37 YI35 YI31 YI2v YI2w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Ltac wr2 HE2 := eapply ra_wr_ok; [exact HE2 | lia | lia | left; cbn; lia].
Lemma ra_W4 : forall cx L A mem md regs0 p icl idl R c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) ->
0 <= R -> (forall j, 0 <= j -> 1 + 2 * j < c_h cx -> R + j + 1 <= c_h cx) ->
at_LX API PC_L4P cx L A mem md regs0 p icl idl R c1 ->
SR src2segs c1 (fun c' => exists m, ((2 <= c_h cx /\ 1 <= m /\ 1 + 2 * (m - 1) < c_h cx <= 1 + 2 * m) \/ (c_h cx < 2 /\ m = 0)) /\
at_LX API PC_L4X cx L A mem md regs0 p icl idl (R + m) c').
Proof.
intros cx L A mem md regs0 p icl idl R c1 Hcx HO HB HR0 Hrows
(L2 & A2 & regs2 & mem2 & md2 & pint & -> & HJ2 & Hid2 & HB2 & Hwt & Hpnz & HR & G21 & G22 & G18 & G23 & G19 & G20 & G10 & G11 & Hobjs & HFS).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R25 & R26 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
pose proof HJ2 as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
destruct (pint_seps API cx L A L2 A2 mem2 md2 pint Hcx HB HH2 HB2) as ((Hp0 & Hp1 & Hp16) & Hsr & Hsg & Hsi).
assert (Hsi' : pint + c_nP cx <= c_img cx \/ c_img cx + c_Nimg cx <= pint) by (clear - Hsi; lia).
apply hideR_i in Hsr. apply hideR_i in Hsg. apply hideR_i in Hsi. apply hideR_i in Hsi'.
assert (Hpin : In (pint, c_nP cx) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
assert (Himgin : In (c_img cx, c_Nimg cx) (blocks L2 A2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB2 | right]. eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]. }
assert (HnPlo : 1 <= c_nP cx) by (unfold c_nP; nia). assert (HnPe : c_nP cx = c_w cx * c_h cx) by reflexivity.
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE10 : ew E 10 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE11 : ew E 11 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HS : st_ok src2segs E (ssLX PC_L4P) (mkst regs2 (Z_to_bv 64 PC_L4P) mem2 (seg_rom src2segs))).
{ subst E. unfold ssLX.
apply (ra_st_ok cx (c_rcur cx) regs2 [] mem2 PC_L4P _ false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE10, HE11, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_L4P) mem2 (seg_rom src2segs))) in HJ2.
jrun_to LAWS src2tbl_ok HS HJ2 PC_L4; [wr2 HE2|].
jbranch src2tbl HS.
-
rewrite branch_ltu_U, (U_atom _ 11 _ HE11), U_lit in Hc by lia.
assert (Hh5 : c_h cx < 2) by (destruct (Z.ltb_spec (c_h cx) 2); [lia | discriminate]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 PC_L4X; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists 0. split; [right; lia|].
exists L2, A2, (ms_regs msF), (ms_mem msF), md2, pint. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HK by (cbv; tauto); exact HR|].
split; [rewrite HK by (cbv; tauto); exact G21|]. split; [rewrite HK by (cbv; tauto); exact G22|].
split; [rewrite HK by (cbv; tauto); exact G18|]. split; [rewrite HK by (cbv; tauto); exact G23|].
split; [rewrite HK by (cbv; tauto); exact G19|].
split; [rewrite HK by (cbv; tauto); rewrite G20; f_equal; lia|].
split; [rewrite HK by (cbv; tauto); exact G10|]. split; [rewrite HK by (cbv; tauto); exact G11|].
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
| eapply (frame_savedN_kept src2_msyms 10); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H) ].
-
rewrite branch_ltu_U, (U_atom _ 11 _ HE11), U_lit in Hc by lia.
assert (Hh5 : 2 <= c_h cx) by (destruct (Z.ltb_spec (c_h cx) 2); [discriminate | lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 PC_L4; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (24%bv:reg) as Q24. cbn [ms_regs mkst] in Q24.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (Hobjs' : objs_at (ms_mem msF) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HFS' : frame_savedN src2_msyms 10 regs0 (ms_mem msF) (spZ regs0)).
{ eapply (frame_savedN_kept src2_msyms 10); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (il_loop4 API IMG (Z.to_nat (c_h cx)) 1 R (ms_regs msF) (ms_mem msF) RAWADD_STK (spZ regs0) _ L A mem md L2 A2 md2 pint (c_nP cx) (c_img cx) (c_Nimg cx) (c_w cx) (c_h cx) (c_cfp cx) (cvals cx));
cbn [ms_regs ms_mem];
[ lia | lia | lia | exact Hrows | lia | lia | lia | lia | exact HJ2 | exact Hpin | exact Hwt | exact Himgin | exact (hideR_e _ Hsi')
| exact (proj1 Hobjs') | reflexivity | reflexivity | reflexivity | lia | lia | exact Hcfpal | rewrite HK by (cbv; tauto); exact R9
| rewrite HK by (cbv; tauto); exact G20 | exact Q24 | rewrite HK by (cbv; tauto); exact G10 ]. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & P20 & P24 & P10 & P11 & HKf & Hout & Hgr).
rewrite <- HnPe in Hout.
destruct (after_loop_mem cx (ms_mem msF) mem' pint (c_rcur cx) regs0 Hcx Hp0 Hp1 (hideR_e _ Hsr) (hideR_e _ Hsg) Hout Hspe Hobjs' HFS') as (Hobjs'' & HFS'').
exists m. split; [left; lia|].
exists L2, A2, regs', mem', md2, pint. split; [reflexivity|]. split; [exact HJ'|]. split; [exact Hid2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HKf, !HK by (cbv; tauto); exact HR|].
split; [rewrite HKf, HK by (cbv; tauto); exact G21|]. split; [rewrite HKf, HK by (cbv; tauto); exact G22|].
split; [rewrite HKf, HK by (cbv; tauto); exact G18|]. split; [rewrite HKf, HK by (cbv; tauto); exact G23|].
split; [rewrite HKf, HK by (cbv; tauto); exact G19|].
split; [rewrite P20; f_equal; lia|]. split; [exact P10|]. split; [exact P11|].
split; [exact Hobjs'' | exact HFS''].
Qed.
Lemma ra_il2 : forall cx L A mem md regs0 p icl idl c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) -> 0 <= p <= 8 -> 4 <= idl <= 256 ->
at_L1 API cx L A mem md regs0 p icl idl c1 ->
SR src2segs c1 (at_L4X API cx L A mem md regs0 p icl idl).
Proof.
intros cx L A mem md regs0 p icl idl c1 Hcx HO HB Hp Hidl H1.
pose proof Hcx as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw1 & Hh1 & HnP & _) & _).
eapply SR_bind; [eapply (ra_W1 API IMG cx L A mem md regs0 p icl idl c1 Hcx HO HB H1)|].
cbv beta. intros c2 (m1 & Hm1 & Hm1b & H2).
eapply SR_bind; [eapply (ra_W2 API IMG cx L A mem md regs0 p icl idl m1 c2 Hcx HO HB ltac:(lia) ltac:(intros j Hj Hjh; lia) H2)|].
cbv beta. intros c3 (m2 & Hm2 & H3).
eapply SR_bind; [eapply (ra_W3 API IMG cx L A mem md regs0 p icl idl (m1 + m2) c3 Hcx HO HB ltac:(lia) ltac:(intros j Hj Hjh; lia) H3)|].
cbv beta. intros c4 (m3 & Hm3 & H4).
eapply SR_mono; [eapply (ra_W4 cx L A mem md regs0 p icl idl (m1 + m2 + m3) c4 Hcx HO HB ltac:(lia) ltac:(intros j Hj Hjh; lia) H4)|].
cbv beta. intros c5 (m4 & _ & L2 & A2 & regs2 & mem2 & md2 & pint & -> & HJ2 & Hid2 & HB2 & Hwt & Hpnz & HR & G21 & G22 & G18 & G23 & G19 & G20 & G10 & G11 & Hobjs & HFS).
exists L2, A2, regs2, mem2, md2, pint. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|]. split; [exact HR|].
split; [exact G21|]. split; [exact G22|]. split; [exact G18|]. split; [exact G23|]. split; [exact G19|].
split; [exact G10|]. split; [exact G11|]. split; [exact Hobjs | exact HFS].
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
