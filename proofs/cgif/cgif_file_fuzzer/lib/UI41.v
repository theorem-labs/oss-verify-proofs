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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o YI6a UI1w UI3p UI3m UI3t.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01 YI0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UI4j UI4h UI4d UI42 UI40.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Ltac wr2 HE2 := eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia].
Definition at_L4Xp (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (p icl idl R : Z) (PFX : list Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (pint : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 PC_L4X) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\   res_ok A2 (rb_acc b 1 (prN (c_nP cx))) /\
Permutation (blocks L2 A2) ((pint, c_nP cx) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (pint, c_nP cx) /\ pint <> 0 /\
ra_regs regs2 cx /\ getr regs2 23 = Z_to_bv 64 (c_slct cx) /\ getr regs2 24 = Z_to_bv 64 p /\ getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs2 18 = Z_to_bv 64 icl /\ getr regs2 25 = Z_to_bv 64 idl /\
getr regs2 19 = Z_to_bv 64 pint /\ getr regs2 10 = Z_to_bv 64 (c_h cx) /\ getr regs2 12 = Z_to_bv 64 (c_w cx) /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) /\
garr8 ubs0segs mem2 pint PFX /\ Z.of_nat (length PFX) = c_w cx * R /\ garr8 ubs0segs mem2 (c_img cx) IMGV /\ fbC mem2 cx.
Lemma ra_W4 : forall cx L A mem md regs0 p icl idl R b c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) ->
0 <= R -> c_w cx * R <= c_nP cx -> (forall j, 0 <= j -> 1 + 2 * j < c_h cx -> R + j + 1 <= c_h cx) ->
forall PFX, Z.of_nat (length IMGV) = c_nP cx ->
at_LX API IMGV PC_L4P cx L A mem md regs0 p icl idl R PFX b c1 ->
SR ubs0segs c1 (fun c' => exists m, ((2 <= c_h cx /\ 1 <= m /\ 1 + 2 * (m - 1) < c_h cx <= 1 + 2 * m) \/ (c_h cx < 2 /\ m = 0)) /\
at_L4Xp cx L A mem md regs0 p icl idl (R + m) (PFX ++ ipassZ IMGV (c_w cx) 1 2 m) b c').
Proof using IMG.
intros cx L A mem md regs0 p icl idl R b c1 Hcx HO HB HR0 HRn Hrows PFX HIMGlen
(L2 & A2 & regs2 & mem2 & md2 & pint & -> & HJ2 & Hid2 & HRq2 & HB2 & Hwt & Hpnz & HR & G23 & G24 & G22 & G18 & G25 & G19 & G20 & G21 & G10 & G12 & Hobjs & HFS & HGP & HLP & HIMG2 & HFBC).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
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
pose proof (E_cv regs2 cx (c_rcur cx) []) as HX. rewrite <- HE0 in HX.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE10 : ew E 10 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE12 : ew E 12 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HS : st_ok ubs0segs E (ssLX PC_L4P) (mkst regs2 (Z_to_bv 64 PC_L4P) mem2 (seg_rom ubs0segs))).
{ subst E. unfold ssLX.
apply (ra_st_okW cx (c_rcur cx) regs2 [] mem2 PC_L4P _ 0 0 false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE10, HE12, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_L4P) mem2 (seg_rom ubs0segs))) in HJ2.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L4; [wr2 HE2|].
jbranch ubs0tbl HS.
-
rewrite branch_geu_U, U_lit, (U_atom _ 10 _ HE10) in Hc by lia.
assert (Hh2 : c_h cx < 2) by (destruct (Z.ltb_spec 1 (c_h cx)); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L4X; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 18; 19; 22; 23; 24; 25; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (12%bv:reg) as Q12. cbn [ms_regs mkst] in Q12. rewrite HE35 in Q12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists 0. split; [right; lia|].
exists L2, A2, (ms_regs msF), (ms_mem msF), md2, pint. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HK by (cbv; tauto); exact HR|].
split; [rewrite HK by (cbv; tauto); exact G23|]. split; [rewrite HK by (cbv; tauto); exact G24|].
split; [rewrite HK by (cbv; tauto); exact G22|].
split; [rewrite HK by (cbv; tauto); exact G18|]. split; [rewrite HK by (cbv; tauto); exact G25|].
split; [rewrite HK by (cbv; tauto); exact G19|].
split; [rewrite HK by (cbv; tauto); exact G10|]. split; [exact Q12|].
assert (MEQs : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem2 a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)).
split; [eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQs; lia|].
split; [eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; apply MEQs; lia|].
rewrite app_nil_r, Z.add_0_r.
split; [apply (garr8_frame ubs0segs mem2 _ pint PFX HGP); intros a Ha; apply MEQs; lia|]. split; [exact HLP|].
split; [apply (garr8_frame ubs0segs mem2 _ (c_img cx) IMGV HIMG2); intros a Ha; apply MEQs; unfold c_nP in *; lia | eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQs; lia].
-
rewrite branch_geu_U, U_lit, (U_atom _ 10 _ HE10) in Hc by lia.
assert (Hh2 : 2 <= c_h cx) by (destruct (Z.ltb_spec 1 (c_h cx)); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L4; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 18; 19; 21; 22; 23; 24; 25; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (20%bv:reg) as Q20. cbn [ms_regs mkst] in Q20.
jreg HS (12%bv:reg) as Q12. cbn [ms_regs mkst] in Q12. rewrite HE35 in Q12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (Hobjs' : objs_at (ms_mem msF) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HFS' : frame_savedN ubs0_msyms 12 regs0 (ms_mem msF) (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (MEQs : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem2 a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)).
assert (HGP' : garr8 ubs0segs (ms_mem msF) pint PFX) by (apply (garr8_frame ubs0segs mem2 _ pint PFX HGP); intros a Ha; apply MEQs; lia).
assert (HIMG' : garr8 ubs0segs (ms_mem msF) (c_img cx) IMGV) by (apply (garr8_frame ubs0segs mem2 _ (c_img cx) IMGV HIMG2); intros a Ha; apply MEQs; unfold c_nP in *; lia).
assert (HFBC' : fbC (ms_mem msF) cx) by (eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQs; lia).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (il_loop4 API IMG (Z.to_nat (c_h cx)) 1 R (ms_regs msF) (ms_mem msF) RAWADD_STK (spZ regs0) _ L A mem md L2 A2 md2 pint (c_nP cx) (c_img cx) (c_Nimg cx) (c_w cx) (c_h cx) (c_cfp cx) (cvals cx));
cbn [ms_regs ms_mem];
[ lia | lia | lia | exact Hrows | lia | lia | lia | lia | exact HJ2 | exact Hpin | exact Hwt | exact Himgin | exact (hideR_e _ Hsi')
| exact (proj1 Hobjs') | reflexivity | reflexivity | reflexivity | lia | lia | exact Hcfpal | rewrite HK by (cbv; tauto); exact R9
| rewrite HK by (cbv; tauto); exact G21 | exact Q20 | exact Q12 ]. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & Pd & Pt & P10 & P12 & HKf & Hout & Hgr & Hcp).
rewrite <- HnPe in Hout.
destruct (after_loop_mem IMGV cx (ms_mem msF) mem' pint (c_rcur cx) regs0 R PFX Hcx Hp0 Hp1 (hideR_e _ Hsr) (hideR_e _ Hsg) (hideR_e _ Hsi) Hout ltac:(pose proof (Hrows 0 ltac:(lia) ltac:(lia)); unfold c_nP; nia) Hspe Hobjs' HFS'
HGP' HLP HIMG' HIMGlen HFBC') as (Hobjs'' & HFS'' & HGP'' & HIMG'' & HFBC'').
pose proof (garr8_ipass ubs0segs (ms_mem msF) mem' (c_img cx) pint IMGV (c_w cx) (c_h cx) 1 2 m R HIMG' HIMGlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) Hcp) as HGQ.
exists m. split; [left; lia|].
exists L2, A2, regs', mem', md2, pint. split; [reflexivity|]. split; [exact HJ'|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HKf, !HK by (cbv; tauto); exact HR|].
split; [rewrite HKf, HK by (cbv; tauto); exact G23|]. split; [rewrite HKf, HK by (cbv; tauto); exact G24|].
split; [rewrite HKf, HK by (cbv; tauto); exact G22|].
split; [rewrite HKf, HK by (cbv; tauto); exact G18|]. split; [rewrite HKf, HK by (cbv; tauto); exact G25|].
split; [rewrite HKf, HK by (cbv; tauto); exact G19|].
split; [exact P10|]. split; [exact P12|].
split; [exact Hobjs''|]. split; [exact HFS''|].
split; [apply (proj2 (garr8_app ubs0segs mem' pint PFX _)); split; [exact HGP'' | rewrite HLP; exact HGQ]|].
split; [rewrite length_app, Nat2Z.inj_add, HLP, (ipassZ_length IMGV (c_w cx) (c_h cx) 1 2 m HIMGlen) by (first [lia | intros; lia]); lia|].
split; [exact HIMG'' | exact HFBC''].
Qed.
Lemma ra_il2 : forall cx L A mem md regs0 p icl idl b c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) -> 0 <= p <= 8 -> 4 <= idl <= 256 ->
garr8 ubs0segs mem (c_img cx) IMGV -> Z.of_nat (length IMGV) = c_nP cx ->
at_L1 API cx L A mem md regs0 p icl idl b c1 ->
SR ubs0segs c1 (at_L4X API IMGV cx L A mem md regs0 p icl idl b).
Proof using IMG.
intros cx L A mem md regs0 p icl idl b c1 Hcx HO HB Hp Hidl HIMG0 HIMGlen H1.
pose proof Hcx as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw1 & Hh1 & HnP & _) & _).
eapply SR_bind; [eapply (ra_W1 API IMG IMGV cx L A mem md regs0 p icl idl b c1 Hcx HO HB HIMG0 HIMGlen H1)|].
cbv beta. intros c2 (m1 & Hm1 & Hm1b & H2).
eapply SR_bind; [eapply (ra_W2 API IMG IMGV cx L A mem md regs0 p icl idl m1 b c2 Hcx HO HB ltac:(lia) ltac:(unfold c_nP; nia) ltac:(intros j Hj Hjh; lia) _ HIMGlen H2)|].
cbv beta. intros c3 (m2 & Hm2 & H3).
eapply SR_bind; [eapply (ra_W3 API IMG IMGV cx L A mem md regs0 p icl idl (m1 + m2) b c3 Hcx HO HB ltac:(lia) ltac:(unfold c_nP; nia) ltac:(intros j Hj Hjh; lia) _ HIMGlen H3)|].
cbv beta. intros c4 (m3 & Hm3 & H4).
eapply SR_mono; [eapply (ra_W4 cx L A mem md regs0 p icl idl (m1 + m2 + m3) b c4 Hcx HO HB ltac:(lia) ltac:(unfold c_nP; nia) ltac:(intros j Hj Hjh; lia) _ HIMGlen H4)|].
cbv beta. intros c5 (m4 & Hm4 & L2 & A2 & regs2 & mem2 & md2 & pint & -> & HJ2 & Hid2 & HRq2 & HB2 & Hwt & Hpnz & HR & G23 & G24 & G22 & G18 & G25 & G19 & G10 & G12 & Hobjs & HFS & HGP & HLP & HIMG2 & HFBC).
exists L2, A2, regs2, mem2, md2, pint. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|]. split; [exact HR|].
split; [exact G23|]. split; [exact G24|]. split; [exact G22|]. split; [exact G18|]. split; [exact G25|]. split; [exact G19|].
split; [exact G10|]. split; [exact G12|]. split; [exact Hobjs|]. split; [exact HFS|].
assert (HLn : length IMGV = (Z.to_nat (c_w cx) * Z.to_nat (c_h cx))%nat) by (apply Nat2Z.inj; rewrite Nat2Z.inj_mul, !Z2Nat.id by lia; unfold c_nP in HIMGlen; exact HIMGlen).
assert (MR1 : mrowsN 0 8 (Z.to_nat (c_h cx)) (Z.to_nat m1)) by (apply (mrows_N 0 8 (c_h cx) m1); [lia | lia | lia | lia | unfold mrows; lia]).
assert (MR2 : mrowsN 4 8 (Z.to_nat (c_h cx)) (Z.to_nat m2)) by (apply (mrows_N 4 8 (c_h cx) m2); [lia | lia | lia | lia | unfold mrows; lia]).
assert (MR3 : mrowsN 2 4 (Z.to_nat (c_h cx)) (Z.to_nat m3)) by (apply (mrows_N 2 4 (c_h cx) m3); [lia | lia | lia | lia | unfold mrows; lia]).
assert (MR4 : mrowsN 1 2 (Z.to_nat (c_h cx)) (Z.to_nat m4)) by (apply (mrows_N 1 2 (c_h cx) m4); [lia | lia | lia | lia | unfold mrows; lia]).
pose proof (interlace_passes (Z.to_nat (c_w cx)) (Z.to_nat (c_h cx)) IMGV _ _ _ _ ltac:(lia) HLn MR1 MR2 MR3 MR4) as HIL.
pose proof (interlace_length (Z.to_nat (c_w cx)) (Z.to_nat (c_h cx)) IMGV _ _ _ _ ltac:(lia) HLn MR1 MR2 MR3 MR4) as HILl.
rewrite Z2Nat.id in HIL, HILl by lia.
split; [| split; [rewrite HILl; exact HIMGlen | exact HFBC]].
rewrite HIL. unfold ipassZ in HGP. rewrite <- !app_assoc in HGP. exact HGP.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
