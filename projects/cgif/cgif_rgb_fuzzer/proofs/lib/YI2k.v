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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3m YO3n
YI00 YI02 YI01 YI07 YI03 YI04 YI06 YI5a YI2a YI2b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition tcommon_facts0 : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 8224) (2^63) 4); (8%nat, mkAF 4096 CEIL_MAX 4); (20%nat, mkAF 2 256 0); (21%nat, mkAF 4 512 0);
(18%nat, mkAF CEIL_MIN (2^63) 3); (19%nat, mkAF 0 12 0);
(32%nat, mkAF 4096 CEIL_MAX 4); (33%nat, mkAF 4096 CEIL_MAX 4); (34%nat, mkAF 4096 CEIL_MAX 4); (35%nat, mkAF 4096 CEIL_MAX 4);
(36%nat, mkAF 4096 CEIL_MAX 4); (37%nat, mkAF 4096 CEIL_MAX 4); (38%nat, mkAF 4096 CEIL_MAX 0); (39%nat, mkAF 1 100000000 0);
(40%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2^64 - 4097) 0); (41%nat, mkAF 0 134217726 0); (42%nat, mkAF 0 4096 0); (43%nat, mkAF 0 2047 0) ].
Definition tlzw_ss0 (pc : Z) (sr : list sv) (w : bool) (rs : smem) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr (gen_region w :: rs) None (mkFacts (tcommon_facts0 ++ fs) cs (tcommon_alias ++ al)).
Definition trst_facts : list (nat * afact) := [ (25%nat, mkAF 0 100000000 0); (44%nat, mkAF 4096 CEIL_MAX 1) ].
Definition trst_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 37%nat 0) (SAlu ALU_SLL (SOff 41%nat 0) (SLit 1)), SOff 44%nat 0) ].
Definition trst_regs (two : bool) : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 32%nat 0)) 12%bv (SOff 37%nat 0)) 24%bv (SLit 1))
(if two then 11%bv else 16%bv) (SOff 41%nat 0))
(if two then 15%bv else 13%bv) (SOff 41%nat (-1)).
Definition ss_trst (two : bool) : sstate := tlzw_ss (trst_pc two) (trst_regs two) true [regw 44 2] trst_facts [] trst_alias.
Definition ss_trst1_c : sstate := Eval vm_compute in ss_trst false.
Definition ss_trst2_c : sstate := Eval vm_compute in ss_trst true.
Lemma U_tisz2 : forall E n idl,
ew E n = Z_to_bv 64 idl -> 2 <= idl <= 256 ->
U E (SAlu ALU_SLL (SMd M_MUL (SOff n 0) (SOff n 0)) (SLit 1)) = 2 * idl * idl.
Proof.
intros E n idl Hn Hidl.
assert (Hsq : idl * idl <= 256 * 256) by nia. assert (Hsq0 : 0 <= idl * idl) by nia.
rewrite (U_sll1_small E _ (idl * idl)); [lia | | lia | lia].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n idl Hn) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.

Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Lemma tlzw_st_ok0 : forall cx regs lp dp mp more mem pc w rs fs cs al,
tcx_ok cx -> tcx_ranges cx -> tlzw_regs_fix regs cx -> gen_at mem cx lp dp mp ->
(w = true -> forall a, y_g cx + 60 <= a < y_g cx + 68 -> writable_at src2segs mem a) ->
0 <= lp <= 134217726 -> 0 <= dp <= 4096 -> 0 <= mp <= 2047 ->
let E := Ereg regs (tcx_extra cx lp dp mp ++ more) in
regions_wf (gen_region w :: rs) = true ->
Forall (region_ok src2segs E mem) rs ->
all_disjoint E (gen_region w) rs -> pairwise_disjoint E rs ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok src2segs E (tlzw_ss0 pc sr_atoms w rs fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom src2segs)).
Proof.
intros cx regs lp dp mp more mem pc w rs fs cs al Hcx Hrg HF HG Hw Hlp Hdp Hmp E Hwf Hrs Had Hpd Hfs Hcs Hal. subst E.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof Hrg as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
unfold y_tisz, y_tmsz, y_cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
pose proof (TE_sp regs cx lp dp mp more HF) as HE2. pose proof (TE_g regs cx lp dp mp more HF) as HE8.
pose proof (TE_idl regs cx lp dp mp more HF) as HE20. pose proof (TE_idl2 regs cx lp dp mp more HF) as HE21.
pose proof (TE_pR regs cx lp dp mp more HF) as HE18. pose proof (TE_icl regs cx lp dp mp more HF) as HE19.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_ld regs cx lp dp mp more) as HE37.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_nimg regs cx lp dp mp more) as HE40. pose proof (TE_lp regs cx lp dp mp more) as HE41.
pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
unfold y_nimg in HE40.
apply entry_st_ok_full.
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|exact Hrs].
unfold region_ok, gen_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct w; [apply Hw; [reflexivity | lia] | lia]. }
unfold gen_chunks.
Ltac ck0 S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia | first [exact S | rewrite Z.add_0_r; exact S] ].
constructor; [ck0 V0 HE32|]. constructor; [ck0 V8 HE33|]. constructor; [ck0 V16 HE34|]. constructor; [ck0 V24 HE35|].
constructor; [ck0 V32 HE36|]. constructor; [ck0 V40 HE37|]. constructor; [ck0 V48 HE38|]. constructor; [ck0 V56 HE39|].
constructor; [ck0 V60 HE41|]. constructor; [ck0 V64 HE42|]. constructor; [ck0 V66 HE43|]. constructor.
- split; [exact Had | exact Hpd].
- split; [|split; [exact Hcs|]].
+ unfold tlzw_ss0. cbn [f_atoms]. apply atoms_ok_app; [|exact Hfs].
cbn [atoms_ok tcommon_facts0]. unfold afact_ok, AC, NOTLO. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8, HE20, HE21, HE18, HE19, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE40, HE41, HE42, HE43, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [assumption | lia].
+ unfold tlzw_ss0. cbn [f_alias]. split; [|exact Hal].
apply (alias_nimg _ 38 40 (y_img cx) HE38 HE40). lia.
Qed.
Definition rd_written (cx : lzw_tcx) (lp : Z) (a : Z) : Prop :=
(y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2) \/
(y_ti cx <= a < y_ti cx + y_tisz cx) \/ (y_lm cx <= a < y_lm cx + 8192) \/
(y_lc cx <= a < y_lc cx + 4096) \/ (y_li cx <= a < y_li cx + 8192).
Lemma trst_seg1 : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s',
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
trst_pre cx X s' false regs memc ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 (trst_pc false)) memc (seg_rom src2segs)) mdc)
(fun c' => exists regs' mem' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 TPC_TAIL) mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
ttail_post cx X regs' mem' X' /\ la_s X' = s').
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s' HCX HRG HSEP HBL HWIN HWT HJ HPRE.
destruct X as [TI LM LI TM s lp0 dp mp Cn R].
destruct HPRE as (HFX & HGA & HT & HI & Hdp4096 & H25 & Hs' & H24 & G10 & G12 & GLP1 & GLP).
cbv beta iota in GLP, GLP1. change (trst_pc false) with TPC_RST1.
cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlpx & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (lp_head_bound (y_idl cx) (y_nP cx) (y_MR cx) (mkLA TI LM LI TM s lp0 dp mp Cn R)
ltac:(unfold lzw_par; destruct HCX as (Hidl_ & HnP_ & HMR_ & HMR0_ & _); assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia); lia)
HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
destruct HT as (ATI & ALM & ALI & ATM).
set (lp := lp0 + 1) in *.
assert (Hlp0 : 0 <= lp) by lia. assert (Hlpc : lp < y_cap cx) by (unfold y_cap, cap; lia). assert (Hlpm : lp <= 134217726).
{ destruct HCX as (Hidl_ & HnP_ & HMR_ & HMR0_ & _). assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Hmpb : 1 <= mp <= 2047) by (pose proof (mp_bound (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp0 dp mp Cn R) ltac:(destruct HCX as (Hidl_ & _); lia) HI) as Hq; cbn [la_mp] in Hq; lia).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HBL as [HBt HBi]. destruct HWIN as [W1 W2].
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
assert (Htisz : 8 <= 2 * y_idl cx * y_idl cx <= 131072) by (apply ttisz_range; exact Hidl).
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Ptab : forall d n i, In (d, n) (tcx_tabs cx) -> 0 <= i < n -> present memc (d + i)).
{ intros d n i Hin Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ d n i HH (HBt _ Hin) Hi)). }
remember [Z_to_bv 64 (y_ld cx + 2 * lp)] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HFX) as HE2. pose proof (TE_g regs cx lp dp mp more HFX) as HE8.
pose proof (TE_idl regs cx lp dp mp more HFX) as HE20. pose proof (TE_idl2 regs cx lp dp mp more HFX) as HE21.
pose proof (TE_pR regs cx lp dp mp more HFX) as HE18. pose proof (TE_icl regs cx lp dp mp more HFX) as HE19.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_ld regs cx lp dp mp more) as HE37.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_lp regs cx lp dp mp more) as HE41.
rewrite <- HE0 in HE2, HE8, HE20, HE21, HE18, HE19, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41.
pose proof (TE_idlp2 regs cx lp dp mp more HFX) as HE23. rewrite <- HE0 in HE23.
pose proof (TE_tisz regs cx lp dp mp more HFX) as HE22. rewrite <- HE0 in HE22. unfold y_tisz in HE22.
assert (HE25 : ew E 25 = Z_to_bv 64 s') by (rewrite HE0, (TE_reg regs _ _ _ _ more 25%bv 25) by reflexivity; exact H25).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
assert (HS : st_ok src2segs E ss_trst1_c (mkst regs (Z_to_bv 64 TPC_RST1) memc (seg_rom src2segs))).
{ change ss_trst1_c with (ss_trst false). unfold ss_trst, trst_regs. cbv beta iota. change (trst_pc false) with TPC_RST1.
enough (HS0 : st_ok src2segs E (tlzw_ss TPC_RST1 sr_atoms true [regw 44 2] trst_facts [] trst_alias)
(mkst regs (Z_to_bv 64 TPC_RST1) memc (seg_rom src2segs))).
{ pose proof (st_ok_set_reg' src2segs E _ _ (10%bv:reg) (SOff 32%nat 0) HS0 eq_refl
ltac:(cbn [sv_denot ms_regs]; rewrite HE32, unsigned_lit_small, Z.add_0_r by lia; symmetry; exact G10)) as HS1.
pose proof (st_ok_set_reg' src2segs E _ _ (12%bv:reg) (SOff 37%nat 0) HS1 eq_refl
ltac:(cbn [sv_denot ms_regs]; rewrite HE37, unsigned_lit_small, Z.add_0_r by lia; symmetry; exact G12)) as HS2.
pose proof (st_ok_set_reg' src2segs E _ _ (24%bv:reg) (SLit 1) HS2 eq_refl
ltac:(cbn [sv_denot ms_regs]; symmetry; exact H24)) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
pose proof (st_ok_set_reg' src2segs E _ _ (16%bv:reg) (SOff 41%nat 0) HS3 eq_refl
ltac:(cbn [sv_denot ms_regs]; rewrite HE41, unsigned_lit_small, Z.add_0_r by lia; symmetry; exact GLP1)) as HS4.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
apply (st_ok_set_reg' src2segs E _ _ (13%bv:reg) (SOff 41%nat (-1)) HS4 eq_refl).
cbn [sv_denot ms_regs]. rewrite HE41, unsigned_lit_small by lia. symmetry. etransitivity; [exact GLP|]. f_equal. subst lp. lia. }
unfold tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_RST1 true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros _ a Ha. apply (present_writable src2_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply (Ptab (y_g cx) 72); [cbv; tauto | lia].
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_nil].
apply (region_ok_regw _ E memc 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable src2_msyms). replace (y_ld cx + 2 * lp + o) with (y_ld cx + (2 * lp + o)) by lia.
apply (Ptab (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx))); [cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; tauto | lia].
- cbn [all_disjoint app]; unfold extent_disjoint, regw, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, !unsigned_lit_small by lia. split; [septac HSEP 5%nat 6%nat; lia | exact I].
- cbn [pairwise_disjoint all_disjoint app]. split; exact I.
- unfold trst_facts. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE25, HE44, !unsigned_lit_small by lia. change (2 ^ 1) with 2. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- exact I.
- unfold trst_alias. cbn [alias_ok]. split; [|exact I].
apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_RST1) memc (seg_rom src2segs))) in HJ.
assert (MEM : forall a, 0 <= a < 2 ^ 64 -> ~ rd_written cx lp a ->
mbyte src2segs (ms_mem (mkst regs (Z_to_bv 64 TPC_RST1) memc (seg_rom src2segs))) a = mbyte src2segs memc a)
by (intros; reflexivity).
pose proof (HWT (y_g cx, 72) ltac:(cbv; tauto)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; tauto)) as Wld.
Ltac wr_tac HE2 HE8 HE44 Wg Wld HBt blc :=
wr_norm;
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 8); [reflexivity | ew_havoc; rewrite HE8; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi gen_region]; intros a Ha;
lazymatch type of Wg with wtok' _ _ _ _ (?g, _) => eapply (wr_byte_of_wtok _ _ _ _ _ g 72); [exact Wg | apply HBt; cbv; tauto | lia] end |];
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 44); [reflexivity | ew_havoc; rewrite HE44; apply unsigned_lit_small; lia | | apply wr_ok_nil];
cbn [r_wlo r_whi regw]; intros a Ha;
lazymatch type of Wld with wtok' _ _ _ _ (?d, ?n) => eapply (wr_byte_of_wtok _ _ _ _ _ d n); [exact Wld | apply HBt; cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; tauto | lia] end.
Ltac fold_frameW MEM HE2 HE8 HE44 :=
lazymatch goal with HF : frame_of ?E1 ?rs ?m ?m' |- _ =>
let MEM2 := fresh "MEM" in
lazymatch type of MEM with forall a, _ -> ~ ?Wr a -> _ = mbyte _ ?m0 a =>
assert (MEM2 : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> mbyte src2segs m' a = mbyte src2segs m0 a)
by (intros a Ha Hna; rewrite <- (MEM a Ha Hna); apply tmbyte_eq_of1; apply HF;
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2, ?HE8, ?HE44, ?unsigned_lit_small in Hin0 by lia; unfold rd_written, y_tisz in Hna; lia |]);
destruct Hr0);
clear MEM HF; rename MEM2 into MEM
end end.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset; [wr_tac HE2 HE8 HE44 Wg Wld HBt (blocks Lc Ac)|].
fold_frameW MEM HE2 HE8 HE44.
Ltac do_memset HS HJ MEM d n k HE2 HE8 HE44 HE20 Ptab HWT HBt HSEP ti Hraw idl HE G1 :=
let M10 := fresh "M10" in let M11 := fresh "M11" in let M12 := fresh "M12" in let M1 := fresh "M1" in
(jreg HS (10%bv:reg) as M10); (jreg HS (11%bv:reg) as M11); (jreg HS (1%bv:reg) as M1);
cbn [ms_regs mkst] in M10, M11, M1; try (rewrite (HE 1%nat (1%bv:reg) eq_refl), G1 in M1);
lazymatch type of HS with st_ok ?sg ?E1 ?ss1 ?ms1 =>
(jreg HS (12%bv:reg) as M12); cbn [ms_regs mkst] in M12;
try (lazymatch goal with H22 : ew _ 22 = Z_to_bv 64 _ |- _ => rewrite H22 in M12 end);
eapply SR_bind;
[ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E1 ss1 ms1 _ _ _ _ _ _ _ _ _ _ d 0 n);
[ exact HS | reflexivity | reflexivity | exact HJ
| cbn [ms_regs mkst]; rewrite M10; ew_havoc; first [assumption | symmetry; assumption | reflexivity]
| cbn [ms_regs mkst]; rewrite M11; reflexivity
| cbn [ms_regs mkst]; rewrite M12; reflexivity
| cbn [ms_regs mkst]; exact M1
| first [exact Hraw | apply ret_ok_even; vm_compute; reflexivity]
| lia | lia | lia | lia
| let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi; cbn [ms_mem mkst];
repeat (cbn [ms_mem mkst]; match goal with HG : mem_grows _ ?m' |- present ?m' _ => apply (present_grows _ _ _ HG) end);
cbn [ms_mem mkst]; apply (Ptab d n); [cbv; tauto | exact Hi]
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ d n); [apply HWT; cbv; tauto | apply HBt; cbv; tauto | exact Ha] ]
| ] end;
clear M10 M11 M12 M1;
let regs2 := fresh "regs" in let mem2 := fresh "mem" in
let HJ2 := fresh "HJ" in let Hr10 := fresh "Hr10" in let Hregs := fresh "Hregs" in let Hout := fresh "Hout" in
let Hgr := fresh "Hgr" in let Hzero := fresh "Hzero" in
intros c' (regs2 & mem2 & -> & HJ2 & Hr10 & Hregs & Hout & Hgr & Hzero); clear HJ; rename HJ2 into HJ;
cbn [ms_regs ms_mem mkst] in Hr10, Hregs, Hout, Hgr, Hzero, HJ;
let MEM2 := fresh "MEM" in
lazymatch type of MEM with forall a, _ -> ~ ?Wr a -> mbyte _ ?mc a = mbyte _ ?m0 a =>
assert (MEM2 : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> mbyte src2segs mem2 a = mbyte src2segs m0 a)
by (intros a Ha Hna; rewrite <- (MEM a Ha Hna); apply tmbyte_eq_of1; apply Hout;
rewrite unsigned_lit_small by lia; unfold rd_written, y_tisz in Hna; lia);
clear MEM; rename MEM2 into MEM
end.
Ltac after_memset HS k ra HE2 HE8 HE44 HSEP ti :=
lazymatch goal with Hregs : forall r, reg_in r MEMSET_CLOB = false -> getr ?regs2 r = _, Hout : forall x : word, _ -> ?mem2 x = _, Hgr : mem_grows _ ?mem2' |- _ =>
let HS2 := fresh "HS" in
jafter_stretch HS k regs2 mem2 MEMSET_CLOB ra HS2;
specialize (HS2 Hregs);
let HK := fresh "HK" in
match type of HS2 with ?P -> _ => assert (HK : P);
[ constructor; [|constructor; [|constructor]];
(eapply region_kept_outside; [exact Hout | exact Hgr | | | | cbn; lia | cbn; lia]);
cbn [r_base r_lo r_hi base_val]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite ?HE2, ?HE8, ?HE44, ?unsigned_lit_small by lia;
first [lia | septac HSEP ti 6%nat; lia | septac HSEP ti 5%nat; lia]
| specialize (HS2 HK); clear HK HS Hregs Hout; rename HS2 into HS ] end end.
do_memset HS HJ MEM (y_ti cx) (2 * y_idl cx * y_idl cx) 45%nat HE2 HE8 HE44 HE20 Ptab HWT HBt HSEP 0%nat Hraw (y_idl cx) HE G1.
rename Hzero into Z1. clear Hr10.
after_memset HS 45%nat 0x1650c HE2 HE8 HE44 HSEP 0%nat.
assert (ZT : forall a, (y_ti cx <= a < y_ti cx + 2 * y_idl cx * y_idl cx) -> mbyte src2segs mem0 a = Some (Z_to_bv 8 0)).
{ intros a Ha. replace a with (y_ti cx + (a - y_ti cx)) by lia. apply Z1. lia. }
clear Z1.
Ltac zt_case Ha tac := repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end; tac.
Ltac zt_frame ZT HE2 HE8 HE44 HSEP :=
lazymatch goal with HF : frame_of ?E1 ?rs ?m ?m' |- _ => lazymatch type of ZT with forall a, @?Zs a -> _ =>
let ZT2 := fresh "ZT" in
assert (ZT2 : forall a, Zs a -> mbyte src2segs m' a = Some (Z_to_bv 8 0))
by (let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (ZT a Ha); apply tmbyte_eq_of1; apply HF;
rewrite unsigned_lit_small by (zt_case Ha lia);
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2, ?HE8, ?HE44, ?unsigned_lit_small in Hin0 by lia;
zt_case Ha ltac:(first [lia | septac HSEP 0%nat 6%nat; lia | septac HSEP 1%nat 6%nat; lia | septac HSEP 3%nat 6%nat; lia
| septac HSEP 0%nat 5%nat; lia | septac HSEP 1%nat 5%nat; lia | septac HSEP 3%nat 5%nat; lia]) |]);
destruct Hr0);
clear ZT; rename ZT2 into ZT end end.
Ltac zt_out ZT Hout HSEP :=
lazymatch type of Hout with forall x, _ -> ?m' x = ?m x => lazymatch type of ZT with forall a, @?Zs a -> _ =>
let ZT2 := fresh "ZT" in
assert (ZT2 : forall a, Zs a -> mbyte src2segs m' a = Some (Z_to_bv 8 0))
by (let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (ZT a Ha); apply tmbyte_eq_of1; apply Hout;
rewrite unsigned_lit_small by (zt_case Ha lia);
zt_case Ha ltac:(first [lia | septac HSEP 0%nat 1%nat; lia | septac HSEP 0%nat 2%nat; lia | septac HSEP 0%nat 3%nat; lia
| septac HSEP 1%nat 2%nat; lia | septac HSEP 1%nat 3%nat; lia | septac HSEP 2%nat 3%nat; lia]));
clear ZT; rename ZT2 into ZT end end.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset; [wr_tac HE2 HE8 HE44 Wg Wld HBt (blocks Lc Ac)|].
zt_frame ZT HE2 HE8 HE44 HSEP. fold_frameW MEM HE2 HE8 HE44.
do_memset HS HJ MEM (y_lm cx) 8192 51%nat HE2 HE8 HE44 HE20 Ptab HWT HBt HSEP 1%nat Hraw (y_idl cx) HE G1.
rename Hzero into Z2. clear Hr10. zt_out ZT Hout HSEP.
lazymatch type of ZT with forall a, @?Zs a -> mbyte _ ?m a = _ =>
assert (ZT2 : forall a, (Zs a \/ (y_lm cx <= a < y_lm cx + 8192)) -> mbyte src2segs m a = Some (Z_to_bv 8 0))
by (intros a [Ha|Ha]; [exact (ZT a Ha) | replace a with (y_lm cx + (a - y_lm cx)) by lia; apply Z2; lia]);
clear ZT Z2; rename ZT2 into ZT end.
after_memset HS 51%nat 0x1651c HE2 HE8 HE44 HSEP 1%nat.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset; [wr_tac HE2 HE8 HE44 Wg Wld HBt (blocks Lc Ac)|].
zt_frame ZT HE2 HE8 HE44 HSEP. fold_frameW MEM HE2 HE8 HE44.
do_memset HS HJ MEM (y_lc cx) 4096 57%nat HE2 HE8 HE44 HE20 Ptab HWT HBt HSEP 2%nat Hraw (y_idl cx) HE G1.
clear Hzero Hr10. zt_out ZT Hout HSEP.
after_memset HS 57%nat 0x1652c HE2 HE8 HE44 HSEP 2%nat.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset; [wr_tac HE2 HE8 HE44 Wg Wld HBt (blocks Lc Ac)|].
zt_frame ZT HE2 HE8 HE44 HSEP. fold_frameW MEM HE2 HE8 HE44.
do_memset HS HJ MEM (y_li cx) 8192 63%nat HE2 HE8 HE44 HE20 Ptab HWT HBt HSEP 3%nat Hraw (y_idl cx) HE G1.
rename Hzero into Z4. clear Hr10. zt_out ZT Hout HSEP.
lazymatch type of ZT with forall a, @?Zs a -> mbyte _ ?m a = _ =>
assert (ZT2 : forall a, (Zs a \/ (y_li cx <= a < y_li cx + 8192)) -> mbyte src2segs m a = Some (Z_to_bv 8 0))
by (intros a [Ha|Ha]; [exact (ZT a Ha) | replace a with (y_li cx + (a - y_li cx)) by lia; apply Z4; lia]);
clear ZT Z4; rename ZT2 into ZT end.
after_memset HS 63%nat 0x1653c HE2 HE8 HE44 HSEP 3%nat.
jrun_to LAWS src2tbl_ok HS HJ TPC_TAIL; [wr_tac HE2 HE8 HE44 Wg Wld HBt (blocks Lc Ac)|].
zt_frame ZT HE2 HE8 HE44 HSEP. fold_frameW MEM HE2 HE8 HE44.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx), (st_reset (y_idl cx) (mkLA TI LM LI TM s lp0 dp mp Cn R) (s' - 1)) end.
split; [reflexivity|]. split; [exact HJ|].
split.
{ intros a Ha. apply MEM; [lia|]. unfold rd_written, y_tisz. lia. }
pose proof (inv_reset (y_idl cx) (y_nP cx) Hidl _ (s' - 1) HI ltac:(cbn [la_dp]; exact Hdp4096) ltac:(cbn [la_s]; lia)) as HI'.
cbn [st_reset] in HI'.
unfold ttail_post. cbn [st_reset la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [|lia].
lazymatch type of HS with st_ok _ ?E4 ?ss4 ?ms4 =>
assert (QF : forall r, In r TREGS_FIXL -> getr (ms_regs ms4) r = getr regs r)
by (pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; repeat (apply env_agree_havoc_ge; [cbv; lia|]); apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK; exact HK)
end.
split; [apply (tlzw_regs_fix_kept regs); [exact HFX | exact QF]|].
split.
{ lazymatch type of HS with st_ok _ ?E4 ?ss4 ?ms4 =>
pose proof (tst_ok_region_nth E4 _ _ 0 _ HS eq_refl) as HRg;
assert (G8 : bv_unsigned (ew E4 8) = y_g cx) by (ew_havoc; rewrite HE8; apply unsigned_lit_small; lia);
replace (lp0 + 2) with (lp + 1) by (subst lp; lia);
unfold gen_at; repeat split;
[ change 8%nat with (N.to_nat 8); rewrite <- (Z.add_0_r (y_g cx)); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 0 8); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| change 8%nat with (N.to_nat 8); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 8 8); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| change 8%nat with (N.to_nat 8); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 16 8); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| change 8%nat with (N.to_nat 8); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 24 8); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| change 8%nat with (N.to_nat 8); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 32 8); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| change 8%nat with (N.to_nat 8); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 40 8); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| change 8%nat with (N.to_nat 8); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 48 8); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| change 4%nat with (N.to_nat 4); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 56 4); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia]
| change 4%nat with (N.to_nat 4); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 60 4); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia]
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 64 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia]
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E4 _ _ 8%nat (y_g cx) 66 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia] ];
cbn [sv_denot]; ew_havoc; rewrite ?HE32, ?HE33, ?HE34, ?HE35, ?HE36, ?HE37, ?HE38, ?HE39, ?HE41, ?HE23, ?Z.add_0_r, ?unsigned_lit_small by lia; reflexivity
end. }
split.
{ unfold ttables_at. cbn [la_TI la_LM la_LI la_TM].
split; [|split; [|split]].
- apply arr16_zeros. intros a Ha. rewrite Z2Nat.id in Ha by nia. apply ZT. cbv beta. left. left. nia.
- apply arr16_zeros. intros a Ha. cbn [Z.of_nat] in Ha. apply ZT. cbv beta. left. right. lia.
- apply arr16_zeros. intros a Ha. cbn [Z.of_nat] in Ha. apply ZT. cbv beta. right. lia.
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply MEM; [lia|]. unfold rd_written, y_tisz.
septac HSEP 4%nat 6%nat. septac HSEP 4%nat 5%nat. septac HSEP 0%nat 4%nat. septac HSEP 1%nat 4%nat. septac HSEP 2%nat 4%nat. septac HSEP 3%nat 4%nat.
lia. }
split; [exact HI'|].
split; [replace (s' - 1 + 1) with s' by lia; treg_val HS (25%bv:reg)|].
split; [lia|]. unfold s8_one. treg_val HS (24%bv:reg).
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
