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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03 YI04 YI06 YI5a UI0s UI2a UI2b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac rsep HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
Local Ltac rd_blk HWT HBt Hc p n :=
apply (sub_cond_of_wtok _ _ _ _ _ p n (HWT (p, n) ltac:(cbv [tcx_tabs y_tisz y_tmsz y_cap cap In]; tauto))
(HBt (p, n) ltac:(cbv [tcx_tabs y_tisz y_tmsz y_cap cap In]; tauto)) ltac:(lia) Hc);
apply inFP_cons; left; lia.
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
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma tlzw_st_ok0 : forall cx regs lp dp mp more mem pc w rs fs cs al,
tcx_ok cx -> tcx_ranges cx -> tlzw_regs_fix regs cx -> gen_at mem cx lp dp mp ->
(w = true -> forall a, y_g cx + 60 <= a < y_g cx + 68 -> writable_at ubs2segs mem a) ->
0 <= lp <= 134217726 -> 0 <= dp <= 4096 -> 0 <= mp <= 2047 ->
let E := Ereg regs (tcx_extra cx lp dp mp ++ more) in
regions_wf (gen_region w :: rs) = true ->
Forall (region_ok ubs2segs E mem) rs ->
all_disjoint E (gen_region w) rs -> pairwise_disjoint E rs ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs2segs E (tlzw_ss0 pc sr_atoms w rs fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)).
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
Definition ss_trst : sstate := tlzw_ss TPC_RST sr_atoms false [] [] [] [].
Definition rd_fp (cx : lzw_tcx) (lp : Z) : list (Z * Z) :=
[(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (y_ti cx, y_ti cx + 2 * y_idl cx * y_idl cx);
(y_lm cx, y_lm cx + 8192); (y_lc cx, y_lc cx + 4096); (y_li cx, y_li cx + 8192)].
Lemma rd_fp_written : forall cx lp a, inFP (rd_fp cx lp) a -> rd_written cx lp a.
Proof.
intros cx lp a Hf. unfold rd_fp in Hf. unfold rd_written, y_tisz.
repeat (apply inFP_cons in Hf as [Hf|Hf]; [tauto|]). destruct Hf as (r & [] & _).
Qed.
Lemma rd_fp_sub : forall cx STK sp0 FP L A Lc Ac lp,
tcx_ranges cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_wtok STK sp0 FP (blocks L A) cx ->
alloc_ceiling + STK <= sp0 -> 0 <= lp -> lp < y_cap cx ->
forall a, inFP (rd_fp cx lp) a ->
(inFP FP a /\ a < alloc_ceiling) \/ (exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n).
Proof.
intros cx STK sp0 FP L A Lc Ac lp HRG [HBt _] HWT Hc Hlp0 Hlpc a Hf.
pose proof HRG as ((Rti1 & Rti2 & _) & (Rlm1 & Rlm2 & _) & (Rlc1 & Rlc2 & _) & (Rli1 & Rli2 & _) & _ & (Rld1 & Rld2 & _) & (Rg1 & Rg2 & _) & _).
unfold y_tisz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rld1, Rld2.
unfold rd_fp in Hf.
apply inFP_cons in Hf as [Hf|Hf]; [rd_blk HWT HBt Hc (y_g cx) 72|].
apply inFP_cons in Hf as [Hf|Hf]; [rd_blk HWT HBt Hc (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx))|].
apply inFP_cons in Hf as [Hf|Hf]; [rd_blk HWT HBt Hc (y_ti cx) (2 * y_idl cx * y_idl cx)|].
apply inFP_cons in Hf as [Hf|Hf]; [rd_blk HWT HBt Hc (y_lm cx) 8192|].
apply inFP_cons in Hf as [Hf|Hf]; [rd_blk HWT HBt Hc (y_lc cx) 4096|].
apply inFP_cons in Hf as [Hf|Hf]; [rd_blk HWT HBt Hc (y_li cx) 8192|].
destruct Hf as (r & [] & _).
Qed.
Lemma tcx_nodup : forall cx, tcx_ranges cx -> tcx_seps cx -> NoDup [y_g cx; y_ti cx; y_lm cx; y_lc cx; y_li cx; y_ld cx].
Proof.
intros cx HRG HSEP.
pose proof HRG as ((_ & _ & _ & Rti4) & (_ & _ & _ & Rlm4) & (_ & _ & _ & Rlc4) & (_ & _ & _ & Rli4) & _ & (_ & _ & _ & Rld4) & (_ & _ & _ & Rg4) & _).
unfold y_tisz, y_cap, cap in *. cbn [fst snd] in Rti4, Rld4.
assert (N1 : y_ti cx <> y_lm cx) by (clear - HSEP Rti4 Rlm4; rsep HSEP 0%nat 1%nat; lia).
assert (N2 : y_ti cx <> y_lc cx) by (clear - HSEP Rti4 Rlc4; rsep HSEP 0%nat 2%nat; lia).
assert (N3 : y_ti cx <> y_li cx) by (clear - HSEP Rti4 Rli4; rsep HSEP 0%nat 3%nat; lia).
assert (N4 : y_ti cx <> y_ld cx) by (clear - HSEP Rti4 Rld4; rsep HSEP 0%nat 5%nat; lia).
assert (N5 : y_ti cx <> y_g cx) by (clear - HSEP Rti4 Rg4; rsep HSEP 0%nat 6%nat; lia).
assert (N6 : y_lm cx <> y_lc cx) by (clear - HSEP Rlm4 Rlc4; rsep HSEP 1%nat 2%nat; lia).
assert (N7 : y_lm cx <> y_li cx) by (clear - HSEP Rlm4 Rli4; rsep HSEP 1%nat 3%nat; lia).
assert (N8 : y_lm cx <> y_ld cx) by (clear - HSEP Rlm4 Rld4; rsep HSEP 1%nat 5%nat; lia).
assert (N9 : y_lm cx <> y_g cx) by (clear - HSEP Rlm4 Rg4; rsep HSEP 1%nat 6%nat; lia).
assert (N10 : y_lc cx <> y_li cx) by (clear - HSEP Rlc4 Rli4; rsep HSEP 2%nat 3%nat; lia).
assert (N11 : y_lc cx <> y_ld cx) by (clear - HSEP Rlc4 Rld4; rsep HSEP 2%nat 5%nat; lia).
assert (N12 : y_lc cx <> y_g cx) by (clear - HSEP Rlc4 Rg4; rsep HSEP 2%nat 6%nat; lia).
assert (N13 : y_li cx <> y_ld cx) by (clear - HSEP Rli4 Rld4; rsep HSEP 3%nat 5%nat; lia).
assert (N14 : y_li cx <> y_g cx) by (clear - HSEP Rli4 Rg4; rsep HSEP 3%nat 6%nat; lia).
assert (N15 : y_ld cx <> y_g cx) by (clear - HSEP Rld4 Rg4; rsep HSEP 5%nat 6%nat; lia).
clear - N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14 N15.
apply NoDup_ListNoDup. repeat (apply List.NoDup_cons; [cbn [In]; intuition congruence|]). apply List.NoDup_nil.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
