(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "iff"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "cell"; "sprop"; "obj_holds"; "rw"; "sstate"; "obj_range"; "rl"; "rm"; "smatch"; "eval"; "holds"; "ob_base"; "ob_cells"; "ob_dflt"; "outside_all"; "ss_objs"; "ob_hi"; "ob_lo"; "ss_facts"; "soff"; "ss_lenient"; "sv_eqb"; "swf"; "covered"; "mkSS"; "odefault"; "pairwise_disjoint"; "ss_fcsr"; "ss_fregs"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "DUnknown"; "SLit"; "c_off"; "c_val"; "c_width"; "rd"; "ro_addr"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "true"; "option"; "nat"; "list"; "pair"; "Some"; "cons"; "app"; "fst"; "None"; "andb"; "negb"; "false"; "nil"; "length"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "of_nat"; "modulo"; "sub"; "mul"; "opp"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zsupported"; "psupported"; "zholds"; "zl_of"; "zr_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.WithSegs.RE.Reab"; "m'"; "NREL"; "touched"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "setp"; "objs_matchb"; "set_par"; "obj_matchb"; "keys_distinct"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "in_rng"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "diffs_ok"; "set_rm"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "obj_vars_all"; "sprop_vars_all"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "cell_holds"; "le_byte"; "loc_addr"; "mc_loc"; "mc_w"; "MCell"; "VLo5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "byteview_of"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "odefault_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.WithSegs.Passengers"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.WithSegs.RE.Run"; "POST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface MallocIfaceI Contract Glue ReprGlue ObjBytes ZEval WalkArith WalkLink.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint set_par (rhoA rhoB : valuation) (l : list (positive * sv)) : valuation :=
  match l with
  | [] => rhoB
  | (j, e) :: t => set_par rhoA (rho_set_rw rhoB j (eval rhoA e)) t
  end.
Definition setp (rhoB : valuation) (l : list (positive * sv)) : valuation := set_par rhoB rhoB l.

Fixpoint keys_distinct (l : list positive) : bool :=
  match l with [] => true | j :: t => negb (in_vars t j) && keys_distinct t end.

Lemma set_par_rl : ltac2:(tb__ "0|0|
SaS3cS38S7S8A2A1SaS0S7S3cS48Q8A1A1F_;S11S63R3R1R2A3A1S11R1A1A3FrhoB;Fl;FrhoA;").
Proof. intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_rm : ltac2:(tb__ "0|0|
SaS3cS38S7S8A2A1SaS0S48Q40A1S3aS48Q8A1A1F_;S12S63R3R1R2A3A1S12R1A1A3FrhoB;Fl;FrhoA;").
Proof. intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_other : ltac2:(tb__ "0|1|
SaS3cS38S7S8A2M0A1SaS7S0S37S57S67G0S7S41S7S8A2R3A4R1A2S45A3S0S48Q40A1SeS63R5R3R4A3R2A2SeR3R2A2A3F_;Fu;FrhoB;Fl;FrhoA;").
Proof.
  intros rhoA l. induction l as [|[j e] t IH]; intros rhoB u Hu; [reflexivity|].
  cbn in Hu. apply Bool.orb_false_iff in Hu as [H1 H2]. cbn. rewrite IH by exact H2. cbn [rw rho_set_rw]. rewrite H1. reflexivity.
Qed.
Lemma set_par_get : ltac2:(tb__ "0|1|
SaS3cS38S7S8A2M0A1SaS7S8S0S37S65S67G0S7S41S7S8A2R4A4A1S39A3S33G0S3dS7S8R3R2A4R5A3S0S48Q40A1SeS63R7R5R6A3R4A2S14R7R3A2A3F_;F_;Fe;Fj;FrhoB;Fl;FrhoA;").
Proof.
  intros rhoA l. induction l as [|[j' e'] t IH]; intros rhoB j e Hd Hin; [destruct Hin|].
  cbn in Hd. apply andb_prop in Hd as [Hn Hd]. cbn. destruct Hin as [E|Hin].
  - injection E as E1 E2. subst j' e'.
    rewrite set_par_other. { cbn [rw rho_set_rw]. rewrite Pos.eqb_refl. reflexivity. }
    destruct (in_vars (map fst t) j); [discriminate|reflexivity].
  - apply IH; assumption.
Qed.
Lemma setp_get : ltac2:(tb__ "0|1|
SaS3cS38S7S8A2M0A1S7S8S0S37S65S67G0S7S41S7S8A2R3A4A1S39A3S33G0S3dS7S8R3R2A4R4A3S0S48Q40A1SeS61R6R5A2R4A2S14R6R3A2A3F_;F_;Fe;Fj;Fl;FrhoB;").
Proof. intros. unfold setp. apply set_par_get; assumption. Qed.
Lemma setp_other : ltac2:(tb__ "0|1|
SaS3cS38S7S8A2M0A1S7S0S37S57S67G0S7S41S7S8A2R2A4R1A2S45A3S0S48Q40A1SeS61R4R3A2R2A2SeR4R2A2A3F_;Fu;Fl;FrhoB;").
Proof. intros. unfold setp. apply set_par_other; assumption. Qed.
Lemma setp_rl : ltac2:(tb__ "0|0|
SaS3cS38S7S8A2A1S0S7S3cS48Q8A1A1F_;S11S61R2R1A2A1S11R2A1A3Fl;FrhoB;"). Proof. intros. apply set_par_rl. Qed.
Lemma setp_rm : ltac2:(tb__ "0|0|
SaS3cS38S7S8A2A1S0S48Q40A1S3aS48Q8A1A1F_;S12S61R2R1A2A1S12R2A1A3Fl;FrhoB;"). Proof. intros. apply set_par_rm. Qed.

Fixpoint scratch_of (d : list (sv * sv)) : list (positive * sv) :=
  match d with
  | [] => []
  | (e, SVar j) :: t => if (200 <=? j)%positive then (j, e) :: scratch_of t else scratch_of t
  | _ :: t => scratch_of t
  end.

Definition obj_matchb (o o' : sobj) : bool := ltac2:(tb__ "0|3|
S43S43S43S43S43S20S16Vo;A1S16Vo';A1A2S20S1cVo;A1S1cVo';A1A2A2S20S1bVo;A1S1bVo';A1A2A2S8fS18Vo;A1S18Vo';A1A2A2S34SbSbS35SbS8eR1A1M0S17Vo';A1M1A3Lc;S17Vo;A1M2A3A2S34SbSbS35SbG0G2A3Lc;G1A3A2").
Fixpoint objs_matchb (os os' : list sobj) : bool :=
  match os, os' with
  | [], [] => true
  | o :: t, o' :: t' => obj_matchb o o' && objs_matchb t t'
  | _, _ => false
  end.

Lemma cells_incl_of (cs cs' : list cell) : ltac2:(tb__ "0|0|
S0S37S34SbSbS35SbS8eR1A1Vcs';A3Lc;Vcs;A3S39A3SbS33SbR1Vcs;A3S33SbR2Vcs';A3F_;Fc;F_;").
Proof.
  intros H c Hc. pose proof (proj1 (forallb_forall _ _) H c Hc) as E. apply existsb_exists in E as (c' & Hc' & Ec).
  apply cell_eqb_sound in Ec. subst c'. exact Hc'.
Qed.

Lemma obj_matchb_sound o o' : ltac2:(tb__ "0|2|
S0S37S64Vo;Vo';A2S39A3S1S0S8S16Vo;A1S16Vo';A1A3S1S0S8S1cVo;A1S1cVo';A1A3S1S0S8S1bVo;A1S1bVo';A1A3S1S0S24S18Vo;A1S18Vo';A1A3S1SbS33SbR1S17Vo;A1M0A3S33SbR2S17Vo';A1M1A3F_;Fc;SbS33SbR1G1A3S33SbR2G0A3F_;Fc;A2A2A2A2A2F_;").
Proof.
  unfold obj_matchb. intros H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. apply odefault_eqb_sound in H4.
  repeat split; try assumption; apply cells_incl_of; assumption.
Qed.

Lemma obj_range_match rhoX o o' : ltac2:(tb__ "0|0|
S0S37S64Vo;Vo';A2S39A3S0S38S6S6A2S10VrhoX;Vo;A2S10VrhoX;Vo';A2A3F_;").
Proof. intros H. destruct (obj_matchb_sound o o' H) as (E1 & E2 & E3 & _). unfold obj_range, obj_lo_of, obj_hi_of. rewrite E1, E2, E3. reflexivity. Qed.

Lemma covered_match rhoX cs cs' off : ltac2:(tb__ "0|0|
SbS33SbR1Vcs;A3S33SbR2Vcs';A3F_;Fc;S22VrhoX;Vcs;Voff;A3S22VrhoX;Vcs';Voff;A3F_;F_;").
Proof. intros Hi Cv. unfold covered in *. apply Exists_exists in Cv as (c & Hc & IC). apply Exists_exists. exists c. auto. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma obj_holds_match rhoX msX o o' : ltac2:(tb__ "0|0|
S0S37S64Vo;Vo';A2S39A3SdVsegs;VrhoX;VmsX;Vo;A4SdVsegs;VrhoX;VmsX;Vo';A4F_;F_;").
Proof using .
  intros H HO. destruct (obj_matchb_sound o o' H) as (E1 & E2 & E3 & E4 & I1 & I2).
  destruct HO as (Hb & Hw & Hc & Hd & Hdi). unfold obj_holds, obj_lo_of, obj_hi_of in *.
  destruct o as [b1 l1 h1 c1 d1], o' as [b2 l2 h2 c2 d2]. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *. subst b2 l2 h2 d2.
  split; [exact Hb|]. split; [exact Hw|]. split.
  - apply Forall_forall. intros c Hc'. exact (proj1 (Forall_forall _ _) Hc c (I2 c Hc')).
  - split; [|exact Hdi]. intros off Hoff NC. apply Hd; [exact Hoff|]. intros Cv. apply NC. exact (covered_match rhoX _ _ off I1 Cv).
Qed.

Lemma objs_matchb_holds rhoX msX os os' : ltac2:(tb__ "0|1|
S0S37S62Vos;Vos';A2S39A3S66S9SdVsegs;VrhoX;VmsX;A3M0Vos;A3S66S9G0Vos';A3F_;F_;").
Proof using .
  revert os'. induction os as [|o os IH]; intros [|o' os'] H HF; cbn [objs_matchb] in H; try discriminate; [constructor|].
  apply andb_prop in H as [H1 H2]. apply Forall_cons_iff in HF as [HF0 HFt]. constructor; [exact (obj_holds_match rhoX msX o _ H1 HF0) | apply IH; assumption].
Qed.

Lemma objs_matchb_ranges rhoX os os' : ltac2:(tb__ "0|2|
S0S37S62Vos;Vos';A2S39A3S0S3cS38S6S6A2M0A1S67S9G0S10VrhoX;A1M1Vos;A4S67S9G0G1Vos';A4A3F_;").
Proof using .
  revert os'. induction os as [|o os IH]; intros [|o' os'] H; cbn [objs_matchb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. cbn [map]. rewrite (obj_range_match rhoX o _ H1), (IH os' H2). reflexivity.
Qed.

Lemma outside_all_match rhoX os os' a : ltac2:(tb__ "0|0|
S0S37S62Vos;Vos';A2S39A3S19VrhoX;Vos';Va;A3S19VrhoX;Vos;Va;A3F_;F_;").
Proof using .
  revert os'. induction os as [|o os IH]; intros [|o' os'] H HO; cbn [objs_matchb] in H; try discriminate; [constructor|].
  apply andb_prop in H as [H1 H2]. cbn [map] in HO. unfold outside_all in *. apply Forall_cons_iff in HO as [Hx Hl].
  constructor; [| exact (IH os' H2 Hl)]. cbn zeta in Hx |- *. rewrite (obj_range_match rhoX o o' H1). exact Hx.
Qed.

Section RE.
Variable rhoW : valuation.
Variables (zr : positive -> Z) (zl : positive -> list Z).

Hypothesis Hzr : ltac2:(tb__ "0|0|
S7S0S6S5dVrhoW;R1A2Vzr;R1A1A3Fi;").
Hypothesis Hzl : ltac2:(tb__ "0|0|
S7S0S3cS6A1S5cVrhoW;R1A2Vzl;R1A1A3Fl;").

Lemma zeval_rhoW : ltac2:(tb__ "0|0|
S8S0S6S58S5dVrhoW;A1S5cVrhoW;A1R1A3S58Vzr;Vzl;R1A3A3Fe;").
Proof using Hzl Hzr. intros e. apply zeval_ext; assumption. Qed.

Lemma EVW : ltac2:(tb__ "0|1|
S8S0S37S59R1A1S39A3S0S48Q40M0A1S14VrhoW;R2A2S49G0S58Vzr;Vzl;R2A3A2A3F_;Fe;").
Proof using Hzl Hzr.
  intros e He. rewrite <- zeval_rhoW. rewrite <- (eval_zeval rhoW e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma EV : ltac2:(tb__ "0|1|
SaS8S55VrhoW;R2A2S0S37S7aS56R2A2S39A3S0S37S59R3A1S39A3S0S48Q40M0A1S14R5R4A2S49G0S58Vzr;Vzl;R4A3A2A3F_;F_;F_;Fe;Frho';").
Proof using Hzl Hzr. intros rho' e Hag Hv Hs. rewrite (eval_agrees rhoW rho' e Hag Hv). apply EVW. exact Hs. Qed.

Lemma EVu : ltac2:(tb__ "0|0|
SaS8S55VrhoW;R2A2S0S37S7aS56R2A2S39A3S0S37S59R3A1S39A3S0S6S4aQ40S14R5R4A2A2S58Vzr;Vzl;R4A3A3F_;F_;F_;Fe;Frho';").
Proof using Hzl Hzr. intros rho' e Hag Hv Hs. rewrite (EV rho' e Hag Hv Hs). apply u64_of_sum. apply zeval_range. exact Hs. Qed.

Lemma HOLDS : ltac2:(tb__ "0|0|
SaScS55VrhoW;R2A2S0S37S7cS56R2A2S39A3S0S37S5aR3A1S39A3S4S15R5R4A2S5bVzr;Vzl;R4A3A2F_;F_;F_;Fp;Frho';").
Proof using Hzl Hzr.
  intros rho' p (Hw & Hl & _) Hv Hs.
  rewrite (holds_agree_vars below200 rho' rhoW p Hw Hl Hv).
  rewrite (holds_zholds rhoW p Hs). apply zholds_ext; assumption.
Qed.

Lemma rw_agrees : ltac2:(tb__ "0|0|
SaS7S55VrhoW;R2A2S0S37S56R2A1S39A3S0S48Q40A1SeR4R3A2SeVrhoW;R3A2A3F_;F_;Fj;Frho';").
Proof using . intros rho' j (Hw & _) Hj. exact (Hw j Hj). Qed.

Section Run.
Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S3cS71A1S72OF_;F_;").
Hypothesis HK : ltac2:(tb__ "0|0|
S69Vsegs;Vok;VK;A3").
Variable CUTS : list Z.

Lemma seg_run : ltac2:(tb__ "0|1|
S3bSfS3cS89A1M0S75SaS0S37S1fR4A1S45A3S94Pc8S28R5A1A2S0S3aG0A1S8bVsegs;R7VCUTS;R6S39A5S3eG0R5A2A3S55VrhoW;R4A2S89SaS73S33S89R3RaA3S55VrhoW;R3A2S68Vsegs;VK;S8aR5A1R4R3A5RcR4A1F_;F_;F_;Fw;Frho'';FLf;S74Vsegs;Vok;S68Vsegs;VK;R9R6A4R7A4F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using HK.
  intros fuel S leaves Q rho' Hl Hn Hrun Hag HQ.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple; exact (sym_run_sound_strict segs fuel CUTS S leaves ok K rho' Hl Hrun HK)].
  intros w (Lf & rho'' & Hin & Hab & Hsm & HKw). apply (HQ Lf rho'' w Hin).
  - eapply agrees_below; [exact Hag | exact Hab | exact Hn].
  - split; [exact Hsm | exact HKw].
Qed.

Definition POST (Cs : sstate) : assn := ltac2:(tb__ "0|0|
S73S2SaSaS1S55VrhoW;R1A2S68Vsegs;VK;VCs;R1R2A5A2Lrho'';A2Lw;").

Lemma from_POST : ltac2:(tb__ "0|0|
SfS75SaS55VrhoW;R1A2S74Vsegs;Vok;S68Vsegs;VK;R4R2A4R3A4F_;Frho';S74Vsegs;Vok;S91R3A1R2A4F_;FQ;FCs;").
Proof using . intros Cs Q H. unfold POST. apply triple_ex. intros rho'. apply triple_pure. apply H. Qed.

Lemma leaf_fact : ltac2:(tb__ "0|0|
SaSfS73ScS55VrhoW;R4A2S68Vsegs;VK;R4R5R3A5S33ScR3S1dR5A1A3S0S37S7cS56R4A2S39A3S0S37S5aR5A1S39A3S5bVzr;Vzl;R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';").
Proof using Hzl Hzr.
  intros rho' Lf w p Hag HSP Hin Hv Hs. apply (proj1 (HOLDS rho' p Hag Hv Hs)).
  exact (proj1 (Forall_forall _ _) (SP_facts_hold segs K rho' Lf w HSP) p Hin).
Qed.

Lemma ZF_holds : ltac2:(tb__ "0|0|
SaS3cScA1S55VrhoW;R2A2S0S37S34ScS7cS56A1R2A3S39A3S0S37S34ScS5aR3A3S39A3S66ScS5bVzr;Vzl;A2R4A3S66ScS15R6A1R5A3F_;F_;F_;F_;Fl;Frho';").
Proof using Hzl Hzr.
  intros rho' l Hag Hv Hs HZ. apply Forall_forall. intros p Hp.
  apply (proj2 (HOLDS rho' p Hag (proj1 (forallb_forall _ _) Hv p Hp) (proj1 (forallb_forall _ _) Hs p Hp))).
  exact (proj1 (Forall_forall _ _) HZ p Hp).
Qed.

Lemma agrees_setp : ltac2:(tb__ "0|1|
SaS3cS38S7S8A2M0A1S55VrhoW;R2A2S0S37S34S7S7S44S56R1A1A1Lj;S67G0S7S41S7S8A2R2A4A3S39A3S55VrhoW;S61R4R3A2A2F_;F_;Fl;FrhoB;").
Proof using .
  intros rhoB l (Hw & Hl & Hm) Hb. split; [|split; [intros l0; rewrite setp_rl; apply Hl | rewrite setp_rm; exact Hm]].
  intros u Hu. rewrite setp_other; [apply Hw; exact Hu|].
  rewrite forallb_forall in Hb. destruct (in_vars (map fst l) u) eqn:E; [|reflexivity].
  unfold in_vars in E. apply existsb_exists in E as (u' & Hu' & E). apply Pos.eqb_eq in E. subst u'.
  specialize (Hb u Hu'). rewrite Hu in Hb. discriminate.
Qed.

Lemma relinkp : ltac2:(tb__ "0|4|
SaSfSfS73S3cS38S7S8A2M0A1S3cS38S8S8A2A1M1S3cScA1M2S0S37S7dS7S44S57S67G0S7S41S7S8A2R4A4R1A2A1Lu;R6A2S39A3S0S37S21R6A1S39A3S0S3aS38G1G2A2M3A1S79R8R7A2S3eG3S3dG1G2R4R3A4A2A3S77S61RaR6A2R5A2S66ScS15S61RbR7A2A1R5A3S68Vsegs;VK;RbRcR9A5S68Vsegs;VK;RbS61RdR9A2RaA5F_;F_;F_;F_;F_;F_;Fnf;Fd;Fl;Fw;FS';FS;FrhoB;").
Proof using .
  intros rhoB S S' w l d nf Hvars Hwf Hsd Hd Hnf HSP.
  eapply SP_restate; [exact Hwf | exact Hsd | exact Hd | exact Hnf |].
  destruct HSP as [Hsm HK']. split; [|exact HK'].
  apply (smatch_agree_vars segs (fun u => negb (in_vars (map fst l) u)) rhoB); try assumption.
  - intros u Hu. symmetry. apply setp_other. destruct (in_vars (map fst l) u); [discriminate|reflexivity].
  - intros l0. rewrite setp_rl. reflexivity.
  - rewrite setp_rm. reflexivity.
Qed.

Lemma linkp : ltac2:(tb__ "0|6|
SfSfS3cS38S7S8A2M0A1S3cS38S8S8A2A1M1S3cScA1M2SaS73S0S37S7dS7S44S57S67G0S7S41S7S8A2R6A4M3R1A2A1Lu;R7A2S39A3S0S37S34S7S7S44S56R1A1A1Lj;G3A3S39A3S0S37S21R8A1S39A3S0S3aS38G1G2A2M4A1S79RaR9A2S3eG4S3dG1G2R7R6A4A2A3S55VrhoW;R6A2S55VrhoW;S61R7RaA2A2S66ScS15R8A1S1dRdA1A3S1S77S61R9RcA2M5RbA2S66ScS15G5A1RaA3A2F_;F_;S68Vsegs;VK;RdR8R7A5S91RdR8A2F_;F_;F_;F_;F_;F_;F_;Fw;FrhoB';Fnf;Fd;Fsets;FCs;FLf;").
Proof using .
  intros Lf Cs sets d nf rhoB' w Hvars Hb Hwf Hsd Hag Hsem HSP.
  pose proof (agrees_setp rhoB' sets Hag Hb) as Hag'.
  destruct (Hsem Hag' (SP_facts_hold segs K rhoB' Lf w HSP)) as [Hd Hnf].
  exists (setp rhoB' sets). split; [exact Hag'|].
  exact (relinkp rhoB' Lf Cs w sets d nf Hvars Hwf Hsd Hd Hnf HSP).
Qed.
End Run.

Variable D : Type.
Variables (obj_of : D -> sobj) (dlo dhi : D -> Z) (dcells : D -> list (Z * nat * sv)) (drom : D -> option positive).
Variable DS : D -> Prop.
Variable mW : word -> option byte.
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S48Q40A1S3aS48Q8A1A1F_;S12VrhoW;A1VmW;A3").

Hypothesis rngD : ltac2:(tb__ "0|0|
VD;SaVDS;R2A1S55VrhoW;R2A2S0S38S6S6A2S10R3Vobj_of;R4A1A2S3dS6S6Vdlo;R4A1Vdhi;R4A1A4A3F_;F_;FrhoX;Fd;").
Hypothesis range64D : ltac2:(tb__ "0|0|
VD;VDS;R1A1S1S4bZ0Vdlo;R2A1A2S4cVdhi;R2A1S4eZ2Z3fA2A2A2F_;Fd;").
Hypothesis cellsD : ltac2:(tb__ "0|1|
VD;S6S3bS8VDS;R4A1S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bR4R3A4R2A4Vdcells;R5A1A3S2SbSbS1S33SbR1S17Vobj_of;R7A1A1A3S1S0S8S2fR1A1R4A3S1S0S3bS54S30R1A1A1R5A3SaS55VrhoW;R1A2S0S6S4dS4aQ40S14R2S16Vobj_of;R9A1A1A2A2S1eR2S2eR3A1A2A2S4dVdlo;R9A1R8A2A3F_;FrhoX;A2A2A2Lc;A2F_;F_;Fe;Fw;Foff;Fd;").
Hypothesis cellsInD : ltac2:(tb__ "0|1|
VD;S6S3bS8VDS;R4A1S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bR4R3A4R2A4Vdcells;R5A1A3S1S4bZ0R5A2S1S4bS4dR5S4fR4A1A2S51Vdhi;R6A1Vdlo;R6A1A2A2S87R4U8A2A2A2F_;F_;Fe;Fw;Foff;Fd;").
Hypothesis semD : ltac2:(tb__ "0|1|
VD;S6S3bS8VDS;R4A1S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bR4R3A4R2A4Vdcells;R5A1A3S1S0S37S7aS56R3A2S39A3S0S37S59R3A1S39A3A2F_;F_;Fe;Fw;Foff;Fd;").
Hypothesis coverD : ltac2:(tb__ "0|2|
VD;S6VDS;R2A1S0S3aS7A1Vdrom;R3A1S42S7A1A3S1S4bVdlo;R4A1R3A2S4cR3Vdhi;R4A1A2A2S2S6S6S2S3bS3bS2S8S8S1S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bR3R2A4R1A4Vdcells;R8A1A3S1S4bR3S51R7Vdlo;R8A1A2M1A2S4cG1S4dR3S4fR2A1A2A2A2A2Le;A2Lw;A2Loff;A2F_;F_;F_;Fx;Fd;").
Hypothesis dunkD : ltac2:(tb__ "0|0|
VD;VDS;R1A1S0S3aS7A1Vdrom;R2A1S42S7A1A3S0S24S18Vobj_of;R3A1A1S2cA3F_;F_;Fd;").
Hypothesis romD : ltac2:(tb__ "0|2|
VD;S7S6VDS;R3A1S0S3aS7A1Vdrom;R4A1S3eS7R3A2A3S1S4bVdlo;R5A1R3A2S4cR3Vdhi;R5A1A2A2S1S0S37S32Vsegs;S49Q40R4A2M0A2S39A3S0S3aS48Q8A1M1A1VmW;G0A1S42G1A1A3A2F_;F_;F_;Fx;Fl;Fd;").

Lemma soff_litX rhoX z : ltac2:(tb__ "0|1|
S1S4bS53S4eZ2Z3eA2M0A1Vz;A2S4bVz;G0A2A2S0S6S1eVrhoX;S2dVz;A1A2Vz;A3F_;").
Proof using . intros. apply soff_lit_small. lia. Qed.
Lemma soff_semX rhoX e z : ltac2:(tb__ "0|0|
S55VrhoW;VrhoX;A2S0S37S7aS56Ve;A2S39A3S0S37S59Ve;A1S39A3S0S6S58Vzr;Vzl;Ve;A3Vz;A3S1S4bZ0Vz;A2S4cVz;S4eZ2Z3fA2A2A2S0S6S1eVrhoX;Ve;A2Vz;A3F_;F_;F_;F_;F_;").
Proof using Hzl Hzr.
  intros Hag Hv Hs Ez Hz. unfold soff. rewrite (EV rhoX e Hag Hv Hs), Ez. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  rewrite u64_of_sum by lia. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma in_ranges_decD (l : list D) x : ltac2:(tb__ "0|1|
S8dS2VD;VD;S1S33VD;R1Vl;A3S1S4bVdlo;R1A1Vx;A2S4cVx;Vdhi;R1A1A2A2A2Ld;A2M0S3G0A1A2").
Proof using .
  induction l as [|d t IH].
  - right. intros (d & [] & _).
  - destruct (Z_le_dec (dlo d) x) as [A|A]; [destruct (Z_lt_dec x (dhi d)) as [B|B]|].
    + left. exists d. split; [left; reflexivity | lia].
    + destruct IH as [Y|N]; [left; destruct Y as (d' & Hd' & R); exists d'; split; [right; exact Hd' | exact R]|].
      right. intros (d' & [<-|Hd'] & R); [lia|]. apply N. exists d'. auto.
    + destruct IH as [Y|N]; [left; destruct Y as (d' & Hd' & R); exists d'; split; [right; exact Hd' | exact R]|].
      right. intros (d' & [<-|Hd'] & R); [lia|]. apply N. exists d'. auto.
Qed.

Lemma od_cell_bytes d rhoX msX off w e : ltac2:(tb__ "0|3|
VDS;Vd;A1S55VrhoW;VrhoX;A2SdVsegs;VrhoX;VmsX;Vobj_of;Vd;A1A4S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bVoff;Vw;A4Ve;A4Vdcells;Vd;A1A3S3bS88R1Vw;A2S0S3aS48Q8M1A1M2A1S31VmsX;S49Q40S4dS4dVdlo;Vd;A1Voff;A2S4fR2A1A2A2A2S3eG2S49G1S7fS58Vzr;Vzl;Ve;A3Vw;R2A3A2A2A3F_;Fj;F_;F_;F_;F_;").
Proof using Hzl Hzr cellsD cellsInD semD.
  intros Hd Hag HO Hin j Hj.
  destruct (cellsD d off w e Hd Hin) as (c & Hc & Ev & Ew & Eoff).
  pose proof (cell_bytes_sym segs rhoX msX (obj_of d) c j HO Hc ltac:(rewrite Ew; exact Hj)) as B.
  rewrite (Eoff rhoX Hag), Ew, Ev in B. rewrite B. f_equal.
  destruct (semD d off w e Hd Hin) as [S1 S2].
  rewrite (EV rhoX e Hag S1 S2). apply nth_enc_bytes; [exact Hj|].
  exact (proj2 (proj2 (cellsInD d off w e Hd Hin))).
Qed.

Section Reab.
Variables (ms : machine_state).
Hypothesis Hrom : rom_ok segs ms.
Variables (tr : list event) (md : Model) (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agrees rhoW rhoF.

Variables (SF : sstate) (oStkF : sobj) (objsF : list sobj) (dsF dsC : list D).
Definition NREL : list sobj := map obj_of dsF.
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S0S3cS9A1S1aVSF;A1S3fS9VoStkF;VobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S0S37S62VobjsF;S5fA2S39A3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S13Vsegs;VrhoF;VSF;S3dS3cS71A1S6fVtr;S70VmsF;Vmd;A2A4A4").
Hypothesis HdsF : ltac2:(tb__ "0|0|
VD;S33VD;R1VdsF;A3VDS;R2A1F_;Fd;").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S0S37S34S9S7bS56A1S5fA3S39A3").

Variable unchanged : D -> Prop.
Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
VD;S33VD;R1VdsF;A3S5Vunchanged;R2A1S33VD;R2VdsC;A3A2F_;Fd;").
Hypothesis Hent_hold : ltac2:(tb__ "0|0|
VD;S33VD;R1VdsF;A3Vunchanged;R2A1SdVsegs;VrhoW;S76Vms;VmW;A2Vobj_of;R3A1A4F_;F_;Fd;").
Hypothesis HdsC_sub : ltac2:(tb__ "0|0|
VD;S33VD;R1VdsC;A3S1S33VD;R2VdsF;A3S0S3aS7A1Vdrom;R2A1S42S7A1A3A2F_;Fd;").

Lemma rngF d : ltac2:(tb__ "0|0|
S33VD;Vd;VdsF;A3S0S38S6S6A2S10VrhoF;Vobj_of;Vd;A1A2S3dS6S6Vdlo;Vd;A1Vdhi;Vd;A1A4A3F_;").
Proof using HagF HdsF rngD. intros Hd. apply rngD; [exact (HdsF d Hd) | exact HagF]. Qed.
Lemma rngW d : ltac2:(tb__ "0|0|
S33VD;Vd;VdsF;A3S0S38S6S6A2S10VrhoW;Vobj_of;Vd;A1A2S3dS6S6Vdlo;Vd;A1Vdhi;Vd;A1A4A3F_;").
Proof using HdsF rngD. intros Hd. apply rngD; [exact (HdsF d Hd) | apply agrees_refl]. Qed.

Lemma HOF : ltac2:(tb__ "0|0|
S66S9SdVsegs;VrhoF;VmsF;A3S3fS9VoStkF;S5fA3A3").
Proof using HSF_match HSF_objs HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  rewrite HSF_objs in Hall. apply Forall_cons_iff in Hall as [H0 Ht]. constructor; [exact H0|]. apply (objs_matchb_holds rhoF msF objsF NREL HSF_match). exact Ht.
Qed.
Lemma HOF_d d : ltac2:(tb__ "0|0|
S33VD;Vd;VdsF;A3SdVsegs;VrhoF;VmsF;Vobj_of;Vd;A1A4F_;").
Proof using HSF_match HSF_objs HsmF. intros Hd. apply (proj1 (Forall_forall _ _) HOF). right. unfold NREL. apply in_map. exact Hd. Qed.
Lemma rmF : ltac2:(tb__ "0|0|
S48Q40A1S0S3aS48Q8A1A1S12VrhoF;R1A2VmW;R1A1A3Fa;").
Proof using EmW HagF. intros a. destruct HagF as (_ & _ & E). rewrite E. rewrite EmW. reflexivity. Qed.
Lemma HfrF : ltac2:(tb__ "0|0|
S48Q40A1S19VrhoF;S3fS9VoStkF;S5fA3R1A3S0S3aS48Q8A1A1S6dVmsF;R2A2VmW;R2A1A3F_;Fa;").
Proof using EmW HSF_match HSF_objs HagF HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  intros a Ha. rewrite HSF_objs in Hfr. rewrite (Hfr a); [apply rmF|].
  apply Forall_cons_iff in Ha as [H0 Ht]. constructor; [exact H0|]. apply (outside_all_match rhoF objsF NREL a HSF_match). exact Ht.
Qed.
Lemma HromF : rom_ok segs msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
Lemma HroF : ro_clear segs msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.

Definition m' : word -> option byte := ltac2:(tb__ "0|0|
S93VrhoF;S5fVmsF;A3").

Lemma in_NREL x : ltac2:(tb__ "0|0|
S1S4bZ0Vx;A2S4cVx;S4eZ2Z40A2A2A2S4S92VrhoF;S5fS49Q40Vx;A2A3S2VD;VD;S1S33VD;R1VdsF;A3S1S4bVdlo;R1A1Vx;A2S4cVx;Vdhi;R1A1A2A2A2Ld;A2A2F_;").
Proof using HagF HdsF rngD.
  intros Hx. unfold in_ranges, NREL. rewrite u64_of_sum by lia. split.
  - intros (o & Ho & R). apply in_map_iff in Ho as (d & <- & Hd). exists d. rewrite (rngF d Hd) in R. cbn [fst snd] in R. auto.
  - intros (d & Hd & R). exists (obj_of d). split; [apply in_map; exact Hd|]. rewrite (rngF d Hd). exact R.
Qed.

Lemma m'_in d x : ltac2:(tb__ "0|1|
S33VD;Vd;VdsF;A3S1S4bVdlo;Vd;A1Vx;A2S4cVx;Vdhi;Vd;A1A2A2S1S4bZ0Vx;A2S4cVx;S4eZ2Z40A2A2A2S0S3aS48Q8A1A1S5eS49Q40Vx;A2M0A1S6dVmsF;G0A2A3F_;F_;F_;").
Proof using HagF HdsF rngD. intros Hd Hx R. unfold m'. apply release_in. apply (in_NREL x R). exists d. auto. Qed.
Lemma m'_out x : ltac2:(tb__ "0|1|
S1S4bZ0Vx;A2S4cVx;S4eZ2Z40A2A2A2VD;S33VD;R1VdsF;A3S3S1S4bVdlo;R2A1Vx;A2S4cVx;Vdhi;R2A1A2A2A1F_;Fd;S0S3aS48Q8A1A1S5eS49Q40Vx;A2M0A1VmW;G0A1A3F_;F_;").
Proof using EmW HagF HdsF rngD.
  intros R H. unfold m'. rewrite release_out; [apply rmF|]. intros IN. apply (in_NREL x R) in IN as (d & Hd & Hx). exact (H d Hd Hx).
Qed.

Lemma msF_out a : ltac2:(tb__ "0|0|
S19VrhoF;S3fS9VoStkF;S5fA3Va;A3S0S3aS48Q8A1A1S6dVmsF;Va;A2VmW;Va;A1A3F_;").
Proof using EmW HSF_match HSF_objs HagF HsmF. exact (HfrF a). Qed.

Lemma od_byte_same d x : ltac2:(tb__ "0|1|
S33VD;Vd;VdsF;A3Vunchanged;Vd;A1S1S4bVdlo;Vd;A1Vx;A2S4cVx;Vdhi;Vd;A1A2A2S1S0S3aS48Q8A1A1S6aVsegs;S5eS49Q40Vx;A2M0A3S6aVsegs;VmW;G0A3A3S0S37S6bVsegs;S5eG0A3S6bVsegs;VmW;G0A3A3A2F_;F_;F_;").
Proof using HSF_match HSF_objs HagF HdsF Hent_hold Hrom HsmF Hzl Hzr cellsD cellsInD coverD dunkD range64D rngD romD semD.
  intros Hd Hok Hx. pose proof (range64D d (HdsF d Hd)) as R64.
  pose proof (HOF_d d Hd) as HO. pose proof (Hent_hold d Hd Hok) as HE.
  rewrite (rd_of_at segs m' msF _ HromF (m'_in d x Hd Hx ltac:(lia))).
  destruct (drom d) as [l|] eqn:Er.
  -
    destruct (romD d l x (HdsF d Hd) Er Hx) as [RO N0].
    pose proof (HroF _ RO) as N1.
    split.
    + unfold rd, ms_read_byte, Glue.rd_of. rewrite N1, N0. rewrite HromF. reflexivity.
    + rewrite (wok_of_mem segs m' mW); [reflexivity|]. rewrite (m'_in d x Hd Hx) by lia. rewrite N1, N0. reflexivity.
  - destruct (coverD d x (HdsF d Hd) Er Hx) as (off & w & e & Hin & Hoff).
    pose proof (od_cell_bytes d rhoF msF off w e (HdsF d Hd) HagF HO Hin (Z.to_nat (x - dlo d - off)) ltac:(lia)) as B1.
    pose proof (od_cell_bytes d rhoW (with_mem ms mW) off w e (HdsF d Hd) (agrees_refl rhoW) HE Hin (Z.to_nat (x - dlo d - off)) ltac:(lia)) as B0.
    rewrite Z2Nat.id in B1, B0 by lia. replace (dlo d + off + (x - dlo d - off)) with x in B1, B0 by lia.
    rewrite (rd_with_mem segs ms mW _ Hrom) in B0.
    split; [rewrite B1, B0; reflexivity|].
    destruct (dunk_byte segs rhoF msF (obj_of d) x HO (dunkD d (HdsF d Hd) Er) ltac:(rewrite (rngF d Hd); exact Hx)) as [_ W1].
    destruct (dunk_byte segs rhoW (with_mem ms mW) (obj_of d) x HE (dunkD d (HdsF d Hd) Er) ltac:(rewrite (rngW d Hd); exact Hx)) as [_ W0].
    rewrite (wok_of_at segs m' msF _ (m'_in d x Hd Hx ltac:(lia)) W1). symmetry. apply wok_of_wview. exact W0.
Qed.

Definition touched (x : Z) : Prop := ltac2:(tb__ "0|0|
S2VD;VD;S1S33VD;R1VdsC;A3S1S4bVdlo;R1A1Vx;A2S4cVx;Vdhi;R1A1A2A2A2Ld;A2").

Lemma touched_dec x : ltac2:(tb__ "0|1|
S8dS60Vx;A1M0S3G0A1A2").
Proof using . exact (in_ranges_decD dsC x). Qed.

Let bv0 : byteview := ltac2:(tb__ "0|0|
S85S6aVsegs;VmW;A2S6bVsegs;VmW;A2A2").
Let rv0 : byteview := ltac2:(tb__ "0|0|
S85S6aVsegs;VmW;A2S48Q40A1S39L_;A2").
Let bv1 : byteview := ltac2:(tb__ "0|0|
S85S6aVsegs;S5eA2S6bVsegs;S5eA2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
S85S6aVsegs;S5eA2S48Q40A1S39L_;A2").

Lemma views_of_eq x : ltac2:(tb__ "0|2|
S0S3aS48Q8A1A1S6aVsegs;S5eS49Q40Vx;A2M0A3S6aVsegs;VmW;G0A3A3S0S37S6bVsegs;S5eG0A3S6bVsegs;VmW;G0A3A3S1S0S3aS6A1M1Vbv1;Vx;A1Vbv0;Vx;A1A3S0G1Vrv1;Vx;A1Vrv0;Vx;A1A3A2F_;F_;").
Proof using . intros E1 E2. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto. Qed.

Theorem V1 : ltac2:(tb__ "0|1|
S6S1S4bZ0R1A2S4cR1S4eZ2Z40A2A2A2S3S60R2A1A1S1S0S3aS6A1M0Vbv1;R3A1Vbv0;R3A1A3S0G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
Proof using EmW HSF_match HSF_objs HagF HdsF HdsF_ent Hent_hold Hrom HsmF Hzl Hzr cellsD cellsInD coverD dunkD range64D rngD romD semD.
  intros x Hx NT.
  destruct (in_ranges_dec rhoF NREL (Z_to_bv 64 x)) as [IN|OUT].
  - apply (in_NREL x Hx) in IN as (d & Hd & R).
    destruct (HdsF_ent d Hd) as [Hok | HC]; [| exfalso; apply NT; exists d; auto].
    destruct (od_byte_same d x Hd Hok R) as [E1 E2]. apply views_of_eq; assumption.
  - apply views_of_eq.
    + apply rd_of_mem. apply (m'_out x Hx). intros d Hd R. apply OUT. apply (in_NREL x Hx). exists d. auto.
    + apply wok_of_mem. apply (m'_out x Hx). intros d Hd R. apply OUT. apply (in_NREL x Hx). exists d. auto.
Qed.

Theorem VM : ltac2:(tb__ "0|0|
S6S1S4bZ0R1A2S4cR1S4eZ2Z40A2A2A2S60R2A1S3S0S3aS6A1Vbv1;R3A1S42S6A1A3A1F_;F_;Fx;").
Proof using HSF_match HSF_objs HagF HdsC_sub HdsF HsmF dunkD rngD.
  intros x Hx (d & HdC & R). destruct (HdsC_sub d HdC) as [Hd Hrom'].
  destruct (dunk_byte segs rhoF msF (obj_of d) x (HOF_d d Hd) (dunkD d (HdsF d Hd) Hrom') ltac:(rewrite (rngF d Hd); exact R)) as [[b Hb] W].
  unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  cbn [andb]. rewrite (wok_of_at segs m' msF _ (m'_in d x Hd R Hx) W).
  rewrite (rd_of_at segs m' msF _ HromF (m'_in d x Hd R Hx)), Hb. discriminate.
Qed.

Lemma chg_byte d off w e j : ltac2:(tb__ "0|1|
S33VD;Vd;VdsC;A3S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bVoff;Vw;A4Ve;A4Vdcells;Vd;A1A3S88Vj;Vw;A2S0S3aS6A1Vbv1;S4dS4dVdlo;Vd;A1Voff;A2S4fVj;A1A2A1S3eS6S7fS58Vzr;Vzl;Ve;A3Vw;Vj;A3A2A3F_;F_;F_;").
Proof using HSF_match HSF_objs HagF HdsC_sub HdsF HsmF Hzl Hzr cellsD cellsInD dunkD range64D rngD semD.
  intros HdC Hin Hj. destruct (HdsC_sub d HdC) as [Hd Hrom']. pose proof (range64D d (HdsF d Hd)) as R64.
  pose proof (cellsInD d off w e (HdsF d Hd) Hin) as (C1 & C2 & C3).
  assert (Hx : dlo d <= dlo d + off + Z.of_nat j < dhi d) by lia.
  pose proof (od_cell_bytes d rhoF msF off w e (HdsF d Hd) HagF (HOF_d d Hd) Hin j Hj) as B.
  destruct (dunk_byte segs rhoF msF (obj_of d) _ (HOF_d d Hd) (dunkD d (HdsF d Hd) Hrom') ltac:(rewrite (rngF d Hd); exact Hx)) as [_ W].
  unfold bv1, byteview_of.
  replace ((0 <=? dlo d + off + Z.of_nat j) && (dlo d + off + Z.of_nat j <? 2 ^ 64))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  cbn [andb]. rewrite (wok_of_at segs m' msF _ (m'_in d _ Hd Hx ltac:(lia)) W).
  rewrite (rd_of_at segs m' msF _ HromF (m'_in d _ Hd Hx ltac:(lia))), B. cbn iota beta. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma cell_from_od (Ly : layout) d off (w : nat) e c z : ltac2:(tb__ "0|2|
S33VD;Vd;VdsC;A3S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bVoff;Vw;A4Ve;A4Vdcells;Vd;A1A3S0S6S80VLy;S81Vc;A1A2S4dVdlo;Vd;A1Voff;A2A3S0S3bS82Vc;A1Vw;A3S0S3aS6A1S8cVLy;Vc;A2S3eS6Vz;A2A3S0S6S50Vz;S4eZ2S52Z8S4fVw;A1A2A2M1A2S50S58Vzr;Vzl;Ve;A3G1A2A3S7eVLy;Vbv1;Vc;A3F_;F_;F_;F_;F_;F_;").
Proof using HSF_match HSF_objs HagF HdsC_sub HdsF HsmF Hzl Hzr cellsD cellsInD dunkD range64D rngD semD.
  intros HdC Hin Ha Hw Hz Ez. destruct c as [loc wc val]. cbn [mc_loc mc_w mc_val cellZ] in *. subst wc.
  assert (BY : forall j, (j < w)%nat -> bv1 (loc_addr Ly loc + Z.of_nat j) = Some (le_byte z w j)).
  { intros j Hj. rewrite Ha, (chg_byte d off w e j HdC Hin Hj). f_equal. unfold le_byte. rewrite Ez. reflexivity. }
  unfold cell_holds. cbn [mc_loc mc_w mc_val]. destruct val; try (injection Hz as <-; exact BY). discriminate.
Qed.

Lemma cell_from_od_sub (Ly : layout) d off (w : nat) e (k : nat) c z : ltac2:(tb__ "0|2|
S33VD;Vd;VdsC;A3S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bVoff;Vw;A4Ve;A4Vdcells;Vd;A1A3S0S6S80VLy;S81Vc;A1A2S4dS4dVdlo;Vd;A1Voff;A2S4fVk;A1A2A3S87S86Vk;S82Vc;A1M1A2Vw;A2S0S3aS6A1S8cVLy;Vc;A2S3eS6Vz;A2A3S3bS88R1G1A2S0S6S7fVz;G1R2A3S7fS58Vzr;Vzl;Ve;A3Vw;S86Vk;R2A2A3A3F_;Fj;S7eVLy;Vbv1;Vc;A3F_;F_;F_;F_;F_;F_;").
Proof using HSF_match HSF_objs HagF HdsC_sub HdsF HsmF Hzl Hzr cellsD cellsInD dunkD range64D rngD semD.
  intros HdC Hin Ha Hw Hz Ez. destruct c as [loc wc val]. cbn [mc_loc mc_w mc_val cellZ] in *.
  assert (BY : forall j, (j < wc)%nat -> bv1 (loc_addr Ly loc + Z.of_nat j) = Some (le_byte z wc j)).
  { intros j Hj. rewrite Ha. replace (dlo d + off + Z.of_nat k + Z.of_nat j) with (dlo d + off + Z.of_nat (k + j)) by lia.
    rewrite (chg_byte d off w e (k + j) HdC Hin ltac:(lia)). f_equal. symmetry. exact (Ez j Hj). }
  unfold cell_holds. cbn [mc_loc mc_w mc_val]. destruct val; try (injection Hz as <-; exact BY). discriminate.
Qed.

Lemma le_byte_0 w j : le_byte 0 w j = 0.
Proof using . unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma cell_from_od_zero (Ly : layout) d off (w : nat) e (k : nat) c : ltac2:(tb__ "0|2|
S33VD;Vd;VdsC;A3S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bVoff;Vw;A4Ve;A4Vdcells;Vd;A1A3S0S6S80VLy;S81Vc;A1A2S4dS4dVdlo;Vd;A1Voff;A2S4fVk;A1A2A3S87S86Vk;S82Vc;A1A2Vw;A2S0S3aS6A1S8cVLy;Vc;A2S3eS6Z0M1A2A3S0S6S58Vzr;Vzl;Ve;A3G1A3S7eVLy;Vbv1;Vc;A3F_;F_;F_;F_;F_;F_;").
Proof using HSF_match HSF_objs HagF HdsC_sub HdsF HsmF Hzl Hzr cellsD cellsInD dunkD range64D rngD semD.
  intros HdC Hin Ha Hw Hz Ez. apply (cell_from_od_sub Ly d off w e k c 0 HdC Hin Ha Hw Hz).
  intros j Hj. rewrite Ez, !le_byte_0. reflexivity.
Qed.

Lemma cell5_from_od (Ly : layout) d off e loc a : ltac2:(tb__ "0|3|
S33VD;Vd;VdsC;A3S33S38S38S6S3bA2M0S8A2S3dG0S8S3dS6S3bVoff;U1M1A4Ve;A4Vdcells;Vd;A1A3S0S6S80VLy;Vloc;A2S4dVdlo;Vd;A1Voff;A2A3S1S4bZ0S58Vzr;Vzl;Ve;A3M2A2S4cG2Z100A2A2S0S6S50G2Z20A2Va;A3S7eVLy;Vbv1;S83Vloc;G1S84Va;A1A3A3F_;F_;F_;F_;F_;").
Proof using HSF_match HSF_objs HagF HdsC_sub HdsF HsmF Hzl Hzr cellsD cellsInD dunkD range64D rngD semD.
  intros HdC Hin Ha He Ea. unfold cell_holds. cbn [mc_loc mc_w mc_val].
  exists (zeval zr zl e). split; [|exact Ea].
  pose proof (chg_byte d off 1 e 0 HdC Hin ltac:(lia)) as B. cbn [Z.of_nat] in B. rewrite Z.add_0_r in B. rewrite Ha, B.
  f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite Z.mod_mod, Z.mod_small by lia. reflexivity.
Qed.

Lemma bv1_untouched x : ltac2:(tb__ "0|0|
S1S4bZ0Vx;A2S4cVx;S4eZ2Z40A2A2A2S3S60Vx;A1A1S0S3aS6A1Vbv1;Vx;A1Vbv0;Vx;A1A3F_;F_;").
Proof using EmW HSF_match HSF_objs HagF HdsF HdsF_ent Hent_hold Hrom HsmF Hzl Hzr cellsD cellsInD coverD dunkD range64D rngD romD rv0 rv1 semD. intros Hx NT. exact (proj1 (V1 x Hx NT)). Qed.

Lemma m'_kept a : ltac2:(tb__ "0|8|
S1S4bZ0Va;A2S4cVa;S4eZ2Z40A2A2A2VD;S33VD;R1VdsC;A3S3S1S4bVdlo;R2A1Va;A2S4cVa;Vdhi;R2A1A2A2A1F_;Fd;VD;S7S33VD;R2VdsF;A3S0S3aS7A1M0Vdrom;R3A1M1S3eS7R2A2A3S3S1S4bVdlo;R4A1Va;A2S4cVa;Vdhi;R4A1A2A2M2A1F_;F_;Fl;Fd;VD;S33VD;R1VdsF;A3M3Vunchanged;R2A1S0G0G1S42S7A1M4A3G2S0S3aS48Q8A1A1M5VmW;S49Q40Va;A2M6A1M7S6dVms;G6A2A3F_;F_;F_;F_;Fd;S5S0G5S5eG6A1G7A3S2VD;VD;S1G3S1Vunchanged;R1A1S1S0G0Vdrom;R1A1G4A3S1S4bVdlo;R1A1Va;A2S4cVa;Vdhi;R1A1A2A2A2A2A2Ld;A2A2F_;F_;F_;F_;").
Proof using EmW HagF HdsF HdsF_ent rngD.
  intros Ha NC NR _.
  destruct (in_ranges_decD dsF a) as [IN|OUT].
  - destruct IN as (d & Hd & R). right. exists d. split; [exact Hd|].
    destruct (HdsF_ent d Hd) as [U|Cd]; [|exfalso; exact (NC d Cd R)].
    split; [exact U|]. split; [|exact R]. destruct (drom d) as [l|] eqn:E; [exfalso; exact (NR d l Hd E R) | reflexivity].
  - left. apply m'_out; [exact Ha|]. intros d Hd R. apply OUT. exists d. auto.
Qed.

End Reab.
End RE.

Section Passengers.

Lemma obj_holds_on_mem rho ms m m' o : ltac2:(tb__ "0|1|
S48Q40M0A1S6cS10Vrho;Vo;A2S4aG0R1A2A2S0S3aS48Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fa;SdVsegs;Vrho;S76Vms;Vm;A2Vo;A4SdVsegs;Vrho;S76Vms;Vm';A2Vo;A4F_;F_;").
Proof using .
  intros Hm HO. apply (obj_holds_mem_ext segs rho (with_mem ms m) (with_mem ms m') o); [intros a; reflexivity | | exact HO].
  intros off Hoff. cbn [with_mem ms_mem]. apply Hm. destruct HO as (Hb & _).
  unfold in_rng, obj_range. cbn [fst snd]. rewrite u64_of_sum by lia. lia.
Qed.

Lemma release_tail : ltac2:(tb__ "0|8|
SaSfS3cS71A1M0S6eS72S3cS9A1M1G1S7S13Vsegs;R8R7S3dG0S6fR6S70R5R4A2A4A4S0G1S1aR8A1S40S9R4R3A3A3S23S29R9A1S2aR9A1S27R9A1S26R9A1S2bR9A1R5S1dR9A1R3S1fR9A1A9SfS0S37S21R1A1S39A3S2S48Q40M2A1M3S3aS48Q8A1A1M4F_;M5G5S1S13Vsegs;S78RdR1A2R3S3dG0S6fRbS70RaR9A2A4A4S1G3S9S33S9R1R9A3M6S3S6cS10R10R2A2S4aG2R3A2A2M7A1F_;Fp;S0G4R3R2A1S12RfR2A2A3F_;Fa;S1G3S9G6G7S0G4R5R4A1S6dReR4A2A3F_;F_;Fp;Fa;S66S9SdVsegs;RdS76RaR1A2A3R7A3A2A2A2Lm';A2F_;TS';F_;F_;Fnx;FP;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs P nx Hsm Hobjs S' Hwf.
  pose proof Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in Hall, Hpd, Hfr, Hrom.
  set (m' := fun a => if in_ranges_dec rho P a then ms_mem ms a else rm rho a).
  assert (IN1 : forall a, in_ranges rho P a <-> exists p, In p P /\ in_rng (obj_range rho p) (bv_unsigned a)).
  { intros a. unfold in_ranges, in_rng. split; intros (o' & H1 & H2); exists o'; auto. }
  assert (M'in : forall a p, In p P -> in_rng (obj_range rho p) (bv_unsigned a) -> m' a = ms_mem ms a).
  { intros a p Hp Ha. subst m'. cbn beta. destruct (in_ranges_dec rho P a) as [|Hn]; [reflexivity|]. exfalso. apply Hn. apply IN1. exists p. auto. }
  assert (M'out : forall a, (forall p, In p P -> ~ in_rng (obj_range rho p) (bv_unsigned a)) -> m' a = rm rho a).
  { intros a Ha. subst m'. cbn beta. destruct (in_ranges_dec rho P a) as [Hi|]; [|reflexivity]. exfalso. apply IN1 in Hi as (p & Hp & R). exact (Ha p Hp R). }
  exists m'. split; [|split; [exact M'out | split; [exact M'in|]]].
  -
    rewrite Hobjs in Hall, Hpd, Hfr. apply Forall_app in Hall as [HallA HallP].
    unfold smatch. cbn [fst snd cfg_ms cfg_model].
    assert (EVr : forall e, eval (set_rm rho m') e = eval rho e) by (intros e; induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity).
    pose proof (smatch_set_rm segs rho S (tr, mkCfg ms md) m') as SR.
    assert (Hsm1 : smatch segs (set_rm rho m') S (tr, mkCfg ms md)).
    { unfold set_rm. apply SR; [|exact Hsm]. intros a Ha. apply M'out. intros p Hp R.
      rewrite Hobjs in Ha. apply outside_all_app in Ha as [_ Ha]. unfold outside_all in Ha.
      pose proof (proj1 (Forall_forall _ _) Ha p Hp) as X. exact (X R). }
    pose proof Hsm1 as (_ & Hpc1 & Hpend1 & Hhalt1 & Hrom1 & Hro1 & Hr1 & Hf1 & Hc1 & Hv1 & (Hall1 & Hpd1 & Hfr1) & Hfa1).
    cbn [fst snd cfg_ms cfg_model] in Hall1, Hpd1, Hfr1.
    split; [exact Hwf|]. split; [exact Hpc1|]. split; [exact Hpend1|]. split; [exact Hhalt1|]. split; [exact Hrom1|]. split; [exact Hro1|].
    split; [exact Hr1|]. split; [exact Hf1|]. split; [exact Hc1|]. split; [exact Hv1|]. split; [|exact Hfa1].
    cbn [ss_objs]. rewrite Hobjs in Hall1, Hpd1, Hfr1. split; [|split].
    + apply Forall_app in Hall1 as [X _]. exact X.
    + exact (pairwise_disjoint_app_l _ _ _ Hpd1).
    + intros a Ha. cbn [set_rm rm].
      destruct (in_ranges_dec rho P a) as [Hi|Hn].
      * apply IN1 in Hi as (p & Hp & R). symmetry. exact (M'in a p Hp R).
      * rewrite (M'out a) by (intros p Hp R; apply Hn; apply IN1; exists p; auto).
        apply Hfr. apply outside_all_app. split; [|].
        -- unfold outside_all in Ha |- *. apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Ha o Ho) as X.
           cbn beta in X. rewrite obj_range_set_rm in X. exact X.
        -- unfold outside_all. apply Forall_forall. intros p Hp R. apply Hn. apply IN1. exists p. split; [exact Hp|]. exact R.
  -
    rewrite Hobjs in Hall. apply Forall_app in Hall as [_ HallP].
    apply Forall_forall. intros p Hp. apply (obj_holds_on_mem rho ms (ms_mem ms) m' p).
    + intros a Ha. exact (M'in a p Hp Ha).
    + replace (with_mem ms (ms_mem ms)) with ms by (destruct ms; reflexivity). exact (proj1 (Forall_forall _ _) HallP p Hp).
Qed.

Lemma restore_rm : ltac2:(tb__ "0|2|
SaSfS38S3cS71A1S6fA2S48Q40A1M0S3aS48Q8A1A1M1F_;S13Vsegs;R4R3R2A4G0S19R6S1aR5A1R1A3S0G1R4R2A1S12R7R2A2A3F_;Fa;S13Vsegs;S78R6R3A2R5R4A4F_;F_;Fm0;Fw;FS;Frho;").
Proof using . intros rho S w m0 Hsm Hm. unfold set_rm. apply smatch_set_rm; assumption. Qed.

Lemma obj_holds_agreeing (f : positive -> bool) rho rho' ms o : ltac2:(tb__ "0|0|
S7S0S37Vf;R1A1S39A3S0S48Q40A1SeVrho';R2A2SeVrho;R2A2A3F_;Fv;S7S0S3cS48Q8A1A1S11Vrho';R1A2S11Vrho;R1A2A3Fl;S0S37S7bVf;Vo;A2S39A3SdVsegs;Vrho;Vms;Vo;A4SdVsegs;Vrho';Vms;Vo;A4F_;F_;F_;F_;").
Proof using .
  intros Hv Hl Ho HO. apply (obj_holds_agree_vars segs f rho rho' ms o); [intros v Hfv; symmetry; apply Hv; exact Hfv | intros l; symmetry; apply Hl | exact Ho | exact HO].
Qed.
Lemma obj_range_agreeing (f : positive -> bool) rho rho' o : ltac2:(tb__ "0|0|
S7S0S37Vf;R1A1S39A3S0S48Q40A1SeVrho';R2A2SeVrho;R2A2A3F_;Fv;S7S0S3cS48Q8A1A1S11Vrho';R1A2S11Vrho;R1A2A3Fl;S0S37S7bVf;Vo;A2S39A3S0S38S6S6A2S10Vrho';Vo;A2S10Vrho;Vo;A2A3F_;F_;F_;").
Proof using .
  intros Hv Hl Ho. unfold obj_vars_all in Ho. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hb Hlo].
  unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite (eval_agree_vars f rho' rho _ Hv Hl Hb), (eval_agree_vars f rho' rho _ Hv Hl Hhi), (eval_agree_vars f rho' rho _ Hv Hl Hlo). reflexivity.
Qed.

Fixpoint remove_nth {A} (n : nat) (l : list A) : list A :=
  match l, n with [], _ => [] | _ :: t, O => t | x :: t, S n' => x :: remove_nth n' t end.
Lemma remove_nth_spec {A} (n : nat) (l : list A) x : ltac2:(tb__ "0|1|
S0S3aVA;A1S36VA;Vl;Vn;A3S3eVA;Vx;A2A3S2S3cVA;A1M0G0S2G0G0S1S0G0Vl;S40VA;R2S3fVA;Vx;R1A3A3A3S1S0G0S90VA;Vn;Vl;A3S40VA;R2R1A3A3S0S3bS47VA;R2A2Vn;A3A2A2Ll2;A2Ll1;A2F_;").
Proof using .
  revert n. induction l as [|y t IH]; intros [|n] H; cbn in H; try discriminate.
  - injection H as ->. exists [], t. auto.
  - destruct (IH n H) as (l1 & l2 & E1 & E2 & E3). exists (y :: l1), l2. cbn. rewrite <- E2, <- E3. rewrite E1 at 1. auto.
Qed.
Lemma pairwise_disjoint_app3 rho l1 x l2 : ltac2:(tb__ "0|0|
S25Vrho;S40S9Vl1;S3fS9Vx;Vl2;A3A3A2S25Vrho;S40S9S40S9Vl1;Vl2;A3S3fS9Vx;S46S9A1A3A3A2F_;").
Proof using .
  intros H. apply pairwise_disjoint_app_inv in H as (P1 & P2 & X12).
  destruct P2 as [Fx P2].
  apply SymFrame.pairwise_disjoint_app.
  - apply SymFrame.pairwise_disjoint_app; [exact P1 | exact P2 |]. intros o1 o2 H1 H2. apply X12; [exact H1 | right; exact H2].
  - split; [constructor | exact I].
  - intros o1 o2 H1 [<-|[]]. apply in_app_iff in H1 as [H1|H1].
    + exact (X12 o1 x H1 ltac:(left; reflexivity)).
    + pose proof (proj1 (Forall_forall _ _) Fx o1 H1) as D. cbn beta in D. clear - D. unfold SymState.ranges_disjoint in *. destruct (obj_range rho x) as [a b], (obj_range rho o1) as [c d]; cbn [fst snd] in *. lia.
Qed.
Lemma smatch_move_last : ltac2:(tb__ "0|0|
SaSfS38S3cS71A1S6fA2S3bS9S0S3aS9A1S36S9S1aR4A1R2A3S3eS9R1A2A3S23S29R5A1S2aR5A1S27R5A1S26R5A1S2bR5A1S40S9S90S9R3S1aR5A1A3S3fS9R2S46S9A1A3A3S1dR5A1S28R5A1S1fR5A1A9SfS13Vsegs;R7R6R5A4S13Vsegs;R8R2R6A4F_;TS';F_;Fo;Fn;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] n o Hn S' Hsm.
  destruct (remove_nth_spec n (ss_objs S) o Hn) as (l1 & l2 & E1 & E2 & _).
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model ss_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next ss_lenient S'].
  split.
  { unfold swf in *. cbn [ss_objs ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next S'].
    repeat (apply andb_prop in Hswf as [Hswf ?X]).
    rewrite E1 in X0. rewrite forallb_app in X0. apply andb_prop in X0 as [W1 W2]. cbn [forallb] in W2. apply andb_prop in W2 as [Wx W3].
    rewrite E2. repeat (apply andb_true_intro; split); try assumption.
    rewrite forallb_app. apply andb_true_intro. split; [rewrite forallb_app; apply andb_true_intro; auto|]. cbn. rewrite Wx. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  rewrite E1 in Hall, Hpd, Hfr. rewrite E2. split; [|split].
  - apply Forall_app in Hall as [A1 A2]. apply Forall_cons_iff in A2 as [Ax A3]. apply Forall_app. split; [apply Forall_app; auto|]. constructor; [exact Ax | constructor].
  - exact (pairwise_disjoint_app3 rho l1 o l2 Hpd).
  - intros a Ha. apply Hfr. unfold outside_all in *. apply Forall_app in Ha as [Ha Hx]. apply Forall_app in Ha as [H1 H2]. apply Forall_cons_iff in Hx as [Hx _].
    apply Forall_app. split; [exact H1|]. constructor; [exact Hx | exact H2].
Qed.
End Passengers.
End WithSegs.
