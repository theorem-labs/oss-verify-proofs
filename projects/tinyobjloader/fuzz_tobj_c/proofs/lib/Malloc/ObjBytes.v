(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "and"; "ex"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "obj_range"; "cell"; "eval"; "rd"; "rl"; "smatch"; "sstate"; "sv"; "mkVal"; "ob_base"; "obj_holds"; "rm"; "rw"; "c_width"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "DRom"; "DUnknown"; "c_off"; "c_val"; "covered"; "enc_bytes"; "rom_ok"; "soff"; "@Corelib.Init.Datatypes"; "option"; "list"; "bool"; "pair"; "Some"; "fst"; "true"; "None"; "cons"; "nil"; "prod"; "snd"; "app"; "nat"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "wview"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "in_ranges_dec"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.WithSegs"; "release_mem"; "@Stdlib.ZArith.BinInt.Z"; "to_nat"; "add"; "le"; "lt"; "of_nat"; "sub"; "@Corelib.Lists.ListDef"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Peano"; "lt"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma cell_bytes_sym : ltac2:(tb__ "0|3|
SaS3eS9ScS3dS15Vsegs;R5R4R3A4S53ScR3S1aR4A1A3S52R3S49S18R4A1A1A2S0S30S4Q8M0A1M1A1SeR7S5Q40M2S4aS4aS6G2SdR8S14R6A1A2A2S2fR8S2aR5A1A2A2S4dR4A1A2A2A2S34G1S4fG1R4S2dS49S18R5A1A1SdR8S2bR5A1A2A2S5G0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;FmsX;FrhoX;").
Proof using .
  intros rhoX msX o c j (Hb & _ & Hc & _) Hin Hj.
  pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (C1 & C2 & C3).
  unfold obj_lo_of, obj_hi_of in *.
  pose proof (rd_bytes_nth msX (Z.to_nat (c_width c)) _ _ j C3 Hj) as R.
  unfold oaddr in R. rewrite Z_to_bv_unsigned in R.
  assert (W : bv_wrap 64 (bv_unsigned (eval rhoX (ob_base o)) + soff rhoX (c_off c)) = bv_unsigned (eval rhoX (ob_base o)) + soff rhoX (c_off c)).
  { apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  rewrite W in R. apply R. lia.
Qed.

Lemma covered_dec : ltac2:(tb__ "0|1|
SaS31ScA1S7S45S2cR3R2R1A3M0S1G0A1A2Foff;Fcs;FrhoX;").
Proof using . intros rhoX cs off. unfold covered. apply Exists_dec. intros c. apply in_cell_dec. Qed.

Lemma dunk_byte : ltac2:(tb__ "0|4|
SaS3eS9S7S15Vsegs;R4R3R2A4S0S1eS1bR3A1S29A3S2S4bS35S7S7SbR6R4A2M0A3R3A2S4cR3S3bS7S7G0A3A2A2S2S3S4Q8A1M1G1S0S30G1A1M2SeR7S5Q40M3R5A2A2S34G1R1A2A3Lb;A2S1S0G2S40Vsegs;S3fR6A1S5G3R4A2A3S37G1A1A3A1A2F_;F_;F_;Fx;Fo;FmsX;FrhoX;").
Proof using .
  intros rhoX msX o x HO Hd Hx. pose proof HO as (Hb & Hw & Hc & Hdf & _).
  unfold obj_range, obj_lo_of, obj_hi_of in *. cbn [fst snd] in Hx.
  set (b := bv_unsigned (eval rhoX (ob_base o))) in *.
  replace x with (b + (x - b)) by lia. split.
  - destruct (covered_dec rhoX (ob_cells o) (x - b)) as [C|NC].
    + unfold covered in C. apply Exists_exists in C as (c & Hcin & IC). unfold in_cell in IC.
      pose proof (cell_bytes_sym rhoX msX o c (Z.to_nat (x - b - soff rhoX (c_off c))) HO Hcin ltac:(lia)) as R.
      fold b in R. rewrite Z2Nat.id in R by lia. replace (b + soff rhoX (c_off c) + (x - b - soff rhoX (c_off c))) with (b + (x - b)) in R by lia.
      eexists. exact R.
    + specialize (Hdf (x - b) ltac:(lia) NC). rewrite Hd in Hdf. exact Hdf.
  - apply Hw; [lia|]. rewrite Hd. reflexivity.
Qed.

Lemma drom_byte : ltac2:(tb__ "0|3|
SaS3eS9S8S7S15Vsegs;R5R4R3A4S0S1eS1bR4A1S28R3A1A3S0S31ScA1S1aR5A1S39ScA1A3S2S4bS35S7S7SbR8R6A2M0A3R4A2S4cR4S3bS7S7G0A3A2A2S0S30S4Q8M1A1M2A1SeR8S5Q40R5A2A2S34G2S4fG2S49S4eR5S35S7S7SbR9R7A2A3A2A1SfR9R6A2S5G1Z0A2A4A2A3F_;F_;F_;F_;Fx;Fl;Fo;FmsX;FrhoX;").
Proof using .
  intros rhoX msX o l x HO Hd Hc Hx. pose proof HO as (Hb & Hw & _ & Hdf & _).
  unfold obj_range, obj_lo_of, obj_hi_of in *. cbn [fst snd] in Hx |- *.
  set (b := bv_unsigned (eval rhoX (ob_base o))) in *.
  specialize (Hdf (x - b) ltac:(lia)). rewrite Hc in Hdf. specialize (Hdf ltac:(intros C; apply Exists_nil in C; exact C)).
  rewrite Hd in Hdf. cbn [dflt_holds] in Hdf. replace (b + (x - b)) with x in Hdf by lia.
  rewrite Hdf. do 2 f_equal. lia.
Qed.

Lemma wok_of_mem : ltac2:(tb__ "0|3|
S4Q40A1M0S30S4Q8A1A1M1F_;M2G2G0S0G1R3R1A1R2R1A1A3S0S32S47Vsegs;R4R2A3S47Vsegs;R3R2A3A3F_;Fw;Fmm;Fm;").
Proof using . intros m mm w E. unfold Glue.wok_of. rewrite E. reflexivity. Qed.
Lemma rd_of_mem : ltac2:(tb__ "0|3|
S4Q40A1M0S30S4Q8A1A1M1F_;M2G2G0S0G1R3R1A1R2R1A1A3S0G1S46Vsegs;R4R2A3S46Vsegs;R3R2A3A3F_;Fw;Fmm;Fm;").
Proof using . intros m mm w E. unfold Glue.rd_of. rewrite E. reflexivity. Qed.
Lemma rd_of_at : ltac2:(tb__ "0|2|
S4Q40A1M0S30S4Q8A1A1M1F_;S3eG0S2eVsegs;R2A2S0G1R4R2A1S3fR3R2A2A3S0G1S46Vsegs;R5R3A3SeR4R3A2A3F_;F_;Fa;FmsX;Fm;").
Proof using . intros. apply rd_of_eq_rd; assumption. Qed.
Lemma wok_of_at : ltac2:(tb__ "0|3|
S4Q40A1M0S30S4Q8A1M1A1M2F_;S3eG0S0G2R3R1A1S3fR2R1A2A3S1S0G2S40Vsegs;S3fR3A1R2A3S37G1A1A3A1S0S32S47Vsegs;R5R3A3S36A3F_;F_;Fa;FmsX;Fm;").
Proof using . intros m msX a E W. rewrite (wok_of_mem m (ms_mem msX) a E). apply wok_of_wview. exact W. Qed.

Lemma shape_range : ltac2:(tb__ "0|0|
SaS9S9S0S12S14R2A1S14R1A1A3S0S12S1dR3A1S1dR2A1A3S0S12S1cR4A1S1cR3A1A3S0S3aS7S7A2SbR6R5A2SbR6R4A2A3F_;F_;F_;Fb;Fa;FrhoX;").
Proof using . intros rhoX a b E1 E2 E3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite E1, E2, E3. reflexivity. Qed.

Definition release_mem (rho : valuation) (R : list sobj) (ms : machine_state) : word -> option byte := ltac2:(tb__ "0|2|
S4Q40A1S45S43Vrho;VR;R1A3M0S1G0A1M1A2S30S4Q8A1A1L_;S44Vrho;VR;R1A3G0S3fVms;R2A2L_;G1S16Vrho;R2A2L_;X45x2La;").

Lemma release_in : ltac2:(tb__ "0|0|
SaS31S9A1S3eS4Q40A1S43R4R3R1A3S0S30S4Q8A1A1S48R5R4R3R2A4S3fR3R2A2A3F_;Fa;Fms;FR;Frho;").
Proof using . intros rho R ms a H. unfold release_mem. destruct (in_ranges_dec rho R a) as [|N]; [reflexivity|]. exfalso. exact (N H). Qed.
Lemma release_out : ltac2:(tb__ "0|0|
SaS31S9A1S3eS4Q40A1S1S43R4R3R1A3A1S0S30S4Q8A1A1S48R5R4R3R2A4S16R5R2A2A3F_;Fa;Fms;FR;Frho;").
Proof using . intros rho R ms a H. unfold release_mem. destruct (in_ranges_dec rho R a) as [Y|]; [|reflexivity]. exfalso. exact (H Y). Qed.

Lemma eval_set_rm : ltac2:(tb__ "0|1|
SaS4Q40A1M0S30S4Q8A1A1F_;S12S0G0SdS13S17R3A1SfR3A1R2A3R1A2SdR3R1A2A3Fe;Fm;Frho;").
Proof using . intros rho m e. induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity. Qed.

Lemma obj_range_set_rm' : ltac2:(tb__ "0|0|
SaS4Q40A1S30S4Q8A1A1F_;S9S0S3aS7S7A2SbS13S17R3A1SfR3A1R2A3R1A2SbR3R1A2A3Fo;Fm;Frho;").
Proof using . intros rho m o. unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !eval_set_rm. reflexivity. Qed.

Lemma smatch_drop_suffix : ltac2:(tb__ "0|2|
SaS11S31S51A1M0S3eS50S31S9A1M1G1S8S10Vsegs;R8R7S33G0S41R6S42R5R4A2A4A4S0G1S23R8A1S3cS9R4R3A3A3S19S24R9A1S25R9A1S21R9A1S20R9A1S26R9A1R5S1fR9A1R3S22R9A1A9S11S0S32S27R1A1S36A3S4Q40A1S43RdR7R1A3S0S30S4Q8A1A1S3fRbR2A2S16ReR2A2A3F_;Fa;S10Vsegs;RdR3S33G0S41RbS42RaR9A2A4A4F_;F_;TS';F_;F_;Fnx;FR2;FR1;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md R1 R2 nx Hsm Hobjs S' Hwf Hagree.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Hobjs in Hm. destruct Hm as (Hall & Hpd & Hfr).
  apply Forall_app in Hall as [Hall _].
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [exact Hall|]. split; [eapply pairwise_disjoint_app_l; exact Hpd|].
  intros a Ha. destruct (in_ranges_dec rho R2 a) as [IN|OUT]; [apply Hagree; exact IN|].
  apply Hfr. apply outside_all_app_iff. split; [exact Ha|].
  apply Forall_forall. intros o Ho. cbn zeta. intros Hin. apply OUT. exists o. split; [exact Ho | exact Hin].
Qed.

Theorem smatch_release_tail : ltac2:(tb__ "0|2|
SaS11S31S51A1M0S3eS50S9S31S9A1M1S8S10Vsegs;R8R7S33G0S41R6S42R5R4A2A4A4S0G1S23R8A1S38S9R4R3A3A3S48RaR4R7A3S4Q40A1S30S4Q8A1A1F_;S19S24RaA1S25RaA1S21RaA1S20RaA1S26RaA1S38S9R6S39S9A1A3S1fRaA1R4S22RaA1A9S11S0S32S27R1A1S36A3S10Vsegs;S13S17RdA1SfRdA1R3A3R2S33G0S41RbS42RaR9A2A4A4F_;TS';Tm';F_;F_;Fnx;FR;Fo0;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md o0 R nx Hsm Hobjs m' S' Hwf.
  assert (Hsm1 : smatch segs (mkVal (rw rho) (rl rho) m') S (tr, mkCfg ms md)).
  { apply smatch_set_rm; [|exact Hsm]. intros a Ha. unfold m'. apply release_out.
    intros (o & Ho & Hin). rewrite Hobjs in Ha. inversion Ha as [|x l _ Ht]; subst.
    exact (proj1 (Forall_forall _ _) Ht o Ho Hin). }
  apply (smatch_drop_suffix (mkVal (rw rho) (rl rho) m') S tr ms md [o0] R nx Hsm1).
  - rewrite Hobjs. reflexivity.
  - exact Hwf.
  - intros a (o & Ho & Hin). cbn [rm]. unfold m'. symmetry. apply release_in. exists o. split; [exact Ho|].
    rewrite obj_range_set_rm' in Hin. exact Hin.
Qed.

End WithSegs.
