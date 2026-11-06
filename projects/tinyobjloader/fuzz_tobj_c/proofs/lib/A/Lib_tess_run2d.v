(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "valuation"; "sprop"; "SAlu"; "SLit"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "pair"; "prod"; "Some"; "bool"; "option"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states"; "K_rf"; "E_rf"; "Posts_r2"; "Pre_r2"; "SEL"; "rf_unit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.ZArith.BinInt.Z"; "land"; "lxor"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_run2d_chk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_run2d_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessRun2dAddr.

Lemma rf_diff : ltac2:(tb__ "0|4|
S13S11SeSaSeS0S0A2M0A1M1SaS3A1M2A2M3A1S26S1fS15A1S1fS14A1A2SfG3SdG1G2SbG0SdS0S0S18S5Z0A1A4ScG0A1A3SbS3S19ScS3A1A3A4A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma K_rf_swf : ltac2:(tb__ "0|0|
S13S10S6S1fS14A1A1S12A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma U_xor : ltac2:(tb__ "0|1|
S2S0S0S13S20S8Q40M0S1R3S4S25R2R1A3A2A2S28S8G0S1R3R2A2A2S8G0S1R3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. unfold alu64, alu. rewrite bv_xor_unsigned. reflexivity. Qed.
Lemma U_and : ltac2:(tb__ "0|1|
S2S0S0S13S20S8Q40M0S1R3S4S24R2R1A3A2A2S27S8G0S1R3R2A2A2S8G0S1R3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. unfold alu64, alu. rewrite bv_and_unsigned. reflexivity. Qed.

Lemma E_rf_K_rf : ltac2:(tb__ "0|0|
S1bS2SaS9Q40A1A1S21S1aS7R4S15R3R2R1A6S1aS7R5S14R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp.
  pose proof (SPA_facts_hold segs J rho E_rf tp w Hsp) as HF.
  change K_rf with (ax_setS E_rf (ax_S K_rf)).
  eapply (SPA_restate segs J rho E_rf (ax_S K_rf) tp w [(SEL, SLit 0)] [rf_unit]);
    [exact K_rf_swf | exact rf_diff | reflexivity | | | exact Hsp].
  all: concrete_facts HF; pick_facts HF [0%nat; 1%nat; 6%nat; 7%nat].
  all: cbv [rf_facts SEL I4 szI vN rf_unit] in *.
  -
    constructor; [|constructor]. cbn [fst snd].
    apply bv_eq. rewrite U_and, CursorGlue.U_add, U_sltu, U_xor, CursorGlue.U_add, !U_sll_lit, !CursorGlue.U_lit, !eval_var.
    zholds_rw_in H. zholds_rw_in H0. rewrite ?U_sll_lit, ?CursorGlue.U_add, ?U_sll_lit, ?CursorGlue.U_lit, ?eval_var in H0.
    zholds_rw_in H1. zholds_rw_in H2.
    pose proof (CursorGlue.U_range (rw rho 13)) as R13. pose proof (CursorGlue.U_range (rw rho 123)) as R123.
    change (2 ^ (2 mod 64)) with 4 in *. unfold M64v in *.
    replace ((bv_unsigned (rw rho 13) * 4) mod 18446744073709551616 + -4 mod 18446744073709551616)
      with (bv_unsigned (rw rho 123) * 4 + 18446744073709551616) by lia.
    rewrite (Z.mod_small (bv_unsigned (rw rho 123) * 4)) by lia.
    replace ((bv_unsigned (rw rho 123) * 4 + 18446744073709551616) mod 18446744073709551616)
      with (bv_unsigned (rw rho 123) * 4) by (rewrite <- Z.add_mod_idemp_r, Z.mod_same, Z.add_0_r, Z.mod_small by lia; reflexivity).
    rewrite Z.lxor_nilpotent. cbn. reflexivity.
  -
    constructor; [|constructor]. zholds_rw_goal.
    zholds_rw_in H. zholds_rw_in H0. zholds_rw_in H1. zholds_rw_in H2.
    rewrite ?U_sll_lit, ?CursorGlue.U_add, ?U_sll_lit, ?CursorGlue.U_lit, ?eval_var in H0.
    pose proof (CursorGlue.U_range (rw rho 13)) as R13. pose proof (CursorGlue.U_range (rw rho 123)) as R123.
    change (2 ^ (2 mod 64)) with 4 in *. unfold M64v in *.
    rewrite !Z.mod_small in H0 by lia. rewrite !Z.mod_small by lia. lia.
Qed.

Theorem run2d_sum : ltac2:(tb__ "0|0|
S21OF_;S1bS2SaS9Q40A1A1S1dS7R4R3A3S1eS7S23R4A3S22S7R6S1aS7R5S17R4R3A5S1cS7R5S23R4R3S16A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_r2 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_r2 cutpcs_r2 NF cuts_r2 exits_r2 (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_r2) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_r2.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply exit_postA. in_nth 0.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hsp. left. exists K_rf, rhoE. split; [cbn; tauto|]. apply E_rf_K_rf. exact Hsp.
  - left; reflexivity.
Qed.
