(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require CfgGlueA TobjJA.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartStates e7 StartHm e0.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From Stdlib Require Sorting.Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.

(* [comment removed for export] *)
Module Lib_scan_double_xc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "v173"; "CI"; "CN"; "C1"; "Ce"; "Cen"; "Cm"; "Cp"; "Cs"; "Cx"; "FUEL_sd"; "P_none"; "P_num"; "Pre_sd"; "cutpcs_sd"; "v172"; "vI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "SVar"; "sprop"; "SExt"; "SPUle"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SLTU"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_xc"; "vTop"; "X_b0"; "X_b1"; "X_in0"; "X_in1"; "nCp"; "varP"; "vchain"; "vcuts_sd"; "vexits_sd"; "vposts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymSoundW
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA.

Definition Fcp : list sprop := ltac2:(tb__ "0|1|
S2S1cS1eS19S21S1bPb8A1S1aS1fZ2M0Z1fA2A1A3S1aS20S1fG0Z20A2Z1A2A1A2S3S1cA1A3").
Definition Cp' : axst := ax_add_facts Fcp Cp.
Definition varP (e : sv) : sv := ltac2:(tb__ "0|1|
S19S24S1aS20S1fZ2Z40A2Z1M0A2A1S19S21S19S22S1dS6Q20Ve;A3S1aG0A1A3S19S23S1aZ0A1Ve;A3A3A3").
Definition nCp : vnodeA := mkVNA Cp' 4 (varP (SVar 184)).

Definition vchain : list vnodeA := ltac2:(tb__ "0|2|
S2S0S1S9Z1M0Z9c160A2ZfS8A3S2S0S1S9Z2M1Z9c198A2ZeS8A3S2S0S1S9Z3Z9c1d0A2ZdS8A3S2S0S1S9Z4Z9c208A2ZcS8A3S2S0S1S9Z5Z9c240A2ZbS8A3S2S0S1S9Z6Z9c278A2ZaS8A3S2S0S1S9Z7Z9c2b0A2Z9S8A3S2S0S1SaG0Z9c090A2Z11S8A3S2S0S1SaG1Z9c0c8A2Z10S8A3S3S0A1A3A3A3A3A3A3A3A3A3").
Definition vcuts_sd : list vnodeA := ltac2:(tb__ "0|1|
S4S0S2S0S1S15Z14S18A3S2S0S1SbZ13S17A3S2S0S1S10Z12S8A3S2S0S1SeZ8S8A3S2S0S1ScZ7M0S8A3S2S0S1SdG0S8A3S2S0S1S11Z6S8A3S2S0S2aS3S0A1A3A3A3A3A3A3A3A3S2cA3").

Definition X_in0 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_sd cutpcs_sd Cx sd_Lp) Pre_sd.
Definition X_in1 : axst := Eval vm_compute in nth 1 (leavesA_at FUEL_sd cutpcs_sd Cx sd_Lp) Pre_sd.
Definition X_b0 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_sd cutpcs_sd Cp sd_Lp) Pre_sd.
Definition X_b1 : axst := Eval vm_compute in nth 1 (leavesA_at FUEL_sd cutpcs_sd Cp sd_Lp) Pre_sd.
Goal length (leavesA_at FUEL_sd cutpcs_sd Cx sd_Lp) = 2%nat /\ length (leavesA_at FUEL_sd cutpcs_sd Cp sd_Lp) = 2%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vTop : sv := SLit (2 ^ 64 - 1).
Definition vposts_sd : list vnodeA := ltac2:(tb__ "0|1|
S2S0S1S13Z0M0S25A3S2S0S1S14G0S25A3S3S0A1A3A3").
Definition vexits_sd : list vnodeA := ltac2:(tb__ "0|3|
S4S0S2fS2S0S1S28Z5M0S8A3S2S0S1S29G0S8A3S2S0S1S26Z3M1S2bS1bPb8A1A1M2A3S2S0S1S27G1G2A3S3S0A1A3A3A3A3A3").

Lemma echeck_sd : ltac2:(tb__ "0|0|
S32S5S35S33S12S16S31S2dS2eA6S7A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition s_of (X : axst) : wsub := ltac2:(tb__ "0|0|
S34S31S30VX;A1S30SfA1A3").
Definition s_in0 := s_of X_in0.  Definition s_in1 := s_of X_in1.
Definition s_b0 := s_of X_b0.    Definition s_b1 := s_of X_b1.

Goal entailsA X_in0 Cp s_in0 = true /\ entailsA X_in1 Cp s_in1 = true /\ entailsA X_b0 Cp s_b0 = true /\ entailsA X_b1 Cp s_b1 = true
     /\ wsub_get s_b0 184 = SAluW ALU_SRL (SVar 184) (SLit 1) /\ wsub_get s_b1 184 = SAluW ALU_SRL (SVar 184) (SLit 1).
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

End Lib_scan_double_xc.

(* [comment removed for export] *)
Module Lib_scan_double_ex.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sv"; "valuation"; "SLit"; "SAluW"; "sprop"; "ss_facts"; "SVar"; "holds"; "SAlu"; "SPBranch"; "SPNot"; "SPUle"; "rw"; "@Corelib.Init.Logic"; "eq"; "not"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "le"; "lt"; "modulo"; "add"; "div"; "ltb"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_xc"; "varP"; "Fcp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRL"; "aluop"; "ALU_ADD"; "BC_EQ"; "@Corelib.Init.Datatypes"; "bool"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "v173"; "Posts_sd"; "Pre_sd"; "two40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymSoundW
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_xc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr.

Lemma w_shift_range : ltac2:(tb__ "0|2|
S4S26S3S3S14S0Q40M0S2R4SbS27S6R3R2R1A3S5S12Z2M1Z1fA2A1A3A2A2S0G0S2R4S5S13S12G1Z20A2Z1A2A1A2A2A2Fb;Fa;Fop;Frho;").
Proof.
  intros rho op a b. rewrite U_add, !U_lit. unfold M64v.
  pose proof (aluw_range rho op a b) as R. unfold soff, i32min, i32max in R.
  pose proof (urange (eval rho (SAluW op a b))) as UR.
  set (u := bv_unsigned (eval rho (SAluW op a b))) in *.
  assert (SU : bv_signed (eval rho (SAluW op a b)) = (if u <? 2 ^ 63 then u else u - 2 ^ 64)).
  { unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
    fold u. destruct (Z.ltb_spec u (2 ^ 63)).
    - rewrite Z.mod_small by lia. lia.
    - replace (u + 2 ^ 63) with ((u - 2 ^ 63) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite SU in R.
  change (2 ^ 31 mod 18446744073709551616) with (2 ^ 31). change ((2 ^ 32 - 1) mod 18446744073709551616) with (2 ^ 32 - 1).
  destruct (Z.ltb_spec u (2 ^ 63)).
  - rewrite Z.mod_small by lia. lia.
  - replace (u + 2 ^ 31) with ((u + 2 ^ 31 - 18446744073709551616) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma Fcp_ok : ltac2:(tb__ "0|0|
S20S4S26S3S3S10S3S21R5Pb8A2S6R3R2R1A3A3S24S7SaS1fR5R6A2A1S1eA3F_;Fb;Fa;Fop;Frho;Fs;").
Proof.
  intros s rho op a b Hs. unfold Fcp. constructor; [|constructor].
  apply (proj1 (sprop_subst_sound rho s (SPUle (SAlu ALU_ADD (SVar 184) (SLit (2 ^ 31))) (SLit (2 ^ 32 - 1))) _ eq_refl)).
  cbn [sprop_subst sv_subst]. rewrite Hs. cbn [holds]. rewrite mk_alu_sound.
  change (alu64 ALU_ADD (eval rho (SAluW op a b)) (eval rho (SLit (2 ^ 31))))
    with (eval rho (SAlu ALU_ADD (SAluW op a b) (SLit (2 ^ 31)))).
  apply w_shift_range.
Qed.

Lemma U_srlw1 : ltac2:(tb__ "0|2|
S4S3S10S1bS0Q40M0S2R2S6S25R1S5Z1A1A3A2A2S18S16S0G0S2R2R1A2A2S12Z2M1Z20A2A2G1A2A3Fa;Frho;").
Proof.
  intros rho a. cbn [eval]. unfold alu32, alu.
  pose proof (urange (eval rho a)) as R1.
  assert (M : bv_unsigned (bv_and (low32 (Z_to_bv 64 1)) (Z_to_bv 32 31)) = 1).
  { rewrite bv_and_unsigned, low32_umod. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). reflexivity. }
  assert (L : bv_unsigned (low32 (eval rho a)) = bv_unsigned (eval rho a) mod 2 ^ 32) by (apply low32_umod).
  assert (Hm : 0 <= bv_unsigned (eval rho a) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (R : bv_unsigned (bv_shiftr (low32 (eval rho a)) (bv_and (low32 (Z_to_bv 64 1)) (Z_to_bv 32 31)))
              = (bv_unsigned (eval rho a) mod 2 ^ 32) / 2).
  { rewrite bv_shiftr_unsigned, M, L. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
    first [ reflexivity
          | apply bv_wrap_small; change (bv_modulus 32) with (2 ^ 32); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] ]. }
  rewrite sext64_32_small by (rewrite R; apply Z.div_lt_upper_bound; lia). exact R.
Qed.

Lemma U_varP : ltac2:(tb__ "0|5|
S4S3S10S1bS0Q40M0S2R2S1dR1A1A2A2S13S13S12Z2M1Z40A2Z1M2A2S17S1aG1S16S0G0S2R2R1A2A2M3S12G1Z20A2A2A2S29S1bL_;S19Z0M4G3A2G2G4X29x2A2A2A3Fe;Frho;").
Proof.
  intros rho e. unfold varP. rewrite <- zv_sound. cbn [zv ext_width_ok]. rewrite !zv_sound.
  unfold M64v. pose proof (urange (eval rho e)) as R. set (u := bv_unsigned (eval rho e)) in *.
  assert (Hm : 0 <= u mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  change (Z.of_N 32) with 32. change (2 ^ (1 mod 64)) with 2.
  change (0 mod 18446744073709551616) with 0. change ((2 ^ 64 - 1) mod 18446744073709551616) with (2 ^ 64 - 1).
  assert (B : 0 <= (if 0 <? u then 1 else 0) <= 1) by (destruct (0 <? u); lia).
  rewrite (Z.mod_small (u mod 2 ^ 32 * 2)) by lia.
  rewrite (Z.mod_small (u mod 2 ^ 32 * 2 + _)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma varP_srlw_lt : ltac2:(tb__ "0|4|
S4S20S10S3S21R1Pb8M0A2S6S25S9G0A1M1S5Z1A1A3A3S11S10S1bS0Q40M2SfR3G0A2A2Z0A3A1S15S0G2S2R4S1dG1A1M3A2A2S0G2S2S1fR4R3A2G3A2A2A2F_;F_;Fs;Frho;").
Proof.
  intros rho s Hs Hnz. rewrite !U_varP.
  change (eval (rho_sub rho s) (SVar 184)) with (rw (rho_sub rho s) 184%positive). cbn [rw rho_sub]. rewrite Hs.
  rewrite U_srlw1. rewrite !eval_var.
  pose proof (urange (rw rho 184%positive)) as R. set (u := bv_unsigned (rw rho 184%positive)) in *.
  assert (Hm : 0 <= u mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  set (h := u mod 2 ^ 32 / 2) in *.
  assert (Hh : 0 <= h) by (subst h; apply Z.div_pos; lia).
  assert (Hh2 : 2 * h <= u mod 2 ^ 32) by (subst h; apply Z.mul_div_le; lia).
  assert (Hh3 : h < 2 ^ 31) by (subst h; apply Z.div_lt_upper_bound; lia).
  rewrite (Z.mod_small h) by lia.
  replace (if 0 <? u then 1 else 0) with 1 by (destruct (Z.ltb_spec 0 u); lia).
  destruct (Z.ltb_spec 0 h); lia.
Qed.

Lemma X_b_var : ltac2:(tb__ "0|4|
S23S20S4S10S3S21R2Pb8M0A2S6S25S9G0A1M1S5Z1A1A3A3S30S7SdScS28G1S5Z0A1A3A1S8S22R4A1A1A3S24S7SaR3A1S8S22R5A1A1A3S15S0Q40M2S2R4S1dG1A1M3A2A2S0G2S2S1fR4R5A2G3A2A2A2F_;F_;F_;Frho;Fs;FX;").
Proof.
  intros X s rho Hs Hin HF. apply (varP_srlw_lt rho s Hs).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hnz. apply holds_nbeq in Hnz.
  rewrite eval_var, U_lit in Hnz. unfold M64v in Hnz. rewrite Z.mod_small in Hnz by lia. exact Hnz.
Qed.

Lemma X_in_var : ltac2:(tb__ "0|1|
S23S20S4S30S7SeS2bS5S2eA1A2S8S22R3A1A1A3S24S7SaR2A1S8S22R4A1A1A3S14S0Q40M0S2R3S2bA2A2S0G0S2S1fR3R4A2S1dS9Pb8A1A1A2A2A2F_;F_;Frho;Fs;FX;").
Proof.
  intros X s rho Hin HF. rewrite U_varP.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hle. cbn [holds] in Hle.
  change (bv_unsigned (eval rho v173) <= bv_unsigned (eval rho (SLit two40))) in Hle.
  rewrite (U_lit rho two40) in Hle. unfold two40, M64v in Hle. rewrite Z.mod_small in Hle by lia.
  pose proof (urange (eval (rho_sub rho s) (SVar 184))) as R. set (u := bv_unsigned (eval (rho_sub rho s) (SVar 184))) in *.
  assert (Hm : 0 <= u mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (0 <? u); unfold v173 in *; lia.
Qed.

Theorem scan_double_sum_ex : ltac2:(tb__ "0|0|
S34S4S2aS1Q40A1A1S35S1cS2fR3A3S31S1cS33S1cR4S2dR3R2A5S32S1cR4S2fR3R2S2cA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  set (J' := withGA (fun r => agree_below NF rho r) J).
  assert (HstJ' : stableA segs NF J').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_sd rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_sd with (vna_state (mkVNA Pre_sd 20 vI)).
  apply (cfg_complete_autoIA segs FUEL_sd cutpcs_sd NF vcuts_sd vexits_sd J' (LQA segs J NF rho tp Posts_sd) tp HstJ').
  - intros n Hin. unfold vcuts_sd, vchain in Hin. cbn [app] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]; cbv; congruence.
  - exact echeck_sd.
  - intros E rhoE HinE. unfold vexits_sd, vposts_sd in HinE. cbn [app] in HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + apply (eexit_post_IA0 segs J NF rho vcuts_sd Posts_sd (mkVNA P_none 0 vTop)). in_nth 0.
    + apply (eexit_post_IA0 segs J NF rho vcuts_sd Posts_sd (mkVNA P_num 0 vTop)). in_nth 1.
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_in0 5 v173) nCp Fcp Cp s_in0 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_ok s_in0 r _ _ _ ltac:(vm_compute; reflexivity))|].
      right. split; [| cbn; lia]. cbn [vna_var]. exact (X_in_var X_in0 s_in0 r ltac:(vm_compute; tauto) HF).
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_in1 5 v173) nCp Fcp Cp s_in1 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_ok s_in1 r _ _ _ ltac:(vm_compute; reflexivity))|].
      right. split; [| cbn; lia]. cbn [vna_var]. exact (X_in_var X_in1 s_in1 r ltac:(vm_compute; tauto) HF).
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_b0 3 (varP (SVar 184))) nCp Fcp Cp s_b0 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_ok s_b0 r _ _ _ ltac:(vm_compute; reflexivity))|].
      left. cbn [vna_var]. exact (X_b_var X_b0 s_b0 r ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto) HF).
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_b1 3 (varP (SVar 184))) nCp Fcp Cp s_b1 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_ok s_b1 r _ _ _ ltac:(vm_compute; reflexivity))|].
      left. cbn [vna_var]. exact (X_b_var X_b1 s_b1 r ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto) HF).
  - left; reflexivity.
Qed.
End Lib_scan_double_ex.

(* [comment removed for export] *)
Module Lib_load_obj_boxkit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "cons"; "true"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "JA"; "NDA"; "amode"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bxK"; "bxV"; "bxt"; "bitem"; "bxN"; "bxS"; "BIc"; "bd_nn"; "bd_wpos"; "bsumK"; "bsumV"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Init.Logic"; "and"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Box.
Variable AInv : ltac2:(tb__ "0|0|
S22S9S2S1cQ40A1A1S21OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S3S3SaSaA2SaA2A1").
Variable PA : AA -> Prop.

Lemma SPA_rebox : ltac2:(tb__ "0|2|
S13S13S2S3S8S8A2A1S2S3S3S8SaA2S8A2A1S2S14A1M0G0SfS1eS9S2S1cQ40A1A1S1dS0S16RbA1S16RaA1A2S0S15RcA1S15RbA1A2S0Z0M1S12RcA1A2S0G1S11RdA1A2S20S4S19RaA1S6A3S20S4S19RcA1S6A3S18RdR9A2S1fS18RdRaA2S1fS0S1S1bRdRaA2S12R11A1A2S1S1bReRaA2S12R12A1A2A2S0S1S1aRdRaA2S11R11A1A2S1S1aReRaA2S11R12A1A2A2A2A2F_;F_;ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R11VPA;SeRfReRdRbA4AcRaR9R8R7A6ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R11VPA;SeR10RfRdRcA4AcRbRaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd';Fbd;Ffr;Ftv;FBX';FBX;").
Proof.
  intros BX BX' tv fr bd bd' am A rho tp w HS HN HV0 HK0 Hw' HI [Hsm (Ai & kc & HJ)].
  split; [exact Hsm|]. exists Ai, kc.
  apply (JAi_rebx AInv CST XGL NP Kc rho0 P0f FB FF BX BX' PA (NDA tv fr bd am) bd' Ai kc rho tp _ _); [|exact HN|exact HJ].
  cbn [nd_bd nd_am]. intros HBU HCK Hkc. pose proof HBU as (A1 & A2 & A3 & A4 & A5 & Hw & Hnn & B1 & B2).
  destruct (HI Hw Hnn) as (Hnn' & LV & LK).
  pose proof (apot_range am rho) as [[R1 _] [R2 _]].
  unfold bxa, bxV, bxK, capK in *. cbn [fst snd] in *. split; [|lia].
  unfold BUD. cbn [fst snd]. split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact Hw'|]. split; [exact Hnn'|]. lia.
Qed.

Lemma SPA_box_out : ltac2:(tb__ "0|4|
S13S13SaSaS2S3S8S8A2A1S2S3S3S8SaA2S8A2A1S2S14A1M0G0SfS1eS9S2S1cQ40A1A1S1dS0S16RcA1S16RdA1A2S0S15RdA1S15ReA1A2S0Z0M1S12RfA1A2S0G1S11R10A1A2S0S1S12R11A1RfA2S12R10A1A2S0S1S11R12A1RfA2S11R11A1A2S0G1R11A2M2G2ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R14VPA;SeR11R10S7S14RfReA3RdA4AcRcRbRaR9A6ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R16VPA;SeR12R11S5S14S17Z1M3G1R14A3S5S14S17G1G3R13A3RfA3A3ReA4AcRdRcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fam;Frest;Fpre;Ffr;Ftv;Fk;Fc;FBXL;FBX;").
Proof.
  intros BX BXL c k tv fr pre rest am A rho tp w HS HN HV0 HK0 HV HK Hc Hk HW.
  assert (Hwp : bd_wpos (pre ++ rest) = true).
  { destruct HW as [_ (Ai & kc & HJ)]. destruct (JAi_proj_BUD AInv CST XGL NP Kc rho0 P0f FB FF BXL PA _ Ai kc rho tp _ _ HJ) as ((_ & _ & _ & _ & _ & Hw & _) & _). exact Hw. }
  assert (Hwr : bd_wpos pre = true /\ bd_wpos rest = true) by (unfold bd_wpos in *; rewrite forallb_app in Hwp; apply andb_prop in Hwp; exact Hwp).
  apply (SPA_rebox BXL BX tv fr (pre ++ rest) (BIc 1 0 c :: BIc 0 1 k :: rest) am A rho tp w HS HN HV0 HK0); [| |exact HW].
  - unfold bd_wpos in *. unfold BIc. cbn [forallb bi_v bi_k]. rewrite (proj2 Hwr). reflexivity.
  - intros _ Hnn. unfold bd_nn in Hnn. apply Forall_app in Hnn as [Hn1 Hn2].
    destruct (bsum_nonneg pre rho (proj1 Hwr) Hn1) as [S1 S2].
    rewrite bsumV_app, bsumK_app. unfold BIc. cbn [bsumV bsumK bi_v bi_k]. unfold bival at 1 2 3 4. cbn [bi_f bi_c lfval].
    split; [|lia]. unfold bd_nn. constructor; [unfold bival; cbn [bi_f bi_c lfval]; lia|]. constructor; [unfold bival; cbn [bi_f bi_c lfval]; lia | exact Hn2].
Qed.

Lemma SPA_JA_P0_get : ltac2:(tb__ "0|0|
S13S10S1eS9S2S1cQ40A1A1S1dScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R6VPA;R5AcR4R3R2R1A6VP0f;Vrho0;A1F_;Fw;Ftp;Frho;FA;Fnd;FBX;").
Proof.
  intros BX nd A rho tp w [_ (Ai & kc & HJ)]. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). exact HP0.
Qed.
Lemma SPA_JA_P0_set : ltac2:(tb__ "0|0|
S9OF_;S13S10S1eS9S2S1cQ40A1A1S1dR7Vrho0;A1ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R7VPA;R6AcR5R4R3R2A6ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;R9VFB;VFF;R8VPA;R7AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fnd;FBX;FP0f';").
Proof.
  intros P0f' BX nd A rho tp w HP' [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK|]. split; [exact HP'|]. split; [exact HXA|]. split; [exact HBU|]. split; [exact HPA|]. split; [exact HCK | exact HCN].
Qed.
End Box.
End Lib_load_obj_boxkit.

(* [comment removed for export] *)
Module Start1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "prod"; "true"; "option"; "Some"; "pair"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "sym_runA"; "mkAX"; "axst"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "SLit"; "rw"; "sprop"; "rm"; "SVar"; "reg_sv"; "SAlu"; "SPUle"; "sstate"; "agree_below"; "eval"; "sprop_below"; "ss_next"; "sv_below"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "leaf"; "RsSymJump"; "mkLeaf"; "sym_run"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "event"; "vm_limit"; "vm_noaccess"; "vm_reserved"; "VmMaps"; "mkVmMapsFull"; "vm_brk"; "vm_init_sp"; "vm_mmap_base"; "vm_start_brk"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States"; "L_hm"; "E_b3"; "E_b4"; "E_s2"; "E_b2"; "E_b2_S"; "SPINb2"; "SPINb3"; "SPINb4"; "S_hm"; "E_b3_S"; "E_b4_S"; "S_ctor_x"; "Z1"; "Z2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "agree_vars"; "objs_clear_e"; "RMH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Start1.Seg1"; "m2"; "m3"; "m4"; "Post1"; "vcuts1"; "vexits1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Start1"; "ECALL_MMAP"; "G1"; "FUEL1"; "cutpcs1"; "F1x"; "S_b4ok"; "cuts1"; "sd_hm"; "HMCUT"; "S_b2fail"; "S_b2ok"; "S_b3fail"; "S_b3ok"; "S_b4fail"; "Xhm"; "ZHEAD"; "exits1"; "rho_hm"; "xf1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartStates"; "S_ctor"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib"; "Kx"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm"; "smear_sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init StartStates StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECALL_MMAP : Z := 0x7050c.
Definition ZHEAD : Z := 0x70178.
Definition HMCUT : Z := 0x713c0.

Definition xf1 : list xform := ltac2:(tb__ "0|0|
S1S7dS7eU6S17Z180ec0A1A2S1S7dS7eU7S17Z181ec0A1A2S1S7dS7eU8S17Z182ec0A1A2S0S7dA1A3A3A3").

Definition F1x : list sprop := ltac2:(tb__ "0|1|
S1S19S1eS1bP1A1M0S1bP4A1A2S1S19S1eG0S1bP6A1A2S0S19A1A3A3").
Lemma xf1_ok : ltac2:(tb__ "0|0|
S12S5S1fA1S7fS86S68S77A2S76A2S6S1fS47A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1x_below : ltac2:(tb__ "0|0|
S12S8S88S19S22S23S77A1A1S68A3S4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma run_hm : ltac2:(tb__ "0|1|
S12S5S2S2aA1M0A1S2dS9Ufa0S1S10S6cS0S10A1A3S47S4A5S6G0S1S2aS2cS3bS29A2S0S2aA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run_b2 : ltac2:(tb__ "0|1|
S12S5S2S2aA1M0A1S2dS9Ufa0S1S10S64S0S10A1A3S44S4A5S6G0S1S2aS2cS40S29A2S0S2aA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Xhm : sv := SAlu ALU_ADD (SVar 1%positive) (SLit (-160)).
Lemma L_hm_a0 : ltac2:(tb__ "0|0|
S12S15S1cS3bZaA2S85S72S1S10Z1S1S10Z2S1S10Z4S1S10Z8S1S10Z10S1S10Z20S0S10A1A3A3A3A3A3A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sd_hm := Eval vm_compute in (match state_diff L_hm S_hm with Some p => p | None => ([], []) end).
Lemma sd_hm_eq : ltac2:(tb__ "0|1|
S12S5S3S2S3S15S15A2A1S2S19A1A2M0A1S57S3bS44A2S6G0S6bA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd_hm_shape : ltac2:(tb__ "0|3|
S12S3S2S3S15S15A2M0A1M1S2S19A1M2A2S6bS7G1G2S1G0S7S15S15S1cS3bZaA2S17S50S4fZ2Z2fA2Z1A2A1A4S1G0S7S15S15S1cS3bZfA2S1bP19A1A4S0G0A1A3A3S0S19A1A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma swf_S_hm : swf S_hm = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma next_L_hm : ss_next L_hm = 25%positive.
Proof. reflexivity. Qed.
Lemma below_a5_L_hm : ltac2:(tb__ "0|0|
S12S8S24P19S1cS3bZfA2A2S4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition rho_hm (rho : valuation) : valuation := ltac2:(tb__ "0|0|
S82Vrho;P19S21Vrho;S1cS3bZfA2A2A3").

Lemma restate_hm : ltac2:(tb__ "0|1|
S2S30A1S2fOF_;F_;S16S7aS7bS9R3S3bR2R1A5S13S20P19R3S75R3A1M0A3S7bS9R4S44G0R2A5A2F_;Fw;Frho;FK;").
Proof.
  intros K rho w Hsp.
  assert (Hag : agree_below 25%positive rho (rho_hm rho)) by (unfold rho_hm; apply agree_below_set_rw; lia).
  split; [exact Hag|].
  pose proof (SP_facts_hold segsA K rho L_hm w Hsp) as HF.
  assert (Hv1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x7fffffffff20).
  { assert (X1 : In (SPUle (SLit 140735340871680) (SVar 1%positive)) (ss_facts L_hm)) by (vm_compute; tauto).
    assert (X2 : In (SPUle (SVar 1%positive) (SLit 140737488355104)) (ss_facts L_hm)) by (vm_compute; tauto).
    pose proof (proj1 (Forall_forall _ _) HF _ X1) as Y1. pose proof (proj1 (Forall_forall _ _) HF _ X2) as Y2.
    cbn [holds eval] in Y1, Y2. rewrite Z_to_bv_unsigned in Y1, Y2.
    change (bv_wrap 64 140735340871680) with 140735340871680 in Y1. change (bv_wrap 64 140737488355104) with 140737488355104 in Y2. lia. }
  destruct Hsp as [Hsm Hk]. split; [|exact Hk].
  apply (smatch_restate segsA (rho_hm rho) L_hm S_hm w (fst sd_hm) (snd sd_hm)).
  - eapply smatch_agree; [rewrite next_L_hm; exact Hag | exact Hsm].
  - exact swf_S_hm.
  - rewrite sd_hm_eq. destruct sd_hm; reflexivity.
  - rewrite sd_hm_shape. cbn [fst]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite L_hm_a0. rewrite <- (eval_agree 25%positive rho (rho_hm rho) (smear_sv Xhm [1; 2; 4; 8; 16; 32]) Hag ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
      cbn [eval]. apply eval_smear_sv_47. unfold Xhm. cbn [eval]. rewrite add_val, Z_to_bv_unsigned.
      change (bv_wrap 64 (-160)) with (2 ^ 64 - 160).
      replace (bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 160)) with ((bv_unsigned (rw rho 1%positive) - 160) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
    + unfold rho_hm at 2. cbn [eval]. rewrite rho_set_rw_at. symmetry. exact (eval_agree 25%positive rho (rho_hm rho) _ Hag below_a5_L_hm).
  - rewrite sd_hm_shape. cbn [snd]. apply Forall_nil.
Qed.

Definition S_b2ok : axst := ltac2:(tb__ "0|0|
SdS58S40Z7fff7000A2S0S3S15S15A2A1S17S51A1A3").
Definition S_b3ok : axst := ltac2:(tb__ "0|0|
SdS58S45Z8fff7000A2S0S3S15S15A2A1S17S51A1A3").
Definition S_b4ok : axst := ltac2:(tb__ "0|0|
SdS58S46Z2008fff7000A2S0S3S15S15A2A1S17S51A1A3").
Definition S_b2fail : axst := ltac2:(tb__ "0|0|
SdS58S40S59A2S0S3S15S15A2A1S17S51A1A3").
Definition S_b3fail : axst := ltac2:(tb__ "0|0|
SdS58S45S59A2S0S3S15S15A2A1S17S51A1A3").
Definition S_b4fail : axst := ltac2:(tb__ "0|0|
SdS58S46S59A2S0S3S15S15A2A1S17S51A1A3").

Lemma runF_b2 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9U190S1S10Z662b8S0S10A1A3S6dS4A5S6G0S1SaSbS41S29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin_b2 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9U2S1S10Z662b8S0S10A1A3S41S4A5S6G0S1SaSbS41S29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runO_b2 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9Ubb8S1S10S64S0S10A1A3S6eS4A5S6G0S1SaSbS3cS29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runF_b3 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9U190S1S10Z662ccS0S10A1A3S6fS4A5S6G0S1SaSbS42S29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin_b3 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9U2S1S10Z662ccS0S10A1A3S42S4A5S6G0S1SaSbS42S29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runO_b3 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9Ubb8S1S10S64S0S10A1A3S70S4A5S6G0S1SaSbS3dS29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runF_b4 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9U190S1S10Z662e0S0S10A1A3S71S4A5S6G0S1SaSbS43S29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin_b4 : ltac2:(tb__ "0|1|
S12S5S2SaA1M0A1ScS9U2S1S10Z662e0S0S10A1A3S43S4A5S6G0S1SaSbS43S29A2S0SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition G1 : positive := 26%positive.
Definition FUEL1 : nat := (12 * 1000)%nat.
Definition cutpcs1 : list Z := ltac2:(tb__ "0|0|
S1S10S73S1S10S64S0S10A1A3A3").
Definition cuts1 : list axst := ltac2:(tb__ "0|0|
S1SeS69S1SeS48S1SeS49S0SeA1A3A3A3").
Definition exits1 : list axst := [E_s2].
Definition check1__runs : ltac2:(tb__ "0|0|
S2S5S2SaA1A1A1") := ltac2:(tb__ "0|0|
S87S9S66S67S6aA4").
Lemma check1 : ltac2:(tb__ "0|0|
S12S8S5cS9S66S67S65S6aS74A6S4A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUEL1 cutpcs1 G1 cuts1 exits1 check1__runs); [unfold check1__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Section Seg1.

Variables (m : Model) (B : Z).
Hypothesis Hh0 : m_halted m = None.
Hypothesis Hlz : m_vm_lazy m = [].
Hypothesis Hmt : m_vm_materialized m = [].
Hypothesis Hres : ltac2:(tb__ "0|1|
S12S2S3S26Q40A1M0G0A2A1S33S2eVm;A1A1S84S9A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|2|
S12S2S3S26Q40A1M0G0A2M1A1S3aS2eVm;A1A1S0G1A1A3").
Hypothesis Hna : ltac2:(tb__ "0|2|
S12S2S3S26Q40A1M0G0A2M1A1S32S2eVm;A1A1S0G1A1A3").
Hypothesis HusedB : vm_backing_used m <= B.
Hypothesis HBlim : ltac2:(tb__ "0|0|
S4eVB;S31S2eVm;A1A1A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).

Variable ok : assn.
Hypothesis OK0 : ltac2:(tb__ "0|0|
S7cS9Vok;S80Vm;A1A3").
Hypothesis OKF : ltac2:(tb__ "0|1|
S4cS16S2S26Q40A1A1S2S30A1M0S2fR5R4R3R2R1A4S12G0R3S0S30A1A3F_;Fmd;Ftr;Ftp;Frho;S4dS9Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4cS16S2S26Q40A1A1S2S30A1M0S2fR5R4R3R2R1A4S12G0R3S0S30A1A3F_;Fmd;Ftr;Ftp;Frho;S83S9Vok;R2A3F_;FJ;").

Definition m2 : Model := lazy_rw_model 0x7fff7000 0x10000000 m.
Definition m3 : Model := lazy_none_model 0x8fff7000 0x20000000000 m2.
Definition m4 : Model := lazy_rw_model 0x2008fff7000 0xdfff0001000 m3.

Lemma OKFx : ltac2:(tb__ "0|0|
S2fS10S4dS9Vok;S28R2R1A2A3FBB;Fmm;").
Proof using OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma OKPx : ltac2:(tb__ "0|0|
S2fS10S83S9Vok;S28R2R1A2A3FBB;Fmm;").
Proof using OKP. intros. apply OKP. intros; eapply KxA_nil; eassumption. Qed.

Lemma m2_vmmaps : ltac2:(tb__ "0|4|
S12S34S2eS5eA1S35S33S2eVm;A1M0A1S1S3S26Q40M1A1M2G2A2M3S7G2G2S25G1Z7fff7000A2S25G1Z10000000A2A4S0G3A1A3S32G0A1S39G0A1S36G0A1S31G0A1S38G0A1S37G0A1A8A3").
Proof using Hmaps. unfold m2, lazy_rw_model, lazy_rw_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, Hmaps. reflexivity. Qed.
Lemma m3_vmmaps : ltac2:(tb__ "0|5|
S12S34S2eS5fA1S35S33S2eVm;A1M0A1S1S3S26Q40M1A1M2G2A2M3S7G2G2S25G1Z8fff7000A2S25G1Z20000000000A2A4M4S1G3S7G2G2S25G1Z7fff7000A2S25G1Z10000000A2A4S0G3A1A3A3S1G3G4S32G0A1A3S39G0A1S36G0A1S31G0A1S38G0A1S37G0A1A8A3").
Proof using Hmaps. unfold m3, lazy_none_model, none_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, m2_vmmaps. reflexivity. Qed.
Lemma m4_vmmaps : ltac2:(tb__ "0|5|
S12S34S2eS60A1S35S33S2eVm;A1M0A1S1S3S26Q40M1A1M2G2A2M3S7G2G2S25G1Z2008fff7000A2S25G1Zdfff0001000A2A4S1G3S7G2G2S25G1Z8fff7000A2S25G1Z20000000000A2A4M4S1G3S7G2G2S25G1Z7fff7000A2S25G1Z10000000A2A4S0G3A1A3A3A3S1G3G4S32G0A1A3S39G0A1S36G0A1S31G0A1S38G0A1S37G0A1A8A3").
Proof using Hmaps. unfold m4, lazy_rw_model, lazy_rw_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, m3_vmmaps. reflexivity. Qed.

Lemma clear_b2 : ltac2:(tb__ "0|0|
S12S8S53S0S3S15S10A2A1SfS3fA1A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma clear_b3 : ltac2:(tb__ "0|0|
S12S8S53S0S3S15S10A2A1SfS3cA1A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma clear_b4 : ltac2:(tb__ "0|0|
S12S8S53S0S3S15S10A2A1SfS3dA1A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg_b2 : ltac2:(tb__ "0|2|
S16S79S9Vok;S4aS9S28Vm;VB;A2S3fR1S0S26Q40M0A1A1M1A5S4bS9S28S5eVB;A2P1aS56R1S55S1aR1A1S25G0Z7fff7000A2S25G0Z10000000A2A3A2G1S1SaSbS3cS29A2S0SaA1A3A6A4Frho;").
Proof using Hmaps Hres Htop OKF OKP.
  intros rho.
  eapply (node_seg ok (KxA m B) (KxA m2 B) (OKFx _ _) (OKFx _ _) (fun n => stableA_KxA segsA n m B) (fun n => stableA_KxA segsA n m2 B)
            E_b2 S_b2ok SPINb2 E_b3 rho _ [] [] 400%nat 0x662b8 3000%nat ECALL_MMAP).
  - apply (lazy_noreplace_rw_node ok OKF OKP E_b2 0x7fff7000 0x10000000 m B []);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact Htop | exact clear_b2 | exact Hres | rewrite Hmaps; intros b s [] | intros e sz [] ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact runF_b2.
  - exact spin_b2.
  - reflexivity.
  - exact runO_b2.
Qed.

Lemma init_sp_ok_m2 : init_sp_ok (m_vmmaps m2).
Proof using Hmaps Htop. rewrite m2_vmmaps. unfold init_sp_ok in *. cbn [vm_init_sp]. exact Htop. Qed.
Lemma init_sp_ok_m3 : init_sp_ok (m_vmmaps m3).
Proof using Hmaps Htop. rewrite m3_vmmaps. unfold init_sp_ok in *. cbn [vm_init_sp]. exact Htop. Qed.
Lemma init_sp_ok_m4 : init_sp_ok (m_vmmaps m4).
Proof using Hmaps Htop. rewrite m4_vmmaps. unfold init_sp_ok in *. cbn [vm_init_sp]. exact Htop. Qed.

Lemma seg_b3 : ltac2:(tb__ "0|2|
S16S79S9Vok;S4aS9S28S5eVB;A2S3cR1S0S26Q40M0A1A1M1A5S4bS9S28S5fVB;A2P1aS56R1S55S1aR1A1S25G0Z8fff7000A2S25G0Z20000000000A2A3A2G1S1SaSbS3dS29A2S0SaA1A3A6A4Frho;").
Proof using Hmaps Hres Htop OKF OKP.
  intros rho.
  eapply (node_seg ok (KxA m2 B) (KxA m3 B) (OKFx _ _) (OKFx _ _) (fun n => stableA_KxA segsA n m2 B) (fun n => stableA_KxA segsA n m3 B)
            E_b3 S_b3ok SPINb3 E_b4 rho _ [] [] 400%nat 0x662cc 3000%nat ECALL_MMAP).
  - apply (lazy_noreplace_none_node ok OKF OKP E_b3 0x8fff7000 0x20000000000 m2 B []);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m2 | exact clear_b3 | rewrite m2_vmmaps; exact Hres
      | rewrite m2_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact runF_b3.
  - exact spin_b3.
  - reflexivity.
  - exact runO_b3.
Qed.

Lemma seg_b4 : ltac2:(tb__ "0|2|
S16S79S9Vok;S4aS9S28S5fVB;A2S3dR1S0S26Q40M0A1A1M1A5S4bS9S28S60VB;A2S65S56R1S55S1aR1A1S25G0Z2008fff7000A2S25G0Zdfff0001000A2A3A2G1S1SaSbS3eS2bA2S0SaA1A3A6A4Frho;").
Proof using Hmaps Hres Htop OKF OKP.
  intros rho. set (rho' := set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))).
  eapply triple_seq.
  { apply triple1_triple.
    apply (lazy_noreplace_rw_node ok OKF OKP E_b4 0x2008fff7000 0xdfff0001000 m3 B []);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m3 | exact clear_b4 | rewrite m3_vmmaps; exact Hres
      | rewrite m3_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[[= <- <-]|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ]. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA m3 B) (OKFx _ _) (fun n => stableA_KxA segsA n m3 B) _ SPINb4 400%nat 0x662e0);
      [ reflexivity | reflexivity | reflexivity | exact runF_b4 | exact spin_b4 ].
  - change (lazy_rw_model 0x2008fff7000 0xdfff0001000 m3) with m4.
    change (mkAX (S_ret_lit (ax_S E_b4) 0x2008fff7000) [] (SLit SHB)) with S_b4ok.
    change (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))) with rho'.
    assert (HstG : stableA segsA G1 (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))).
    { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply stableA_KxA]. }
    assert (HokG : ok_frameA segsA ok (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))).
    { apply OKF. intros r t tr md [_ HK]. eapply KxA_nil; eassumption. }
    eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segsA (KxA m4 B) G1 S_b4ok rho' [] w Hw) | intros w Hw; exact Hw |].
    apply (cfg_soundA segsA FUEL1 cutpcs1 G1 cuts1 exits1 (withGA (fun r => agree_below G1 rho' r) (KxA m4 B)) ok
             (LQA segsA (KxA m4 B) G1 rho' [] [mkLeafA E_s2 RsSymJump]) [] HokG HstG check1); [|left; reflexivity].
    intros E rhoE [<-|[]]. apply exit_postA. left; reflexivity.
Qed.

Definition Post1 (rho : valuation) : assn := ltac2:(tb__ "0|0|
S7aS14S16S16S13S52P19Vrho;R1A3S13S54Vrho;R1A2S4aS9S28S60VB;A2S3eR1S0S26Q40A1A1R2A6A2A2Lrho';A2Lw;").

Lemma agree_vars_set_rw_ge : ltac2:(tb__ "0|0|
S11S16S16S11S26Q40A1S89R5R2A2S52R6R5R4A3S52R7R6S82R5R4R3A3A3F_;F_;Fv;Fi;Frho';Frho;Fn;").
Proof. intros n rho rho' i v Hi [A1 A2]. split; [intros j Hj; rewrite rho_set_rw_other by lia; apply A1; exact Hj | intros l; cbn; apply A2]. Qed.

Theorem start1_sum_A : ltac2:(tb__ "0|2|
S16S4eS27Q40M0S18R1P1M1A2A2S27G0S18R1P4A2A2A2S4eS27G0S18R2G1A2A2S27G0S18R2P6A2A2A2S4eZ7fff80000000S27G0S18R3G1A2A2A2S79S9Vok;S7bS9S80Vm;A1S77R4A4S61R4A1A4F_;F_;F_;Frho;").
Proof using All.
  intros rho H14 H16 HX1.

  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w [Hsm Hk].
    exact (SP_xforms segsA (Kx m) xf1 rho (add_facts F1x S_ctor) S_ctor_x w xf1_ok
             (conj (smatch_add_facts segsA rho F1x S_ctor w Hsm ltac:(unfold F1x; repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; assumption) F1x_below) Hk)). }

  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_sound; [apply run_hm | exact OK0 | intros H; discriminate]. }
  apply triple_ex; intros L. apply triple_ex; intros rho1. apply triple_pure; intros HinL. apply triple_pure; intros Hag1.
  destruct HinL as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho1 L_hm w /\ liftK (Kx m) rho1 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) L_hm rho1).

  eapply triple_conseq; [intros w Hw; exact (proj2 (restate_hm (Kx m) rho1 w Hw)) | intros w Hw; exact Hw |].
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_sound; [apply run_b2 | exact OK0 | intros H; discriminate]. }
  apply triple_ex; intros L2. apply triple_ex; intros rho2. apply triple_pure; intros HinL2. apply triple_pure; intros Hag2.
  destruct HinL2 as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho2 E_b2_S w /\ liftK (Kx m) rho2 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) E_b2_S rho2).

  assert (Hw12 : ivs_wf (vm_maps (m_vmmaps m)) /\ ivs_wf (vm_noaccess (m_vmmaps m))) by (rewrite Hmaps, Hna; split; apply ivs_wf_nil).
  eapply triple_conseq; [intros w Hw; exact (SP_SPA m B E_b2_S rho2 w Hlz Hmt HusedB HBlim (proj1 Hw12) (proj2 Hw12) Hw) | intros w Hw; exact Hw |].
  change (axA E_b2_S) with E_b2.

  eapply triple_seq; [apply seg_b2|].
  apply triple_ex; intros L3. apply triple_ex; intros rho3. apply triple_pure; intros HinL3. apply triple_pure; intros Hag3.
  destruct HinL3 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho3 [] E_b3 w /\ KxA m2 B rho3 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m2 B) E_b3 rho3 []).

  eapply triple_seq; [apply seg_b3|].
  apply triple_ex; intros L4. apply triple_ex; intros rho4. apply triple_pure; intros HinL4. apply triple_pure; intros Hag4.
  destruct HinL4 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho4 [] E_b4 w /\ KxA m3 B rho4 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m3 B) E_b4 rho4 []).

  eapply triple_seq; [apply seg_b4|].
  apply triple_ex; intros L5. apply triple_ex; intros rho5. apply triple_pure; intros HinL5. apply triple_pure; intros Hag5.
  destruct HinL5 as [<-|[]]. cbn [la_state].
  eapply triple_conseq; [ | | apply triple_refl]; [intros w Hw; exact Hw|].
  intros w [Hsm Hk]. exists rho5.

  assert (A1 : agree_vars 25 rho rho1) by (eapply agree_vars_below; [apply agree_vars_refl | exact Hag1]).
  assert (A2 : agree_vars 25 rho rho2).
  { eapply agree_vars_below; [| eapply agree_below_le; [|exact Hag2]; cbv; discriminate]. unfold rho_hm. apply agree_vars_set_rw_ge; [lia | exact A1]. }
  assert (A3 : agree_vars 25 rho rho3) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A2 | eapply agree_below_le; [|exact Hag3]; cbv; discriminate]).
  assert (A4 : agree_vars 25 rho rho4) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A3 | eapply agree_below_le; [|exact Hag4]; cbv; discriminate]).
  assert (A5 : agree_vars 25 rho rho5) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A4 | eapply agree_below_le; [|exact Hag5]; cbv; discriminate]).
  split; [exact A5|]. split.
  { eapply RMH_below; [|exact Hag5]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag4]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag3]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag2]. unfold rho_hm. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag1]. apply RMH_refl. }
  split; [exact Hsm | exact Hk].
Qed.

Definition vcuts1 : list vnodeA := ltac2:(tb__ "0|1|
S1S5aS5bS69Z64S17Z0A1A3S1S5aS5bS48Z32S1dS81S17Z182ebfA1S1bP1aA1M0A3A3S1S5aS5bS49Z28S1dS81S17Z181ebfA1G0A3A3S0S5aA1A3A3A3").
Definition vexits1 : list vnodeA := ltac2:(tb__ "0|0|
S1S5aS5bS3eZaS17Z0A1A3S0S5aA1A3").
Lemma echeck1 : ltac2:(tb__ "0|0|
S12S8S5dS9S66S67S65S62S63A6S4A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUEL1 cutpcs1 G1 vcuts1 vexits1 check1__runs); [unfold check1__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Lemma eseg_b2 : ltac2:(tb__ "0|2|
S16S78S9S4aS9S28Vm;VB;A2S3fR1S0S26Q40M0A1A1M1A5S4bS9S28S5eVB;A2P1aS56R1S55S1aR1A1S25G0Z7fff7000A2S25G0Z10000000A2A3A2G1S1SaSbS3cS29A2S0SaA1A3A6A3Frho;").
Proof using Hmaps Hres Htop.
  intros rho.
  apply (enode_seg (KxA m B) (KxA m2 B) E_b2 S_b2ok E_b3 rho _ [] [] 3000%nat ECALL_MMAP (fun n => stableA_KxA segsA n m2 B)); [| reflexivity | exact runO_b2].
  apply (lazy_noreplace_rw_enode E_b2 0x7fff7000 0x10000000 m B []);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact Htop | exact clear_b2 | exact Hres | rewrite Hmaps; intros b s [] | intros e sz [] ].
Qed.

Lemma eseg_b3 : ltac2:(tb__ "0|2|
S16S78S9S4aS9S28S5eVB;A2S3cR1S0S26Q40M0A1A1M1A5S4bS9S28S5fVB;A2P1aS56R1S55S1aR1A1S25G0Z8fff7000A2S25G0Z20000000000A2A3A2G1S1SaSbS3dS29A2S0SaA1A3A6A3Frho;").
Proof using Hmaps Hres Htop.
  intros rho.
  apply (enode_seg (KxA m2 B) (KxA m3 B) E_b3 S_b3ok E_b4 rho _ [] [] 3000%nat ECALL_MMAP (fun n => stableA_KxA segsA n m3 B)); [| reflexivity | exact runO_b3].
  apply (lazy_noreplace_none_enode E_b3 0x8fff7000 0x20000000000 m2 B []);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m2 | exact clear_b3 | rewrite m2_vmmaps; exact Hres
      | rewrite m2_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ].
Qed.

Lemma eseg_b4 : ltac2:(tb__ "0|2|
S16S78S9S4aS9S28S5fVB;A2S3dR1S0S26Q40M0A1A1M1A5S4bS9S28S60VB;A2S65S56R1S55S1aR1A1S25G0Z2008fff7000A2S25G0Zdfff0001000A2A3A2G1S1SaSbS3eS2bA2S0SaA1A3A6A3Frho;").
Proof using Hmaps Hres Htop.
  intros rho. set (rho' := set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))).
  eapply etriple_seq.
  { apply (lazy_noreplace_rw_enode E_b4 0x2008fff7000 0xdfff0001000 m3 B []);
      [ reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m3 | exact clear_b4 | rewrite m3_vmmaps; exact Hres
      | rewrite m3_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[[= <- <-]|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ]. }
  change (lazy_rw_model 0x2008fff7000 0xdfff0001000 m3) with m4.
  change (mkAX (S_ret_lit (ax_S E_b4) 0x2008fff7000) [] (SLit SHB)) with S_b4ok.
  change (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))) with rho'.
  assert (HstG : stableA segsA G1 (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply stableA_KxA]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segsA (KxA m4 B) G1 S_b4ok rho' [] w Hw) | intros w Hw; exact Hw |].
  change S_b4ok with (vna_state (mkVNA S_b4ok 100 (SLit 0))).
  apply (cfg_complete_autoA segsA FUEL1 cutpcs1 G1 vcuts1 vexits1 (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))
           (LQA segsA (KxA m4 B) G1 rho' [] [mkLeafA E_s2 RsSymJump]) [] HstG); [ | exact echeck1 | | left; reflexivity].
  - intros n [<-|[<-|[<-|[]]]]; cbv; discriminate.
  - intros E rhoE [<-|[]]. apply eexit_postA. left; reflexivity.
Qed.

Theorem start1_sum_ex_A : ltac2:(tb__ "0|2|
S16S4eS27Q40M0S18R1P1M1A2A2S27G0S18R1P4A2A2A2S4eS27G0S18R2G1A2A2S27G0S18R2P6A2A2A2S4eZ7fff80000000S27G0S18R3G1A2A2A2S78S9S7bS9S80Vm;A1S77R4A4S61R4A1A3F_;F_;F_;Frho;").
Proof using Hlz Hmt HusedB HBlim Hmaps Hna Hres Htop.
  intros rho H14 H16 HX1.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w [Hsm Hk].
    exact (SP_xforms segsA (Kx m) xf1 rho (add_facts F1x S_ctor) S_ctor_x w xf1_ok
             (conj (smatch_add_facts segsA rho F1x S_ctor w Hsm ltac:(unfold F1x; repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; assumption) F1x_below) Hk)). }
  eapply etriple_seq.
  { eapply sym_run_etriple; [reflexivity | apply run_hm]. }
  apply etriple_ex; intros L. apply etriple_ex; intros rho1. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag1.
  destruct HinL as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho1 L_hm w /\ liftK (Kx m) rho1 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) L_hm rho1).
  eapply etriple_conseq; [intros w Hw; exact (proj2 (restate_hm (Kx m) rho1 w Hw)) | intros w Hw; exact Hw |].
  eapply etriple_seq.
  { eapply sym_run_etriple; [reflexivity | apply run_b2]. }
  apply etriple_ex; intros L2. apply etriple_ex; intros rho2. apply etriple_pure; intros HinL2. apply etriple_pure; intros Hag2.
  destruct HinL2 as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho2 E_b2_S w /\ liftK (Kx m) rho2 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) E_b2_S rho2).
  assert (Hw12 : ivs_wf (vm_maps (m_vmmaps m)) /\ ivs_wf (vm_noaccess (m_vmmaps m))) by (rewrite Hmaps, Hna; split; apply ivs_wf_nil).
  eapply etriple_conseq; [intros w Hw; exact (SP_SPA m B E_b2_S rho2 w Hlz Hmt HusedB HBlim (proj1 Hw12) (proj2 Hw12) Hw) | intros w Hw; exact Hw |].
  change (axA E_b2_S) with E_b2.
  eapply etriple_seq; [apply eseg_b2|].
  apply etriple_ex; intros L3. apply etriple_ex; intros rho3. apply etriple_pure; intros HinL3. apply etriple_pure; intros Hag3.
  destruct HinL3 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho3 [] E_b3 w /\ KxA m2 B rho3 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m2 B) E_b3 rho3 []).
  eapply etriple_seq; [apply eseg_b3|].
  apply etriple_ex; intros L4. apply etriple_ex; intros rho4. apply etriple_pure; intros HinL4. apply etriple_pure; intros Hag4.
  destruct HinL4 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho4 [] E_b4 w /\ KxA m3 B rho4 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m3 B) E_b4 rho4 []).
  eapply etriple_seq; [apply eseg_b4|].
  apply etriple_ex; intros L5. apply etriple_ex; intros rho5. apply etriple_pure; intros HinL5. apply etriple_pure; intros Hag5.
  destruct HinL5 as [<-|[]]. cbn [la_state].
  eapply etriple_conseq; [ | | apply etriple_refl]; [intros w Hw; exact Hw|].
  intros w [Hsm Hk]. exists rho5.
  assert (A1 : agree_vars 25 rho rho1) by (eapply agree_vars_below; [apply agree_vars_refl | exact Hag1]).
  assert (A2 : agree_vars 25 rho rho2).
  { eapply agree_vars_below; [| eapply agree_below_le; [|exact Hag2]; cbv; discriminate]. unfold rho_hm. apply agree_vars_set_rw_ge; [lia | exact A1]. }
  assert (A3 : agree_vars 25 rho rho3) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A2 | eapply agree_below_le; [|exact Hag3]; cbv; discriminate]).
  assert (A4 : agree_vars 25 rho rho4) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A3 | eapply agree_below_le; [|exact Hag4]; cbv; discriminate]).
  assert (A5 : agree_vars 25 rho rho5) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A4 | eapply agree_below_le; [|exact Hag5]; cbv; discriminate]).
  split; [exact A5|]. split.
  { eapply RMH_below; [|exact Hag5]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag4]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag3]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag2]. unfold rho_hm. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag1]. apply RMH_refl. }
  split; [exact Hsm | exact Hk].
Qed.
End Seg1.
End Start1.

(* [comment removed for export] *)
Module StartNodes3.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "valuation"; "ss_next"; "sprop"; "SPUle"; "SVar"; "eval"; "rw"; "SPAlign"; "agree_below"; "rm"; "ss_objs"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "mkAX"; "ax_base"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "prod"; "list"; "nil"; "cons"; "pair"; "bool"; "true"; "Some"; "app"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "m_vmmaps"; "Model"; "vm_maps"; "vm_reserved"; "vm_init_sp"; "VmMaps"; "mkVmMapsFull"; "vm_add_lazy"; "vm_brk"; "vm_limit"; "vm_mmap_base"; "vm_noaccess"; "vm_start_brk"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "LB_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "alloc_ceiling_hi"; "mmap_place_ok"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_flags_core"; "mmap_modeled_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3.LazyNullRw"; "null_rw_facts"; "null_rw_h"; "null_rw_model"; "null_rw_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple1"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma mmap_modeled_b_intro_core : ltac2:(tb__ "0|2|
S16Q40M0A1M1G1G1S0S24S17G0R3A2Z3A3S0S24S45R3A1Z22A3S0G1R3S18G0Z0A2A3S0S1fS46R6R5R4A3S20A3F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->. unfold mmap_modeled_b.
  rewrite Hp, Hf. unfold PROT_READ, PROT_WRITE, PROT_NONE, MAP_PRIVATE, MAP_ANONYMOUS. cbn. reflexivity.
Qed.

Section LazyNullRw.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S37S7S1bS16Q40A1A1S1bS25A1M0S27R5R4R3R2R1A4S0G0R3S1cS25A1A3F_;Fmd;Ftr;Ftp;Frho;S38S19Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S37S7S1bS16Q40A1A1S1bS25A1M0S27R5R4R3R2R1A4S0G0R3S1cS25A1A3F_;Fmd;Ftr;Ftp;Frho;S57S19Vok;R2A3F_;FJ;").

Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Definition null_rw_h (md : Model) (a : word) : VmMaps := ltac2:(tb__ "0|1|
S26Vmd;A1S2bS2cS29R1A1S1dS1aS16Q40A1M0G0A2S1eG0G0Va;Vn;A4S28R1A1A3S31R1A1S32R1A1S2eR1A1S2fR1A1S30R1A1S2aR1A1A8Th;").
Definition null_rw_model (md : Model) (a : word) : Model := ltac2:(tb__ "0|0|
S2dVa;Vn;S33S4bVmd;Va;A2Vmd;A2A3").

Definition null_rw_facts : list sprop := ltac2:(tb__ "0|2|
S1dS9SeS8S13VE;A1A1M0ZcA2S1dS9SaS5S3fVlenZ;A1A1SbG0A1M1A2S1dS9SaG1S5S3bS41VlenZ;A2A1A2S1cS9A1A3A3A3").
Definition null_rw_ok : axst := ltac2:(tb__ "0|1|
S14S52S4aS53S13VE;A1M0SbS8G0A1A1S11G0A1Vnxt;A4A2S1cS1aS4S4A2A1S5S34A1A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S4S15VE;A1S5S34A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S23S3cA1S56S19S12S13VE;A1A1A2S21S3cS3dA2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1Z11A2S5ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZaA2S5Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZbA2S5VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZcA2S5Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZdA2S5Z4022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZeA2S5ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZfA2S5Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S58S8S13VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S1fS35VGl;S13VE;A1A2S20A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S1bS1aS16Q40A1M0G0A2A1S29S26Vm;A1A1S44S19A1A3").

Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S49S22S1aS16Q40A1M0G0A2S29S26Vm;A1M1A1S28G1A1A3S48S47A3").

Variable rho_of : ltac2:(tb__ "0|0|
S7S16Q40A1S7F_;F_;").
Hypothesis Hrho_ag : ltac2:(tb__ "0|0|
S7S16Q40A1SfS8S13VE;A1A1S51R2S50S10R2A1R1Vn;A3A2Vrho_of;R2R1A2A3Fa;Frho;").
Hypothesis Hrho_at : ltac2:(tb__ "0|1|
S7S16Q40A1M0S0G0SdVrho_of;R2R1A2S8S13VE;A1A1A2R1A3Fa;Frho;").

Lemma n_valW : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. unfold n. apply u64_of_lit. clear -Hpos Hsmall. lia. Qed.

Lemma place_ok_none_of : ltac2:(tb__ "0|3|
S16Q40M0A1M1S27G1G1S42S18G0Z0A2M2R4R3R2R1A5S40G2R4R3R2A4F_;Fa;Flen;Fmd;Fflags;").
Proof. intros flags md len a (P1 & P2 & P3 & P4 & _). unfold mmap_place_ok_none. repeat split; assumption. Qed.

Theorem lazy_null_rw_node : ltac2:(tb__ "0|6|
S7S1bS16Q40M0A1M1A1S4S24S43S1aS4S24A2S1eS4S24R2R1A4VGl;A3S3S2G1G1S2G1G1S1S43S1aG1G1A2S1eG1G1R2R1A4S28S26Vm;A1M2A1A3S1S3aS17G0R2A2M3S17G0ScR7R5A2A2M4A2S3aS39G4R4A2S39G3S17G0R1A2A2A2A2A2Ls;A2Lb;A2S3aS39S17G0ScR5R3A2A2R2A2S3fVlenZ;A1A2A2F_;Fsz;Fe;S0S24S17G0SdR3P1A2A2S17G0S2aG2A1A2A3S4eS19Vok;S36S19S3eVm;VB;A2M5VE;R4R3A5S4fS3S36S19G5S14S54S13VE;A1S55A2S1cS1aS4S4A2A1S5S34A1A3R5R4R1A6S2G1G1S1S40S18G0Z0A2Vm;Vn;R1A4S36S19S3eS4cVm;R1A2VB;A2S4dVrho_of;R6R1A2R5R2A6A2La;A2A2Lw;A4F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1.
  pose proof n_valW as Nv. pose proof (alloc_top_lt (m_vmmaps m)) as CL.
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_swf segsA _ _ _ _ Hsp) as Hswf.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  assert (Hshape : mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true).
  { apply mmap_modeled_b_intro_core; [rewrite G2; reflexivity | rewrite G3; apply mmap_flags_core_16418; reflexivity | rewrite G5; reflexivity]. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  split.
  - apply (OKP (KxA m B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (mmap_only_okA segsA ms md _ Hh H222 Hlen Hshape).
  - intros w' Hw.
    destruct (wstep_mmap_invA segsA ms md _ Hh H222 Hlen Hshape [] w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit (bv_unsigned (errno_ret ENOMEM))) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
      replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a.
      rewrite G0, G1 in Hpl.
      assert (HnZn : mmap_nZ n = lenZ) by (rewrite <- G1; exact HnZ').
      assert (Hmn : mmap_n n = n) by (rewrite <- G1 at 1; exact HnZ).
      assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n a).
      { apply (place_ok_none_of (ms_gpr ms 3) m n a). unfold mmap_place_ok in Hpl |- *. rewrite Evm in Hpl.
        destruct Hpl as (P1 & P2 & P3 & P4 & P5). repeat split; try assumption.
        unfold mmap_noreserve_backed_ok in P5 |- *. rewrite G3 in P5 |- *. rewrite (mmap_noreserve_b_16418 (Z_to_bv 64 16418) eq_refl) in P5 |- *. exact P5. }
      split; [exact Hplm|].
      pose proof Hplm as (Pal & Ppos & Pceil & Pfree). rewrite HnZn in Pceil. rewrite Hmn in Pfree.
      pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hplm) as (PLB & Pimg & Pband & Ptop & Phi).
      assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Pfree)).
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16418; reflexivity).
      unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ.
      set (rho' := rho_of rho a).
      split.
      * unfold null_rw_ok.
        assert (SM : smatchA segsA rho' tp (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E)) nxt))
                       ([], mkCfg (after_sys_mem ms a (zero_range (ms_mem ms) a n)) (vm_add_lazy a n (with_vmmaps (null_rw_h md a) md)))).
        { eapply (smatchA_after_grant_lazy segsA rho rho' tp E [] ms md [] (null_rw_h md a)); try exact Hsp.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- exact Pal.
          -- rewrite Nv. exact Hnl.
          -- rewrite Nv. exact Hpos.
          -- rewrite Nv. unfold two_pow_64 in CL. lia.
          -- exact Hfree_m.
          -- intros z Hz. apply find_segment_none_A. rewrite Nv in Hz. lia.
          -- intros o Ho. rewrite Nv.
             apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
             ++ lia.
             ++ right. revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil.
             ++ intros x Hx. lia.
             ++ intros e sz Hin x Hx Hblk. destruct (HG e sz Hin) as [(b & s0 & Hm & Hb1 & Hb2) | Hlow]; [|lia].
                pose proof (region_free_In _ _ _ _ _ Hfree_m ltac:(rewrite Evm; exact Hm)) as R.
                unfold iv_overlap in R. rewrite Nv in R.
                apply andb_false_iff in R. destruct R as [R|R]; apply Z.ltb_ge in R; lia.
             ++ exact Ho.
          -- rewrite HX. intros rr y [] _.
          -- subst rho'. apply Hrho_ag.
          -- lia.
          -- cbn. apply Pos.ltb_lt. exact Hnxt.
          -- subst rho'. cbn [eval]. apply Hrho_at. }

        replace E with (mkAX (ax_S E) [] (SLit SHB)) in SM by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
        destruct SM as (Ssm & SMI & Swf & Ssh & Shz). cbn [ax_S ax_setS ax_X ax_base] in Ssm, Swf, Ssh.
        split; [|split; [exact SMI|split; [|split; [|exact Shz]]]].
        -- cbn [ax_S]. apply smatch_add_facts; [exact Ssm| |].
           ++ unfold null_rw_facts. assert (E1 : rw rho' (ss_next (ax_S E)) = a) by (subst rho'; apply Hrho_at).
              repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
              ** change (2 ^ 12) with 4096. split; [lia|exact Pal].
              ** rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
              ** unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
           ++ assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt). cbn. rewrite !X. reflexivity.
        -- unfold axwf in Swf |- *. cbn [ax_S ax_X ax_base ss_next add_facts] in Swf |- *. exact Swf.
        -- unfold shadow_ok. cbn. constructor.
      * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
        { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
          rewrite Nv. unfold two_pow_64 in CL. lia. }
        assert (Hpaid' : paid (null_rw_model md a) tp <= B).
        { unfold null_rw_model. rewrite (paid_add_lazy (with_vmmaps (null_rw_h md a) md) a n tp Hclr), paid_with_vmmaps.
          pose proof (used_rw_noreserve_le md (null_rw_h md a) a n (MI_ivs_wf segsA _ _ HMI)
                        Pal ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                        ltac:(rewrite Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
          lia. }
        assert (Hem' : erase_mat (null_rw_model md a) = erase_mat (null_rw_model m a)).
        { unfold null_rw_model, null_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
        split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyNullRw.
End StartNodes3.

(* [comment removed for export] *)
Module StartGlueA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "SLit"; "eval"; "obj_range"; "ss_objs"; "sstate"; "rm"; "ob_dflt"; "obj_holds"; "ss_next"; "cell"; "odefault"; "DZero"; "mem_match"; "ranges_disjoint"; "rl"; "rw"; "ob_cells"; "ss_facts"; "agree_below"; "smatch"; "enc_bytes"; "mkCell"; "mkObj"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "outside_all"; "rom_ok"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "DImage"; "DUnknown"; "SAlu"; "holds"; "pairwise_disjoint"; "sprop"; "swf"; "SMd"; "c_val"; "dflt_writable"; "image_byte"; "@Corelib.Init.Datatypes"; "list"; "bool"; "option"; "nat"; "cons"; "true"; "app"; "nil"; "pair"; "Some"; "prod"; "fst"; "false"; "snd"; "None"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "modulo"; "of_nat"; "opp"; "div"; "sub"; "ge"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "ax_X"; "la_state"; "ax_base"; "xr_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "LQA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "page_size"; "m_vm_lazy"; "m_vmmaps"; "page_in_ranges"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "nth_error"; "filter"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "add_cell_front"; "cells_clear_lit"; "pageZ"; "pages_rev"; "move_obj_last"; "obj_to_unknown"; "unknown_obj_at"; "noX"; "split_chain"; "withX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "wsub"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "image_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "vms"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA.WithSegs"; "drop_zero_cells"; "bump_next"; "KxAt"; "M4096"; "is_zero_cell"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "xshadow_outside"; "zero_page_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "M_REMU";
"aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "uncovered"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ranges_disjoint_sym : ltac2:(tb__ "0|1|
S43S0S0A2M0G0S18R2R1A2S18R2R3A2F_;Fr2;Fr1;").
Proof. intros [a b] [c d]. unfold ranges_disjoint. cbn. lia. Qed.

Lemma pairwise_disjoint_move_last : ltac2:(tb__ "0|1|
S9S39S8A1M0S8G0S32R4S3fS8R3S3dS8R2R1A3A3A2S32R5S3fS8R4S3fS8R2S3dS8R3S40S8A1A3A3A3A2F_;FB;Fx;FA;Frho;").
Proof.
  intros rho A x B H.
  apply pairwise_disjoint_app_inv in H as (HA & HxB & Hcross). cbn in HxB. destruct HxB as [Hx HB].
  apply pairwise_disjoint_app; [exact HA | |].
  - apply pairwise_disjoint_app; [exact HB | cbn; split; constructor |].
    intros o1 o2 H1 [<-|[]]. apply ranges_disjoint_sym. exact (proj1 (Forall_forall _ _) Hx o1 H1).
  - intros o1 o2 H1 H2. apply in_app_iff in H2 as [H2|[<-|[]]].
    + apply Hcross; [exact H1 | right; exact H2].
    + apply Hcross; [exact H1 | left; reflexivity].
Qed.

Lemma mem_match_move_last : ltac2:(tb__ "0|1|
S39S9fA1S9S39S8A1M0S8G0S67S17R6R5S3fS8R4S3dS8R3R2A3A3R1A4S17R7R6S3fS8R5S3fS8R3S3dS8R4S40S8A1A3A3A3R2A4F_;Fms;FB;Fx;FA;Frho;Fsegs;").
Proof.
  intros segs rho A x B ms (Hh & Hpd & Hfr).
  assert (P : Permutation (A ++ x :: B) (A ++ B ++ [x])).
  { apply Permutation_app_head. apply Permutation_cons_append. }
  split; [|split].
  - apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) Hh o).
    eapply Permutation_in; [apply Permutation_sym; exact P | exact Ho].
  - apply pairwise_disjoint_move_last. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. apply Forall_forall. intros o Ho.
    apply (proj1 (Forall_forall _ _) Hout o). eapply Permutation_in; [exact P | exact Ho].
Qed.

Lemma firstn_skipn_split : forall {T} (l : list T) i,
  (i < length l)%nat -> exists x, firstn 1 (skipn i l) = [x] /\ l = firstn i l ++ x :: skipn (S i) l.
Proof.
  intros T l. induction l as [|y t IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn.
  - exists y. split; reflexivity.
  - destruct (IH i ltac:(lia)) as (x & H1 & H2). exists x. split; [exact H1|]. rewrite H2 at 1. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma SPA_move_last : ltac2:(tb__ "0|2|
S63S9S5bS3cS39S57Q40A1A1S70S8aR3S48S8SeS5aR4A1A1A2A2S3S39S43SaSaA2M0A1S5eR5A1S40G0A1A3S3S3aS8cS5aR6A1M1S81G1R5A2A2S3eA3S62Vsegs;R9R7R8R5R4A6S62Vsegs;RaS5cR8S81S5aR8A1R7A2A2R9R6R5A6F_;F_;F_;F_;Fw;Ftp;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i tp w Hi HX Hsame Hsp.
  destruct (firstn_skipn_split (ss_objs (ax_S A)) i Hi) as (x & H1 & H2).
  apply (SPA_reobj segs J rho A (move_obj_last (ax_S A) i) tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segs _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segs _ _ _ _ _ S0) as MM.
    unfold move_obj_last. cbn [ss_objs set_objs]. rewrite H1. rewrite H2 in MM.
    apply mem_match_move_last. exact MM.
  - unfold xshadow_outside. rewrite HX. constructor.
Qed.

Lemma image_byte_none_A : ltac2:(tb__ "0|2|
S57Q40M0A1S4bZ646000S58G0R1A2A2S3S3bS57Q8A1M1A1S38S4aR2A2S47G1A1A3F_;Fa;").
Proof.
  intros a Ha. unfold image_byte, memory_read. change (Z.of_N 1) with 1.
  rewrite (find_segment_none_A (bv_unsigned a) ltac:(lia)). reflexivity.
Qed.

Lemma dzero_obj_bytes_A : ltac2:(tb__ "0|3|
S9S67S8S27S4aR2A2S12S4aR4R3R2A4S3S15S11R3A1S16A3S3S39S14A1S1bR4A1S40S14A1A3S4bZ646000S44S0S0SdR7R5A2A3A2S0S4S4bS44S0S0SdR9R7A2M0A3R1A2S4dR1S46S0S0G0A3A2A2S3S3bS57Q8M1A1M2A1S68R9S59Q40R2A2A2S42G2S59G1Z0A2A2A3F_;Fa;F_;F_;F_;F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hrom (Hb & Hw & Hc & Hd & Hi) Hz Hcells Hlo a Ha.
  unfold obj_range in Hlo, Ha. cbn [fst snd] in Hlo, Ha.
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  specialize (Hd (a - b) ltac:(lia)). rewrite Hcells in Hd.
  assert (Hnc : ~ SymState.covered rho [] (a - b)) by (intros X; inversion X).
  specialize (Hd Hnc). rewrite Hz in Hd. cbn in Hd. replace (b + (a - b)) with a in Hd by lia.
  unfold rd, ms_read_byte in Hd.
  destruct (ms_mem ms (Z_to_bv 64 a)) as [v|] eqn:E; [congruence|].
  exfalso. unfold rom_ok in Hrom. rewrite Hrom in Hd. rewrite image_byte_none_A in Hd; [discriminate|].
  rewrite Z_to_bv_unsigned. pose proof (bv_wrap_small 64 a). change (bv_modulus 64) with (2 ^ 64) in H. lia.
Qed.

Lemma SPA_dzero_bytes_A : ltac2:(tb__ "0|5|
S63S5bS9S39S57Q40M0A1A1S39S6aA1M1S67S69S8S62S4aR8R7R6R5S41G1S74R4S75R3R2A2A4A6S76S8R2SeS5aR8A1A1A3S3S15S11R3A1S16A3S3S39S14A1S1bR4A1S40S14A1A3S4bZ646000S44S0S0SdRaR5A2A3A2S0S4S4bS44S0S0SdRcR7A2M2A3R1A2S4dR1S46S0S0G2A3A2A2S3S3bS57Q8M3A1M4A1S68S90R9RcRaA3S59G0R2A2A2S42G4S59G3Z0A2A2A3F_;Fa;F_;F_;F_;F_;F_;Fo;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp tr ms md o [Hsm _] Hin Hz Hcells Hlo.
  pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0.
  pose proof (smatch_mm segsA _ _ _ _ _ S0) as (Hh & _ & _).
  pose proof S0 as (_ & _ & _ & _ & Hrom & _). cbn [cfg_ms w_cfg snd] in Hrom.
  apply (dzero_obj_bytes_A rho (vms md tp ms) o Hrom (proj1 (Forall_forall _ _) Hh o Hin) Hz Hcells Hlo).
Qed.

Lemma rm_absorb_inside : ltac2:(tb__ "0|0|
S9S39S8A1S67S57Q40A1S88R4R3R1A3S3S3bS57Q8A1A1S10S87R5R4R3A3R2A2S68R3R2A2A3F_;Fa;Fms;FR;Frho;").
Proof.
  intros rho R ms a H. unfold rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho R a) as [|Hn]; [reflexivity | exfalso; exact (Hn H)].
Qed.

Lemma rm_absorb_outside : ltac2:(tb__ "0|0|
S9S39S8A1S67S57Q40A1S5S88R4R3R1A3A1S3S3bS57Q8A1A1S10S87R5R4R3A3R2A2S10R5R2A2A3F_;Fa;Fms;FR;Frho;").
Proof.
  intros rho R ms a H. unfold rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho R a) as [Hi|]; [exfalso; exact (H Hi) | reflexivity].
Qed.

Lemma rw_absorb : ltac2:(tb__ "0|0|
S9S39S8A1S67S1S3S57Q40A1S1aS87R4R3R2A3R1A2S1aR4R1A2A3Fv;Fms;FR;Frho;").
Proof. intros; reflexivity. Qed.
Lemma rl_absorb : ltac2:(tb__ "0|0|
S9S39S8A1S67S1S3S39S57Q8A1A1S19S87R4R3R2A3R1A2S19R4R1A2A3Fl;Fms;FR;Frho;").
Proof. intros; reflexivity. Qed.

Lemma set_objs_set_objs : ltac2:(tb__ "0|1|
SfS39S8A1M0G0S3SfS8dS8dR3R2A2R1A2S8dR3R1A2A3Fl2;Fl1;FS;").
Proof. intros S l1 l2. reflexivity. Qed.
Lemma set_objs_self : ltac2:(tb__ "0|0|
SfS3SfS8dR1SeR1A1A2R1A3FS;").
Proof. intros S. destruct S; reflexivity. Qed.
Lemma ax_setS_ax_setS : ltac2:(tb__ "0|0|
S5bSfSfS3S5bS5cS5cR3R2A2R1A2S5cR3R1A2A3FS2;FS1;FA;").
Proof. intros A S1 S2. reflexivity. Qed.
Lemma ax_setS_self : ltac2:(tb__ "0|0|
S5bS3S5bS5cR1S5aR1A1A2R1A3FA;").
Proof. intros A. destruct A; reflexivity. Qed.
Lemma ax_S_ax_setS : ltac2:(tb__ "0|0|
S5bSfS3SfS5aS5cR2R1A2A1R1A3FS;FA;").
Proof. intros A S. reflexivity. Qed.

Lemma SPA_prepay_page_rm : ltac2:(tb__ "0|c|
S63S9S5bS57Q40M0A1M1S39G1A1M2S39S6aA1M3S67S69S62S4aR8R6R7R4S41G3S74R3S75R2R1A2A4A6S3S0S50S58G0R6A2S6bA2Z0M4A3S3S3aS6eR7S6cR3A1A2S3eA3S5S76G1R8R7A3A1S0S4S4bG4R1A2S4dR1S6bA2A2S3S3aS98S6fS6dR7A1A1S4cS58G0RbA2R2A2A2S45A3F_;Fj;S55S91R6R9A2S6bA2S79S8S8S18SdReR1A2S41S0S0S58G0RcA2M5S4cG5S6bA2A4A2Lo;SeS5aRcA1A1A3S9S9G2G2R13R4R2ReRcA4R14R4R2RfRdA4F_;Ft';Ft;Fr';Fr;S4bZ646000S58G0RdA2A2S87R10S3dS8S9aReA1S40S8A1A3S90RaS3dG1ReRdA3RbA3A3S9S4S62S4aR12R10R1S3dG1RfReA3S41G3S74RdS75RcRbA2A4A6S4S0S4S4bS58G0R10A2M6R1A2S4dR1S4cG6S6bA2M7A2A2S3S3bS57Q8M8A1M9A1MaS10R3S59G0R2A2A2S42G9S59G8G4A2A2A3F_;Fa;G1S5S4S4bG6S58G0R1A2MbA2S4dGbG7A2A2A1S3GaS10R3R2A2S10R13R2A2A3F_;Fa;A2A2Trho';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Fp;FA;Frho;FJ;").
Proof.
  intros J rho A p tp tr ms md Hsp Hal Hlz Hnin Hacc Hroom Hdisj HJ Hhigh rho'.
  pose proof (SPA_prepay_zero segsA J rho A p tp tr ms md Hsp Hal Hlz Hnin Hacc Hroom Hdisj ltac:(apply HJ)) as H1.
  pose proof (urange p) as Up. pose proof (page_aligned_end p Hal) as Pend.
  assert (R : obj_range rho (zero_page_obj p) = (bv_unsigned p, bv_unsigned p + page_size)).
  { unfold obj_range, obj_lo_of, obj_hi_of, soff, zero_page_obj. cbn [ob_base ob_lo ob_hi eval].
    rewrite Z_to_bv_bv_unsigned.
    replace (bv_signed (Z_to_bv 64 0)) with 0 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change page_size with 4096. replace (bv_signed (Z_to_bv 64 4096)) with 4096 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Z.add_0_r. reflexivity. }
  split; [|split].
  - pose proof (SPA_unobj segsA J rho (ax_setS A (set_objs (ax_S A) (ss_objs (ax_S A) ++ [zero_page_obj p])))
                  (ss_objs (ax_S A)) [zero_page_obj p] (p :: tp) tr ms md eq_refl H1 ltac:(apply HJ)) as H2.
    cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, set_objs_set_objs, set_objs_self, ax_setS_self in H2. exact H2.
  - intros a Ha. subst rho'. rewrite rm_absorb_inside.
    + apply (SPA_dzero_bytes_A J _ rho (p :: tp) tr ms md (zero_page_obj p) H1);
        [cbn [ax_S ax_setS set_objs ss_objs]; apply in_app_iff; right; left; reflexivity | reflexivity | reflexivity | rewrite R; cbn [fst]; lia | rewrite R; cbn [fst snd]; exact Ha].
    + exists (zero_page_obj p). split; [left; reflexivity|]. rewrite R. cbn [fst snd]. rewrite u64_of_lit; [exact Ha | unfold page_size in Ha, Pend; lia].
  - intros a Ha. subst rho'. apply rm_absorb_outside. intros (o & [<-|[]] & Hr). rewrite R in Hr. cbn [fst snd] in Hr. exact (Ha Hr).
Qed.

Lemma paid_cons_ge : ltac2:(tb__ "0|1|
S69S57Q40A1M0S39G0A1S4bS8fR3R1A2S8fR3S3dG0R2R1A3A2A2Ftp;Fp;Fmd;").
Proof.
  intros md p tp. unfold paid, unpaid. cbn [List.filter].
  destruct (page_in_ranges p (m_vm_lazy md) && negb (page_mem p (m_vm_materialized md))); cbn [length]; unfold page_size; lia.
Qed.
Lemma paid_app_le : ltac2:(tb__ "0|2|
S69S39S57Q40A1M0A1M1G1S4bS8fR3S3fG0R2R1A3A2S4cS8fR3R1A2S4fS6bS51S48G0R2A2A1A2A2A2Ftp;Fl;Fmd;").
Proof.
  intros md l tp. induction l as [|p l IH]; cbn [app length]; [lia|].
  pose proof (paid_cons_le md p (l ++ tp)). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma eval_ext_rwrl : ltac2:(tb__ "0|1|
S9S9SaS1S3S57Q40A1M0S1aR3R1A2S1aR4R1A2A3Fi;S1S3S39S57Q8A1A1S19R4R1A2S19R5R1A2A3Fl;S3G0ScR4R3A2ScR5R3A2A3F_;F_;Fe;Frho';Frho;").
Proof.
  intros rho rho' e Hrw Hrl. induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe, ?Hrw, ?Hrl; try reflexivity.
  all: try (rewrite IHe3; reflexivity).
Qed.

Lemma In_pages_rev : ltac2:(tb__ "0|1|
S0S3cS57Q40A1M0S76G0R1S80R3R2A2A3S7S3cS3cS4S8aR1R4A2S3G0R3S7fR5R1A2A3A2Lk;A2F_;Fp;Fn;Fq;").
Proof.
  intros q n p. induction n as [|n IH]; cbn; intros H; [destruct H|].
  destruct H as [<-|H]; [exists n; split; [lia|reflexivity]|].
  destruct (IH H) as (k & Hk & ->). exists k. split; [lia|reflexivity].
Qed.
Lemma length_pages_rev : ltac2:(tb__ "0|0|
S0S3cS3S3cS48S57Q40A1S80R2R1A2A2R1A3Fn;Fq;").
Proof. intros q n. induction n; cbn; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma SPA_prepay_pages_rm : ltac2:(tb__ "0|c|
S63S5bS0S3cS9S39S57Q40M0A1M1A1M2S39S6aA1M3S67S69S62S4aR9R8R5R4S41G3S74R3S75R2R1A2A4A6S9S9G2G2ReR4R2R8R6A4RfR4R2R9R7A4F_;Ft';Ft;Fr';Fr;S3S0S50R9Z1000M4A2Z0M5A3S4bZ646000RaA2S4bS4cRbS4fG4S51RaA1A2A2S4eZ2Z40A2A2S3cS8aR1RcA2S3S3aS6eS7fReR2A2S6cR8A1A2S3eA3F_;Fk;S3cS8aR1RdA2S5S76G1S7fRfR2A2RcA3A1F_;Fk;S0S4S4bRfR1A2S4dR1S4cRfS4fG4S51ReA1M6A2A2A2A2S3S3aS98S6fS6dRaA1A1R2A2S45A3F_;Fz;S55S91R9RcA2S4fS6bG6A2A2S79S8S8S18SdRfR1A2S41S0S0R11S4cR11S4fG4S51R10A1A2A2A4A2Lo;SeS5aR11A1A1A3S7S9S9S4S62S4aR14R13R1S3fG1S80R12R11A2RfA3S41G3S74ReS75RdRcA2A4A6S4S1S3G1S1aR2R1A2S1aR11R1A2A3Fi;S4S1S3S39S57Q8M7A1M8A1S19R2R1A2S19R11R1A2A3Fl;S4S0S4S4bR13R1A2S4dR1S4cR13S4fG4S51R12A1A2A2M9A2A2S3S3bG8A1MaS10R3S59G0R2A2A2S42G8S59G7G5A2A2A3F_;Fa;G1S5S4S4bR13S58G0R1A2MbA2S4dGbG9A2A2A1S3GaS10R3R2A2S10R12R2A2A3F_;Fa;A2A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fn;Fq;FA;FJ;").
Proof.
  intros J A q n. induction n as [|n IH]; intros rho tp tr ms md Hsp HJ Hqal Hqlo Hqhi Hlz Hnin Hacc Hroom Hdisj.
  - exists rho. cbn [pages_rev app]. split; [exact Hsp|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros a Ha; cbn in Ha; lia | intros; reflexivity].
  - rewrite Nat2Z.inj_succ in *. unfold page_size in Hroom.
    destruct (IH rho tp tr ms md Hsp HJ Hqal Hqlo ltac:(lia) ltac:(intros k Hk; apply Hlz; lia) ltac:(intros k Hk; apply Hnin; lia)
                 ltac:(intros z Hz; apply Hacc; lia) ltac:(unfold page_size; lia)) as (rho1 & Hsp1 & Hrw1 & Hrl1 & Hz1 & Ho1).
    { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. lia. }
    set (p := pageZ q n).
    assert (Up : bv_unsigned p = q + 4096 * Z.of_nat n) by (unfold p, pageZ; apply u64_of_lit; lia).
    assert (Hobj : forall o, In o (ss_objs (ax_S A)) -> obj_range rho1 o = obj_range rho o).
    { intros o Ho. unfold obj_range, obj_lo_of, obj_hi_of, soff.
      rewrite !(eval_ext_rwrl rho rho1) by assumption. reflexivity. }
    destruct (SPA_prepay_page_rm J rho1 A p (pages_rev q n ++ tp) tr ms md Hsp1) as (Hsp2 & Hz2 & Ho2).
    + rewrite Up. change page_size with 4096. replace (q + 4096 * Z.of_nat n) with (q + Z.of_nat n * 4096) by lia. rewrite Z_mod_plus_full. exact Hqal.
    + apply Hlz. lia.
    + intros Hin. apply in_app_iff in Hin as [Hin|Hin].
      * apply In_pages_rev in Hin as (k & Hk & E). apply (f_equal bv_unsigned) in E. rewrite Up in E. unfold pageZ in E. rewrite u64_of_lit in E by lia. lia.
      * exact (Hnin n ltac:(lia) Hin).
    + intros j Hj. rewrite Up. apply Hacc. unfold page_size in Hj. lia.
    + unfold headroom in Hroom |- *. pose proof (paid_app_le md (pages_rev q n) tp) as PL. rewrite length_pages_rev in PL. unfold page_size in PL |- *. lia.
    + apply Forall_forall. intros o Ho. rewrite (Hobj o Ho). pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
      rewrite Up. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. unfold page_size. lia.
    + apply HJ.
    + rewrite Up. lia.
    + cbv zeta in Hsp2, Hz2, Ho2.
      exists (rho_absorb rho1 [zero_page_obj p] (vms md (p :: pages_rev q n ++ tp) ms)).
      split; [exact Hsp2|]. split; [intros i; rewrite rw_absorb; apply Hrw1|]. split; [intros l; rewrite rl_absorb; apply Hrl1|]. split.
      * intros a Ha. destruct (Z_lt_dec a (q + 4096 * Z.of_nat n)) as [Hlt|Hge].
        -- rewrite Ho2; [apply Hz1; lia|]. rewrite u64_of_lit by lia. rewrite Up. unfold page_size. lia.
        -- apply Hz2. rewrite Up. unfold page_size. lia.
      * intros a Ha. rewrite Ho2; [apply Ho1; lia|]. rewrite Up. unfold page_size. lia.
Qed.

Lemma xr_ok_of_zero : ltac2:(tb__ "0|9|
S9S39S8A1S0S43SaSaA2S0S0S58Q40M0ScR6S44SaSaR3A3A2A2S0S58G0ScR7S46SaSaR4A3A2A2S0S3S0S50R2Z8M1A2Z0M2A3S4bS4cR3R2A2S4eZ2Z40A2M3A2S4bG2R6A2S4bR6G3A2S3S0S50R8G1A2G2A3M4G4S0S4S4bR9R1A2S4dR1S4cR9R8A2A2A2S4S4bRcS4cReS53R2G1A2A2M5A2S4dG5RbA2A2F_;Fa;S0S4S4bRcR1A2S4dR1RbA2A2S3S3bS57Q8M6A1M7A1S10R11S59G0R2A2M8A2S42G7S59G6G2A2A2A3F_;Fz;S0S4S4bRdR1A2S4dR1RcA2A2S26R12R11G8A3F_;Fz;S61R11R10RfReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;TL;TB;Fhi;Flo;Fr;Foff;Fobjs;Frho;").
Proof.
  intros rho objs off r lo hi B L HB8 HBL Hlo Hhi Hlo8 Hhi8 Hin Hz Hout.
  unfold xr_ok. cbv zeta. fold B L. split; [exact HB8|]. split; [exact HBL|].
  intros a Ha. pose proof (Hin a Ha) as Hs.
  assert (W : forall j, 0 <= j < 8 -> lo <= (off + a / 8) / 8 * 8 + j < hi).
  { intros j Hj. pose proof (Z.div_mod (off + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + a / 8) 8 ltac:(lia)).
    apply Z.mod_divide in Hlo8 as [kl Hkl]; [|lia]. apply Z.mod_divide in Hhi8 as [kh Hkh]; [|lia]. nia. }
  split; [lia|]. split.
  - unfold shadow_addr. apply Hout. lia.
  - split.
    + intros j Hj. unfold word_byte. split; [apply Hout; apply W; exact Hj|]. rewrite Hz; [discriminate | apply W; exact Hj].
    + exists (Z_to_bv 8 0). unfold shadow_addr. split; [apply Hz; lia|]. left. reflexivity.
Qed.

Lemma obj_holds_to_unknown : ltac2:(tb__ "0|0|
S9S67S8S3S15S11R1A1S16A3S12S4aR4R3R2A4S12S4aR5R4S82R3A1A4F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hz (Hb & Hw & Hc & Hd & Hi). unfold obj_to_unknown. rewrite Hz in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [exact Hc|]. split; [|exact I].
  cbn [ob_dflt ob_cells ob_lo ob_base]. intros off Hoff Hnc. cbn. exists (Z_to_bv 8 0). exact (Hd off Hoff Hnc).
Qed.

Lemma mem_match_to_unknown : ltac2:(tb__ "0|1|
S9S39S8A1M0S8G0S67S3S15S11R3A1S16A3S17S4aR6S3fS8R5S3dS8R4R3A3A3R2A4S17S4aR7S3fS8R6S3dS8S82R5A1R4A3A3R3A4F_;F_;Fms;FB;Fx;FA;Frho;").
Proof.
  intros rho A x B ms Hz (Hh & Hpd & Hfr).
  assert (RNG : obj_range rho (obj_to_unknown x) = obj_range rho x) by reflexivity.
  split; [|split].
  - apply Forall_app in Hh as [HA HxB]. inversion HxB; subst. apply Forall_app. split; [exact HA|]. constructor; [apply obj_holds_to_unknown; assumption | assumption].
  - rewrite (pairwise_disjoint_pdr) in Hpd |- *. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Lemma SPA_obj_to_unknown : ltac2:(tb__ "0|3|
S63S9S5bS3cS39S57Q40M0A1A1S70S8aR3S48S8SeS5aR4A1A1A2A2S3S39S43SaSaA2M1A1S5eR5A1S40G1A1A3S3S15S11S7bS8R5SeS5aR6A1A1S9aS59G0Z0A2A1A4A1S16A3S3S3aS8cS5aR7A1M2S83G2R6A2A2S3eA3S62S4aRaR8R9R6R5A6S62S4aRbS5cR9S83S5aR9A1R8A2A2RaR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i tp w Hi HX Hz Hsame Hsp.
  destruct (firstn_skipn_split (ss_objs (ax_S A)) i Hi) as (x & H1 & H2).
  assert (Hx : nth i (ss_objs (ax_S A)) (zero_page_obj (Z_to_bv 64 0)) = x).
  { rewrite H2. rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn. replace (i - Nat.min i (length (ss_objs (ax_S A))))%nat with 0%nat by lia. reflexivity. }
  rewrite Hx in Hz.
  apply (SPA_reobj segsA J rho A (unknown_obj_at (ax_S A) i) tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segsA _ _ _ _ _ S0) as MM.
    unfold unknown_obj_at. cbn [ss_objs set_objs]. rewrite H1. cbn [map]. rewrite H2 in MM.
    apply mem_match_to_unknown; assumption.
  - unfold xshadow_outside. rewrite HX. constructor.
Qed.

Lemma SPA_split_chain : ltac2:(tb__ "0|0|
S63S9S39S43S3cSaA2A1S5bSfS39S57Q40A1A1S70S3S3bSfA1S85S5aR4A1R5A2S42SfR3A2A3S62Vsegs;R8R5R7R3R2A6S62Vsegs;R9S5cR6R5A2R8R4R3A6F_;F_;Fw;Ftp;FS';FA;Fl;Frho;FJ;").
Proof.
  intros J rho l. induction l as [|[i mid] l IH]; intros A S' tp w H Hsp; cbn [split_chain] in H.
  - injection H as <-. rewrite ax_setS_self. exact Hsp.
  - destruct (split_obj_at (ax_S A) i mid) as [S1|] eqn:E; [|discriminate].
    pose proof (SPA_split segs J rho A i mid S1 tp w E Hsp) as H1.
    pose proof (IH (ax_setS A S1) S' tp w H H1) as H2. rewrite ax_setS_ax_setS in H2. exact H2.
Qed.

Definition KxAt (m : Model) (B : Z) (tp0 : list word) : jpredA := ltac2:(tb__ "0|1|
S9S39S57Q40A1A1M0S39S6aA1S69S4S3G0R3Vtp0;A3S8bVm;VB;R4R3R2R1A6A2Lmd;Ltr;Lt;Lr;").

Lemma stableA_KxAt : ltac2:(tb__ "0|0|
S1S69S0S39S57Q40A1A1S64Vsegs;R4S94R3R2R1A3A3Ftp0;FB;Fm;Fn;").
Proof.
  intros n m B tp0 rho rho' tp tr md md' Hag Hme [-> HK]. split; [reflexivity|].
  exact (stableA_KxA segs n m B rho rho' tp0 tr md md' Hag Hme HK).
Qed.

Lemma call_pureA : ltac2:(tb__ "0|4|
S73S5bS5bS39S5dA1S89S39S8A1M0S69S0S39S57Q40A1A1M1S9S73S63S9G1S39S6aA1M2S69R5R4R3R2R1A4S3G2R3S40S6aA1A3F_;Fmd;Ftr;Ftp;Frho;S66Vsegs;RdR2A3F_;FJ;S3S3bG0A1S9cRbRaR8A3S42G0R7A2A3S3S3aS9bRcRbR9R8S7aS5dS5bS5fRaA4A5S3eA3S63S9G1S66Vsegs;R11R3A3S64Vsegs;S13S5aR10A1A1R4A3S72Vsegs;R13S62Vsegs;R5R11R4R3A5S65Vsegs;R5S13S5aR11A1A1M3R4R3R10A6A4F_;F_;Ftp1;Frho1;FJ;S5dS9S76S5dR2ReA3S1dG3R9R2A3S72Vsegs;R13S62Vsegs;S8bRdRcA2S9dRfR11S5fR4A1R12ReA5R3RbA5R9A4F_;F_;Frho';FL;S72Vsegs;R10S62Vsegs;S8bRaR9A2RfR7R8A5R6A4F_;F_;F_;F_;F_;FQ;Frho;Ftp0;FB;Fm;FR;Fs;FPosts;FPre;FC;Fok;").
Proof.
  intros ok C Pre Posts s R m B tp0 rho Q OKF He Hchk Hsum Hcont.
  apply (call_soundA segs ok (KxA m B) (KxAt m B tp0) (KxAt m B tp0) (KxAt m B tp0) C Pre s R Posts Q rho tp0 He Hchk).
  - intros rho1 tp1. apply Hsum; [|apply stableA_KxAt]. apply OKF. intros r t tr md [_ HK]. exact (KxA_nil _ _ _ _ _ _ HK).
  - intros tr ms md Hsm HK. split; [reflexivity | exact HK].
  - intros L rho' rhoL tpL tr ms md tr' md' Hin Hsm HK HLK [-> HK']. split; [reflexivity | exact HK'].
  - intros L rho' tpL Hin Hag n HgQ w [Hsm [-> HK]]. apply (Hcont L rho' Hin Hag n HgQ w). split; [exact Hsm | exact HK].
Qed.

Lemma ecall_pureA : ltac2:(tb__ "0|2|
S5bS5bS39S5dA1S89S39S8A1M0S69S0S39S57Q40A1A1M1S9S70OF_;S3S3bG0A1S9cRaR9R7A3S42G0R6A2A3S3S3aS9bRbRaR8R7S7aS5dS5bS5fR9A4A5S3eA3S63S9G1S64Vsegs;S13S5aReA1A1R3A3S71Vsegs;S62Vsegs;R4RfR3R2A5S65Vsegs;R4S13S5aRfA1A1R3R2ReA6A3F_;Ftp1;Frho1;FJ;S5dS9S76S5dR2RdA3S1dS13S5aR10A1A1R8R2A3S71Vsegs;S62Vsegs;S8bRcRbA2S9dReR10S5fR4A1R11RdA5R3RaA5R8A3F_;F_;Frho';FL;S71Vsegs;S62Vsegs;S8bR9R8A2ReR6R7A5R5A3F_;F_;F_;F_;FQ;Frho;Ftp0;FB;Fm;FR;Fs;FPosts;FPre;FC;").
Proof.
  intros C Pre Posts s R m B tp0 rho Q He Hchk Hsum Hcont.
  apply (call_completeA segs (KxA m B) (KxAt m B tp0) (KxAt m B tp0) (KxAt m B tp0) C Pre s R Posts Q rho tp0 He Hchk).
  - intros rho1 tp1. apply Hsum. apply stableA_KxAt.
  - intros tr ms md Hsm HK. split; [reflexivity | exact HK].
  - intros L rho' rhoL tpL tr ms md tr' md' Hin Hsm HK HLK [-> HK']. split; [reflexivity | exact HK'].
  - intros L rho' tpL Hin Hag w [Hsm [-> HK]]. apply (Hcont L rho' Hin Hag w). split; [exact Hsm | exact HK].
Qed.

Lemma mem_match_replace : ltac2:(tb__ "0|1|
S9S39S8A1M0S8S8G0S67S3S43S0S0A2SdR6R3A2SdR6R4A2A3S12S4aR7R2R5A4S12S4aR8R3R5A4F_;S17S4aR8S3fS8R7S3dS8R6R4A3A3R3A4S17S4aR9S3fS8R8S3dS8R6R5A3A3R4A4F_;F_;F_;Fms;FB;Fo';Fo;FA;Frho;").
Proof.
  intros rho A o o' B ms RNG Himp (Hh & Hpd & Hfr). split; [|split].
  - apply Forall_app in Hh as [HA HxB]. inversion HxB; subst. apply Forall_app. split; [exact HA|]. constructor; [apply Himp; assumption | assumption].
  - rewrite (pairwise_disjoint_pdr) in Hpd |- *. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Lemma firstn_skipn_of_split : forall {T} (l1 l2 : list T) (a : T),
  firstn (length l1) (l1 ++ a :: l2) = l1 /\ skipn (S (length l1)) (l1 ++ a :: l2) = l2.
Proof.
  intros T l1 l2 a. split.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r.
  - rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia.
    rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma outside_all_ranges : ltac2:(tb__ "0|3|
S9S39S8A1M0G0S57Q40A1S3S39S43S0S0A2M1A1S7aS8G1SdR4A1M2R2A4S7aS8G1G2R3A4A3S26R5R4R2A3S26R6R4R3A3F_;F_;Fa;Fobjs';Fobjs;Frho;").
Proof.
  intros rho objs objs' a Hm H. unfold outside_all in *. rewrite Forall_forall in H |- *. intros o' Ho'.
  assert (Hin : In (obj_range rho o') (map (obj_range rho) objs)) by (rewrite <- Hm; apply in_map; exact Ho').
  apply in_map_iff in Hin as (o & Ho & Hino). cbv zeta. rewrite <- Ho. exact (H o Hino).
Qed.

Lemma xshadow_outside_ranges : ltac2:(tb__ "0|3|
S9S5bS39S8A1M0G0S3S39S43S0S0A2M1A1S7aS8G1SdR4A1M2R1A4S7aS8G1G2R2A4A3S99R5R4R3A3S99R6R5R3A3F_;F_;Fobjs';Fobjs;FA;Frho;").
Proof.
  intros rho A objs objs' Hm H. unfold xshadow_outside in *. rewrite Forall_forall in H |- *. intros r Hr a j Ha Hj.
  eapply outside_all_ranges; [exact Hm | exact (H r Hr a j Ha Hj)].
Qed.

Lemma SPA_replace_obj : ltac2:(tb__ "0|1|
S63S9S5bS3cS8S8S39S57Q40A1A1S70S3S3bS8A1S77S8SeS5aR6A1A1R5A3S42S8R4A2A3S3S43S0S0A2SdR8R4A2SdR8R5A2A3S67S27S4aR1A2S12S4aRbR2R8A4S12S4aRcR3R8A4F_;F_;Fms;S3S3aS8cS5aR9A1M0S7cG0R8R6A3A2S3eA3S62S4aRcRaRbR6R5A6S62S4aRdS5cRbS7cS5aRbA1RaR8A3A2RcR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fo';Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o o' tp w Hn RNG Himp Hsame Hsp.
  destruct (nth_error_split _ _ Hn) as (l1 & l2 & Hl & Hlen).
  assert (Eobjs : ss_objs (replace_obj_at (ax_S A) i o') = l1 ++ o' :: l2).
  { unfold replace_obj_at. cbn [ss_objs set_objs]. rewrite Hl, <- Hlen. destruct (firstn_skipn_of_split l1 l2 o) as [-> ->]. reflexivity. }
  apply (SPA_reobj segsA J rho A (replace_obj_at (ax_S A) i o') tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segsA _ _ _ _ _ S0) as MM. pose proof S0 as (_ & _ & _ & _ & Hrom & _). cbn [cfg_ms w_cfg snd] in Hrom.
    rewrite Eobjs. rewrite Hl in MM.
    apply (mem_match_replace rho l1 o o' l2); [exact RNG | apply Himp; exact Hrom | exact MM].
  - destruct Hsp as [Hsm _]. apply (xshadow_outside_ranges rho A (ss_objs (ax_S A))).
    + rewrite Eobjs, Hl, !map_app. cbn [map]. rewrite RNG. reflexivity.
    + apply shadow_ok_outside. exact (smatchA_shadow segsA _ _ _ _ Hsm).
Qed.

Lemma cells_clear_lit_uncovered : ltac2:(tb__ "0|0|
S9S39S14A1S0S0S3S3aS7eR3R2R1A3S3eA3Sa5R5R4R3R2A4F_;Fk;Foff;Fcells;Frho;").
Proof.
  intros rho cells off k H j Hj Hcov. unfold SymState.covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hin).
  pose proof (proj1 (forallb_forall _ _) H c Hc) as X. cbv beta in X. unfold in_cell in Hin.
  destruct (c_off c) as [co| | | | | | |]; try discriminate. rewrite soff_lit in Hin.
  apply Bool.orb_true_iff in X as [X|X]; [apply Z.leb_le in X | apply Z.leb_le in X]; lia.
Qed.

Lemma obj_holds_add_img_cell : ltac2:(tb__ "0|5|
S9S67S8S0S0S0S0S0S27S4aR7A2S12S4aR9R8R7A4S3S15S11R8A1S2eA3S3SaS23R9A1SbZ0M0A1A3S3SaS25RaA1SbR9A1M1A3S3SaS24RbA1G1A3S4bS52S4eZ2Z3fA2M2A1RbA2S4dRbG2A2S4bRdRbA2S4bS4cRcRbA2RdA2S4S4dG0RcA2S4bRcZ8A2A2S3S3aS7eS1bR11A1ReRdA3S3eA3S3S3bS39S57Q8A1A1M3A1S8eS4aRfS56ReA1M4A3S42G3S1fG4S59Q40RdA2A2A2A3S12S4aR15R14S7dR13S20SbR10A1RfSbReA1A3A2A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fhi;Flo;Fo;Fms;Frho;").
Proof.
  intros rho ms o lo hi off k v Hrom Ho Hz Hb Hlo Hhi Hlo63 Hhi63 H1 H2 Hk Hclr Himg.
  assert (Elo : obj_lo_of rho o = lo) by (unfold obj_lo_of; rewrite Hlo; apply soff_lit_small; lia).
  assert (Ehi : obj_hi_of rho o = hi) by (unfold obj_hi_of; rewrite Hhi; apply soff_lit_small; lia).
  unfold add_cell_front.
  apply (obj_holds_add_cells segsA rho ms o [mkCell (SLit off) k (SLit v)] Ho).
  constructor; [|constructor]. unfold cell_holds. cbn [c_off c_width c_val]. rewrite soff_lit_small by lia. rewrite Elo, Ehi.
  split; [lia|]. split; [lia|].
  rewrite (obj_read_image segsA rho ms o off k _ Hrom Ho Hz Hb ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)
             (cells_clear_lit_uncovered rho _ _ _ Hclr) Himg).
  reflexivity.
Qed.

Lemma SPA_add_img_cell : ltac2:(tb__ "0|8|
S63S9S5bS3cS8S0S0S0S0S0S39S57Q40M0A1A1S70S3S3bS8A1S77S8SeS5aRaA1A1R9A3S42S8R8A2A3S3S15S11R9A1S2eA3S3SaS23RaA1SbZ0M1A1A3S3SaS25RbA1SbRaA1M2A3S3SaS24RcA1G2A3S4bS52S4eZ2Z3fA2M3A1RcA2S4dRcG3A2S4bReRcA2S4bS4cRdRcA2ReA2S4S4dG1RdA2S4bRdZ8A2A2S3S3aS7eS1bR12A1RfReA3S3eA3S3S3bS39S57Q8A1A1M4A1S8eS4aR10S56RfA1M5A3S42G4S1fG5S59G0ReA2A2A2A3S3S3aS8cS5aR16A1M6S7cG6R15S7dR14S20SbR11A1M7R10SbRfA1A3A2A3A2S3eA3S62S4aR19R17R18RfReA6S62S4aR1aS5cR18S7cS5aR18A1R17S7dR16S20SbR13A1R12G7A3A2A3A2R19R10RfA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fv;Fk;Foff;Fhi;Flo;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o lo hi off k v tp w Hn Hz Hb Hlo Hhi Hlo63 Hhi63 H1 H2 Hk Hclr Himg Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms Hrom Ho. eapply obj_holds_add_img_cell; eauto.
Qed.

Lemma smatch_carve_unknown : ltac2:(tb__ "0|5|
S9SfS39S6aA1M0S67S69SaS0S0S1S1eS4aR9R8S41G0S74R7S75R6R5A2A4A4S22S2bR9A1S2cR9A1S29R9A1S28R9A1S2dR9A1S3fS8SeR9A1S3dS8S21R5SbR4A1SbR3A1S40S14A1S2fA5S40S8A1A3A3S1cR9A1R2S2aR9A1A9SfS3S3aS34R1A1S3eA3S58Q40M1ScRcR7A2A2S0S4bS52S4eZ2M2Z3fA2M3A1R7A2S4S4bR8R7A2S4dR7G3A2A2S4dS54R8R9A2G3A2S4bZ0S4cR4RaA2A2S4bS4cR5RaA2S4eG2Z40A2A2S79S8S8S18SdR13R1A2S41S0S0S4cR7RdA2S4cR7RcA2A4A2Lo';SeR11A1A3S0S4S4bS4cR8ReA2R1A2S4dR1S4cR8RdA2A2A2S5S3S3bS57Q8A1M4A1S10R15S59G1R2A2A2S47G4A1A3A1F_;Fa;S1eS4aR14RaS41G0S74R12S75R11R10A2A4A4F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof.
  intros rho S tr ms md base lo hi nx Hsm S' Hwf' b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base (SLit lo) (SLit hi) [] DUnknown).
  assert (Hlo' : soff rho (SLit lo) = lo) by (rewrite soff_lit_small; lia).
  assert (Hhi' : soff rho (SLit hi) = hi) by (rewrite soff_lit_small; lia).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi]. rewrite Hlo', Hhi'. reflexivity. }
  assert (Hout : forall a, b + lo <= a < b + hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. apply Forall_forall. intros o Ho. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite u64_of_lit by lia. lia. }
  assert (MEM : forall a, b + lo <= a < b + hi -> exists v, ms_mem ms (Z_to_bv 64 a) = Some v).
  { intros a Ha. rewrite (Hfr _ (Hout a Ha)). destruct (rm rho (Z_to_bv 64 a)) as [v|] eqn:E; [exists v; reflexivity | exfalso; exact (Hbytes a Ha E)]. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. rewrite Hlo', Hhi'.
    split; [lia|]. split.
    { intros off Hoff _. unfold wview. destruct (MEM (b + off) ltac:(lia)) as [v Hmv]. rewrite Hmv. discriminate. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. destruct (MEM (b + off) ltac:(lia)) as [v Hmv]. rewrite Hmv. exists v. reflexivity.
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. fold newo. rewrite Hnr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_unknown : ltac2:(tb__ "0|b|
S63S9S5bS39S57Q40M0A1A1S39S6aA1M1S67S69SaS0S0S1S62S4aRbR9RaR8S41G1S74R7S75R6R5A2A4A6S22S2bS5aRaA1M2A1S2cG2A1S29G2A1S28G2A1S2dG2A1S3fS8SeG2A1S3dS8S21R5SbR4A1SbR3A1S40S14A1S2fA5S40S8A1A3A3S1cG2A1R2S2aG2A1A9SfS3S3aS34R1A1S3eA3S97S13S5aRcA1A1R4A2S58G0ScReR8A2A2S0S4bS52S4eZ2M3Z3fA2M4A1R8A2S4S4bR9R8A2S4dR8G4A2A2S4dS54R9RaA2G4A2S4bZ0M5S4cR4RbA2A2S4bS4cR5RbA2S4eG3Z40A2A2S79S8S8S18SdR15R1A2S41S0S0S4cR7ReA2S4cR7RdA2A4A2Lo';SeS5aR13A1A1A3S0S4S4bS4cR8RfA2R1A2S4dR1S4cR8ReA2A2A2S5S3S3bS57Q8A1M6A1S10R17S59G0R2A2A2S47G6A1A3A1F_;Fa;S43SaSaA2M7S0S0S76G7R3S5eR18A1A3S4S4bS58G0ScR1aS44SaSaR4A3A2A2M8R3A2S4dR3S4cG8S58G0ScR1aS46SaSaR4A3A2A2A2A2A2S4S4bG5R3A2S4dR3Z8M9A2A2S5S4S4bS4cReR15A2S4cS4fS53S4cS58G0ScR1cS60R1bA1A2A2S53R5G9A2A2G9A2G9A2R4A2MaA2S4dGaS4cReR14A2A2A2A1F_;F_;F_;Fj;Fy;Frr;S62S4aR18S5cR16RcA2R17R15S41G1S74R14S75R13R12A2A4A6F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp tr ms md base lo hi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S' Hwf' Hnx b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes Hxs.
  split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_unknown rho (ax_S A) tr (vms md tp ms) (vmd md) base lo hi nx Hsm Hwf' Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. fold b.
    rewrite !soff_lit_small by lia.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

Lemma SPA_released_defined : ltac2:(tb__ "0|6|
S63S5bS9S39S57Q40M0A1A1S39S6aA1M1S67S69S39S8A1M2S8S3G2SeS5aR8A1A1S3fS8R2S3dS8R1S40S8A1M3A3A3A3S3S3aS37S11R2A1A1S3eA3S4bZ646000S44S0S0SdR9R3A2A3A2S62S4aRcRbRaR9S41G1S74R8S75R7R6A2A4A6S0S4S4bS44S0S0SdRcR6A2M4A3R1A2S4dR1S46S0S0G4A3A2A2S5S3S3bS57Q8A1M5A1S10S87RdS3dS8R7G3A3S90R9RcRaA3A3S59G0R2A2A2S47G5A1A3A1F_;Fa;F_;F_;F_;F_;Fo;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp tr ms md objs o Ho Hw Hlo [Hsm _] a Ha.
  pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0.
  pose proof (smatch_mm segsA _ _ _ _ _ S0) as (Hh & _ & _).
  pose proof (proj1 (Forall_forall _ _) Hh o ltac:(rewrite Ho; apply in_app_iff; right; left; reflexivity)) as ((B1 & B2 & B3 & B4) & Hwv & _).
  unfold obj_range in Ha, Hlo. cbn [fst snd] in Ha, Hlo.
  rewrite rm_absorb_inside.
  - specialize (Hwv (a - bv_unsigned (eval rho (ob_base o))) ltac:(lia) Hw).
    replace (bv_unsigned (eval rho (ob_base o)) + (a - bv_unsigned (eval rho (ob_base o)))) with a in Hwv by lia.
    unfold wview in Hwv. destruct (ms_mem (vms md tp ms) (Z_to_bv 64 a)) as [v|] eqn:E; [congruence|].
    exfalso. apply Hwv. change (Z.of_N 1) with 1. rewrite (find_segment_none_A (bv_unsigned (Z_to_bv 64 a))); [reflexivity|].
    rewrite u64_of_lit by lia. lia.
  - exists o. split; [left; reflexivity|]. unfold obj_range. cbn [fst snd]. rewrite u64_of_lit by lia. lia.
Qed.

Definition bump_next (St : sstate) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S22S2bVSt;A1S2cVSt;A1S29VSt;A1S28VSt;A1S2dVSt;A1SeVSt;A1S1cVSt;A1Vnx;S2aVSt;A1A9").

Lemma smatch_bump_agree : ltac2:(tb__ "0|0|
S9S9SfS1S43S39S6aA1S74A2S1dS13R3A1R5R4A3S97S13R4A1R3A2S1eS4aR7R5R3A4S1eS4aR7S93R6R5A2R4A4F_;F_;F_;Fw;Fnx;FS;Frho';Frho;").
Proof.
  intros rho rho' S nx [tr [ms md]] Hag Hle Hsm.
  pose proof (smatch_agree segsA rho rho' S _ Hag Hsm) as H.
  destruct H as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch, bump_next. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
  split; [apply swf_mono_next; assumption|].
  repeat (split; [assumption|]). exact Hfacts.
Qed.

Lemma SPA_bump_agree : ltac2:(tb__ "0|1|
S63S9S9S5bS1S39S57Q40A1A1M0S70S9S9G0S39S6aA1S69RcR5R3R2R1A4RdR5R4R3R2A4F_;Fmd;Ftr;Ft;Fr';Fr;S1dS13S5aR5A1A1R7R6A3S97S13S5aR6A1A1R5A2S62S4aRaR7R9R5R4A6S62S4aRbS5cR8S93S5aR8A1R7A2A2R9R6R5A6F_;F_;F_;F_;Fw;Ftp;Fnx;FA;Frho';Frho;FJ;").
Proof.
  intros J rho rho' A nx tp w HJ Hag Hle [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|eapply HJ; exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [ax_S ax_setS]. apply (smatch_bump_agree rho rho'); assumption.
  - unfold axwf in Hwf |- *. cbn [ax_S ax_setS ax_X ax_base bump_next ss_next] in Hwf |- *. apply andb_prop in Hwf as [HX Hb].
    apply andb_true_intro. split.
    + apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) HX r Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2]. apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply (shadow_ok_stable A _ rho rho' Hag Hwf (proj1 Hsm) eq_refl eq_refl eq_refl Hsh).
Qed.

Definition M4096 : Z := 18446744073709547520.

Lemma U_and_m4096 : ltac2:(tb__ "0|2|
S9SaS3S0S58Q40M0ScR2S30Sa1R1SbS95A1A3A2A2S54S58G0ScR2R1A2A2M1S50G1Z1000A2A2A3Fe;Frho;").
Proof.
  intros rho e. cbn [eval]. rewrite and_val. unfold M4096. rewrite u64_of_lit by lia.
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_high_mask; [reflexivity | lia | apply urange].
Qed.

Lemma U_remu_4096 : ltac2:(tb__ "0|2|
S9SaS3S0S58Q40M0ScR2S35Sa2R1SbZ1000M1A1A3A2A2S50S58G0ScR2R1A2A2G1A2A3Fe;Frho;").
Proof.
  intros rho e. cbn [eval]. unfold mul_div. rewrite u64_of_lit by lia. cbn [Z.eqb].
  rewrite bv_modu_unsigned. rewrite u64_of_lit by lia. reflexivity.
Qed.

Lemma U_add_lit : ltac2:(tb__ "0|1|
S9SaS0S4bZ0R1A2S4dS4cS58Q40M0ScR4R3A2A2R2A2S4eZ2Z40A2A2S3S0S58G0ScR5S30Sa0R4SbR3A1A3A2A2S4cS58G0ScR5R4A2A2R3A2A3F_;F_;Fc;Fe;Frho;").
Proof.
  intros rho e c Hc Hb. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  pose proof (urange (eval rho e)). rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma triple_SPA_absurd : ltac2:(tb__ "0|0|
S70OF_;S63S5bS9S39S57Q40A1A1S73S79S33S31R3A1S1cS5aR4A1A1A3S6F_;S72S4aR7S62S4aR6R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof.
  intros ok J A rho tp Q H. apply triple_factsA. intros HF. exfalso. exact (H HF).
Qed.
Lemma etriple_SPA_absurd : ltac2:(tb__ "0|0|
S63S5bS9S39S57Q40A1A1S70OF_;S79S33S31R3A1S1cS5aR4A1A1A3S6F_;S71S4aS62S4aR6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp Q H. apply etriple_factsA. intros HF. exfalso. exact (H HF).
Qed.

Definition is_zero_cell (c : cell) : bool := ltac2:(tb__ "0|4|
SaS3aLx;S36Vc;A1S0S0S3aLz;R1S3eS1S45Lp;M0G0X0x3Lz;S1S45Li;Sa3SaSaS45Lb;La;M1Lop;M2G2Sa4G1Lop;M3G3S3aS2SaS45La;Lw;Lsgn;S1SaS0S45Lk;Li;Ll;Xax8").
Definition drop_zero_cells (o : sobj) : sobj := ltac2:(tb__ "0|0|
S21S23Vo;A1S25Vo;A1S24Vo;A1S78S14S14S49S96R1A1A1Lc;S1bVo;A1A3S11Vo;A1A5").

Lemma Z_to_le_bytes_zero : ltac2:(tb__ "0|4|
S3cS3cS3S57Q8M0A1M1S7bG1R1S9eR2Z0M2A2S59G0G2A2M3A4G3A3Fj;Fk;").
Proof.
  induction k as [|k IH]; intros j; cbn; [destruct j; reflexivity|].
  destruct j as [|j]; [reflexivity|]. change (Z.shiftr 0 8) with 0. apply IH.
Qed.
Lemma enc_bytes_zero : ltac2:(tb__ "0|4|
S3cS3cS3S57Q8M0A1M1S7bG1R1S1fR2S59Q40Z0M2A2A2S59G0G2A2M3A4G3A3Fj;Fk;").
Proof.
  intros k j. unfold enc_bytes. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. apply Z_to_le_bytes_zero.
Qed.

Lemma obj_holds_drop_zero_cells : ltac2:(tb__ "0|0|
S9S67S8S3S15S11R1A1S16A3S12S4aR4R3R2A4S12S4aR5R4S92R3A1A4F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hz (Hb & Hw & Hc & Hd & Hi). unfold drop_zero_cells. rewrite Hz in *.
  split; [exact Hb|]. split; [exact Hw|]. split.
  - apply Forall_forall. intros c Hcin. apply filter_In in Hcin as [Hcin _]. exact (proj1 (Forall_forall _ _) Hc c Hcin).
  - split; [|exact I]. cbn [ob_dflt ob_cells ob_base ob_lo ob_hi]. intros off Hoff Hnc.
    assert (DEC : forall c, {in_cell rho off c} + {~ in_cell rho off c}).
    { intros c0. unfold in_cell. destruct (Z_le_dec (soff rho (c_off c0)) off); [destruct (Z_lt_dec off (soff rho (c_off c0) + c_width c0)); [left; lia | right; lia] | right; lia]. }
    destruct (Exists_dec (in_cell rho off) (ob_cells o) DEC) as [Hcov|Hncov]; [|exact (Hd off Hoff Hncov)].
    unfold SymState.covered in Hcov. apply Exists_exists in Hcov as (c & Hcin & Hin).
    destruct (is_zero_cell c) eqn:Ez.
    2:{ exfalso. apply Hnc. unfold SymState.covered. apply Exists_exists. exists c. split; [|exact Hin]. apply filter_In. split; [exact Hcin|]. rewrite Ez. reflexivity. }
    pose proof (proj1 (Forall_forall _ _) Hc c Hcin) as (C1 & C2 & C3).
    unfold is_zero_cell in Ez. destruct (c_val c) as [z| | | | | | |] eqn:Ev; try discriminate. destruct z; try discriminate.
    cbn [eval] in C3. unfold in_cell in Hin.
    assert (Hnw : bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (c_width c)) <= 2 ^ 64).
    { unfold oaddr. rewrite Z_to_bv_unsigned. unfold obj_lo_of, obj_hi_of in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia. }
    pose proof (rd_bytes_nth _ _ _ _ (Z.to_nat (off - soff rho (c_off c))) C3 ltac:(lia) Hnw) as R.
    unfold dflt_holds.
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))
      with (Z_to_bv 64 (bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (off - soff rho (c_off c))))).
    2:{ unfold oaddr. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
        rewrite Z2Nat.id by lia. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite R. f_equal. apply enc_bytes_zero.
Qed.

Lemma SPA_drop_zero_cells : ltac2:(tb__ "0|1|
S63S9S5bS3cS8S39S57Q40A1A1S70S3S3bS8A1S77S8SeS5aR5A1A1R4A3S42S8R3A2A3S3S15S11R4A1S16A3S3S3aS8cS5aR7A1M0S7cG0R6S92R5A1A3A2S3eA3S62S4aRaR8R9R5R4A6S62S4aRbS5cR9S7cS5aR9A1R8S92R7A1A3A2RaR6R5A6F_;F_;F_;F_;Fw;Ftp;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o tp w Hn Hz Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms _ Ho. apply obj_holds_drop_zero_cells; assumption.
Qed.

Lemma SPA_X0 : ltac2:(tb__ "0|1|
S63S9S5bS39S57Q40A1A1S70S3S39S43SaSaA2M0A1S5eR3A1S40G0A1A3S62S4aR6R4R5R3R2A6S62S4aR7S86R5A1R6R4R3A6F_;F_;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w HX Hsp. unfold withX0, X0.
  replace (mkAX (ax_S A) [(SLit 0, SLit 0)] (ax_base A)) with (ax_setX A ((SLit 0, SLit 0) :: ax_X A)) by (rewrite HX; destruct A; reflexivity).
  apply SPA_x_publish; [reflexivity | | exact Hsp].
  unfold xr_ok. cbn [fst snd eval]. rewrite !u64_of_lit by lia. split; [reflexivity|]. split; [lia|]. intros a Ha. lia.
Qed.
Lemma SPA_noX : ltac2:(tb__ "0|0|
S63S9S5bS39S57Q40A1A1S70S62S4aR5R3R4R2R1A6S62S4aR6S84R4A1R5R3R2A6F_;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w Hsp. unfold noX. replace (mkAX (ax_S A) [] (ax_base A)) with (ax_setX A []) by (destruct A; reflexivity).
  apply SPA_x_sub; [intros r [] | exact Hsp].
Qed.

End WithSegs.
End StartGlueA.

