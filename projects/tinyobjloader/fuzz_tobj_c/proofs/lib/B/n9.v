(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double na.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mprotect.

(* [comment removed for export] *)
Module Lib_scan_double_xc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "v173"; "CI"; "CN"; "C1"; "Ce"; "Cen"; "Cm"; "Cp"; "Cs"; "Cx"; "FUEL_sd"; "P_none"; "P_num"; "Pre_sd"; "X_t1"; "X_t2"; "X_t3"; "cutpcs_sd"; "v172"; "vI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_xc"; "vTop"; "X_b0"; "X_b1"; "X_in0"; "X_in1"; "nCp"; "varP"; "vchain"; "vcuts_sd"; "vexits_sd"; "vposts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "sprop"; "SPUle"; "SVar"; "SAluW"; "SExt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SLTU"; "ALU_SRA"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA.

Definition Fcp : list sprop := ltac2:(tb__ "0|2|
S2S29S2aS2bPb8A1M0S27S30Z2Z1eA2A1M1A2S2S29S2aS2cS36G0S27Z1A1A3G1A2S3S29A1A3A3").
Definition Cp' : axst := ax_add_facts Fcp Cp.
Definition varP (e : sv) : sv := ltac2:(tb__ "0|1|
S28S37S27S31S30Z2Z40A2Z1M0A2A1S28S33S28S34S2dS6Q20Ve;A3S27G0A1A3S28S35S27Z0A1Ve;A3A3A3").
Definition nCp : vnodeA := mkVNA Cp' 4 (varP (SVar 184)).

Definition vchain : list vnodeA := ltac2:(tb__ "0|2|
S2S0S1S9Z1M0Z9a728A2ZfS8A3S2S0S1S9Z2M1Z9a768A2ZeS8A3S2S0S1S9Z3Z9a7a8A2ZdS8A3S2S0S1S9Z4Z9a7e8A2ZcS8A3S2S0S1S9Z5Z9a828A2ZbS8A3S2S0S1S9Z6Z9a868A2ZaS8A3S2S0S1S9Z7Z9a8a8A2Z9S8A3S2S0S1SaG0Z9a62cA2Z11S8A3S2S0S1SaG1Z9a66cA2Z10S8A3S3S0A1A3A3A3A3A3A3A3A3A3").
Definition vcuts_sd : list vnodeA := ltac2:(tb__ "0|1|
S4S0S2S0S1S15Z14S1bA3S2S0S1SbZ13S1aA3S2S0S1S10Z12S8A3S2S0S1SeZ8S8A3S2S0S1ScZ7M0S8A3S2S0S1SdG0S8A3S2S0S1S11Z6S8A3S2S0S21S3S0A1A3A3A3A3A3A3A3A3S23A3").

Definition X_in0 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_sd cutpcs_sd Cx sd_Lp) Pre_sd.
Definition X_in1 : axst := Eval vm_compute in nth 1 (leavesA_at FUEL_sd cutpcs_sd Cx sd_Lp) Pre_sd.
Definition X_b0 : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_sd cutpcs_sd Cp' sd_Lp) Pre_sd.
Definition X_b1 : axst := Eval vm_compute in nth 1 (leavesA_at FUEL_sd cutpcs_sd Cp' sd_Lp) Pre_sd.
Goal length (leavesA_at FUEL_sd cutpcs_sd Cx sd_Lp) = 2%nat /\ length (leavesA_at FUEL_sd cutpcs_sd Cp' sd_Lp) = 2%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vTop : sv := SLit (2 ^ 64 - 1).
Definition vposts_sd : list vnodeA := ltac2:(tb__ "0|1|
S2S0S1S13Z0M0S1cA3S2S0S1S14G0S1cA3S3S0A1A3A3").
Definition vexits_sd : list vnodeA := ltac2:(tb__ "0|4|
S4S0S26S2S0S1S1fZ5M0S8A3S2S0S1S20G0S8A3S2S0S1S1dZ3M1S22S2bPb8A1A1M2A3S2S0S1S1eG1G2A3S2S0S1S16Z0M3S1cA3S2S0S1S17G3S1cA3S2S0S1S18G3S1cA3S3S0A1A3A3A3A3A3A3A3A3").

Lemma echeck_sd : ltac2:(tb__ "0|0|
S32S5S3aS38S12S19S2fS24S25A6S7A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition s_of (X : axst) : wsub := ltac2:(tb__ "0|0|
S39S2fS2eVX;A1S2eSfA1A3").
Definition s_in0 := s_of X_in0.  Definition s_in1 := s_of X_in1.
Definition s_b0 := s_of X_b0.    Definition s_b1 := s_of X_b1.

Goal entailsA X_in0 Cp s_in0 = true /\ entailsA X_in1 Cp s_in1 = true /\ entailsA X_b0 Cp s_b0 = true /\ entailsA X_b1 Cp s_b1 = true
     /\ wsub_get s_b0 184 = SAluW ALU_SRA (SVar 184) (SLit 1) /\ wsub_get s_b1 184 = SAluW ALU_SRA (SVar 184) (SLit 1)
     /\ wsub_get s_in0 184 = SAlu ALU_SUB (SLit 0) (SVar 183) /\ wsub_get s_in1 184 = SVar 183.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

End Lib_scan_double_xc.

(* [comment removed for export] *)
Module Lib_scan_double_ex.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "eval"; "valuation"; "SLit"; "holds"; "ss_facts"; "sv"; "SAluW"; "SVar"; "SPUle"; "rw"; "SAlu"; "SPBranch"; "SPNot"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "le"; "sub"; "lt"; "modulo"; "add"; "div"; "ltb"; "mul"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_xc"; "Fcp"; "varP"; "X_in0"; "X_in1"; "s_in0"; "s_in1"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRA"; "ALU_ADD"; "ALU_SRL"; "BC_EQ"; "aluop"; "@Corelib.Init.Datatypes"; "bool"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "v173"; "Posts_sd"; "Pre_sd"; "two40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_xc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import UbsanArith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr.

Lemma w_shift_range : ltac2:(tb__ "0|2|
S4S2eS8S8S14S0Q40M0S3R4SdS2bS9R3R2R1A3S5S13Z2M1Z1fA2A1A3A2A2S0G0S3R4S5S15S13G1Z20A2Z1A2A1A2A2A2Fb;Fa;Fop;Frho;").
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

Lemma Fcp_of_bound : ltac2:(tb__ "0|0|
S4S14S0Q40ScR1Pb8A2A2S13Z2Z1eA2A2S10S2S6R2A1S23A3F_;Frho';").
Proof.
  intros rho' H. pose proof (urange (rw rho' 184%positive)) as R. unfold Fcp. constructor; [|constructor; [|constructor]].
  - cbn [holds]. rewrite eval_var, U_lit. unfold M64v. rewrite Z.mod_small by lia. exact H.
  - cbn [holds]. rewrite U_sraw1_small by (rewrite eval_var; lia). rewrite eval_var, U_lit. unfold M64v. rewrite Z.mod_small by lia.
    apply Z.lt_le_incl. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma Fcp_in0 : ltac2:(tb__ "0|0|
S4S10S2S6R1A1S7S11S25A1A1A3S10S2S6S1eR2S27A2A1S23A3F_;Frho;").
Proof.
  intros rho HF. apply Fcp_of_bound. cbn [rw rho_sub].
  replace (wsub_get s_in0 184) with (SAlu ALU_SUB (SLit 0) (SVar 183)) by (vm_compute; reflexivity).
  concrete_facts HF. pick_facts HF [1; 6; 7]%nat. zfacts; lia.
Qed.
Lemma Fcp_in1 : ltac2:(tb__ "0|0|
S4S10S2S6R1A1S7S11S26A1A1A3S10S2S6S1eR2S28A2A1S23A3F_;Frho;").
Proof.
  intros rho HF. apply Fcp_of_bound. cbn [rw rho_sub].
  replace (wsub_get s_in1 184) with (SVar 183) by (vm_compute; reflexivity).
  concrete_facts HF. pick_facts HF [1; 6; 7]%nat. zfacts; lia.
Qed.

Lemma Fcp_b : ltac2:(tb__ "0|2|
S12S1fS4S1cS8S20R2Pb8M0A2S9S2aSaG0A1M1S5Z1A1A3A3S29S2SbG1S5S13Z2Z1eA2A1A2S7S11R4A1A1A3S10S2S6R3A1S7S11R5A1A1A3S10S2S6S1eR4R5A2A1S23A3F_;F_;F_;Frho;Fs;FX;").
Proof.
  intros X s rho Hs Hin HF. apply Fcp_of_bound. cbn [rw rho_sub]. rewrite Hs.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hb. apply ule_lit' in Hb; [|unfold M64v; lia]. rewrite eval_var in Hb.
  pose proof (urange (rw rho 184%positive)) as R.
  rewrite U_sraw1_small by (rewrite eval_var; lia). rewrite eval_var.
  apply Z.lt_le_incl. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma U_srlw1 : ltac2:(tb__ "0|2|
S4S8S1cS21S0Q40M0S3R2S9S2cR1S5Z1A1A3A2A2S19S17S0G0S3R2R1A2A2S13Z2M1Z20A2A2G1A2A3Fa;Frho;").
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
S4S8S1cS21S0Q40M0S3R2S24R1A1A2A2S15S15S13Z2M1Z40A2Z1M2A2S18S1bG1S17S0G0S3R2R1A2A2M3S13G1Z20A2A2A2S2fS21L_;S1aZ0M4G3A2G2G4X2fx2A2A2A3Fe;Frho;").
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

Lemma varP_sraw_lt : ltac2:(tb__ "0|4|
S4S1fS1cS8S20R1Pb8M0A2S9S2aSaG0A1M1S5Z1A1A3A3S14S0Q40M2ScR3G0A2A2S13Z2Z1eA2A2S1dS1cS21S0G2ScR4G0A2A2Z0A3A1S16S0G2S3R5S24G1A1M3A2A2S0G2S3S1eR5R4A2G3A2A2A2F_;F_;F_;Fs;Frho;").
Proof.
  intros rho s Hs Hb Hnz. rewrite !U_varP.
  change (eval (rho_sub rho s) (SVar 184)) with (rw (rho_sub rho s) 184%positive). cbn [rw rho_sub]. rewrite Hs.
  rewrite U_sraw1_small by (rewrite eval_var; lia). rewrite !eval_var.
  pose proof (urange (rw rho 184%positive)) as R. set (u := bv_unsigned (rw rho 184%positive)) in *.
  rewrite (Z.mod_small u) by lia.
  set (h := u / 2) in *.
  assert (Hh : 0 <= h) by (subst h; apply Z.div_pos; lia).
  assert (Hh2 : 2 * h <= u) by (subst h; apply Z.mul_div_le; lia).
  rewrite (Z.mod_small h) by lia.
  replace (if 0 <? u then 1 else 0) with 1 by (destruct (Z.ltb_spec 0 u); lia).
  destruct (Z.ltb_spec 0 h); lia.
Qed.

Lemma X_b_var : ltac2:(tb__ "0|4|
S12S1fS4S1cS8S20R2Pb8M0A2S9S2aSaG0A1M1S5Z1A1A3A3S29S2SfSeS2dG1S5Z0A1A3A1S7S11R4A1A1A3S29S2SbG1S5S13Z2Z1eA2A1A2S7S11R5A1A1A3S10S2S6R4A1S7S11R6A1A1A3S16S0Q40M2S3R5S24G1A1M3A2A2S0G2S3S1eR5R6A2G3A2A2A2F_;F_;F_;F_;Frho;Fs;FX;").
Proof.
  intros X s rho Hs Hin Hinb HF.
  pose proof (proj1 (Forall_forall _ _) HF _ Hinb) as Hb. apply ule_lit' in Hb; [|unfold M64v; lia]. rewrite eval_var in Hb.
  apply (varP_sraw_lt rho s Hs Hb).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hnz. apply holds_nbeq in Hnz.
  rewrite eval_var, U_lit in Hnz. unfold M64v in Hnz. rewrite Z.mod_small in Hnz by lia. exact Hnz.
Qed.

Lemma X_in_var : ltac2:(tb__ "0|1|
S12S1fS4S29S2SbS31S5S34A1A2S7S11R3A1A1A3S10S2S6R2A1S7S11R4A1A1A3S14S0Q40M0S3R3S31A2A2S0G0S3S1eR3R4A2S24SaPb8A1A1A2A2A2F_;F_;Frho;Fs;FX;").
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
S39S4S30S1Q40A1A1S3aS22S35R3A3S36S22S38S22R4S33R3R2A5S37S22R4S35R3R2S32A6A3F_;Ftp;Frho;FJ;").
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
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
    + apply (eexit_post_IA0 segs J NF rho vcuts_sd Posts_sd (mkVNA P_none 0 vTop)). in_nth 0.
    + apply (eexit_post_IA0 segs J NF rho vcuts_sd Posts_sd (mkVNA P_num 0 vTop)). in_nth 1.
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_in0 5 v173) nCp Fcp Cp s_in0 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_in0 r HF)|].
      right. split; [| cbn; lia]. cbn [vna_var]. exact (X_in_var X_in0 s_in0 r ltac:(vm_compute; tauto) HF).
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_in1 5 v173) nCp Fcp Cp s_in1 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_in1 r HF)|].
      right. split; [| cbn; lia]. cbn [vna_var]. exact (X_in_var X_in1 s_in1 r ltac:(vm_compute; tauto) HF).
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_b0 3 (varP (SVar 184))) nCp Fcp Cp s_b0 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_b X_b0 s_b0 r ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto) HF)|].
      left. cbn [vna_var]. exact (X_b_var X_b0 s_b0 r ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto) ltac:(vm_compute; tauto) HF).
    + apply (eexit_reenter_IA segs J' NF vcuts_sd _ (mkVNA X_b1 3 (varP (SVar 184))) nCp Fcp Cp s_b1 tp);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HstJ' | reflexivity
        | | cbn; lia | cbn; lia].
      intros r t tr md _ HF. split; [exact (Fcp_b X_b1 s_b1 r ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto) HF)|].
      left. cbn [vna_var]. exact (X_b_var X_b1 s_b1 r ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto) ltac:(vm_compute; tauto) HF).
    + apply (eexit_contraA segs _ X_t1). intros r tp' tr md _ HF. exact (contra_t1 r HF).
    + apply (eexit_contraA segs _ X_t2). intros r tp' tr md _ HF. exact (contra_t2 r HF).
    + apply (eexit_contraA segs _ X_t3). intros r tp' tr md _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
Qed.
End Lib_scan_double_ex.

(* [comment removed for export] *)
Module StartGlueC.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "cell"; "sobj"; "sv"; "valuation"; "mkObj"; "obj_holds"; "odefault"; "ss_objs"; "DImage"; "ob_dflt"; "rom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "cell_eqb"; "shadow_ok"; "@Stdlib.Lists.List"; "In"; "nth_error"; "existsb"; "forallb"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nat"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "obj_to_unknown"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC"; "cells_incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "xshadow_outside"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma obj_holds_img_to_unknown : ltac2:(tb__ "0|0|
S3S25S1SaSbR2A2ScS6S9R2A1S8A3S5SbR5R4R3A4S5SbR6R5S20R4A1A4F_;F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hrom Hd (Hb & Hw & Hc & Hdf & Hi). unfold obj_to_unknown. rewrite Hd in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [exact Hc|]. split; [|exact I].
  cbn [ob_dflt ob_cells ob_lo ob_base]. intros off Hoff Hnc. cbn.
  destruct (Hdf off Hoff Hnc) as [Hnone [b Hb']]. exists b.
  unfold rd, ms_read_byte. rewrite Hnone. rewrite (Hrom _). exact Hb'.
Qed.

Lemma SPA_img_to_unknown : ltac2:(tb__ "0|1|
S1eS3SeS19S1S16S24Q40A1A1S22ScS1bS1A1S13S1S7SdR5A1A1R4A3S1aS1R3A2A3ScS6S9R4A1S8A3ScS17S23SdR7A1M0S1fG0R6S20R5A1A3A2S18A3S1dSbRaR8R9R5R4A6S1dSbRbSfR9S1fSdR9A1R8S20R7A1A3A2RaR6R5A6F_;F_;F_;F_;Fw;Ftp;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o tp w Hn Hd Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms Hrom Ho. apply obj_holds_img_to_unknown; assumption.
Qed.

Lemma obj_holds_cells_equiv : ltac2:(tb__ "0|2|
S3S25S2S2S2S16S0A1M0G0S6S0S12S0R1R3A3S12S0R2R5A3M1F_;Fc;S0S12S0R1R5A3G1F_;Fc;S5SbRaR9S4R8R7R6R5R3A5A4S5SbRbRaS4R9R8R7R5R4A5A4F_;F_;F_;Fd;Fcs';Fcs;Fhi;Flo;Fb;Fms;Frho;").
Proof.
  intros rho ms b lo hi cs cs' d H1 H2 (Hb & Hw & Hc & Hdf & Hi). cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split.
  - apply Forall_forall. intros c Hc'. exact (proj1 (Forall_forall _ _) Hc c (H1 c Hc')).
  - split; [|exact Hi]. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. intros off Hoff Hnc. apply Hdf; [exact Hoff|].
    intros Hcov. apply Hnc. unfold SymState.covered in *. apply Exists_exists in Hcov as (c & Hcin & Hin).
    apply Exists_exists. exists c. split; [apply H2; exact Hcin | exact Hin].
Qed.

Lemma SPA_cells_equiv : ltac2:(tb__ "0|3|
S1eS3SeS19S2S2S2S16S0A1M0G0S6S16S24Q40A1A1S22ScS1bS1A1S13S1S7SdRaA1A1R9A3S1aS1S4R8R7R6R5R3A5A2A3S0S12S0R1R6A3S12S0R2R8A3M1F_;Fc;S0S12S0R1R8A3G1F_;Fc;ScS17S23SdRdA1M2S1fG2RcS4RbRaR9R7R6A5A3A2S18A3S1dSbR10ReRfR6R5A6S1dSbR11SfRfS1fSdRfA1ReS4RdRcRbR9R8A5A3A2R10R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fd;Fcs';Fcs;Fhi;Flo;Fb;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i b lo hi cs cs' d tp w Hn H1 H2 Hsame Hsp.
  apply (SPA_replace_obj J rho A i (mkObj b lo hi cs d)); try assumption.
  - reflexivity.
  - intros ms _ Ho. apply (obj_holds_cells_equiv rho ms b lo hi cs cs' d H1 H2 Ho).
Qed.

Definition cells_incl (cs cs' : list cell) : bool := ltac2:(tb__ "0|0|
S15S0S0S14S0S10R1A1Vcs';A3Lc;Vcs;A3").
Lemma cell_eqb_eq : ltac2:(tb__ "0|0|
S0S0ScS17S10R2R1A2S18A3ScS0R3R2A3F_;Fc';Fc;").
Proof.
  intros [o k v] [o' k' v'] H. unfold cell_eqb in H. cbn in H. apply andb_prop in H as [H Hv]. apply andb_prop in H as [Ho Hk].
  apply sv_eqb_sound in Ho. apply sv_eqb_sound in Hv. apply Z.eqb_eq in Hk. subst. reflexivity.
Qed.
Lemma cells_incl_sound : ltac2:(tb__ "0|1|
S16S0A1M0G0ScS17S27R2R1A2S18A3S0S12S0R1R4A3S12S0R2R4A3F_;Fc;F_;Fcs';Fcs;").
Proof.
  intros cs cs' H c Hc. unfold cells_incl in H. pose proof (proj1 (forallb_forall _ _) H c Hc) as X.
  apply existsb_exists in X as (c' & Hc' & E). apply cell_eqb_eq in E. subst. exact Hc'.
Qed.

Lemma xshadow_outside_incl : ltac2:(tb__ "0|0|
S3SeS16S1A1S1S12S1R1R2A3S12S1R2S7SdR4A1A1A3F_;Fo;S11R4R3A2S28R5R4R3A3F_;F_;Fobjs';FA;Frho;").
Proof.
  intros rho A objs' Hincl Hsh. unfold xshadow_outside, shadow_ok in *. apply Forall_forall. intros [b l] Hr a j Ha Hj.
  pose proof (proj1 (Forall_forall _ _) Hsh _ Hr) as X. unfold xr_ok in X. cbn [fst snd] in X, Ha |- *.
  destruct X as (_ & _ & X). destruct (X a Ha) as (_ & _ & Hwd & _). destruct (Hwd j Hj) as [Hout _].
  unfold outside_all in *. apply Forall_forall. intros o Ho. exact (proj1 (Forall_forall _ _) Hout o (Hincl o Ho)).
Qed.

Lemma SPA_move_lastX : ltac2:(tb__ "0|1|
S1eS3SeS19S16S24Q40A1A1S22S26R3S1cS1S7SdR4A1A1A2A2ScS17S23SdR5A1M0S21G0R4A2A2S18A3S1dSbR8R6R7R4R3A6S1dSbR9SfR7S21SdR7A1R6A2A2R8R5R4A6F_;F_;F_;Fw;Ftp;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i tp w Hi Hsame Hsp.
  destruct (firstn_skipn_split (ss_objs (ax_S A)) i Hi) as (x & H1 & H2).
  apply (SPA_reobj segsA J rho A (move_obj_last (ax_S A) i) tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segsA _ _ _ _ _ S0) as MM.
    unfold move_obj_last. cbn [ss_objs set_objs]. rewrite H1. rewrite H2 in MM.
    apply mem_match_move_last. exact MM.
  - destruct Hsp as [(_ & _ & _ & Hsh & _) _]. apply xshadow_outside_incl; [|exact Hsh].
    intros o Ho. unfold move_obj_last in Ho. cbn [ss_objs set_objs] in Ho.
    rewrite !in_app_iff in Ho. destruct Ho as [Ho|[Ho|Ho]]; [eapply In_firstn_In; exact Ho | eapply In_skipn_In; exact Ho | eapply In_skipn_In; eapply In_firstn_In; exact Ho].
Qed.

Lemma SPA_exJ : forall {T : Type} (P : T -> Prop) (K : T -> jpredA) A rho tp w,
  SPA segsA (fun r t tr md => exists x, P x /\ K x r t tr md) A rho tp w <-> exists x, P x /\ SPA segsA (K x) A rho tp w.
Proof.
  intros T P K A rho tp w. split.
  - intros [Hsm (x & Hx & HK)]. exists x. split; [exact Hx|]. split; assumption.
  - intros (x & Hx & [Hsm HK]). split; [exact Hsm|]. exists x. split; assumption.
Qed.
End StartGlueC.

(* [comment removed for export] *)
Module StartWit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "gw_sizes"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "list"; "length"; "app"; "cons"; "nat"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "modulo"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_maps"; "vm_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "init_sp_ok"; "mmap_place_ok_none"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA GlueA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma gw_sizes_app : ltac2:(tb__ "0|3|
S6S5S12Q40A1M0G0A2M1A1M2G2S0S4S3S8G1R2R1A3A1SdS3R2A1S3R1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. induction l1 as [|[b s] l1 IH]; cbn [gw_sizes List.app]; [lia|]. cbn [snd]. rewrite IH. lia. Qed.

Lemma gw_sizes_cons : ltac2:(tb__ "0|3|
S12Q40M0A1M1G1S6S5G1G1A2M2A1S0S4S3S9G2SbG1G1R3R2A4R1A3A1SdS14G0R2A2S3R1A1A2A3Fl;Fs;Fb;").
Proof. intros. reflexivity. Qed.

Lemma gw_sizes_segsA : ltac2:(tb__ "0|2|
S1S0S4S3S19S1aA1M0A1Z633000A3S0SaS7S5S12Q40A1M1G1A2G0A2U4A3A2").
Proof. rewrite segments_reserved_A. cbn [gw_sizes length snd]. rewrite !u64_of_lit by lia. split; reflexivity. Qed.

Theorem place_witness : ltac2:(tb__ "0|6|
S16S6S5S12Q40M0A1M1G1A2M2A1M3S4S4S0G3S18S15R4A1A1S19S1aA1A3S0G3S17S15R5A1A1R4A3S1bS15R6A1A1SfZ0M4R5A2S0S4S10R6Z1000A2G4A3ScR7SeZ2M5Z26A2A2ScS3R9A1R7A2ScR8SeG5Z2dA2A2ScS11S7G2RbA2A1Z40A2S2G1G1S1cS13G0G4A2ReS13G0RcA2R1A4La;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftot;Flen;FL;Fmd;").
Proof.
  intros md L len tot HR HM HT Hpos Hal Hlen Htot Htot2 Hcnt.
  pose proof gw_sizes_segsA as [GS GL].
  destruct (free_gap_below_top (m_vmmaps md) len 0x10007fff8000 (0x633000 + tot) HT ltac:(lia) ltac:(reflexivity) ltac:(lia)) as (g & Gal & Gfl & Gc & Gtop & Gfree).
  { rewrite HR, HM, gw_sizes_app, GS. lia. }
  { rewrite HR, HM, length_app, GL, Nat2Z.inj_add. change (Z.of_nat 4) with 4. unfold alloc_ceiling_lo. nia. }
  exists (Z_to_bv 64 g). unfold alloc_ceiling_lo in Gc. unfold page_size in Gal.
  destruct (mmap_nZ_of_pages len Hpos Hal ltac:(lia)) as [NZ Nn].
  unfold mmap_place_ok_none. rewrite NZ, Nn, u64_of_lit by lia. unfold page_size.
  split; [exact Gal|]. split; [lia|]. split; [exact Gtop|]. exact Gfree.
Qed.
End StartWit.

(* [comment removed for export] *)
Module Lib_vec_reserveN.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "None"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "sobj"; "SAlu"; "SMd"; "DUnknown"; "mkObj"; "SPAlign"; "FcsrFrm0"; "SVar"; "mkSS"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "tv_factsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN"; "kbytes"; "nd0"; "vK"; "vDt"; "c8"; "vW"; "vDn"; "vKn"; "vE"; "vN"; "vAl"; "vV"; "z0"; "vDp"; "X_vr"; "bdP"; "ndG"; "vC"; "vr_facts"; "B32"; "canon_objs"; "kn15"; "ndN"; "pC"; "spm"; "tv0"; "O_Fv"; "O_W"; "O_alv"; "O_data"; "O_vec"; "Pre_vr"; "T_c8okA"; "T_cW0okA"; "X15"; "pR"; "two47"; "B_EW"; "C_c15"; "C_cW1"; "C_r8"; "C_rW0"; "E_c8"; "E_cW0"; "E_r15"; "E_rW1"; "FUEL_vr"; "KLG"; "N15"; "N8"; "NW0"; "NW1"; "PHI"; "P_fail"; "P_fail_S"; "P_grown"; "P_grown_S"; "P_keep"; "P_keep_S"; "Pre_c"; "Pre_vr_S"; "T_c8n"; "T_c8ok"; "T_c8ok0"; "T_cW0n"; "T_cW0ok"; "T_cW0ok0"; "T_r15f"; "T_r15ok"; "T_r15ok0"; "T_rW1f"; "T_rW1ok"; "T_rW1ok0"; "X8"; "XW0"; "XW1"; "cutpcs_vr"; "grown_facts"; "inj"; "tvP"; "two48"; "vUD"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "drop_obj_at"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "batom"; "bitem"; "ASv"; "BI"; "ALog"; "KU"; "ZK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.VRNAddr"; "vr_ret"; "calloc_pc"; "vr_entry"; "vr_nc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.RA"; "ndR"; "P_fail"; "P_ok"; "Pre_ra"; "tv0"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "AE_A"; "Pre_calloc"; "UStopLe"; "ulink"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.RA.ReallocAddr"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "opp"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRNAddr.
  Definition vr_entry : Z := 0x949d4.
  Definition vr_nc : Z := 0x94a4c.
  Definition vr_ret : Z := 0x94aa4.
  Definition vr_realloc_ret : Z := 0x94adc.
  Definition vr_calloc_ret : Z := 0x94bbc.
  Definition calloc_pc : Z := 0x5e1f8.
End VRNAddr.
Import VRNAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.

Definition FUEL_vr : nat := 400%nat.
Definition two48 : Z := 2 ^ 48.
Definition B_EW : Z := 2863311530.
Definition B32 : Z := 4294967295.

Definition vV : sv := SVar 12. Definition vW : sv := SVar 13. Definition vAl : sv := SVar 14.
Definition vDt : sv := SVar 15. Definition vC : sv := SVar 16. Definition vK : sv := SVar 17. Definition vE : sv := SVar 18.
Definition vDp : sv := SVar 19.
Definition vN : sv := SVar 59.
Definition kbytes (k : sv) : sv := SMd M_MUL vE k.

Definition O_Fv (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11S14PaA1SaN40A1SaZ0A1Vcells;S10A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S11S39Z40A1S2eSaZ0A1S2ScA1S10A5").
Definition O_vec (d c k e : sv) : sobj := ltac2:(tb__ "0|1|
S11S2cSaZ0M0A1SaZ20A1S0ScS25G0Vd;A2S0ScS25Z8Vc;A2S0ScS25Z10Vk;A2S0ScS25Z18Ve;A2S2ScA1A3A3A3A3S10A5").
Definition O_alv : sobj := ltac2:(tb__ "0|2|
S11S2bSaZ0M0A1M1SaZ30A1S0ScS25G0SaSa0A1A2S0ScS25Z8SaSa1A1A2S0ScS25Z10G1A2S0ScS25Z18SaSa2A1A2S0ScS25Z20G1A2S0ScS25Z28S72A2S2ScA1A3A3A3A3A3A3S10A5").
Definition O_data (d bytes : sv) : sobj := ltac2:(tb__ "0|0|
S11Vd;SaZ0A1Vbytes;S2ScA1S10A5").

Definition vr_facts : list sprop := ltac2:(tb__ "0|e|
S0S9S12PaM0Z4M1A2S0S9SbS14G0A1M2SaS45A1M3A2S0S9SbS14P1eA1M4SeS73S39Z40A1M5S2eA3A2S0S9SbG4S39Za0A1A2S0S9SbG4G5A2S0S9SbG4G2A2S0S9S16S75SaN1060A1S2eA3S0S9S16S75S2eSaSa8Sa9Z2Z27A2A1A1A3S0S9S12PcZ3M6A2S0S9SbSaZ1000A1M7S2cA2S0S9SbSeS73S2cSaZ20A1A3G4A2S0S9SbS2cG3A2S0S9S12PeG6A2S0S9SbG7S2bA2S0S9SbSeS73S2bSaZ30A1A3G4A2S0S9SbS2bG3A2S0S9S12PfG1A2S0S9SbS24G4A2S0S9SbSeS73S24S21S23A1M8A3G4A2S0S9SbS24G3A2S0S9SbSaZ1A1S29A2S0S9SbS29G7A2S0S9SbS26SaS71A1A2S0S9SbS32S23A2S0S9SbS23SaS34A1M9A2S0S9SbS21S26A1MaSaS46A1MbA2S0S9SbG8G9A2S0S9SbS26S2aA2S0S9SbGaS21S2aA1McA2S0S9SbGcGbA2S0S9SbSaZ7fff7f800000A1MdG4A2S0S9SbG4SaZ7fffff800000A1A2S0S9SbGdG2A2S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_vr (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S2cSaZ20A1A4S0G0S1S8S8S2bSaZ30A1A4S0G0S1S8S8Vd;S21Vk;A1A4S2G0A1A3A3A3").
Definition Pre_vr_S : sstate := ltac2:(tb__ "0|0|
S15S8fS8cS89S13S5S8A1S6SdS0SdS3bS2ScA1A1S0SdS3cS0SdS3fS24S32S23S29A4S0SdS3dS0SdS3eS24S21S23A1A2S2SdA1A3A3A3A3A3S86A3S33S88S7A9").
Definition Pre_vr : axst := ltac2:(tb__ "0|0|
S85S5dS2fS24S23A2A2").

Definition cutpcs_vr : list Z := ltac2:(tb__ "0|0|
S0S1fS90S0S1fS9fS0S1fS8eS2S1fA1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_vr end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S9eS18Vk;S87S4fS6dVS;Vpc;A4S40A4").

Definition X15 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 0.
Definition XW1 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 1.
Definition XW0 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 2.
Definition X8 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 3.

Definition kn15 : sv := ltac2:(tb__ "0|0|
SeS73SeS76S23SaZ1A1A3S23A3").
Definition inj (kn : sv) : list sprop := ltac2:(tb__ "0|3|
S0S9SbSfS74SaZ4A1M0S21S23A1A3SfS74SaZ3A1S21Vkn;A1M1A3A2S0S9SbSfS74G0G1A3SeS73SfS74SaZ6A1S21S26A1A3SfS74SaZ20A1S29A3A3A2S0S9SbG1SaS34A1M2A2S0S9SbSaZ1A1G1A2S0S9SbVkn;G2A2S2S9A1A3A3A3A3A3").
Definition N15 : axst := ltac2:(tb__ "0|0|
Sa3S6fS36A1S43A2").
Definition NW1 : axst := ax_add_facts (inj vW) XW1.
Definition NW0 : axst := ax_add_facts (inj vW) XW0.
Definition N8 : axst := ax_add_facts (inj (SLit 8)) X8.

Definition E_r15 : axst := Eval vm_compute in leafA_at N15 ra_entry 0.
Definition E_rW1 : axst := Eval vm_compute in leafA_at NW1 ra_entry 0.
Definition C_c15 : axst := Eval vm_compute in leafA_at N15 calloc_pc 0.
Definition C_cW1 : axst := Eval vm_compute in leafA_at NW1 calloc_pc 0.
Definition E_cW0 : axst := Eval vm_compute in leafA_at NW0 calloc_pc 0.
Definition E_c8 : axst := Eval vm_compute in leafA_at N8 calloc_pc 0.
Definition C_rW0 : axst := Eval vm_compute in leafA_at NW0 ra_entry 0.
Definition C_r8 : axst := Eval vm_compute in leafA_at N8 ra_entry 0.

Definition tvf0 : list sprop := ltac2:(tb__ "0|0|
S1eS1S8S8S24S21S23A1A4A1").

Definition xf_rcall : list axform := ltac2:(tb__ "0|2|
S0S78S7dU1M0SaN60M1A1A2S0S78S79G0G1A2S2S78A1A3A3").
Definition E_r15x : axst := Eval vm_compute in optA (apply_axforms E_r15 xf_rcall).
Definition E_rW1x : axst := Eval vm_compute in optA (apply_axforms E_rW1 xf_rcall).
Definition E_r15f : axst := ax_add_facts tvf0 E_r15x.
Definition E_rW1f : axst := ax_add_facts tvf0 E_rW1x.
Definition s_r (E : axst) : wsub := ltac2:(tb__ "0|0|
S0S3S20S8A2S1S20S8P13SeS73S2eSaZ60A1A3A4S97PaS19VE;A1S19S94A1A3A3").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_r15 : list sobj := Eval vm_compute in optR (entails_frA E_r15f RA.Pre_ra (s_r E_r15f)).
Definition R_rW1 : list sobj := Eval vm_compute in optR (entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f)).
Goal entails_frA E_r15f RA.Pre_ra (s_r E_r15f) = Some R_r15 /\ call_checkPA E_r15f RA.Pre_ra (s_r E_r15f) R_r15 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f) = Some R_rW1 /\ call_checkPA E_rW1f RA.Pre_ra (s_r E_rW1f) R_rW1 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_cW0' : axst := E_cW0.
Definition E_c8' : axst := E_c8.
Definition Pre_c : axst := ltac2:(tb__ "0|0|
S9aS99S2S9cA1S9bA3").
Definition s_c (E : axst) : wsub := ltac2:(tb__ "0|0|
S97PaS19VE;A1S19S5cA1A3").
Definition R_cW0 : list sobj := Eval vm_compute in optR (entails_frA E_cW0' Pre_c (s_c E_cW0')).
Definition R_c8 : list sobj := Eval vm_compute in optR (entails_frA E_c8' Pre_c (s_c E_c8')).
Goal entails_frA E_cW0' Pre_c (s_c E_cW0') = Some R_cW0 /\ call_checkPA E_cW0' Pre_c (s_c E_cW0') R_cW0 [L_calloc_null AE_A [] UStopLe; L_calloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_c8' Pre_c (s_c E_c8') = Some R_c8 /\ call_checkPA E_c8' Pre_c (s_c E_c8') R_c8 [L_calloc_null AE_A [] UStopLe; L_calloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition PD_ra : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S3S18S1cA2M0S1S18S1cS92S91S95S2S7fA1M1A2A4S0G0S1S18S1cS93S91S96G1A2A4S2G0A1A3A3").
Definition Xk_r : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S2cSaZ20A1A4S0G0S1S8S8S2bSaZ30A1A4S2G0A1A3A3").
Definition T_r15f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_fail Xk_r.
Definition T_r15ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_ok Xk_r.
Definition T_rW1f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_fail Xk_r.
Definition T_rW1ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_ok Xk_r.
Definition T_cW0n0 : axst := Eval vm_compute in T_afterA Pre_c E_cW0' (s_c E_cW0') R_cW0 (L_calloc_null AE_A [] UStopLe).
Definition T_cW0ok0 : axst := Eval vm_compute in T_afterA Pre_c E_cW0' (s_c E_cW0') R_cW0 (L_calloc_ok AE_A [] UStopLe).
Definition T_c8n0 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_null AE_A [] UStopLe).
Definition T_c8ok0 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_ok AE_A [] UStopLe).

Definition T_cW0n : axst := T_cW0n0.
Definition T_c8n : axst := T_c8n0.
Definition pC (T : axst) : sv := reg_sv (ax_S T) 10.
Definition reshape_blk (T : axst) (kn : sv) : axst := ltac2:(tb__ "0|3|
Sa4S1aVT;Sa5S19VT;A1U1S11S38VT;A1M0SaZ0A1S21Vkn;A1M1S2ScA1S10A5A3A2S6S3S8S8A2M2S9dG2U3S1bVT;A1A3S0G2S1S8S8G0G1A4S2G2A1A3A3A2").
Definition T_cW0okA : axst := reshape_blk T_cW0ok0 vW.
Definition T_c8okA : axst := reshape_blk T_c8ok0 (SLit 8).
Definition T_cW0ok2 : axst := ltac2:(tb__ "0|0|
S1aS42S7aS19S42A1U7A2A2").
Definition T_c8ok2 : axst := ltac2:(tb__ "0|0|
S1aS41S7aS19S41A1U7A2A2").
Definition T_cW0ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_cW0ok0, kbytes vW)) T_cW0ok2.
Definition T_c8ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_c8ok0, kbytes (SLit 8))) T_c8ok2.

Definition xf_rback : list axform := ltac2:(tb__ "0|2|
S0S78S79U1M0Z60A2S0S78S7cS0S4G0S0S4U0M1S0S4U2S0S4U3S0S4U4S0S4U5S0S4U6S0S4U7S2S4A1A3A3A3A3A3A3A3A3A1S0S78S7bG1A1S2S78A1A3A3A3").
Definition T_r15f : axst := Eval vm_compute in optA (apply_axforms T_r15f0 xf_rback).
Definition T_rW1f : axst := Eval vm_compute in optA (apply_axforms T_rW1f0 xf_rback).
Definition T_r15okB : axst := Eval vm_compute in optA (apply_axforms T_r15ok0 xf_rback).
Definition T_rW1okB : axst := Eval vm_compute in optA (apply_axforms T_rW1ok0 xf_rback).
Definition pR (T : axst) : sv := reg_sv (ax_S T) 10.
Definition T_r15ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_r15ok0, kbytes kn15)) T_r15okB.
Definition T_rW1ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_rW1ok0, kbytes vW)) T_rW1okB.

Definition canon_objs (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S6SdS0SdS3bS2ScA1A1S0SdS3cS0SdS3fVd;S32Vk;S29A4S0SdS3dS0SdS3eVd;S21Vk;A1A2S2SdA1A3A3A3A3A3S86A3").
Definition P_keep_S : sstate := ltac2:(tb__ "0|1|
S15S8dS8bS8aS88A1S0S3S4S8A2M0S1S4S8UaSaZ1A1A4S2G0A1A3A2S89S13S5S8A1S35S24S23A2S0S9SbS26S23A2S33A3S98S7A9").
Definition P_keep : axst := ltac2:(tb__ "0|0|
S85S5bS2fS24S23A2A2").
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S15S8dS8bS8aS88A1S0S3S4S8A2M0S1S4S8UaSaZ0A1A4S2G0A1A3A2S89S13S5S8A1S35S24S23A2S33S98S7A9").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S85S57S2fS24S23A2A2").
Definition vDn : sv := SVar 140. Definition vKn : sv := SVar 141.
Definition grown_facts : list sprop := ltac2:(tb__ "0|7|
S0S9SbS26S28A2S0S9S12P8cZ4M0A2S0S9S17S16S77S27SaZ0A1A3A1S0S9SbSaZ1000A1S27A2S0S9SbS27S14P1eA1M1A2S0S9SbSeS73S27S21S28A1M2A3G1A2S0S9SbS27SaS45A1A2S0S9SbSaSa6A1S27A2S0S9SbSfS74SaG0A1G2A3M3SeS73SfS74SaZ6A1M4S21S26A1A3SfS74SaZ20A1S29A3M5A3A2S0S9SbG3SeS73SfS74G4S21S2aA1A3G5A3A2S0S9SbG2SaS34A1M6A2S0S9SbSaZ1A1G2A2S0S9SbS32S28A2S0S9SbS28G6A2S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition P_grown_S : sstate := ltac2:(tb__ "0|1|
S15S8dS8bS8aS88A1S0S3S4S8A2M0S1S4S8UaSaZ1A1A4S2G0A1A3A2S89S13S5S8A1S35S27S28A2S6S9S6eS33A3P8eS7A9").
Definition P_grown : axst := ltac2:(tb__ "0|0|
S85S59S2fS27S28A2A2").

Definition PHI (w k : sv) : bitem := ltac2:(tb__ "0|2|
S81Z1Z0M0S0S3S1fS7eA2M1S1S1fS7eZ6S80S21Vw;A1A1A4S0G1S1S1fS7eN4S80S21Vk;A1A1A4S0G1S1S1fS7eZ20S80S29A1A4S2G1A1A3A3A3G0A4").
Definition KLG (k : sv) : bitem := ltac2:(tb__ "0|1|
S81Z0Sa7Z2S83A2S0S3S1fS7eA2M0S1S1fS7eN1S82Vk;A1A4S2G0A1A3S84A4").
Definition bdP (w k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S7fS55Vw;Vk;A2S0S7fS50Vk;A1S2S7fA1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S24S21S23A1A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S27S21S28A1A4S2G0A1A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS3aS2S3S3S8S1fA2S8A2A1S30S2aS23A2A3").
Definition ndN (kn : sv) : ndesc := ltac2:(tb__ "0|0|
S1dS3aS2S3S3S8S1fA2S8A2A1S30S2aVkn;A2A3").
Definition ndG (p kn : sv) : ndesc := ltac2:(tb__ "0|1|
S1dS0S3S8S8A2M0S1S8S8Vp;S21Vkn;A1A4S2G0A1A3S2S3S3S8S1fA2S8A2A1S30S2aVkn;A2A3").

Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S18S1cA2M0S3S1fS8A2M1A2M2S1G0G1S1S18S1cS40S22A4S1S1fS8Z64S2dA4A4S0G2S1G0G1S1S18S1cS51S22A4S1S1fS8Z50S2dA4M3A4S0G2S1G0G1S1S18S1cS54S22A4G3A4S0G2S1G0G1S1S18S1cS53S22A4G3A4S0G2S1G0G1S1S18S1cS52S22A4G3A4S0G2S1G0G1S1S18S1cS64S37S36A1A4S1S1fS8Z3cS2dA4M4A4S0G2S1G0G1S1S18S1cS65S31S44S66A1S36A2A4G4A4S0G2S1G0G1S1S18S1cS67S37S26A1M5A4G4A4S0G2S1G0G1S1S18S1cS68S31S44S69A1S26A2A4G4A4S0G2S1G0G1S1S18S1cS61G5A4G4A4S0G2S1G0G1S1S18S1cS62S31S38S63A1S26A2A4G4A4S0G2S1G0G1S1S18S1cS5eS37SaZ8A1M6A1A4G4A4S0G2S1G0G1S1S18S1cS5fS31S38S60A1G6A2A4G4A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S18S1cA2M0S3S1fS8A2M1A2M2S1G0G1S1S18S1cS43S22A4S1S1fS8Z5aS2dA4M3A4S0G2S1G0G1S1S18S1cS6cS22A4G3A4S0G2S1G0G1S1S18S1cS6bS22A4G3A4S0G2S1G0G1S1S18S1cS6aS22A4G3A4S0G2S1G0G1S1S18S1cS4dS22A4S1S1fS8Z46S2dA4M4A4S0G2S1G0G1S1S18S1cS4eS22A4G4A4S0G2S1G0G1S1S18S1cS47S22A4G4A4S0G2S1G0G1S1S18S1cS48S22A4G4A4S0G2S1G0G1S1S18S1cS4cS22A4G4A4S0G2S1G0G1S1S18S1cS4bS22A4G4A4S0G2S1G0G1S1S18S1cS4aS22A4G4A4S0G2S1G0G1S1S18S1cS49S22A4G4A4S0G2S1G0G1S1S18S1cS5aS22A4S1S1fS8Z0S2dA4M5A4S0G2S1G0G1S1S18S1cS56S1dS3aS2S3S3S8S1fA2S8A2A1M6S2S7fA1A3A4G5A4S0G2S1G0G1S1S18S1cS58S1dS70G6S30S2aS28A2A3A4G5A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_vec_reserveN.

(* [comment removed for export] *)
Module MuslMalloc40.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sv"; "ss_lenient"; "rw"; "sprop"; "sobj"; "SLit"; "agree_below"; "SAlu"; "SVar"; "rm"; "ss_facts"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "false"; "nil"; "cons"; "pair"; "option"; "app"; "Some"; "nat"; "snd"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "mkLeafA"; "sym_runA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.MuslMalloc40"; "VK"; "okT"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "event"; "vm_reserved"; "Model"; "vm_limit"; "vm_init_sp"; "region_free"; "alloc_top"; "m_vm_lazy"; "vm_brk"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.MuslMalloc40States"; "N18"; "E22f"; "E22g"; "N22g"; "N22f"; "refuse"; "vBRK"; "vRES"; "E18"; "S18"; "S19f"; "S22f"; "S22g"; "U24c"; "cont"; "E18t"; "E19"; "E20f"; "E20g"; "E21f"; "RET0a"; "RET0b"; "RET0f"; "RET0g"; "RETPf"; "RETPg"; "S19g"; "S20f"; "S20g_ko"; "S20g_ok"; "S21f"; "U24"; "vGRPf"; "vGRPg"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes"; "brk0w"; "n8w"; "mf_exp"; "Fgrant"; "n3w"; "objs_clear_M"; "TOP"; "mf_res"; "mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post"; "Posts_M"; "post_sub"; "NA"; "out1_model"; "out1"; "KxM"; "NG"; "out1_ok"; "out1_tp"; "m40_B"; "m40_al"; "m40_band"; "m40_hi"; "m40_lim"; "m40_lo"; "m40_lz"; "m40_res"; "m40_sb"; "m40_top"; "rm_kept_outside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "etriple"; "assn"; "world"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.MuslMalloc40.Assembly"; "SP0"; "grow_out"; "Z8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface"; "Pre_M"; "facts_M"; "D_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "init_sp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "mmap_obj"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "tp_in_maps"; "lazy_in_maps"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import
  Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA MmapA MmapFixedA MmapBrkA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Code KxA Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Steps.
Variable ok : assn.

Lemma run1 : ltac2:(tb__ "0|1|
S2cS1fS14S13A1S26S26Sa0S5S14S21Q40A1A1S8dS0S1cS14S27A1M0A1S29S4R8R7R6S16A5S1eG0S1aS27S28R5R4A2S19S27A1A3A2A3S2dS4Vok;RaA3S12S2eS4R1RcA3Fn;S0S15S8S25R9A1A1S18A3S5SdS6S25RbA1A1R8R1A3S8bS4Vok;S2bS4RfRbR2R8A5R7A4F_;Frho';S8bS4Vok;S2bS4ReRbR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fr;FL;FS;Fcuts;Ffuel;FJ;").
Proof.
  intros J fuel cuts S L r rho tp Q Hrun Hok Hst Hlen H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_soundA; [exact Hrun | exact Hok | exact Hlen | apply Hst]|].
  apply triple_LQA_of_leaves. intros L' rho' [<-|[]] Hag. cbn [la_state]. apply H. exact Hag.
Qed.

Lemma erun1 : ltac2:(tb__ "0|1|
S2cS1fS14S13A1S26S26Sa0S5S14S21Q40A1A1S8eOF_;S0S1cS14S27A1M0A1S29S4R8R7R6S16A5S1eG0S1aS27S28R5R4A2S19S27A1A3A2A3S12S2eS4R1RbA3Fn;S0S15S8S25R8A1A1S18A3S5SdS6S25RaA1A1R7R1A3S8cS4S2bS4ReRaR2R7A5R6A3F_;Frho';S8cS4S2bS4RdRaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;Fr;FL;FS;Fcuts;Ffuel;FJ;").
Proof.
  intros J fuel cuts S L r rho tp Q Hrun Hst Hlen H.
  eapply etriple_seq; [eapply sym_run_etripleA; [exact Hlen | apply Hst | exact Hrun]|].
  apply etriple_LQA_of_leaves. intros L' rho' [<-|[]] Hag. cbn [la_state]. apply H. exact Hag.
Qed.

Lemma post_fin : ltac2:(tb__ "0|2|
S2cS26S6dS14S17S26S6dA2M0A1S5S14S21Q40A1A1M1S5G1S8fG0S1bS26S6dR7R6A4R5A3S14S39A1S3bRbR5R4R2R1A4RaR8R7R6R5R3R2A6F_;Fmd;Ftr;S97S24R6R4A3S8bS4Vok;S2bS4RbRaR5R4A5S6cS4S24R7R6R8A5A4F_;F_;F_;Ftp;Frho;Ftp0;Frho0;FPosts;FJL;FP;FJ;").
Proof.
  intros J P JL Posts rho0 tp0 rho tp Hin HJ Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. eapply LQPA_intro; [exact Hin | exact Hw | exact Hag |]. intros HJw. apply HJ. exact HJw.
Qed.

Lemma epost_fin : ltac2:(tb__ "0|2|
S2cS26S6dS14S17S26S6dA2M0A1S5S14S21Q40A1A1M1S5G1S8fG0S1bS26S6dR7R6A4R5A3S14S39A1S3bRbR5R4R2R1A4RaR8R7R6R5R3R2A6F_;Fmd;Ftr;S97S24R6R4A3S8cS4S2bS4RbRaR5R4A5S6cS4S24R7R6R8A5A3F_;F_;F_;Ftp;Frho;Ftp0;Frho0;FPosts;FJL;FP;FJ;").
Proof.
  intros J P JL Posts rho0 tp0 rho tp Hin HJ Hag w Hw. exists w. split; [apply wsteps_refl|].
  eapply LQPA_intro; [exact Hin | exact Hw | exact Hag |]. intros HJw. apply HJ. exact HJw.
Qed.
End Steps.

Definition VK (rho0 : valuation) (lo hi : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1S97S24Vrho0;Vrho;A3S8aVlo;Vhi;Vrho0;Vrho;A4A2").

Lemma VK_refl : ltac2:(tb__ "0|1|
S5S35R1Z0M0G0R1A4Frho;").
Proof. intros rho. split; [apply agree_vals_refl | intros x _; reflexivity]. Qed.

Lemma VK_agree : ltac2:(tb__ "0|0|
S5S13S13S5S5S12S66S24R1A2S35R7R6R5R4A4SdR3R5R4A3S35R9R8R7R5A4F_;F_;F_;Fn;Frho';Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho rho' n Hn [Hav Hrm] (A1 & A2 & A3). split.
  - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; apply A1; lia | exact A2].
  - intros x Hx. rewrite <- A3. apply Hrm. exact Hx.
Qed.

Lemma VK_set_rw : ltac2:(tb__ "0|0|
S5S13S13S5S12S21Q40A1S66S24R2A2S35R7R6R5R4A4S35R8R7R6S9fR5R4R3A3A4F_;F_;Fa;Fv;Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho v a Hv [Hav Hrm]. split.
  - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; rewrite rho_set_rw_other by lia; reflexivity | intros l; reflexivity].
  - intros x Hx. rewrite rho_set_rw_rm. apply Hrm. exact Hx.
Qed.

Lemma VK_sub : ltac2:(tb__ "0|0|
S5S13S13S5S69S0S15S68R1S24A2S16A3S35R6R5R4R3A4S35R7R6R5S6aR4R3A2A4F_;F_;Fs;Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho s Hs [Hav Hrm]. pose proof (rho_sub_agree s NF rho Hs) as (A1 & A2 & A3). split.
  - eapply agree_vals_trans; [exact Hav|]. split; [exact A1 | exact A2].
  - intros x Hx. cbn. apply Hrm. exact Hx.
Qed.

Lemma VK_widen : ltac2:(tb__ "0|0|
S5S13S13S13S13S5S13S1S30R6R1A2S31R1R5A2A2S1S30R5R2A2S31R2R4A2A2F_;Fz;S35R7R6R5R2A4S35R8R5R4R3A4F_;F_;Frho;Fhi';Flo';Fhi;Flo;Frho0;").
Proof. intros rho0 lo hi lo' hi' rho H [Hav Hrm]. split; [exact Hav|]. intros x Hx. apply Hrm. intros Hc. apply Hx. apply H. exact Hc. Qed.

Lemma VK_set_rm : ltac2:(tb__ "0|4|
S5S13S13S5S21Q40M0A1M1S1cS21Q8A1A1M2Fx;S35R5R4R3R2A4G1S3S1S30R6S22G0R1A2M3A2S31G3R5A2A2A1S0G2R4R2A1S10R5R2A2A3F_;Fx;S35R7R6R5Sa6R4R3A2A4F_;F_;Ff;Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho f [Hav Hrm] Hf. split.
  - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; reflexivity | intros l; reflexivity].
  - intros x Hx. unfold set_rm. cbn. rewrite (Hf x Hx). apply Hrm. exact Hx.
Qed.

Lemma unmap_range_outside : ltac2:(tb__ "0|5|
S21Q40M0A1M1S1cS21Q8A1A1M2F_;G1G1G1S3S1S30S22G0R3A2M3S22G0R1A2M4A2S31G4S2fG3S22G0R2A2A2A2A2A1S0G2Sa5R5R4R3R2A4R5R2A1A3F_;Fx;Fn;Fa;Fmem;").
Proof.
  intros mem a n x Hx. rewrite unmap_range_at. destruct (in_range a n x) eqn:E; [|reflexivity].
  exfalso. apply Hx. apply in_range_spec. exact E.
Qed.

Lemma rw_sub_other : ltac2:(tb__ "0|0|
S5S69S12S0S15S68R2S65R1A1A2S16A3S0S21Q40A1S9S6aR4R3A2R2A2S9R4R2A2A3F_;Fv;Fs;Frho;").
Proof.
  intros rho s v Hs. pose proof (rho_sub_agree s (Pos.succ v) rho Hs) as (A1 & _ & _). symmetry. apply A1. lia.
Qed.

Lemma VK_sp : ltac2:(tb__ "0|2|
S5S13S13S5S13S35R5R4R3R2A4S30R2S22Q40M0S9R6PaM1A2A2A2S30R3S22G0S9R4G1A2A2A2F_;F_;FT;Frho;Fhi;Flo;Frho0;").
Proof. intros rho0 lo hi rho T [[Hav _] _] H. rewrite <- (Hav 10%positive) by (unfold NF; lia). exact H. Qed.

Ltac plia := unfold NF, N18, N22f, N22g, NA, NG, NP in *; lia.

Definition okT : assn := fun _ => True.
Lemma OKF_triv : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;S2dS4S36R2A3F_;FJ;").
Proof. intros J _ rho tp tr ms md msv' _ _ _ _ _. exact I. Qed.
Lemma OKP_triv : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;Sa1S4S36R2A3F_;FJ;").
Proof. intros J _ rho tp tr ms md x8 _ _ _. exact I. Qed.

Section Assembly.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;S2dS4Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;Sa1S4Vok;R2A3F_;FJ;").
Variables (m : Model) (B : Z).
Hypothesis HM : m40_hyps m B.

Let Hres : ltac2:(tb__ "0|1|
S0S14S17S21Q40A1M0G0A2A1S3aS37Vm;A1A1Sa4S4A1A3") := ltac2:(tb__ "0|0|
S87Vm;VB;VHM;A3"). Let Hsb : ltac2:(tb__ "0|1|
S0S21Q40A1S42S37Vm;A1M0A1S41G0A1A3") := ltac2:(tb__ "0|0|
S88Vm;VB;VHM;A3"). Let Hal : ltac2:(tb__ "0|0|
S0S13S32S22Q40S6eVm;A1A2Z1000A2Z0A3") := ltac2:(tb__ "0|0|
S81Vm;VB;VHM;A3"). Let Hlo : ltac2:(tb__ "0|0|
S30Z643000S22Q40S6eVm;A1A2A2") := ltac2:(tb__ "0|0|
S85Vm;VB;VHM;A3").
Let Hhi : ltac2:(tb__ "0|0|
S30S22Q40S6eVm;A1A2Z80643000A2") := ltac2:(tb__ "0|0|
S83Vm;VB;VHM;A3"). Let HB : ltac2:(tb__ "0|0|
S30S2fVB;Z3000A2S3cS37Vm;A1A1A2") := ltac2:(tb__ "0|0|
S80Vm;VB;VHM;A3"). Let Htop : ltac2:(tb__ "0|0|
S9dS37Vm;A1A1") := ltac2:(tb__ "0|0|
S89Vm;VB;VHM;A3"). Let Hband : ltac2:(tb__ "0|2|
S9bS1dS17S21Q40A1M0G0A2S3aS37Vm;A1M1A1S38G1A1A3S9aS99A3") := ltac2:(tb__ "0|0|
S82Vm;VB;VHM;A3").
Let Hlz : ltac2:(tb__ "0|3|
S17S21Q40M0A1M1G1A2M2S8fG2R1S40Vm;A1A3S31Z0S22G0S20G1G1R2A3A2A2F_;Fr;") := ltac2:(tb__ "0|0|
S86Vm;VB;VHM;A3"). Let Hlim : ltac2:(tb__ "0|0|
Sa3Vm;A1") := ltac2:(tb__ "0|0|
S84Vm;VB;VHM;A3").

Definition SP0 (rho0 : valuation) : Prop := ltac2:(tb__ "0|0|
S30S2fS74Vm;A1S95A2S22Q40S9Vrho0;PaA2A2A2").

Lemma OKFx' : ltac2:(tb__ "0|0|
S3bS13S2dS4Vok;S6bR2R1A2A3FBx;Fmx;").
Proof. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma STx : ltac2:(tb__ "0|0|
S3bS13S12S2eS4R1S6bR3R2A2A3Fn;FBx;Fmx;").
Proof. intros. apply stableA_KxA. Qed.

Let brk0 : Z := bv_unsigned (brk0w m).

Lemma mf_res_facts : ltac2:(tb__ "0|5|
S21Q40A1M0S1S0S14S17G0G0A2M1A1M2S3aS37S75Vm;R1A2A1M3A1S3aS37Vm;A1M4A1A3S1S0S13S3cG3A1S3cG4A1A3S1S0G2S38G3A1S1aG1S1bG0G0R1S6fA4S38G4A1A3A3S0G0S3dG3A1S3dG4A1A3A2A2A2Fa;").
Proof. intros a. rewrite mf_res_vmmaps. unfold mmap_none_vm. cbn. repeat split; reflexivity. Qed.

Lemma mf_exp_facts : ltac2:(tb__ "0|5|
S21Q40A1M0S1S0S14S17G0G0A2M1A1M2S3aS37S70Vm;R1A2A1M3A1S3aS37Vm;A1M4A1A3S1S0S13S3cG3A1S3cG4A1A3S1S0G2S38G3A1S1aG1S1bG0G0R1S6fA4S38G4A1A3A3S0G0S3dG3A1S3dG4A1A3A2A2A2Fa;").
Proof.
  intros a. unfold mf_exp, mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_limit vm_maps vm_init_sp].
  rewrite mf_res_vmmaps. unfold mmap_none_vm. cbn. repeat split; reflexivity.
Qed.

Lemma facts_M_in_E22f : ltac2:(tb__ "0|0|
SaS8fSaR1S94A3S8fSaR2S11S25S44A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma objs_clear_E22f : ltac2:(tb__ "0|2|
S0S15S73S1aS17S7S13A2M0S1bS7S13SeS98S4aScZ1000M1A1A3G1A4S19G0A1A3S25S44A1A2S16A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S22f_eq : ltac2:(tb__ "0|1|
S0S26S4eS51S44SfS6S25S44A1A1M0A1S1aSbS9eG0Z1000A2S19SbA1A3S71G0A1S65G0A1A5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RET0f : ltac2:(tb__ "0|1|
S0S15S68S78S59S1aS17S12S7A2M0S1bS12S7S79S4aA4S19G0A1A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RETPf : ltac2:(tb__ "0|1|
S0S15S68S78S5bS1aS17S12S7A2M0S1bS12S7S79S4aA4S1aG0S1bS12S7S7dS63A4S19G0A1A3A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nexts_f : ltac2:(tb__ "0|2|
S1S0S12S6S25S44A1A1S47A3S1S66S24S43A2S1S67S43S47A2S1S0S12S6S25S4eA1M0A1S65S47A1A3S1S0S12S6S25S48S44A1A1M1A1S47A3S1S0S15S8G1A1S18A3S0S15S8G0A1S18A3A2A2A2A2A2A2").
Proof.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [unfold NF, N18; lia|]. split; [unfold N18, N22f; lia|].
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.

Lemma tail_fail : ltac2:(tb__ "0|3|
S5S14S21Q40M0A1M1A1G1S5S90R4A1S9cS23G0Z0A2Vm;S6fR3A4S0G1S9R3S65S43A1A2R4A3S35R7S22G0R5A2M2S2fG2Z2000A2R4A4S8bS4Vok;S2bS4S6bS70Vm;R6A2S2fVB;Z1000A2A2S44R5R7A5S6cS4S24R8R7S77Vm;VB;A2A5A4F_;F_;F_;F_;Frho;Fa;Ftp;Frho0;").
Proof.
  intros rho0 tp a rho HSP0 Hpl Ha HVK. pose proof nexts_f as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls).
  pose proof E22f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  pose proof (mf_exp_facts a) as (Fres & Flim & Fmaps & Finit).
  eapply triple_seq.
  { apply triple1_triple.
    apply (node_rw ok OKF OKP E22f (mf_exp m a) (B + 4096) [(SAlu ALU_ADD vRES (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22f Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22f).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - rewrite Fres, Fmaps. apply band_covered_app_cons. exact Hband.
    - intros e sz [[= <- <-]|[]]. exists a, n8w. rewrite Fmaps. split; [left; reflexivity|].
      unfold vRES. cbn [eval]. rewrite Ha. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hpl as (_ & _ & Pceil & _). change (mmap_nZ n8w) with 8192 in Pceil. pose proof (alloc_top_lt (m_vmmaps m)).
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange a); unfold two_pow_64 in *; lia).
      change (bv_unsigned n8w) with 8192. lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK HSP0). }
  apply triple_disj.
  -
    apply (run1 ok (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M (refuse E22f) RET0f RsSymJump rho tp);
      [exact run_22f_fail | apply OKFx' | apply STx | exact Xlr |].
    intros rho1 Hag1. rewrite Xr in Hag1.
    eapply triple_entailsA; [exact ent_RET0f | exact wid_RET0f | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RET0f [(NA, vRES)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0f). eapply VK_agree; [| exact HVK | exact Hag1]. plia. }
    apply (post_fin ok (KxA (mf_exp m a) (B + 4096)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a). split; [exact Hpl|]. split; [reflexivity|]. split; [|split; [exact (proj2 HVK1)|]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0f [(NA, vRES)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. symmetry. apply (proj1 Hag1). plia.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply triple_ex. intros g. apply triple_pure. intros Hplg.
    rewrite <- S22f_eq.
    apply (run1 ok (KxA (mgrant (mf_exp m a) g) (B + 4096 + 4096)) FUEL_M CUTS_M S22f RETPf RsSymJump _ tp);
      [exact run_22f | apply OKFx' | apply STx | exact Xls |].
    intros rho1 Hag1. rewrite Xs in Hag1.
    eapply triple_entailsA; [exact ent_RETPf | exact wid_RETPf | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RETPf [(NA, vRES); (NG, vGRPf)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPf). eapply VK_agree; [| | exact Hag1]; [plia|]. apply VK_set_rw; [plia|]. exact HVK. }
    apply (post_fin ok _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a), g. split; [exact Hpl|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split; [exact (proj2 HVK1)|]]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. rewrite <- (proj1 Hag1 (Pos.succ N18)) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). reflexivity.
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NG) with vGRPf by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPf. cbn [eval]. rewrite <- (proj1 Hag1 N22f) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Lemma etail_fail : ltac2:(tb__ "0|3|
S5S14S21Q40M0A1M1A1G1S5S90R4A1S9cS23G0Z0A2Vm;S6fR3A4S0G1S9R3S65S43A1A2R4A3S35R7S22G0R5A2M2S2fG2Z2000A2R4A4S8cS4S2bS4S6bS70Vm;R6A2S2fVB;Z1000A2A2S44R5R7A5S6cS4S24R8R7S77Vm;VB;A2A5A3F_;F_;F_;F_;Frho;Fa;Ftp;Frho0;").
Proof.
  intros rho0 tp a rho HSP0 Hpl Ha HVK. pose proof nexts_f as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls).
  pose proof E22f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  pose proof (mf_exp_facts a) as (Fres & Flim & Fmaps & Finit).
  eapply etriple_seq.
  { apply (enode_rw_any E22f (mf_exp m a) (B + 4096) [(SAlu ALU_ADD vRES (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22f Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22f).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - rewrite Fres, Fmaps. apply band_covered_app_cons. exact Hband.
    - intros e sz [[= <- <-]|[]]. exists a, n8w. rewrite Fmaps. split; [left; reflexivity|].
      unfold vRES. cbn [eval]. rewrite Ha. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hpl as (_ & _ & Pceil & _). change (mmap_nZ n8w) with 8192 in Pceil. pose proof (alloc_top_lt (m_vmmaps m)).
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange a); unfold two_pow_64 in *; lia).
      change (bv_unsigned n8w) with 8192. lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK HSP0). }
  apply etriple_disj.
  -
    apply (erun1 (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M (refuse E22f) RET0f RsSymJump rho tp);
      [exact run_22f_fail | apply STx | exact Xlr |].
    intros rho1 Hag1. rewrite Xr in Hag1.
    eapply etriple_entailsA; [exact ent_RET0f | exact wid_RET0f | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RET0f [(NA, vRES)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0f). eapply VK_agree; [| exact HVK | exact Hag1]. plia. }
    apply (epost_fin (KxA (mf_exp m a) (B + 4096)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a). split; [exact Hpl|]. split; [reflexivity|]. split; [|split; [exact (proj2 HVK1)|]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0f [(NA, vRES)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. symmetry. apply (proj1 Hag1). plia.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply etriple_ex. intros g. apply etriple_pure. intros Hplg.
    rewrite <- S22f_eq.
    apply (erun1 (KxA (mgrant (mf_exp m a) g) (B + 4096 + 4096)) FUEL_M CUTS_M S22f RETPf RsSymJump _ tp);
      [exact run_22f | apply STx | exact Xls |].
    intros rho1 Hag1. rewrite Xs in Hag1.
    eapply etriple_entailsA; [exact ent_RETPf | exact wid_RETPf | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RETPf [(NA, vRES); (NG, vGRPf)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPf). eapply VK_agree; [| | exact Hag1]; [plia|]. apply VK_set_rw; [plia|]. exact HVK. }
    apply (epost_fin _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a), g. split; [exact Hpl|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split; [exact (proj2 HVK1)|]]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. rewrite <- (proj1 Hag1 (Pos.succ N18)) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). reflexivity.
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NG) with vGRPf by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPf. cbn [eval]. rewrite <- (proj1 Hag1 N22f) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Definition grow_out (o : out1) : Prop := match o with O1_fail _ => False | _ => True end.

Lemma grow_facts : ltac2:(tb__ "0|9|
S7bS91R1A1S96S38S37Vm;A1M0A1M1A1S0S15S3eS1dS17S21Q40M2A1M3G3A2M4S3aG0A1M5G1A3S6eVm;A1S72A3S16A3S1S0S14G4A1S3aS37S7aVm;R4A2A1M6A1M7G5A3S1S0S13S3cG6A1S3cG0A1A3S1S0G3S3dG6A1S3dG0A1A3S1S2G3G3S2G3G3S1S8fG4S1bG3G3R2R1A4S38S37S7aVm;R6A2A1A1A3S1S30S22G2R2A2M8S2fVbrk0;Z1000A2A2S30S2fVbrk0;Z2000A2S2fG8S22G2R1A2A2A2A2A2Ls;A2Lb;A2S9bS1dG4G7S38G6A1A3S9aS99A3A2A2A2A2F_;F_;F_;Fo;").
Proof.
  intros o Ho Hwf Hfree3. pose proof (mg_vmmaps m Hlo Hhi) as MG. pose proof (n2w_val) as NV. pose proof n3w_val as NV3.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  pose proof (band_clear_of_free _ (brk0w m) n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  assert (BG : band_covered (vm_reserved (m_vmmaps m) ++ (brk0w m, n2w) :: vm_maps (m_vmmaps m)) SHADOW_BAND_LO SHADOW_BAND_HI)
    by (apply band_covered_app_cons; exact Hband).
  destruct o as [| | |a]; cbn [out1_model]; [| | |destruct Ho].
  -   rewrite MG. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact BG].
    exists (brk0w m), n2w. split; [left; reflexivity|]. rewrite NV. unfold brk0. lia.
  -   unfold mg_ok. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_ok_vm. cbn [vm_reserved vm_limit vm_maps vm_init_sp].
    rewrite MG. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact BG].
    exists (brk0w m), n2w. split; [left; reflexivity|]. rewrite NV. unfold brk0. lia.
  -   unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_dead_vm. cbn [vm_reserved vm_limit vm_maps vm_init_sp].
    rewrite MG. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0. fold brk0. rewrite Upg. cbn [maps_subtract].
    assert (Eiv : iv_subtract (brk0w m) n2w brk0 (brk0 + 4096) = [(Z_to_bv 64 (brk0 + 4096), Z_to_bv 64 4096)]).
    { unfold iv_subtract. unfold brk0. rewrite NV. rewrite Z.ltb_irrefl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
      rewrite Z.max_r by lia. f_equal. f_equal. f_equal. lia. }
    rewrite Eiv. cbn [app]. split.
    + exists (Z_to_bv 64 (brk0 + 4096)), (Z_to_bv 64 4096). split; [left; reflexivity|].
      pose proof Hlo. pose proof Hhi. unfold brk0 in *. rewrite !u64_of_lit by lia. lia.
    + apply band_covered_app_cons. apply band_covered_subtract; [exact Hwf | lia | | exact Hband].
      pose proof Hlo. pose proof Hhi. unfold brk0, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0, SHADOW_BAND_LO, SHADOW_BAND_HI in *. right.
      destruct (Z.le_gt_cases (bv_unsigned (brk0w m) + 4096) 0x7fff7000) as [L|L]; [exact L|]. exfalso.
      destruct (Z.le_gt_cases 0x7fff7000 (bv_unsigned (brk0w m))).
      * apply (HBD (bv_unsigned (brk0w m))); lia.
      * apply (HBD 0x7fff7000); lia.
Qed.

Lemma facts_M_in_E22g : ltac2:(tb__ "0|0|
SaS8fSaR1S94A3S8fSaR2S11S25S45A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma objs_clear_E22g : ltac2:(tb__ "0|2|
S0S15S73S1aS17S7S13A2M0S1bS7S13SeS98S49ScZ1000M1A1A3G1A4S19G0A1A3S25S45A1A2S16A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S22g_eq : ltac2:(tb__ "0|1|
S0S26S4fS51S45SfS6S25S45A1A1M0A1S1aSbS9eG0Z1000A2S19SbA1A3S71G0A1S65G0A1A5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RET0g : ltac2:(tb__ "0|1|
S0S15S68S78S5aS1aS17S12S7A2M0S1bS12S7S79S49A4S19G0A1A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RETPg : ltac2:(tb__ "0|1|
S0S15S68S78S5cS1aS17S12S7A2M0S1bS12S7S79S49A4S1aG0S1bS12S7S7dS64A4S19G0A1A3A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nexts_g : ltac2:(tb__ "0|4|
S1S0S12S6S25S45A1A1S46A3S1S66S24S43A2S1S67S43S46A2S1S0S12S6S25S4fA1M0A1S65S46A1A3S1S0S12S6S25S48S45A1A1M1A1S46A3S1S0S15S8G1A1S18A3S1S0S15S8G0A1S18A3S1S0S12S6S25S50A1M2A1S65S65S43A1A1M3A3S1S0S15S8G2A1S18A3S66G3S46A2A2A2A2A2A2A2A2A2A2").
Proof.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [unfold NF, N18; lia|]. split; [unfold N18, N22g; lia|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. unfold N18, N22g; lia.
Qed.

Lemma tail_grow : ltac2:(tb__ "0|2|
S7bS5S14S21Q40A1M0A1S5S90R3A1S91R5A1S7eVm;R6A2S96S38S37Vm;A1A1A1S0G0S9R5S43A2S6eVm;A1A3S35R8Vbrk0;S2fVbrk0;Z2000M1A2R6A4S8bS4Vok;S2bS4S6bS7aVm;RaA2S2fVB;G1A2A2S50R7S7fVm;RaR8A3A5S6cS4S24R9R8S77Vm;VB;A2A5A4F_;F_;F_;F_;F_;F_;Frho;Ftp0;Frho0;Fo;").
Proof.
  intros o rho0 tp0 rho HSP0 Ho Hok Hwf HN18 HVK. pose proof nexts_g as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls & Xu & Xlu & Xun).
  pose proof E22g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  assert (Hfree3 : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (brk0w m) n3w = true)
    by (destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok)).
  destruct (grow_facts o Ho Hwf Hfree3) as (Fres & Flim & Finit & (b1 & s1 & Hb1 & Hb1l & Hb1h) & Fband).
  set (mx := out1_model m o) in *. set (tpx := out1_tp m o tp0) in *.
  apply (run1 ok (KxA mx (B + 8192)) FUEL_M CUTS_M U24c E22g RsCut rho tpx); [exact run_24 | apply OKFx' | apply STx | exact Xlu |].
  intros rho1 Hag1. rewrite Xu in Hag1.
  assert (HN18' : rw rho1 N18 = brk0w m) by (rewrite <- (proj1 Hag1 N18) by plia; exact HN18).
  assert (HVK1 : VK rho0 brk0 (brk0 + 8192) rho1) by (eapply VK_agree; [| exact HVK | exact Hag1]; plia).
  eapply triple_seq.
  { apply triple1_triple.
    apply (node_rw ok OKF OKP E22g mx (B + 8192) [(SAlu ALU_ADD vBRK (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22g Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22g).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - exact Fband.
    - intros e sz [[= <- <-]|[]]. exists b1, s1. split; [exact Hb1|].
      unfold vBRK. cbn [eval]. rewrite HN18'. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hlo. pose proof Hhi. unfold brk0 in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK1 HSP0). }
  apply triple_disj.
  -
    apply (run1 ok (KxA mx (B + 8192)) FUEL_M CUTS_M (refuse E22g) RET0g RsSymJump rho1 tpx);
      [exact run_22g_fail | apply OKFx' | apply STx | exact Xlr |].
    intros rho2 Hag2. rewrite Xr in Hag2.
    eapply triple_entailsA; [exact ent_RET0g | exact wid_RET0g | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RET0g [(NA, vBRK)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0g). eapply VK_agree; [| exact HVK1 | exact Hag2]. plia. }
    apply (post_fin ok (KxA mx (B + 8192)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o. split; [exact Hok|]. split; [reflexivity|]. split; [|split].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0g [(NA, vBRK)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by plia. rewrite HN18'. destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply triple_ex. intros g. apply triple_pure. intros Hplg.
    rewrite <- S22g_eq.
    apply (run1 ok (KxA (mgrant mx g) (B + 8192 + 4096)) FUEL_M CUTS_M S22g RETPg RsSymJump _ tpx);
      [exact run_22g | apply OKFx' | apply STx | exact Xls |].
    intros rho2 Hag2. rewrite Xs in Hag2.
    eapply triple_entailsA; [exact ent_RETPg | exact wid_RETPg | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPg). eapply VK_agree; [| | exact Hag2]; [plia|]. apply VK_set_rw; [plia|]. exact HVK1. }
    apply (post_fin ok _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o, g. split; [exact Hok|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split]].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). rewrite HN18'.
      destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NG) with vGRPg by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPg. cbn [eval]. rewrite <- (proj1 Hag2 N22g) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Lemma etail_grow : forall (o : out1) (rho0 : valuation) (tp0 : list word) (rho : valuation),
  SP0 rho0 -> grow_out o -> out1_ok m o -> ivs_wf (vm_maps (m_vmmaps m)) ->
  rw rho N18 = brk0w m -> VK rho0 brk0 (brk0 + 8192) rho ->
  etriple segsA (SPA segsA (KxA (out1_model m o) (B + 8192)) U24c rho (out1_tp m o tp0))
    (LQPA segsA NF rho0 tp0 (Posts_M m B)).
Proof.
  intros o rho0 tp0 rho HSP0 Ho Hok Hwf HN18 HVK. pose proof nexts_g as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls & Xu & Xlu & Xun).
  pose proof E22g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  assert (Hfree3 : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (brk0w m) n3w = true)
    by (destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok)).
  destruct (grow_facts o Ho Hwf Hfree3) as (Fres & Flim & Finit & (b1 & s1 & Hb1 & Hb1l & Hb1h) & Fband).
  set (mx := out1_model m o) in *. set (tpx := out1_tp m o tp0) in *.
  apply (erun1 (KxA mx (B + 8192)) FUEL_M CUTS_M U24c E22g RsCut rho tpx); [exact run_24 | apply STx | exact Xlu |].
  intros rho1 Hag1. rewrite Xu in Hag1.
  assert (HN18' : rw rho1 N18 = brk0w m) by (rewrite <- (proj1 Hag1 N18) by plia; exact HN18).
  assert (HVK1 : VK rho0 brk0 (brk0 + 8192) rho1) by (eapply VK_agree; [| exact HVK | exact Hag1]; plia).
  eapply etriple_seq.
  { apply (enode_rw_any E22g mx (B + 8192) [(SAlu ALU_ADD vBRK (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22g Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22g).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - exact Fband.
    - intros e sz [[= <- <-]|[]]. exists b1, s1. split; [exact Hb1|].
      unfold vBRK. cbn [eval]. rewrite HN18'. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hlo. pose proof Hhi. unfold brk0 in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK1 HSP0). }
  apply etriple_disj.
  -
    apply (erun1 (KxA mx (B + 8192)) FUEL_M CUTS_M (refuse E22g) RET0g RsSymJump rho1 tpx);
      [exact run_22g_fail | apply STx | exact Xlr |].
    intros rho2 Hag2. rewrite Xr in Hag2.
    eapply etriple_entailsA; [exact ent_RET0g | exact wid_RET0g | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RET0g [(NA, vBRK)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0g). eapply VK_agree; [| exact HVK1 | exact Hag2]. plia. }
    apply (epost_fin (KxA mx (B + 8192)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o. split; [exact Hok|]. split; [reflexivity|]. split; [|split].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0g [(NA, vBRK)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by plia. rewrite HN18'. destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply etriple_ex. intros g. apply etriple_pure. intros Hplg.
    rewrite <- S22g_eq.
    apply (erun1 (KxA (mgrant mx g) (B + 8192 + 4096)) FUEL_M CUTS_M S22g RETPg RsSymJump _ tpx);
      [exact run_22g | apply STx | exact Xls |].
    intros rho2 Hag2. rewrite Xs in Hag2.
    eapply etriple_entailsA; [exact ent_RETPg | exact wid_RETPg | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPg). eapply VK_agree; [| | exact Hag2]; [plia|]. apply VK_set_rw; [plia|]. exact HVK1. }
    apply (epost_fin _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o, g. split; [exact Hok|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split]].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). rewrite HN18'.
      destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NG) with vGRPg by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPg. cbn [eval]. rewrite <- (proj1 Hag2 N22g) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Definition Z8 (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S21Q40M0A1S1S30S2fVbrk0;Z1000A2S22G0R1A2M1A2S31G1S2fVbrk0;Z2000A2A2A2S0S1cS21Q8M2A1M3A1S10Vrho;R2A2S1eG3S23G2Z0A2A2A3F_;Fa;").

Lemma nexts_20 : ltac2:(tb__ "0|5|
S1S0S12S6S25S60A1M0A1S65S43A1M1A3S1S0S12S6S25S5fA1M2A1G1A3S1S0S15S8G0A1S18A3S1S0S15S8G2A1S18A3S1S0S15S68S1aS17S12S7A2M3S1bS12S7G1S49A4S19G3A1M4A3S24A2S16A3S0S15S68S1aG3S1bS12S7G1ScS34S33Z2Z40A2Z1A2A1A4G4A3S24A2S16A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma from_L24 : ltac2:(tb__ "0|2|
S7bS5S14S21Q40A1M0A1S26S69S5S90R5A1S91R7A1S7eVm;R8A2S96S38S37Vm;A1A1A1S0S15S2aR7S62R6A3S16A3S0S15S68R7S24A2S16A3S0S15S68R8S65S43A1A2S16A3S0G0S9R8S43A2S6eVm;A1A3S35RdVbrk0;S2fVbrk0;Z2000M1A2R9A4S92RaA1S8bS4Vok;S2bS4S6bS7aVm;R10A2S2fVB;G1A2A2RdRbS7fVm;R10ReA3A5S6cS4S24RfReS77Vm;VB;A2A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fs;FL;Ftp0;Frho0;Fo;").
Proof.
  intros o rho0 tp0 L s rho HSP0 Ho Hok Hwf He Hs Hs' HN18 HVK HZ8.
  eapply triple_entailsA; [exact He | exact Hs | apply STx |].
  assert (HN18' : rw (rho_sub rho s) N18 = brk0w m) by (rewrite (rw_sub_other rho s N18 Hs'); exact HN18).
  assert (HVK' : VK rho0 brk0 (brk0 + 8192) (rho_sub rho s)) by (apply (VK_sub _ _ _ _ _ Hs); exact HVK).
  eapply triple_conseq; [| intros w Hw; exact Hw | apply (tail_grow o rho0 tp0 (rho_sub rho s) HSP0 Ho Hok Hwf HN18' HVK')].
  intros w Hw. apply (carve24 m Hlo Hhi Htop Hband _ (rho_sub rho s)); [exact HN18' | | exact (VK_sp _ _ _ _ _ HVK' HSP0) | | | exact Hw].
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj1 Hok).
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok).
  + intros a Ha. cbn. apply HZ8. exact Ha.
Qed.

Lemma efrom_L24 : forall (o : out1) (rho0 : valuation) (tp0 : list word) (L : axst) (s : wsub) (rho : valuation),
  SP0 rho0 -> grow_out o -> out1_ok m o -> ivs_wf (vm_maps (m_vmmaps m)) ->
  entailsA L U24 s = true -> wsub_id_below s NF = true -> wsub_id_below s (Pos.succ N18) = true ->
  rw rho N18 = brk0w m -> VK rho0 brk0 (brk0 + 8192) rho -> Z8 rho ->
  etriple segsA (SPA segsA (KxA (out1_model m o) (B + 8192)) L rho (out1_tp m o tp0))
    (LQPA segsA NF rho0 tp0 (Posts_M m B)).
Proof.
  intros o rho0 tp0 L s rho HSP0 Ho Hok Hwf He Hs Hs' HN18 HVK HZ8.
  eapply etriple_entailsA; [exact He | exact Hs | apply STx |].
  assert (HN18' : rw (rho_sub rho s) N18 = brk0w m) by (rewrite (rw_sub_other rho s N18 Hs'); exact HN18).
  assert (HVK' : VK rho0 brk0 (brk0 + 8192) (rho_sub rho s)) by (apply (VK_sub _ _ _ _ _ Hs); exact HVK).
  eapply etriple_conseq; [| intros w Hw; exact Hw | apply (etail_grow o rho0 tp0 (rho_sub rho s) HSP0 Ho Hok Hwf HN18' HVK')].
  intros w Hw. apply (carve24 m Hlo Hhi Htop Hband _ (rho_sub rho s)); [exact HN18' | | exact (VK_sp _ _ _ _ _ HVK' HSP0) | | | exact Hw].
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj1 Hok).
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok).
  + intros a Ha. cbn. apply HZ8. exact Ha.
Qed.

Lemma seg_grow : ltac2:(tb__ "0|6|
S5S14S21Q40A1M0A1S5S90R3A1S0G0S9R2S43A2S6eVm;A1M1A3S1S30S2fVbrk0;Z2000M2A2M3S3fS37Vm;A1M4A1A2S0S15S3eS1dS17G0G0A2S3aG4A1S38G4A1M5A3G1S72A3S16A3A2S96G5A1S35R7Vbrk0;G3R5A4S92R6A1S8bS4Vok;S2bS4S6bS76Vm;A1S2fVB;G2A2A2S55R7R8A5S6cS4S24R9R8S77Vm;VB;A2A5A4F_;F_;F_;F_;F_;F_;Frho;Ftp;Frho0;").
Proof.
  intros rho0 tp rho HSP0 HN18 Hok Hwf HVK HZ8. pose proof nexts_20 as (Xok & Xko & Lok & Lko & Wok & Wko).
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HVK20 : VK rho0 brk0 (brk0 + 8192) (rho20 m rho)).
  { unfold rho20. apply VK_set_rm; [exact HVK|]. intros x Hx. apply unmap_range_outside. rewrite Upg. unfold brk0 in Hx. lia. }
  assert (HZ20 : Z8 (rho20 m rho)).
  { unfold rho20, Z8. intros a Ha. unfold set_rm. cbn [rm]. rewrite unmap_range_outside by (rewrite Upg; unfold brk0 in Ha; lia). apply HZ8. exact Ha. }
  eapply triple_seq; [apply triple1_triple; apply (node20g ok OKF OKP m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho tp (B + 8192) HN18 (VK_sp _ _ _ _ _ HVK HSP0) (proj2 Hok))|].
  apply triple_disj; [|apply triple_disj; [|apply triple_pure; intros _]].
  -
    apply (run1 ok (KxA (mg m) (B + 8192)) FUEL_M (0xd2640 :: CUTS_M) S20g_ko L24ko RsCut rho tp); [exact run_20g_ko | apply OKFx' | apply STx | exact Lko |].
    intros rho1 Hag1. rewrite Xko in Hag1.
    apply (from_L24 O1_kept rho0 tp L24ko _ rho1 HSP0 I Hok Hwf ent_24ko Wko Wko).
    + rewrite <- (proj1 Hag1 N18) by plia. exact HN18.
    + eapply VK_agree; [| exact HVK | exact Hag1]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ8. exact Ha.
  -
    apply (run1 ok (KxA (mg_ok m) (B + 8192)) FUEL_M (0xd2640 :: CUTS_M) S20g_ok L24ok RsCut (rho20 m rho) tp); [exact run_20g_ok | apply OKFx' | apply STx | exact Lok |].
    intros rho1 Hag1. rewrite Xok in Hag1.
    apply (from_L24 O1_ok rho0 tp L24ok _ rho1 HSP0 I Hok Hwf ent_24ok Wok Wok).
    + rewrite <- (proj1 Hag1 N18) by plia. unfold rho20, set_rm. cbn [rw]. exact HN18.
    + eapply VK_agree; [| exact HVK20 | exact Hag1]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ20. exact Ha.
  -
    apply (run1 ok (KxA (mg_dead m) (B + 8192)) FUEL_M (0xd2640 :: CUTS_M) S20g_ko L24ko RsCut (rho20 m rho) (tp20 m tp)); [exact run_20g_ko | apply OKFx' | apply STx | exact Lko |].
    intros rho1 Hag1. rewrite Xko in Hag1.
    apply (from_L24 O1_dead rho0 tp L24ko _ rho1 HSP0 I Hok Hwf ent_24ko Wko Wko).
    + rewrite <- (proj1 Hag1 N18) by plia. unfold rho20, set_rm. cbn [rw]. exact HN18.
    + eapply VK_agree; [| exact HVK20 | exact Hag1]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ20. exact Ha.
Qed.

Lemma eseg_grow : forall (rho0 : valuation) (tp : list word) (rho : valuation),
  SP0 rho0 -> rw rho N18 = brk0w m ->
  brk0 + 8192 <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (brk0w m) n3w = true ->
  ivs_wf (vm_maps (m_vmmaps m)) -> VK rho0 brk0 (brk0 + 8192) rho -> Z8 rho ->
  etriple segsA (SPA segsA (KxA (mg m) (B + 8192)) E20g rho tp) (LQPA segsA NF rho0 tp (Posts_M m B)).
Proof.
  intros rho0 tp rho HSP0 HN18 Hok Hwf HVK HZ8. pose proof nexts_20 as (Xok & Xko & Lok & Lko & Wok & Wko).
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HVK20 : VK rho0 brk0 (brk0 + 8192) (rho20 m rho)).
  { unfold rho20. apply VK_set_rm; [exact HVK|]. intros x Hx. apply unmap_range_outside. rewrite Upg. unfold brk0 in Hx. lia. }
  assert (HZ20 : Z8 (rho20 m rho)).
  { unfold rho20, Z8. intros a Ha. unfold set_rm. cbn [rm]. rewrite unmap_range_outside by (rewrite Upg; unfold brk0 in Ha; lia). apply HZ8. exact Ha. }
  eapply etriple_seq; [apply (enode20g_ok m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho tp (B + 8192) HN18 (VK_sp _ _ _ _ _ HVK HSP0) (proj2 Hok))|].
  apply (erun1 (KxA (mg_ok m) (B + 8192)) FUEL_M (0xd2640 :: CUTS_M) S20g_ok L24ok RsCut (rho20 m rho) tp); [exact run_20g_ok | apply STx | exact Lok |].
  intros rho1 Hag1. rewrite Xok in Hag1.
  apply (efrom_L24 O1_ok rho0 tp L24ok _ rho1 HSP0 I Hok Hwf ent_24ok Wok Wok).
  + rewrite <- (proj1 Hag1 N18) by plia. unfold rho20, set_rm. cbn [rw]. exact HN18.
  + eapply VK_agree; [| exact HVK20 | exact Hag1]. plia.
  + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ20. exact Ha.
Qed.

Lemma nexts_main : ltac2:(tb__ "0|b|
S1S0S12S6S25S93A1M0A1S24A3S1S0S15S8G0A1S18A3S1S0S12S6S25S4bA1A1M1G1A3S1S0S12S6S25S4cA1M2A1S65S43A1M3A3S1S0S15S8G2A1S18A3S1S0S12S6S25S5dA1M4A1G3A3S1S0S15S8G4A1S18A3S1S0S12S6S25S4dA1M5A1G3A3S1S0S15S8G5A1S18A3S1S0S12S6S25S48S54A1A1M6A1G3A3S1S0S15S8G6A1S18A3S1S0S12S6S25S5eA1M7A1S65G3A1M8A3S1S0S15S8G7A1S18A3S1S0S12S6S25S48S56A1A1M9A1G8A3S1S0S15S8G9A1S18A3S1S0S12S6S25S61A1MaA1G8A3S0S15S8GaA1S18A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma wid_RET0a : ltac2:(tb__ "0|0|
S0S15S68S78S57S19S17S12S7A2A1A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RET0b : ltac2:(tb__ "0|0|
S0S15S68S78S58S19S17S12S7A2A1A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma next_E18_ge : ltac2:(tb__ "0|0|
S1S66S24S6S25S4bA1A1A2S66S24S43A2A2").
Proof. split; [vm_compute; discriminate | unfold NF, N18; lia]. Qed.

Theorem musl_malloc40_main : ltac2:(tb__ "0|0|
S5S14S21Q40A1A1Sa2Vm;R1A2S96S38S37Vm;A1A1A1S90R4A1S8bS4Vok;S2bS4S6bVm;VB;A2S93R5R4A5S6cS4S24R5R4S77Vm;VB;A2A5A4F_;F_;F_;Ftp;Frho;").
Proof.
  intros rho0 tp Htp Hwf HSP0.
  pose proof nexts_main as (XnP & XlP & _ & Xn18 & Xl18 & Xn19g & Xl19g & Xn19f & Xl19f & Xn20r & Xl20r & Xn20 & Xl20 & Xn21r & Xl21r & Xn21 & Xl21).
  pose proof next_E18_ge as [XE18 XN18].

  apply (run1 ok (KxA m B) FUEL_M CUTS_M Pre_M E18 RsCut rho0 tp); [exact run_I | apply OKFx' | apply STx | exact XlP |].
  intros rho1 Hag1. rewrite XnP in Hag1.
  assert (HVK1 : VK rho0 0 0 rho1) by (eapply VK_agree; [apply Pos.le_refl | apply VK_refl | exact Hag1]).
  eapply (triple_entailsA segsA ok (KxA m B) NF E18 E18t []); [exact ent_18 | reflexivity | apply STx |].
  assert (HVK1' : VK rho0 0 0 (rho_sub rho1 [])) by (apply (VK_sub _ _ _ _ [] eq_refl); exact HVK1).
  set (rho1' := rho_sub rho1 []) in *.

  eapply triple_seq; [apply triple1_triple; apply (node18 ok OKF OKP m B Hal Hlo Hhi rho1' tp)|].
  assert (HVK2 : VK rho0 0 0 (rho_set_rw rho1' N18 (brk0w m))) by (apply VK_set_rw; [exact XN18 | exact HVK1']).
  apply (run1 ok (KxA m B) FUEL_M CUTS_M S18 E19 RsCut _ tp); [exact run_18 | apply OKFx' | apply STx | exact Xl18 |].
  intros rho2 Hag2. rewrite Xn18 in Hag2.
  assert (HN18 : rw rho2 N18 = brk0w m) by (rewrite <- (proj1 Hag2 N18) by plia; apply rho_set_rw_at).
  assert (HVK3 : VK rho0 0 0 rho2) by (eapply VK_agree; [| exact HVK2 | exact Hag2]; plia).

  eapply triple_seq; [apply triple1_triple; apply (node19 ok OKF OKP m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho2 tp HN18 (VK_sp _ _ _ _ _ HVK3 HSP0))|].
  apply triple_disj.
  -
    apply triple_ex. intros rho3. apply triple_pure. intros Hceil. apply triple_pure. intros Hfree. apply triple_pure. intros (R1 & R2 & R3 & R4).
    assert (HN18' : rw rho3 N18 = brk0w m) by (rewrite R1; exact HN18).
    assert (HVK4 : VK rho0 brk0 (brk0 + 8192) rho3).
    { destruct HVK3 as [Hav Hrm]. split.
      - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; symmetry; apply R1 | intros l; symmetry; apply R2].
      - intros x Hx. rewrite (R3 x) by (unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0; unfold brk0 in Hx; exact Hx). apply Hrm. lia. }
    apply (run1 ok (KxA (mg m) (B + 8192)) FUEL_M CUTS_M S19g E20g RsCut rho3 tp); [exact run_19g | apply OKFx' | apply STx | exact Xl19g |].
    intros rho4 Hag4. rewrite Xn19g in Hag4.
    apply (seg_grow rho0 tp rho4 HSP0).
    + rewrite <- (proj1 Hag4 N18) by plia. exact HN18'.
    + split; [unfold brk0; exact Hceil | exact Hfree].
    + exact Hwf.
    + eapply VK_agree; [| exact HVK4 | exact Hag4]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag4)). apply R4. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0. unfold brk0 in Ha. lia.
  -
    apply (run1 ok (KxA m B) FUEL_M CUTS_M S19f E20f RsCut rho2 tp); [exact run_19f | apply OKFx' | apply STx | exact Xl19f |].
    intros rho3 Hag3. rewrite Xn19f in Hag3.
    assert (HVK4 : VK rho0 0 0 rho3) by (eapply VK_agree; [| exact HVK3 | exact Hag3]; plia).
    eapply triple_seq; [apply triple1_triple; apply (node20f ok OKF OKP m B Hres HB Htop Hband rho3 tp (VK_sp _ _ _ _ _ HVK4 HSP0))|].
    apply triple_disj.
    +
      apply (run1 ok (KxA m B) FUEL_M CUTS_M (refuse E20f) RET0a RsSymJump rho3 tp); [exact run_20f_fail | apply OKFx' | apply STx | exact Xl20r |].
      intros rho4 Hag4. rewrite Xn20r in Hag4.
      eapply triple_entailsA; [exact ent_RET0a | exact wid_RET0a | apply STx |].
      assert (HVK5 : VK rho0 0 0 (rho_sub rho4 (post_sub RET0a []))).
      { apply (VK_sub _ _ _ _ _ wid_RET0a). eapply VK_agree; [| exact HVK4 | exact Hag4]. plia. }
      apply (post_fin ok (KxA m B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK5)].
      intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK5)|].
      exists O0_refused. split; [exact I|]. split; [exact (proj2 HVK5)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
    +
      apply triple_ex. intros a. apply triple_pure. intros Hpl.
      assert (HVK5 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho20f rho3 a)).
      { unfold rho20f. apply VK_set_rw; [plia|]. apply VK_set_rm; [eapply VK_widen; [| exact HVK4]; intros z Hz; lia|].
        intros x Hx. apply unmap_range_outside. change (bv_unsigned n8w) with 8192. exact Hx. }
      apply (run1 ok (KxA (mf_res m a) B) FUEL_M CUTS_M S20f E21f RsCut (rho20f rho3 a) tp); [exact run_20f | apply OKFx' | apply STx | exact Xl20 |].
      intros rho4 Hag4. rewrite Xn20 in Hag4.
      assert (Ha : rw rho4 (Pos.succ N18) = a) by (rewrite <- (proj1 Hag4 (Pos.succ N18)) by plia; unfold rho20f; apply rho_set_rw_at).
      assert (HVK6 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) rho4) by (eapply VK_agree; [| exact HVK5 | exact Hag4]; plia).
      eapply triple_seq; [apply triple1_triple; apply (node21f ok OKF OKP m B Hres HB Htop Hband Hlz Hlim rho4 tp a Ha (VK_sp _ _ _ _ _ HVK6 HSP0) Hpl Htp)|].
      apply triple_disj.
      *
        apply (run1 ok (KxA (mf_res m a) B) FUEL_M CUTS_M (refuse E21f) RET0b RsSymJump rho4 tp); [exact run_21f_fail | apply OKFx' | apply STx | exact Xl21r |].
        intros rho5 Hag5. rewrite Xn21r in Hag5.
        eapply triple_entailsA; [exact ent_RET0b | exact wid_RET0b | apply STx |].
        assert (HVK7 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho5 (post_sub RET0b []))).
        { apply (VK_sub _ _ _ _ _ wid_RET0b). eapply VK_agree; [| exact HVK6 | exact Hag5]. plia. }
        apply (post_fin ok (KxA (mf_res m a) B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK7)].
        intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK7)|].
        exists (O0_reserved a). split; [exact Hpl|]. split; [exact (proj2 HVK7)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
      *
        apply (run1 ok (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M S21f E22f RsCut rho4 tp); [exact run_21f | apply OKFx' | apply STx | exact Xl21 |].
        intros rho5 Hag5. rewrite Xn21 in Hag5.
        apply (tail_fail rho0 tp a rho5 HSP0 Hpl).
        -- rewrite <- (proj1 Hag5 (Pos.succ N18)) by plia. exact Ha.
        -- eapply VK_agree; [| exact HVK6 | exact Hag5]. plia.
Qed.

Theorem musl_malloc40_sum : ltac2:(tb__ "0|0|
S5S14S21Q40A1A1S8bS4Vok;S2bS4S7cVm;VB;A2S93R2R1A5S6cS4S24R2R1S77Vm;VB;A2A5A4Ftp;Frho;").
Proof.
  intros rho tp n Hg w HP. destruct w as [tr [ms md]].
  pose proof HP as [(Hsm & HMI & _) ((Htr & Hem & Hpaid) & HSP0)].
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _).
  apply (musl_malloc40_main rho tp); [| | exact HSP0 | exact Hg | exact (conj (proj1 HP) (proj1 (proj2 HP)))].
  - cbn [cfg_model snd] in HMI. intros p Hp. destruct (MI_tp_in_maps segsA _ _ HMI p Hp) as (Hal' & b & s0 & Hin & Hb). split; [exact Hal'|].
    exists b, s0. rewrite <- Evm. split; [exact Hin | exact Hb].
  - cbn [cfg_model snd] in HMI. rewrite <- Evm. exact (proj1 (MI_ivs_wf segsA _ _ HMI)).
Qed.

Lemma enode18 : ltac2:(tb__ "0|1|
S5S14S21Q40A1A1S8cS4S2bS4S6bVm;VB;A2M0S52R2R1A5S2bS4G0S4cS9fR2S43S6eVm;A1A3R1A5A3Ftp;Frho;").
Proof.
  intros rho tp. pose proof E18_at as (Hpc & Hecall & R17 & R10).
  apply etriple_ecall_detA; [apply STx | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _ & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E18t [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  exists ([], mkCfg (after_sys ms (vm_brk (m_vmmaps md))) md). split.
  - apply (wstep_brk_query_introA segsA ms md _ Hh H214 [] Hp G0).
  - split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
    unfold S18, cont. rewrite Evm. change (vm_brk (m_vmmaps m)) with (brk0w m).
    assert (HN : ss_next (ax_S E18t) = N18) by reflexivity. rewrite <- HN.
    eapply smatchA_after_ret_fresh; [exact Hsp | exact Hh | apply vm_same_refl | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    rewrite HN. unfold F18, vBRK. pose proof Hal as Hal'. pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 in Hal', Hlo', Hhi'.
    constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds eval]; rewrite rho_set_rw_at.
    + split; [lia|]. change (2 ^ 12) with 4096. exact Hal'.
    + rewrite (u64_of_lit 0x643000) by lia. lia.
    + rewrite (u64_of_lit 0x80643000) by lia. lia.
Qed.

Theorem musl_malloc40_main_ex : forall (rho : valuation) (tp : list word),
  tp_in_maps m tp -> ivs_wf (vm_maps (m_vmmaps m)) -> SP0 rho ->
  etriple segsA (SPA segsA (KxA m B) Pre_M rho tp) (LQPA segsA NF rho tp (Posts_M m B)).
Proof.
  intros rho0 tp Htp Hwf HSP0.
  pose proof nexts_main as (XnP & XlP & _ & Xn18 & Xl18 & Xn19g & Xl19g & Xn19f & Xl19f & Xn20r & Xl20r & Xn20 & Xl20 & Xn21r & Xl21r & Xn21 & Xl21).
  pose proof next_E18_ge as [XE18 XN18].
  apply (erun1 (KxA m B) FUEL_M CUTS_M Pre_M E18 RsCut rho0 tp); [exact run_I | apply STx | exact XlP |].
  intros rho1 Hag1. rewrite XnP in Hag1.
  assert (HVK1 : VK rho0 0 0 rho1) by (eapply VK_agree; [apply Pos.le_refl | apply VK_refl | exact Hag1]).
  eapply (etriple_entailsA segsA (KxA m B) NF E18 E18t []); [exact ent_18 | reflexivity | apply STx |].
  assert (HVK1' : VK rho0 0 0 (rho_sub rho1 [])) by (apply (VK_sub _ _ _ _ [] eq_refl); exact HVK1).
  set (rho1' := rho_sub rho1 []) in *.
  eapply etriple_seq; [apply (enode18 rho1' tp)|].
  assert (HVK2 : VK rho0 0 0 (rho_set_rw rho1' N18 (brk0w m))) by (apply VK_set_rw; [exact XN18 | exact HVK1']).
  apply (erun1 (KxA m B) FUEL_M CUTS_M S18 E19 RsCut _ tp); [exact run_18 | apply STx | exact Xl18 |].
  intros rho2 Hag2. rewrite Xn18 in Hag2.
  assert (HN18 : rw rho2 N18 = brk0w m) by (rewrite <- (proj1 Hag2 N18) by plia; apply rho_set_rw_at).
  assert (HVK3 : VK rho0 0 0 rho2) by (eapply VK_agree; [| exact HVK2 | exact Hag2]; plia).

  eapply etriple_seq; [apply (enode19_any m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho2 tp HN18 (VK_sp _ _ _ _ _ HVK3 HSP0))|].
  apply etriple_disj.
  1:{
    apply etriple_ex. intros rho3. apply etriple_pure. intros Hceil. apply etriple_pure. intros Hfree. apply etriple_pure. intros (R1 & R2 & R3 & R4).
    assert (HN18' : rw rho3 N18 = brk0w m) by (rewrite R1; exact HN18).
    assert (HVK4 : VK rho0 brk0 (brk0 + 8192) rho3).
    { destruct HVK3 as [Hav Hrm]. split.
      - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; symmetry; apply R1 | intros l; symmetry; apply R2].
      - intros x Hx. rewrite (R3 x) by (unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0; unfold brk0 in Hx; exact Hx). apply Hrm. lia. }
    apply (erun1 (KxA (mg m) (B + 8192)) FUEL_M CUTS_M S19g E20g RsCut rho3 tp); [exact run_19g | apply STx | exact Xl19g |].
    intros rho4 Hag4. rewrite Xn19g in Hag4.
    apply (eseg_grow rho0 tp rho4 HSP0).
    + rewrite <- (proj1 Hag4 N18) by plia. exact HN18'.
    + split; [unfold brk0; exact Hceil | exact Hfree].
    + exact Hwf.
    + eapply VK_agree; [| exact HVK4 | exact Hag4]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag4)). apply R4. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0. unfold brk0 in Ha. lia. }
  apply (erun1 (KxA m B) FUEL_M CUTS_M S19f E20f RsCut rho2 tp); [exact run_19f | apply STx | exact Xl19f |].
  intros rho3 Hag3. rewrite Xn19f in Hag3.
  assert (HVK4 : VK rho0 0 0 rho3) by (eapply VK_agree; [| exact HVK3 | exact Hag3]; plia).

  eapply etriple_seq; [apply (enode20f_any okT OKF_triv OKP_triv m B Hres HB Htop Hband rho3 tp (VK_sp _ _ _ _ _ HVK4 HSP0))|].
  apply etriple_disj.
  -
    apply (erun1 (KxA m B) FUEL_M CUTS_M (refuse E20f) RET0a RsSymJump rho3 tp); [exact run_20f_fail | apply STx | exact Xl20r |].
    intros rho4 Hag4. rewrite Xn20r in Hag4.
    eapply etriple_entailsA; [exact ent_RET0a | exact wid_RET0a | apply STx |].
    assert (HVK5 : VK rho0 0 0 (rho_sub rho4 (post_sub RET0a []))).
    { apply (VK_sub _ _ _ _ _ wid_RET0a). eapply VK_agree; [| exact HVK4 | exact Hag4]. plia. }
    apply (epost_fin (KxA m B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK5)].
    intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK5)|].
    exists O0_refused. split; [exact I|]. split; [exact (proj2 HVK5)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply etriple_ex. intros a. apply etriple_pure. intros Hpl.
    assert (HVK5 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho20f rho3 a)).
    { unfold rho20f. apply VK_set_rw; [plia|]. apply VK_set_rm; [eapply VK_widen; [| exact HVK4]; intros z Hz; lia|].
      intros x Hx. apply unmap_range_outside. change (bv_unsigned n8w) with 8192. exact Hx. }
    apply (erun1 (KxA (mf_res m a) B) FUEL_M CUTS_M S20f E21f RsCut (rho20f rho3 a) tp); [exact run_20f | apply STx | exact Xl20 |].
    intros rho4 Hag4. rewrite Xn20 in Hag4.
    assert (Ha : rw rho4 (Pos.succ N18) = a) by (rewrite <- (proj1 Hag4 (Pos.succ N18)) by plia; unfold rho20f; apply rho_set_rw_at).
    assert (HVK6 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) rho4) by (eapply VK_agree; [| exact HVK5 | exact Hag4]; plia).

    eapply etriple_seq; [apply (enode21f_any okT OKF_triv OKP_triv m B Hres HB Htop Hband Hlz Hlim rho4 tp a Ha (VK_sp _ _ _ _ _ HVK6 HSP0) Hpl Htp)|].
    apply etriple_disj.
    +
      apply (erun1 (KxA (mf_res m a) B) FUEL_M CUTS_M (refuse E21f) RET0b RsSymJump rho4 tp); [exact run_21f_fail | apply STx | exact Xl21r |].
      intros rho5 Hag5. rewrite Xn21r in Hag5.
      eapply etriple_entailsA; [exact ent_RET0b | exact wid_RET0b | apply STx |].
      assert (HVK7 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho5 (post_sub RET0b []))).
      { apply (VK_sub _ _ _ _ _ wid_RET0b). eapply VK_agree; [| exact HVK6 | exact Hag5]. plia. }
      apply (epost_fin (KxA (mf_res m a) B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK7)].
      intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK7)|].
      exists (O0_reserved a). split; [exact Hpl|]. split; [exact (proj2 HVK7)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
    +
      apply (erun1 (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M S21f E22f RsCut rho4 tp); [exact run_21f | apply STx | exact Xl21 |].
      intros rho5 Hag5. rewrite Xn21 in Hag5.
      apply (etail_fail rho0 tp a rho5 HSP0 Hpl).
      * rewrite <- (proj1 Hag5 (Pos.succ N18)) by plia. exact Ha.
      * eapply VK_agree; [| exact HVK6 | exact Hag5]. plia.
Qed.

Theorem musl_malloc40_sum_ex : ltac2:(tb__ "0|0|
S5S14S21Q40A1A1S8cS4S2bS4S7cVm;VB;A2S93R2R1A5S6cS4S24R2R1S77Vm;VB;A2A5A3Ftp;Frho;").
Proof.
  intros rho tp w HP. destruct w as [tr [ms md]].
  pose proof HP as [(Hsm & HMI & _) ((Htr & Hem & Hpaid) & HSP0)].
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _).
  apply (musl_malloc40_main_ex rho tp); [| | exact HSP0 | exact (conj (proj1 HP) (proj1 (proj2 HP)))].
  - cbn [cfg_model snd] in HMI. intros p Hp. destruct (MI_tp_in_maps segsA _ _ HMI p Hp) as (Hal' & b & s0 & Hin & Hb). split; [exact Hal'|].
    exists b, s0. rewrite <- Evm. split; [exact Hin | exact Hb].
  - cbn [cfg_model snd] in HMI. rewrite <- Evm. exact (proj1 (MI_ivs_wf segsA _ _ HMI)).
Qed.
End Assembly.

Theorem musl_malloc40_sum_A : musl_malloc40_sum_stmt.
Proof. intros ok m B OKF OKP HM rho tp. exact (musl_malloc40_sum ok OKF OKP m B HM rho tp). Qed.

Theorem musl_malloc40_sum_ex_A : musl_malloc40_sum_ex_stmt.
Proof. intros m B HM rho tp. exact (musl_malloc40_sum_ex m B HM rho tp). Qed.
End MuslMalloc40.

