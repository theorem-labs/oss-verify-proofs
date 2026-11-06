(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtClassId.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Ltac art_step F D :=
  stepn F D;
  try (lazymatch goal with
       | |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ =>
           lazymatch v with
           | Z_to_bv 64 ?z => is_Z_lit z
           | _ => let x := fresh "x" in remember v as x
           end
       end).

Section FPX. Context {fx : PropExec.FPState}.

Definition art_cid2_kept (r : reg) : Prop :=
  r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.

#[using="Type"] Lemma art_classid2_hi_run : forall regs (M rom : word -> option byte) (s : word),
  getr regs 19 = s ->
  exists regs',
    msteps ASEGS (mkst regs (0x53ba8 : word) M rom) (mkst regs' (0x53c84 : word) M rom)
    /\ getr regs' 11 = art_cid_w s
    /\ (forall r : reg, art_cid2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom s H19.
  pose (x1 := (v_srli s (1)%Z)). assert (E1 : x1 = (v_srli s (1)%Z)) by reflexivity. clearbody x1.
  pose (x2 := (v_or s x1)). assert (E2 : x2 = (v_or s x1)) by reflexivity. clearbody x2.
  pose (x3 := (v_srli x2 (2)%Z)). assert (E3 : x3 = (v_srli x2 (2)%Z)) by reflexivity. clearbody x3.
  pose (x4 := (v_or x2 x3)). assert (E4 : x4 = (v_or x2 x3)) by reflexivity. clearbody x4.
  pose (x5 := (v_srli x4 (4)%Z)). assert (E5 : x5 = (v_srli x4 (4)%Z)) by reflexivity. clearbody x5.
  pose (x6 := (v_or x4 x5)). assert (E6 : x6 = (v_or x4 x5)) by reflexivity. clearbody x6.
  pose (x7 := (v_srli x6 (8)%Z)). assert (E7 : x7 = (v_srli x6 (8)%Z)) by reflexivity. clearbody x7.
  pose (x8 := (v_or x6 x7)). assert (E8 : x8 = (v_or x6 x7)) by reflexivity. clearbody x8.
  pose (x9 := (v_srli x8 (16)%Z)). assert (E9 : x9 = (v_srli x8 (16)%Z)) by reflexivity. clearbody x9.
  pose (x10 := (v_or x8 x9)). assert (E10 : x10 = (v_or x8 x9)) by reflexivity. clearbody x10.
  pose (x11 := (v_srli x10 (32)%Z)). assert (E11 : x11 = (v_srli x10 (32)%Z)) by reflexivity. clearbody x11.
  pose (x12 := (v_or x10 x11)). assert (E12 : x12 = (v_or x10 x11)) by reflexivity. clearbody x12.
  pose (x13 := (v_xori x12 (-1)%Z)). assert (E13 : x13 = (v_xori x12 (-1)%Z)) by reflexivity. clearbody x13.
  pose (x14 := (v_srli x13 (1)%Z)). assert (E14 : x14 = (v_srli x13 (1)%Z)) by reflexivity. clearbody x14.
  pose (x15 := (v_and x14 (Z_to_bv 64 6148914691236517205))). assert (E15 : x15 = (v_and x14 (Z_to_bv 64 6148914691236517205))) by reflexivity. clearbody x15.
  pose (x16 := (v_sub x13 x15)). assert (E16 : x16 = (v_sub x13 x15)) by reflexivity. clearbody x16.
  pose (x17 := (v_and x16 (Z_to_bv 64 3689348814741910323))). assert (E17 : x17 = (v_and x16 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x17.
  pose (x18 := (v_srli x16 (2)%Z)). assert (E18 : x18 = (v_srli x16 (2)%Z)) by reflexivity. clearbody x18.
  pose (x19 := (v_and x18 (Z_to_bv 64 3689348814741910323))). assert (E19 : x19 = (v_and x18 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x19.
  pose (x20 := (v_add x17 x19)). assert (E20 : x20 = (v_add x17 x19)) by reflexivity. clearbody x20.
  pose (x21 := (v_srli x20 (4)%Z)). assert (E21 : x21 = (v_srli x20 (4)%Z)) by reflexivity. clearbody x21.
  pose (x22 := (v_add x20 x21)). assert (E22 : x22 = (v_add x20 x21)) by reflexivity. clearbody x22.
  pose (x23 := (v_and x22 (Z_to_bv 64 1085102592571150095))). assert (E23 : x23 = (v_and x22 (Z_to_bv 64 1085102592571150095))) by reflexivity. clearbody x23.
  pose (x24 := (v_mul x23 (Z_to_bv 64 72340172838076673))). assert (E24 : x24 = (v_mul x23 (Z_to_bv 64 72340172838076673))) by reflexivity. clearbody x24.
  pose (x25 := (v_srli x24 (56)%Z)). assert (E25 : x25 = (v_srli x24 (56)%Z)) by reflexivity. clearbody x25.
  pose (x26 := (v_subw (Z_to_bv 64 62) x25)). assert (E26 : x26 = (v_subw (Z_to_bv 64 62) x25)) by reflexivity. clearbody x26.
  pose (x27 := (v_slli x25 (1)%Z)). assert (E27 : x27 = (v_slli x25 (1)%Z)) by reflexivity. clearbody x27.
  pose (x28 := (v_srl s x26)). assert (E28 : x28 = (v_srl s x26)) by reflexivity. clearbody x28.
  pose (x29 := (v_sllw (Z_to_bv 64 18446744073709551615) x26)). assert (E29 : x29 = (v_sllw (Z_to_bv 64 18446744073709551615) x26)) by reflexivity. clearbody x29.
  pose (x30 := (v_xori x27 (126)%Z)). assert (E30 : x30 = (v_xori x27 (126)%Z)) by reflexivity. clearbody x30.
  pose (x31 := (v_andi x28 (1)%Z)). assert (E31 : x31 = (v_andi x28 (1)%Z)) by reflexivity. clearbody x31.
  pose (x32 := (v_xori x29 (-1)%Z)). assert (E32 : x32 = (v_xori x29 (-1)%Z)) by reflexivity. clearbody x32.
  pose (x33 := (v_and s x32)). assert (E33 : x33 = (v_and s x32)) by reflexivity. clearbody x33.
  pose (x34 := (v_or x30 x31)). assert (E34 : x34 = (v_or x30 x31)) by reflexivity. clearbody x34.
  pose (x35 := (v_sltu (Z_to_bv 64 0) x33)). assert (E35 : x35 = (v_sltu (Z_to_bv 64 0) x33)) by reflexivity. clearbody x35.
  pose (x36 := (v_add x34 x35)). assert (E36 : x36 = (v_add x34 x35)) by reflexivity. clearbody x36.
  pose (x37 := (v_addi x36 (-2)%Z)). assert (E37 : x37 = (v_addi x36 (-2)%Z)) by reflexivity. clearbody x37.
  eexists. split; [|split].
  - rwH.
      stepn F_53b58 D_53b58. rwH. rewrite <- E1.
      stepn F_53b5c D_53b5c.
      stepn F_53b60 D_53b60.
      stepn F_53b64 D_53b64.
      stepn F_53b68 D_53b68.
      stepn F_53b6c D_53b6c. rwH. rewrite <- E2.
      stepn F_53b70 D_53b70.
      stepn F_53b74 D_53b74.
      stepn F_53b78 D_53b78.
      stepn F_53b7c D_53b7c.
      stepn F_53b80 D_53b80. rwH. rewrite <- E3.
      stepn F_53b84 D_53b84. rwH. rewrite <- E4.
      stepn F_53b88 D_53b88.
      stepn F_53b8c D_53b8c.
      stepn F_53b90 D_53b90.
      stepn F_53b94 D_53b94.
      stepn F_53b98 D_53b98.
      stepn F_53b9c D_53b9c.
      stepn F_53ba0 D_53ba0.
      stepn F_53ba4 D_53ba4.
      stepn F_53ba8 D_53ba8. rwH. rewrite <- E5.
      stepn F_53bac D_53bac. rwH. rewrite <- E6.
      stepn F_53bb0 D_53bb0. rwH. rewrite <- E7.
      stepn F_53bb4 D_53bb4. rwH. rewrite <- E8.
      stepn F_53bb8 D_53bb8. rwH. rewrite <- E9.
      stepn F_53bbc D_53bbc. rwH. rewrite <- E10.
      stepn F_53bc0 D_53bc0. rwH. rewrite <- E11.
      stepn F_53bc4 D_53bc4. rwH. rewrite <- E12.
      stepn F_53bc8 D_53bc8. rwH. rewrite <- E13.
      stepn F_53bcc D_53bcc. rwH. rewrite <- E14.
      stepn F_53bd0 D_53bd0. rwH. rewrite <- E15.
      stepn F_53bd4 D_53bd4. rwH. rewrite <- E16.
      stepn F_53bd8 D_53bd8. rwH. rewrite <- E17.
      stepn F_53bdc D_53bdc. rwH. rewrite <- E18.
      stepn F_53be0 D_53be0. rwH. rewrite <- E19.
      stepn F_53be4 D_53be4. rwH. rewrite <- E20.
      stepn F_53be8 D_53be8. rwH. rewrite <- E21.
      stepn F_53bec D_53bec. rwH. rewrite <- E22.
      stepn F_53bf0 D_53bf0.
      stepn F_53bf4 D_53bf4. rwH. rewrite <- E23.
      stepn F_53bf8 D_53bf8.
      stepn F_53bfc D_53bfc. rwH. rewrite <- E24.
      stepn F_53c00 D_53c00. rwH. rewrite <- E25.
      stepn F_53c04 D_53c04. rwH. rewrite <- E26.
      stepn F_53c08 D_53c08. rwH. rewrite <- E27.
      stepn F_53c0c D_53c0c. rwH. rewrite <- E28.
      stepn F_53c10 D_53c10. rwH. rewrite <- E29.
      stepn F_53c14 D_53c14. rwH. rewrite <- E30.
      stepn F_53c18 D_53c18. rwH. rewrite <- E31.
      stepn F_53c1c D_53c1c. rwH. rewrite <- E32.
      stepn F_53c20 D_53c20. rwH. rewrite <- E33.
      stepn F_53c24 D_53c24. rwH. rewrite <- E34.
      stepn F_53c28 D_53c28. rwH. rewrite <- E35.
      stepn F_53c2c D_53c2c. rwH. rewrite <- E36.
      stepn F_53c30 D_53c30. rwH. rewrite <- E37.
      apply mst_refl.
  - gres. subst. reflexivity.
  - intros r (N1 & N2 & N3 & N4 & N5 & N6). kept_solve.
Qed.
End FPX.
