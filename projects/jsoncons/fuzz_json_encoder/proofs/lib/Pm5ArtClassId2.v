(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib As0Tables ArtMem ArtRegs ArtAtomics ArtTac Pm5ArtClassId.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5b000_5c000.
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

(* [comment removed for export] *)
Definition art_cid2_kept (r : reg) : Prop :=
  r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.

Lemma art_classid2_hi_run : forall regs (M rom : word -> option byte) (s : word),
  getr regs 19 = s ->
  exists regs',
    msteps ASEGS (mkst regs (0x5b6ac : word) M rom) (mkst regs' (0x5b788 : word) M rom)
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
      stepn F_5b664 D_5b664. rwH. rewrite <- E1.
      stepn F_5b668 D_5b668.
      stepn F_5b66c D_5b66c.
      stepn F_5b670 D_5b670.
      stepn F_5b674 D_5b674.
      stepn F_5b678 D_5b678. rwH. rewrite <- E2.
      stepn F_5b67c D_5b67c.
      stepn F_5b680 D_5b680.
      stepn F_5b684 D_5b684.
      stepn F_5b688 D_5b688.
      stepn F_5b68c D_5b68c. rwH. rewrite <- E3.
      stepn F_5b690 D_5b690. rwH. rewrite <- E4.
      stepn F_5b694 D_5b694.
      stepn F_5b698 D_5b698.
      stepn F_5b69c D_5b69c.
      stepn F_5b6a0 D_5b6a0.
      stepn F_5b6a4 D_5b6a4.
      stepn F_5b6a8 D_5b6a8.
      stepn F_5b6ac D_5b6ac.
      stepn F_5b6b0 D_5b6b0.
      stepn F_5b6b4 D_5b6b4. rwH. rewrite <- E5.
      stepn F_5b6b8 D_5b6b8. rwH. rewrite <- E6.
      stepn F_5b6bc D_5b6bc. rwH. rewrite <- E7.
      stepn F_5b6c0 D_5b6c0. rwH. rewrite <- E8.
      stepn F_5b6c4 D_5b6c4. rwH. rewrite <- E9.
      stepn F_5b6c8 D_5b6c8. rwH. rewrite <- E10.
      stepn F_5b6cc D_5b6cc. rwH. rewrite <- E11.
      stepn F_5b6d0 D_5b6d0. rwH. rewrite <- E12.
      stepn F_5b6d4 D_5b6d4. rwH. rewrite <- E13.
      stepn F_5b6d8 D_5b6d8. rwH. rewrite <- E14.
      stepn F_5b6dc D_5b6dc. rwH. rewrite <- E15.
      stepn F_5b6e0 D_5b6e0. rwH. rewrite <- E16.
      stepn F_5b6e4 D_5b6e4. rwH. rewrite <- E17.
      stepn F_5b6e8 D_5b6e8. rwH. rewrite <- E18.
      stepn F_5b6ec D_5b6ec. rwH. rewrite <- E19.
      stepn F_5b6f0 D_5b6f0. rwH. rewrite <- E20.
      stepn F_5b6f4 D_5b6f4. rwH. rewrite <- E21.
      stepn F_5b6f8 D_5b6f8. rwH. rewrite <- E22.
      stepn F_5b6fc D_5b6fc.
      stepn F_5b700 D_5b700. rwH. rewrite <- E23.
      stepn F_5b704 D_5b704.
      stepn F_5b708 D_5b708. rwH. rewrite <- E24.
      stepn F_5b70c D_5b70c. rwH. rewrite <- E25.
      stepn F_5b710 D_5b710. rwH. rewrite <- E26.
      stepn F_5b714 D_5b714. rwH. rewrite <- E27.
      stepn F_5b718 D_5b718. rwH. rewrite <- E28.
      stepn F_5b71c D_5b71c. rwH. rewrite <- E29.
      stepn F_5b720 D_5b720. rwH. rewrite <- E30.
      stepn F_5b724 D_5b724. rwH. rewrite <- E31.
      stepn F_5b728 D_5b728. rwH. rewrite <- E32.
      stepn F_5b72c D_5b72c. rwH. rewrite <- E33.
      stepn F_5b730 D_5b730. rwH. rewrite <- E34.
      stepn F_5b734 D_5b734. rwH. rewrite <- E35.
      stepn F_5b738 D_5b738. rwH. rewrite <- E36.
      stepn F_5b73c D_5b73c. rwH. rewrite <- E37.
      apply mst_refl.
  - gres. subst. reflexivity.
  - intros r (N1 & N2 & N3 & N4 & N5 & N6). kept_solve.
Qed.
End FPX.
