(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib As0Tables ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatClassId_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b.
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

#[using="Type"] Lemma art_classid2_hi_run : forall regs (M rom : word -> option byte) (s : word),
  getr regs 19 = s ->
  exists regs',
    msteps ASEGS (mkst regs (0x52b98 : word) M rom) (mkst regs' (0x52c74 : word) M rom)
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
      stepn F_52780 D_52780. rwH. rewrite <- E1.
      stepn F_52784 D_52784.
      stepn F_52788 D_52788.
      stepn F_5278c D_5278c.
      stepn F_52790 D_52790.
      stepn F_52794 D_52794. rwH. rewrite <- E2.
      stepn F_52798 D_52798.
      stepn F_5279c D_5279c.
      stepn F_527a0 D_527a0.
      stepn F_527a4 D_527a4.
      stepn F_527a8 D_527a8. rwH. rewrite <- E3.
      stepn F_527ac D_527ac. rwH. rewrite <- E4.
      stepn F_527b0 D_527b0.
      stepn F_527b4 D_527b4.
      stepn F_527b8 D_527b8.
      stepn F_527bc D_527bc.
      stepn F_527c0 D_527c0.
      stepn F_527c4 D_527c4.
      stepn F_527c8 D_527c8.
      stepn F_527cc D_527cc.
      stepn F_527d0 D_527d0. rwH. rewrite <- E5.
      stepn F_527d4 D_527d4. rwH. rewrite <- E6.
      stepn F_527d8 D_527d8. rwH. rewrite <- E7.
      stepn F_527dc D_527dc. rwH. rewrite <- E8.
      stepn F_527e0 D_527e0. rwH. rewrite <- E9.
      stepn F_527e4 D_527e4. rwH. rewrite <- E10.
      stepn F_527e8 D_527e8. rwH. rewrite <- E11.
      stepn F_527ec D_527ec. rwH. rewrite <- E12.
      stepn F_527f0 D_527f0. rwH. rewrite <- E13.
      stepn F_527f4 D_527f4. rwH. rewrite <- E14.
      stepn F_527f8 D_527f8. rwH. rewrite <- E15.
      stepn F_527fc D_527fc. rwH. rewrite <- E16.
      stepn F_52800 D_52800. rwH. rewrite <- E17.
      stepn F_52804 D_52804. rwH. rewrite <- E18.
      stepn F_52808 D_52808. rwH. rewrite <- E19.
      stepn F_5280c D_5280c. rwH. rewrite <- E20.
      stepn F_52810 D_52810. rwH. rewrite <- E21.
      stepn F_52814 D_52814. rwH. rewrite <- E22.
      stepn F_52818 D_52818.
      stepn F_5281c D_5281c. rwH. rewrite <- E23.
      stepn F_52820 D_52820.
      stepn F_52824 D_52824. rwH. rewrite <- E24.
      stepn F_52828 D_52828. rwH. rewrite <- E25.
      stepn F_5282c D_5282c. rwH. rewrite <- E26.
      stepn F_52830 D_52830. rwH. rewrite <- E27.
      stepn F_52834 D_52834. rwH. rewrite <- E28.
      stepn F_52838 D_52838. rwH. rewrite <- E29.
      stepn F_5283c D_5283c. rwH. rewrite <- E30.
      stepn F_52840 D_52840. rwH. rewrite <- E31.
      stepn F_52844 D_52844. rwH. rewrite <- E32.
      stepn F_52848 D_52848. rwH. rewrite <- E33.
      stepn F_5284c D_5284c. rwH. rewrite <- E34.
      stepn F_52850 D_52850. rwH. rewrite <- E35.
      stepn F_52854 D_52854. rwH. rewrite <- E36.
      stepn F_52858 D_52858. rwH. rewrite <- E37.
      apply mst_refl.
  - gres. subst. reflexivity.
  - intros r (N1 & N2 & N3 & N4 & N5 & N6). kept_solve.
Qed.
End FPX.
