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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10438 8 0x218a392cd3d5dbf /\ cellA M 0x105c0 1 4 /\ cellA M 0x105e9 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x57c04 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_577ec D_577ec.
  zsd F_577f0 D_577f0 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10438 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105c0 1 4) by (unfold apart in *; recell R2).
  zstep F_577f4 D_577f4. zstep F_577f8 D_577f8. zstep F_577fc D_577fc.
  zbft F_57800 D_57800.
  zstep F_57804 D_57804. zstep F_57808 D_57808.
  zbft F_5780c D_5780c.
  zstep F_57810 D_57810. zstep F_57814 D_57814.
  zbft F_57818 D_57818.
  zstep F_5781c D_5781c. zstep F_57820 D_57820.
  zld F_57824 D_57824 0x10438 C1.
  zstep F_57828 D_57828. zstep F_5782c D_5782c. zstep F_57830 D_57830. zstep F_57834 D_57834. zstep F_57838 D_57838. zstep F_5783c D_5783c.
  zlbu F_57840 D_57840 0x105c0 C2.
  zstep F_57844 D_57844. zstep F_57848 D_57848.
  zbft F_5784c D_5784c.
  zstep F_57850 D_57850. zstep F_57854 D_57854.
  zbft F_57858 D_57858.
  zstep F_5785c D_5785c.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_57860 D_57860 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_57864 D_57864.
  stepret F_57868 D_57868 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x57c04 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_577ec D_577ec.
  zsd F_577f0 D_577f0 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10438 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105e9 1 11) by (unfold apart in *; recell R3).
  zstep F_577f4 D_577f4. zstep F_577f8 D_577f8. zstep F_577fc D_577fc.
  zbft F_57800 D_57800.
  zstep F_57804 D_57804. zstep F_57808 D_57808.
  zbft F_5780c D_5780c.
  zstep F_57810 D_57810. zstep F_57814 D_57814.
  zbft F_57818 D_57818.
  zstep F_5781c D_5781c. zstep F_57820 D_57820.
  zld F_57824 D_57824 0x10438 C1.
  zstep F_57828 D_57828. zstep F_5782c D_5782c. zstep F_57830 D_57830. zstep F_57834 D_57834. zstep F_57838 D_57838. zstep F_5783c D_5783c.
  zlbu F_57840 D_57840 0x105e9 C2.
  zstep F_57844 D_57844. zstep F_57848 D_57848.
  zbft F_5784c D_5784c.
  zstep F_57850 D_57850. zstep F_57854 D_57854.
  zbft F_57858 D_57858.
  zstep F_5785c D_5785c.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_57860 D_57860 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_57864 D_57864.
  stepret F_57868 D_57868 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
