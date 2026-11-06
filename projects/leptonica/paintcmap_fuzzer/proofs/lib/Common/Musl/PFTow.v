(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import MuslTac .
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := rl_segs.
Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition tow_mem (mem : word -> option byte) (f B : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (f + 136)) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 (f + 56)) (W8 B))
    (Z_to_bv 64 (f + 8)) (W8 0))
    (Z_to_bv 64 (f + 16)) (W8 0))
    (Z_to_bv 64 (f + 32)) (W8 (B + 80)))
    (Z_to_bv 64 (f + 40)) (W8 B).
End GD_1.

Section TOW.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL}.
  Variables (mem rom : word -> option byte) (f B : Z).
  Hypotheses (Hf0 : (0 <= f)%Z) (Hf1 : (f + 232 < 2^64)%Z) (HB0 : (0 <= B)%Z) (HB1 : (B + 80 < 2^64)%Z).
  Hypothesis Rmode : rdn SEGS mem (Z_to_bv 64 (f + 136)) 4 = Some (W4 0).
  Hypothesis Rflags : rdn SEGS mem (Z_to_bv 64 f) 4 = Some (W4 0).
  Hypothesis Rbuf : rdn SEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (W8 B).
  Hypothesis Rbsz : rdn SEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (W8 80).
  Hypothesis SOK : store_ok SEGS mem (Z_to_bv 64 f) 232 = true.

  Ltac sok := store_ok_peel; eapply (store_ok_sub SEGS mem (Z_to_bv 64 f) _ 232);
              [u_norm; lia | exact SOK | u_norm; lia | u_norm; cbn; lia].

  Lemma towrite_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 f ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_17aec 0x17aec) mem rom) (mkst regs' ret (tow_mem mem f B) rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 0.
  Proof.
    intros regs ret Hret H1 H10.
    eexists. split.
    - stepLD F_17aec D_17aec (W4 0) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).  (* [comment removed for export] *)
      stepLD F_17af0 D_17af0 (W4 0) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).  (* [comment removed for export] *)
      stepn F_17af4 D_17af4.   (* [comment removed for export] *)
      stepn F_17af8 D_17af8.   (* [comment removed for export] *)
      stepn F_17afc D_17afc.   (* [comment removed for export] *)
      stepST F_17b00 D_17b00 (Z_to_bv 64 (f + 136)) (Z_to_bv 64 18446744073709551615) ltac:(sok).  (* [comment removed for export] *)
      stepb_ft F_17b04 D_17b04 ltac:(apply c_eq_refl).   (* [comment removed for export] *)
      stepLD8 F_17b08 D_17b08 (Z_to_bv 64 B).     (* [comment removed for export] *)
      stepLD8 F_17b0c D_17b0c (Z_to_bv 64 80).    (* [comment removed for export] *)
      stepST F_17b10 D_17b10 (Z_to_bv 64 (f + 56)) (Z_to_bv 64 B) ltac:(sok).   (* [comment removed for export] *)
      stepiv F_17b14 D_17b14 (Z_to_bv 64 (B + 80)) ltac:(gres; unfold v_add; unorm; reflexivity).   (* [comment removed for export] *)
      stepST F_17b18 D_17b18 (Z_to_bv 64 (f + 8)) (Z_to_bv 64 0) ltac:(sok).    (* [comment removed for export] *)
      stepST F_17b1c D_17b1c (Z_to_bv 64 (f + 16)) (Z_to_bv 64 0) ltac:(sok).   (* [comment removed for export] *)
      stepST F_17b20 D_17b20 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (B + 80)) ltac:(sok).   (* [comment removed for export] *)
      stepST F_17b24 D_17b24 (Z_to_bv 64 (f + 40)) (Z_to_bv 64 B) ltac:(sok).   (* [comment removed for export] *)
      stepn F_17b28 D_17b28.   (* [comment removed for export] *)
      stepret F_17b2c D_17b2c ret ltac:(exact H1).
      apply mst_refl.
    - split; [solve_keeps_cs | gres; reflexivity].
  Qed.
End TOW.
