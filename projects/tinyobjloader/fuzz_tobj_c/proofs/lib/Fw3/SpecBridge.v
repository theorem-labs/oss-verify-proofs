(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv"; "bv_extract"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_result"; "machine_state"; "MachineFault"; "MachineOk"; "width_bytes"; "MachineUnmodeled"; "decode_exec"; "decode_exec_accesses"; "drop_access_report"; "interp_eff"; "ov_read_bytes"; "step"; "store_ok"; "write_to_mem"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "option"; "prod"; "bool"; "list"; "pair"; "nil"; "@LinuxProcessSemantics.Riscv.Sem"; "core"; "eff"; "EDone"; "ELoad"; "EStore"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SpecBridge.WithSegs"; "interp_eff0"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vm_lazy"; "@Corelib.Numbers.BinNums"; "N"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "le_bytes_to_word"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mi_account_step"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Fixpoint interp_eff0 (t : eff) (m : word -> option byte)
    : machine_result (core * (word -> option byte)) :=
  match t with
  | EDone c => MachineOk (c, m)
  | EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
  | EIllegal _ | EEcall _ => MachineUnmodeled
  | ELoad n a k =>
      match ov_read_bytes segs m a (width_bytes n) with
      | Some bs => interp_eff0 (k (bv_extract 0 n (le_bytes_to_word bs))) m
      | None => MachineFault
      end
  | EStore n a v k =>
      if store_ok segs m a (width_bytes n)
      then interp_eff0 k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
      else MachineFault
  end.

Lemma interp_eff_interp_eff0 : ltac2:(tb__ "0|1|
S19S0Q40A1S12S0Q8A1A1F_;M0S11S3S13S18G0A2A1ScVsegs;R2R1A3S1dR2R1A2A3Fm;Ft;").
Proof using .
  unfold interp_eff.
  induction t; intros m; cbn; try reflexivity.
  -
    destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|reflexivity].
    rewrite <- (H _ m).
    destruct (interp_eff_accesses segs _ m) as [[v acc]| |]; reflexivity.
  -
    destruct (store_ok segs m a (width_bytes n)); [|reflexivity].
    rewrite <- (IHt _).
    destruct (interp_eff_accesses segs t _) as [[v' acc]| |]; reflexivity.
Qed.

Lemma interp_eff0_EDone : ltac2:(tb__ "0|2|
S18S0Q40A1S12S0Q8A1A1F_;M0S11S3S13S18G0A2M1A1S1dS1aR2A1R1A2S6G1S16S18G0R2R1A4A2A3Fm;Fc;").
Proof using . reflexivity. Qed.

Lemma interp_eff0_ELoad : ltac2:(tb__ "0|7|
S20S0Q40M0A1M1S0R2A1S19F_;G1S12S0Q8A1M2A1F_;M3S11S3S13S18G3A2M4A1M5S1dS1bR4R3R2A3R1A2S12S15G2A1M6A1G5Lx;SdVsegs;R1R3S7R4A1A4G6S1dR3S1G0Q0R5S22R1A1A4A1R2A2Lbs;S5G4A1X12x2A3Fm;Fk;Fa;Fn;").
Proof using . reflexivity. Qed.

Lemma interp_eff0_EStore : ltac2:(tb__ "0|5|
S20S0Q40A1M0S0R2A1S19G0S12S0Q8A1A1F_;M1S11S3S13S18G1A2M2A1M3S1dS1cR5R4R3R2A4R1A2S14G3L_;SfVsegs;R1R4S7R5A1M4A4S1dR2S10R1R4S21G4S2R5R3A2A2A3A2S5G2A1X14x2A3Fm;Fk;Fv;Fa;Fn;").
Proof using . reflexivity. Qed.

Lemma decode_exec_drop : ltac2:(tb__ "0|0|
S4S0Q20A1S11S3S4A1S9Vsegs;R2R1A3SbS4SaVsegs;R2R1A3A2A3Fw;Fst;").
Proof using . reflexivity. Qed.

Lemma mi_account_step_lazy_nil : ltac2:(tb__ "0|4|
S4S1eS11S15S13S0Q40A1M0G0A2M1A1S1fR1A1S17G1A1A3S11S3S13S4S1eA2M2A1M3S23Vsegs;R3R2A3S3S4A1G3Lx;SeVsegs;R3A2S4S6G2S16S4S1eR1R3A4A2Lms';S5G2A1S8G2A1X3x3A3F_;Fmd;Fms;").
Proof using . intros ms md H. apply mi_account_step_no_lazy. exact H. Qed.

End WithSegs.
