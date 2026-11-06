(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan image A), a Theorem Labs lane MnPrefix: the named premise
   H_memnorm_drv_A of the driver loop (lib/A/PresetD1rA.v:80, the loop's three runner segments vp_run / br_run /
   l2_run with memnorm on the full overlay at both ends), PROVED. Each conjunct is the memnorm twin of the core segment
   (lib/A/AD2mnSeg.v vp_run_mn / br_run_mn / l2_run_mn) at P := YAkMemnorm.memnorm tfibsegs, whose laws are
   YSRrMemnorm.srr_inv_laws_memnorm_k.
   rule 24: no function proved. rule 24: proves no function (kind: driver-layer keep re-run). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2mnSeg PresetD1rA.

Theorem H_memnorm_drv_A_holds : PresetD1rA.H_memnorm_drv_A.
Proof.
intros fx. split; [|split].
- intros E W regs mem md HS HMN.
  exact (AD2mnSeg.vp_run_mn _ (YSRrMemnorm.srr_inv_laws_memnorm_k _) E W regs mem md HS HMN).
- intros E W regs mem md HS HMN.
  exact (AD2mnSeg.br_run_mn _ (YSRrMemnorm.srr_inv_laws_memnorm_k _) E W regs mem md HS HMN).
- intros E W ms md HS HMN.
  exact (AD2mnSeg.l2_run_mn _ (YSRrMemnorm.srr_inv_laws_memnorm_k _) E W ms md HS HMN).
Qed.

Print Assumptions H_memnorm_drv_A_holds.
