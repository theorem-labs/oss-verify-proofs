(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan-ubsan image B), a Theorem Labs lane MnPrefix: the named premise
   H_memnorm_drv_B of the driver loop (lib/AU/PresetD1rB.v:80, the loop's three runner segments vp_run / br_run /
   l2_run with memnorm on the full overlay at both ends), PROVED. Each conjunct is the memnorm twin of the core segment
   (lib/Reusable/YD2mnSeg.v vp_run_mn / br_run_mn / l2_run_mn) at P := YAkMemnorm.memnorm tfibsegs, whose laws are
   YSRrMemnorm.srr_inv_laws_memnorm_k.
   rule 24: no function proved. rule 24: proves no function (kind: driver-layer keep re-run). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2mnSeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1rB.

Theorem H_memnorm_drv_B_holds : PresetD1rB.H_memnorm_drv_B.
Proof.
intros fx. split; [|split].
- intros E W regs mem md HS HMN.
  exact (YD2mnSeg.vp_run_mn _ (YSRrMemnorm.srr_inv_laws_memnorm_k _) E W regs mem md HS HMN).
- intros E W regs mem md HS HMN.
  exact (YD2mnSeg.br_run_mn _ (YSRrMemnorm.srr_inv_laws_memnorm_k _) E W regs mem md HS HMN).
- intros E W ms md HS HMN.
  exact (YD2mnSeg.l2_run_mn _ (YSRrMemnorm.srr_inv_laws_memnorm_k _) E W ms md HS HMN).
Qed.

Print Assumptions H_memnorm_drv_B_holds.
