(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecF.v (commit 67deba317dfb, blob d31e0e8fef71) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrecM DMrecT5 DMrecT6.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem dorecycle_ok_r : forall B ARXr AOX DRq RMAXD, DMwalkIFA.dorecycle_ok_t B ARXr AOX DRq RMAXD.
Proof.
intros B ARXr AOX DRq RMAXD TB HRM FR RV RCH CDH inst ly X P W regs mem md PRE.
pose proof PRE as (_ & Hinst & _). subst inst.
exact (DMrecM.dorecycle_arm_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE
  (DMrecT5.T_R_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE)
  (DMrecT6.T_O0_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE) RCH CDH).
Qed.
End c.
Print Assumptions dorecycle_ok_r.
