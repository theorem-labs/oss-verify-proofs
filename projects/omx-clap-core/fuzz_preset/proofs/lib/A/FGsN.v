(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/FGsN.v (commit 67deba317dfb, blob ae60d91e3bc3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 11 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (1 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFhy AFhz AFkp AFk6 AFk8 AFk9.
Import ListNotations. Open Scope Z_scope.

Definition A_EFA : Z := 0x35474.
Definition A_EFA_RET : Z := 0x35574.
Definition A_RTA_EFA : Z := 0x352b0.

Definition REGSF : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SLit A_ALLOCATOR)) 11%bv (SOff rRG 0))
  12%bv (SOff rRB 0)) 13%bv (SOff rNFe 0).

Definition R_TJF : YP09.region := YP09.mkRegion (Some rT) 2768 2800 2768 2800 [YP09.mkChunk 2784 (CVal 8 (SOff rJSM 0))].

Definition R_PF : YP09.region := YP09.mkRegion (Some rP) 0 16 0 16 [YP09.mkChunk 0 (CVal 4 (SOff rN 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))].

Definition LOCKV : Z := 2 ^ 60.

Definition R_RGF : YP09.region := YP09.mkRegion (Some rRG) 0 128 0 128
  [YP09.mkChunk 0 (CVal 8 (SLit LOCKV)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SOff rNF 0));
   YP09.mkChunk 24 (CVal 8 (SOff rMF 0)); YP09.mkChunk 32 (CVal 8 (SOff rAU 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
   YP09.mkChunk 48 (CVal 8 (SOff rMU 0)); YP09.mkChunk 56 (CVal 8 (SLit 0)); YP09.mkChunk 68 (CVal 1 (SOff rJ64 0));
   YP09.mkChunk 80 (CVal 8 (SOff rJNA 0)); YP09.mkChunk 88 (CVal 8 (SOff rJNF 0))].
Definition TAILF : smem := firstn 32 (tl REG0R3) ++ [R_TJF; nth 34 REG0R3 R_TJF; R_PF; R_RGF] ++ skipn 37 REG0R3.
Definition REG0F : smem := YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 [] :: TAILF.
Definition SSF : sstate := mkSS A_EFA REGSF REG0F None FR3.

Lemma TAILF_skel : skeleton TAILF = skeleton (tl REG0R3).
Proof. vm_compute. reflexivity. Qed.

Definition F_D : sstate := Eval vm_compute in runto 0x35498 SSF.
Definition F_RN : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_GEU true (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) F_D).

Definition F_1 : sstate := Eval vm_compute in pin (runto 0x354b0 (arm BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) F_D)) 8%bv (SOff rMF2 0).
Definition F_2 : sstate := Eval vm_compute in pin (runto 0x354d0 (arm BC_GEU false (SOff rMF2 0) (SLit 536870913) (runto 0x354b8 F_1))) 9%bv (SOff rFADR 0).
Definition F_3 : sstate := Eval vm_compute in pin (runto 0x35500 F_2) 18%bv (SLit 262144).
Definition F_4 : sstate := Eval vm_compute in runto 0x6f208 F_3.
Definition F_N : sstate := Eval vm_compute in runtoC 0x7ffffff0 F_4.

Definition F_Ng : sstate := Eval vm_compute in setpc (pin F_N 10%bv (SOff rFADR 0)) 0x652c0.
Definition F_G1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 F_Ng.
Definition F_G2 : sstate := Eval vm_compute in runto 0x7ffffff0 F_G1.
Definition F_MS : sstate := Eval vm_compute in pin (pin F_G2 10%bv (SOff rSHF 0)) 12%bv (SLit 32768).
Definition F_G3 : sstate := Eval vm_compute in ss_after_stretch F_MS (ss_mem F_MS) hMSF CLOB_MS 0x35530.
Definition F_RG : sstate := Eval vm_compute in runto 0x7ffffff0 F_G3.
