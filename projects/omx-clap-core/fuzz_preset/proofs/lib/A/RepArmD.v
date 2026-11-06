(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepArmD.v (commit eb934de95d13, blob 8e194537c091) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 24 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFhy AFhz YFkpcf YFk6cf YFk8cf.
Import ListNotations. Open Scope Z_scope.

Definition addreg (r : YP09.region) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition RGOT : YP09.region :=
  YP09.mkRegion None 0xa2048 0xa2050 0 0 [YP09.mkChunk 0xa2048 (CVal 8 (SLit 0xa3ed8))].
Definition RTNM : YP09.region :=
  YP09.mkRegion None 0xa3ed8 0xa3ee0 0 0 [YP09.mkChunk 0xa3ed8 (CVal 8 (SLit 0x20443))].
Definition RNUL : YP09.region := YP09.mkRegion None 0 0 0 0 [].

Definition R3_XA : sstate := Eval vm_compute in arm BC_GEU true (SOff rMU 262144) (SLit 3758096385) R3_M4.
Definition R3_X : sstate := Eval vm_compute in runto 0x7ffffff0 R3_XA.

Definition R3_XN : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_EQ false (SOff rJEX 0) (SLit 0) R3_X).

Definition R3_XT : sstate :=
  Eval vm_compute in addreg RTNM (addreg RGOT (arm BC_EQ true (SOff rJEX 0) (SLit 0) R3_X)).
Definition R3_XP : sstate := Eval vm_compute in runto 0x67e38 R3_XT.

Definition STKC : YP09.region :=
  Eval vm_compute in match nth_error (ss_mem R3_XP) 2 with Some r => trim_lo r (-224) | None => RNUL end.
Definition R3_XC1 : sstate := Eval vm_compute in ss_after_call R3_XP [STKC] 112 0x37a9c.
Definition R3_XC1b : sstate := Eval vm_compute in runto 0x7ffffff0 R3_XC1.
Definition R3_XK31 : sstate :=
  Eval vm_compute in noconds (pin (runto 0x7ffffff0 (arm BC_EQ true (SOff rCL 0) (SLit 31) R3_XC1b)) 13%bv (SOff rCSZ 0)).
Definition R3_XC0 : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_XC1b).
Definition R3_XK16 : sstate :=
  Eval vm_compute in noconds (pin (runto 0x7ffffff0 (arm BC_LTU false (SLit 16) (SOff rCL 0) R3_XC0)) 13%bv (SOff rCSZ 0)).
Definition R3_XKM : sstate :=
  Eval vm_compute in noconds (pin (runto 0x7ffffff0 (arm BC_LTU true (SLit 16) (SOff rCL 0) R3_XC0)) 13%bv (SOff rCSZ 0)).

Lemma rep_arm_stops :
ss_pc R3_X = 0x37a3c /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_XA) = RS_stopped (SR_branch BC_EQ (SOff rJEX 0) (SLit 0)) /\
sr_get (ss_regs R3_X) 10%bv = SOff rJEX 0 /\
ss_pc R3_XN = 0x37400 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (arm BC_EQ false (SOff rJEX 0) (SLit 0) R3_X))
  = RS_stopped (SR_jalr (SOff 1 0)) /\
ss_resv R3_XN = None /\
sr_get (ss_regs R3_XN) 10%bv = SLit 0 /\ sr_get (ss_regs R3_XN) 1%bv = SOff 1 0 /\
sr_get (ss_regs R3_XN) 4%bv = SLit TFIB_TP /\
Forall (fun r : bv 5 => sr_get (ss_regs R3_XN) r = SOff (Z.to_nat (bv_unsigned r)) 0)
  [2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv /\
(exists cs, nth_error (ss_mem R3_XN) 0 = Some (YP09.mkRegion (Some 2%nat) (-1024) 0 (-1024) 0 cs)) /\
YP09.region_wf RGOT = true /\ YP09.region_wf RTNM = true /\
ss_pc R3_XP = 0x67e38 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_XT) = RS_stopped SR_fetch /\
sr_get (ss_regs R3_XP) 10%bv = SLit 0x1ea2c /\ sr_get (ss_regs R3_XP) 11%bv = SLit 0x20443 /\
sr_get (ss_regs R3_XP) 1%bv = SLit 0x37a9c /\ sr_get (ss_regs R3_XP) 2%bv = SOff 2 (-224) /\
sr_get (ss_regs R3_XP) 3%bv = SOff 3 0 /\ sr_get (ss_regs R3_XP) 4%bv = SLit TFIB_TP /\
sr_get (ss_regs R3_XP) 8%bv = SOff rCL 0 /\ ss_resv R3_XP = None /\
YP09.r_base STKC = Some 2%nat /\ YP09.r_lo STKC = -224 /\ YP09.r_hi STKC = 0 /\
ss_pc R3_XC1 = 0x37a9c /\ ss_resv R3_XC1 = None /\
ss_atoms_lt 112 R3_XP = true /\ regions_wf [STKC] = true /\ no_cdata [STKC] = true /\ mem_atoms_lt 112 [STKC] = true /\
ss_pc R3_XC1b = 0x37aa4 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_XC1) = RS_stopped (SR_branch BC_EQ (SOff rCL 0) (SLit 31)) /\
ss_pc R3_XC0 = 0x37aac /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_XC1b))
  = RS_stopped (SR_branch BC_LTU (SLit 16) (SOff rCL 0)) /\
ss_pc R3_XK31 = 0x67e38 /\ ss_pc R3_XK16 = 0x67e38 /\ ss_pc R3_XKM = 0x67e38 /\
sr_get (ss_regs R3_XK16) 10%bv = SLit 0x202f7 /\ sr_get (ss_regs R3_XK16) 11%bv = SLit 4096 /\
sr_get (ss_regs R3_XK16) 12%bv = SOff rCL 0 /\ sr_get (ss_regs R3_XK16) 13%bv = SOff rCSZ 0 /\
sr_get (ss_regs R3_XK16) 1%bv = SLit 0x37b10 /\ sr_get (ss_regs R3_XK16) 2%bv = SOff 2 (-224) /\
sr_get (ss_regs R3_XK16) 3%bv = SOff 3 0 /\ sr_get (ss_regs R3_XK16) 4%bv = SLit TFIB_TP /\
ss_resv R3_XK16 = None.
Proof.
vm_compute. repeat apply conj; try reflexivity;
try (eexists; reflexivity);
try (repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil).
Qed.

Lemma rep_arm_join : R3_XK31 = R3_XK16 /\ R3_XKM = R3_XK16.
Proof. split; vm_compute; reflexivity. Qed.
