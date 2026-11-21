(* Machine-generated data computed from the task's compiled program image (the start-up checker's hand-off states, collected by running the checker over the image); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states are fuzz_segconf.asan's own, collected by the start-up collector of tools/startup (the start-up tool set of record, hsform.py 9747a6731b7e) running the donor checker of proofs/cgif/cgif_file_fuzzer on this image with the plan of A/AB05.v probed for it; module paths changed; the comment line above is fuzz_command's (A/AB01.v). *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w); then made for LPS 727298f3 in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v: both computed in the build from the start-up run at the 16 GiB limit by check, per CONFIG_RSEQ flag, with BudgetWit/AW/PlanRegen_w.v (as A/AB01r.v), the plan's variables renumbered as in A/AB01r.v; split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's BudgetWit/AW/AB01r_wb.v, AB01r_w0.v and AB01r_w1.v (the hand-off states collected arm by arm of the continuation's first case split); the shape of reac-pw/fuzz_role's copy. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AB01r_wb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
