From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c sprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import sprintf_ro_c sprintf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_ro.
Import ListNotations.
Open Scope Z_scope.

Theorem sprintf_ro_of : sprintf_contract -> sprintf_ro_contract.
Proof.
  intros C. unfold sprintf_ro_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt ps args T junk.
  cbv zeta.
  intros BYF RLO REND PARSE PAOK TEXT DST NRD Hn D0 DLO IMGF ST NRS LO IMGLO SHI FRM HRO TM GG GQ.
  pose proof (C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
           (MemNorm.normalize rsegs m) lo canary fmt ps args T junk
           (MemNorm.bytes_at_normalize rsegs m _ _ HRO BYF) RLO REND PARSE
           (snprintf_ro.pf_args_norm _ _ _ _ _ _ _ HRO PAOK) TEXT
           (rw_cells_norm rsegs m _ _ HRO DST NRD) Hn D0 DLO IMGF (stk_norm rsegs m _ _ HRO ST NRS) LO IMGLO SHI
           FRM (MemNorm.mem_inv_normalize rsegs m) (snprintf_ro.task_mem_norm m TM)
           (MemNorm.bytes_at_normalize rsegs m _ _ HRO GG) (MemNorm.bytes_at_normalize rsegs m _ _ HRO GQ)) as CC.
  eapply evt_mono; [apply (MemNorm.evt_normalize rsegs); [exact snprintf_ro.snprintf_wx | exact HRO | exact CC] |].
  intros s Hs. eapply snprintf_ro.post_back; eassumption.
Qed.

Theorem sprintf_ro_holds : sprintf_ro_contract.
Proof. exact (sprintf_ro_of sprintf_holds). Qed.
