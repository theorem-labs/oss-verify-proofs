From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import CJBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Printf_text G_printf_core_common.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require G_vsnprintf G_sprintf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.I Require InstFmtU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c sprintf_c snprintf.
Import ListNotations.
Open Scope Z_scope.

Lemma c_sprintf : @RStep.sym InstFmtU.N_img_fmt 0x7f000500 = SPRINTF.
Proof. vm_compute. reflexivity. Qed.

Theorem sprintf_holds : sprintf_contract.
Proof.
  unfold sprintf_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt ps args T junk.
  cbv zeta.
  intros BYF RLO REND PARSE PAOK TEXT DST Hn D0 DLO IMGF ST LO IMGLO SHI FRM MI TM GG GQ.
  destruct (text_ok _ _ _ _ _ _ fmt ps args T PAOK PARSE TEXT ltac:(lia)) as (MODEL & P1 & HF).
  set (dn := Z.to_nat (Z.of_nat (length T) + 1)).
  assert (Hdn : Z.of_nat dn = Z.of_nat (length T) + 1) by (unfold dn; lia).
  pose proof (task_bound m (bv_unsigned a0) _ junk MI TM DST ltac:(lia)) as DT.
  pose proof (img_free_bound (bv_unsigned a0) (Z.of_nat (length T) + 1) ltac:(lia) ltac:(lia) IMGF) as IF.
  pose proof (proj2 (rw_cells_iff rsegs m (bv_unsigned a0) [CB dn junk]) DST) as DST1.
  cbn [map cell_to] in DST1.
  unfold SPRINTF_K, RO_LO, RO_END in *.
  pose proof (pargs_ok m (bv_unsigned sp) lo (bv_unsigned a0) (Z.of_nat (length T) + 1) dn ps args _ PAOK
                ltac:(lia) ltac:(lia)) as AOK.
  pose proof (ssp_of_bytes m canary GG GQ) as SSP.
  pose proof (mem_inv_to_cj rsegs m MI TM) as MIc.
  pose proof InstFmtU.N_sprintf as RS. unfold G_sprintf.sprintf_x_stmt in RS.
  specialize (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                 (bv_unsigned a0) (bv_unsigned a1) dn junk (fmt ++ [0])
                 (Printf_text.pf_pargs (map tpc ps) (map ta args)) lo canary (Prelim.zlength T) T).
  cbv zeta in RS. rewrite c_sprintf, c_gtop in RS. unfold PI.STATIC_SPLIT, G_sprintf.SPRINTF_DEPTH in RS.
  pose proof c_pages as PG. unfold IMG_END, IMG_PAGES, TASK_SIZE in *.
  specialize (RS (eq_sym (Z_to_bv_bv_unsigned a0)) (eq_sym (Z_to_bv_bv_unsigned a1))
                 DST1 ltac:(unfold Prelim.zlength; lia) BYF HF P1 AOK MODEL ltac:(unfold Prelim.zlength; lia)
                 ST ltac:(lia) ltac:(lia) SHI SSP MIc FRM
                 ltac:(unfold Prelim.zlength; rewrite length_app; cbn [length]; lia) RLO D0
                 ltac:(lia) ltac:(lia) ltac:(lia)).
  eapply evt_bridge; [| exact RS].
  intros ms' P.
  pose proof (post_of_cj ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (bv_unsigned a0)
                (Z.of_nat (length T) + 1) dn T m canary ms' ltac:(lia) ltac:(lia)) as Q.
  replace (Z.to_nat (Z.of_nat (length T) + 1 - 1)) with (length T) in Q by lia.
  rewrite firstn_all in Q. exact (Q P).
Qed.
