From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_sn_write G_vsnprintf G_snprintf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.I Require InstFmtP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import printf_facts_c snprintf_c printf_model_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import snprintf_m_c snprintf vsnprintf.
Import ListNotations.
Open Scope Z_scope.

(** snprintf_m_holds: snprintf over the full printf model, from the closed relocatable statement
    [InstFmtP.N_snprintf] (G_snprintf.snprintf_x_stmt on segconf's plain image); snprintf.v's snprintf_stk_holds
    with pm_args_ok (vsnprintf.v) in place of pf_args_ok and the model premise taken as given. *)
Theorem snprintf_m_holds : snprintf_m_contract.
Proof.
  unfold snprintf_m_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt args r o junk xs.
  cbv zeta.
  intros BYF RLO REND HF P1 AOK BYX XHI DXS MODEL DST Hn D0 DLO IMGF ST LO IMGLO SHI FRM MI TM GG GQ.
  assert (Edn : exists dn : nat, Z.of_nat dn = Z.min (Z.of_nat (length o)) (bv_unsigned a1 - 1) + 1)
    by (exists (Z.to_nat (Z.min (Z.of_nat (length o)) (bv_unsigned a1 - 1) + 1)); lia).
  destruct Edn as [dn Hdn].
  pose proof (task_bound m (bv_unsigned a0) _ junk MI TM DST ltac:(lia)) as DT.
  pose proof (img_free_bound (bv_unsigned a0) (bv_unsigned a1) ltac:(lia) ltac:(lia) IMGF) as IF.
  pose proof (proj2 (rw_cells_iff rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk]) DST) as DST1.
  cbn [map cell_to] in DST1.
  replace (Z.to_nat (bv_unsigned a1)) with (dn + (Z.to_nat (bv_unsigned a1) - dn))%nat in DST1 by lia.
  destruct (G_sn_write.rw_CB_split _ _ _ _ _ _ DST1) as [DSTd _].
  unfold SNPRINTF_K, RO_LO, RO_END in *.
  pose proof (pm_args_to_g m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) dn args _ AOK
                ltac:(lia) ltac:(lia)) as AOKg.
  pose proof (ssp_of_bytes m canary GG GQ) as SSP.
  pose proof (mem_inv_to_cj rsegs m MI TM) as MIc.
  pose proof (fmt_bytes0 fmt HF) as HF0.
  pose proof InstFmtP.N_snprintf as RS. unfold G_snprintf.snprintf_x_stmt in RS.
  specialize (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) dn (firstn dn junk) (fmt ++ [0]) xs
                 args lo canary r o).
  cbv zeta in RS. rewrite c_snprintf, c_gtop in RS. unfold PI.STATIC_SPLIT, G_snprintf.SNPRINTF_DEPTH in RS.
  pose proof c_pages as PG. unfold IMG_END, IMG_PAGES, TASK_SIZE in *.
  specialize (RS (eq_sym (Z_to_bv_bv_unsigned a0)) (eq_sym (Z_to_bv_bv_unsigned a1)) (eq_sym (Z_to_bv_bv_unsigned a2))
                 DSTd Hdn BYF HF0 P1 BYX ltac:(unfold Prelim.zlength; lia) AOKg MODEL Hn ST ltac:(lia) ltac:(lia) SHI SSP
                 MIc FRM ltac:(unfold Prelim.zlength; rewrite length_app; cbn [length]; lia) RLO D0
                 ltac:(lia) ltac:(unfold Prelim.zlength; lia) ltac:(lia)).
  eapply evt_bridge; [| exact RS].
  intros ms' P. exact (post_of_cj_r ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (bv_unsigned a0) (bv_unsigned a1)
                         dn r o m canary ms' (proj1 Hn) Hdn P).
Qed.
