From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import RoAdapt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import snprintf_ro_c snprintf.
Import ListNotations.
Open Scope Z_scope.

Lemma snprintf_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma task_mem_norm : forall m, MemNorm.task_mem rsegs m -> MemNorm.task_mem rsegs (MemNorm.normalize rsegs m).
Proof.
  intros m H a b E. unfold MemNorm.normalize in E.
  destruct (ro_addr rsegs a); [discriminate E | exact (H a b E)].
Qed.

Lemma task_mem_back : forall m m' m0', MemNorm.task_mem rsegs m -> MemNorm.mem_rel rsegs m' m0' ->
  MemNorm.ro_same rsegs m m' -> MemNorm.task_mem rsegs m0' -> MemNorm.task_mem rsegs m'.
Proof.
  intros m m' m0' T REL RS T0 a b E. destruct (ro_addr rsegs a) eqn:Ro.
  - rewrite (RS a Ro) in E. exact (T a b E).
  - rewrite <- (MemNorm.mem_rel_rw rsegs m' m0' a REL Ro) in E. exact (T0 a b E).
Qed.

Lemma pf_args_norm : forall m S lo D n rs args, MemNorm.ro_agree rsegs m ->
  pf_args_ok m S lo D n rs args -> pf_args_ok (MemNorm.normalize rsegs m) S lo D n rs args.
Proof.
  intros m S lo D n rs args HR. revert rs. induction args as [|a args IH]; intros rs H; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2]. split; [|exact (IH rs H2)].
  destruct a as [v|u|s]; try exact H1.
  destruct H1 as [HF [slack (B & R)]]. split; [exact HF|]. exists slack. split; [|exact R].
  exact (MemNorm.bytes_at_normalize rsegs m _ _ HR B).
Qed.

Lemma post_back : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D r Tw m s,
  MemNorm.ro_agree rsegs m -> MemNorm.task_mem rsegs m ->
  (exists s', printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D r Tw (MemNorm.normalize rsegs m) s'
     /\ MemNorm.ms_rel rsegs s s' /\ MemNorm.ro_same rsegs m (ms_mem s)) ->
  printf_post_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D r Tw m s.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D r Tw m s HRO TM (s' & P & MR & RS).
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & Ft & fc' & m0'
                 & E & MU & WM & MI & TM0 & FR & FK & STK & BY).
  subst s'. destruct s as [regs fregs pc svc resv fcsr mem rom].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem). cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, Ft, fc', mem.
  split; [unfold MS; subst; reflexivity|].
  split; [exact (MemNorm.munch_rel rsegs _ m _ mem m0' REL Hmem RS MU)|].
  split; [exact (MemNorm.wmono_rel rsegs m _ mem m0' REL Hmem RS WM)|].
  split; [exact (MemNorm.ro_agree_same rsegs m mem HRO RS)|].
  split; [exact (task_mem_back m mem m0' TM Hmem RS TM0)|].
  split; [exact FR|]. split; [exact FK|].
  split; [exact (stk_back rsegs mem m0' _ _ Hmem STK) | exact (bytes_at_back rsegs mem m0' _ _ Hmem BY)].
Qed.

Theorem snprintf_ro_of : snprintf_contract -> snprintf_ro_contract.
Proof.
  intros C. unfold snprintf_ro_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt ps args T junk.
  cbv zeta.
  intros BYF RLO REND PARSE PAOK TEXT DST NRD Hn HT D0 DLO IMGF ST NRS LO IMGLO SHI FRM HRO TM GG GQ.
  pose proof (C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
           (MemNorm.normalize rsegs m) lo canary fmt ps args T junk
           (MemNorm.bytes_at_normalize rsegs m _ _ HRO BYF) RLO REND PARSE (pf_args_norm _ _ _ _ _ _ _ HRO PAOK) TEXT
           (rw_cells_norm rsegs m _ _ HRO DST NRD) Hn HT D0 DLO IMGF (stk_norm rsegs m _ _ HRO ST NRS) LO IMGLO SHI
           FRM (MemNorm.mem_inv_normalize rsegs m) (task_mem_norm m TM)
           (MemNorm.bytes_at_normalize rsegs m _ _ HRO GG) (MemNorm.bytes_at_normalize rsegs m _ _ HRO GQ)) as CC.
  eapply evt_mono; [apply (MemNorm.evt_normalize rsegs); [exact snprintf_wx | exact HRO | exact CC] |].
  intros s Hs. eapply post_back; eassumption.
Qed.

Theorem snprintf_ro_holds : snprintf_ro_contract.
Proof. exact (snprintf_ro_of snprintf_holds). Qed.
