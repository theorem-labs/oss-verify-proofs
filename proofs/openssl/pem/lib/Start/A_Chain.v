(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_Top.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import A_HS_000 A_C_000 A_HS_001 A_C_001 A_HS_002 A_C_002 A_HS_003 A_C_003 A_HS_004 A_C_004 A_HS_005 A_C_005 A_HS_006 A_C_006 A_HS_007 A_C_007 A_HS_008 A_C_008 A_HS_009 A_C_009 A_HS_010 A_C_010 A_HS_011 A_C_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition A_HSm : acs := A_HS_011.

Lemma A_chain : chain A_SEGS A_T AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (init_acs_of A_T) A_HSm.
Proof.
  eapply chain_cons; [exact A_IT_000_ok | exact A_cert_000 | reflexivity |].
  eapply chain_cons; [exact A_IT_001_ok | exact A_cert_001 | reflexivity |].
  eapply chain_cons; [exact A_IT_002_ok | exact A_cert_002 | reflexivity |].
  eapply chain_cons; [exact A_IT_003_ok | exact A_cert_003 | reflexivity |].
  eapply chain_cons; [exact A_IT_004_ok | exact A_cert_004 | reflexivity |].
  eapply chain_cons; [exact A_IT_005_ok | exact A_cert_005 | reflexivity |].
  eapply chain_cons; [exact A_IT_006_ok | exact A_cert_006 | reflexivity |].
  eapply chain_cons; [exact A_IT_007_ok | exact A_cert_007 | reflexivity |].
  eapply chain_cons; [exact A_IT_008_ok | exact A_cert_008 | reflexivity |].
  eapply chain_cons; [exact A_IT_009_ok | exact A_cert_009 | reflexivity |].
  eapply chain_cons; [exact A_IT_010_ok | exact A_cert_010 | reflexivity |].
  eapply chain_cons; [exact A_IT_011_ok | exact A_cert_011 | reflexivity |].
  apply chain_nil.
Qed.

(* [comment removed for export] *)
Theorem A_startup_main :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
         (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream),
    valid_sp sp -> valid_brk A_SEGS brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
    entry_stack_fits sp argv envp -> valid_id uid ->
    forall HOLES : nat -> env -> Fs.Fs -> ShapeAlg.TSet,
      (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') ->
      (forall h E fs', HOLES h E fs' []) ->
      holes_stmt A_SEGS A_T AsanInit.LIMIT (HS_one A_HSm) (SINV0 A_PH sp rdraw brk0 argv envp uid hw) (argH0 A_PH sp rdraw argv envp uid hw) (bv_unsigned sp) HOLES fs ->
      srealizes A_SEGS (init_config A_SEGS Asan.M.init_pc A_PH sp brk0 mbase rdraw AsanInit.LIMIT
                         (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
                (HOLES 0%nat (E0 A_PH sp rdraw brk0 argv envp uid hw) fs).
Proof.
  intros sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd Hsp Hbrk Hmb Hva Hve Hfit Huid HOLES HA HN MAIN.
  exact (A_chain_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd
           Hsp Hbrk Hva Hve Hfit Huid A_HSm HOLES HA HN MAIN A_chain).
Qed.
