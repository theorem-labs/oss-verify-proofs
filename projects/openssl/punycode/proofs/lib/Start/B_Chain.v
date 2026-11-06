(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_Top.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import B_HS_000 B_C_000 B_HS_001 B_C_001 B_HS_002 B_C_002 B_HS_003 B_C_003 B_HS_004 B_C_004 B_HS_005 B_C_005 B_HS_006 B_C_006 B_HS_007 B_C_007 B_HS_008 B_C_008 B_HS_009 B_C_009 B_HS_010 B_C_010 B_HS_011 B_C_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition B_HSm : acs := B_HS_011.

Lemma B_chain : chain B_SEGS B_T AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (init_acs_of B_T) B_HSm.
Proof.
  eapply chain_cons; [exact B_IT_000_ok | exact B_cert_000 | reflexivity |].
  eapply chain_cons; [exact B_IT_001_ok | exact B_cert_001 | reflexivity |].
  eapply chain_cons; [exact B_IT_002_ok | exact B_cert_002 | reflexivity |].
  eapply chain_cons; [exact B_IT_003_ok | exact B_cert_003 | reflexivity |].
  eapply chain_cons; [exact B_IT_004_ok | exact B_cert_004 | reflexivity |].
  eapply chain_cons; [exact B_IT_005_ok | exact B_cert_005 | reflexivity |].
  eapply chain_cons; [exact B_IT_006_ok | exact B_cert_006 | reflexivity |].
  eapply chain_cons; [exact B_IT_007_ok | exact B_cert_007 | reflexivity |].
  eapply chain_cons; [exact B_IT_008_ok | exact B_cert_008 | reflexivity |].
  eapply chain_cons; [exact B_IT_009_ok | exact B_cert_009 | reflexivity |].
  eapply chain_cons; [exact B_IT_010_ok | exact B_cert_010 | reflexivity |].
  eapply chain_cons; [exact B_IT_011_ok | exact B_cert_011 | reflexivity |].
  apply chain_nil.
Qed.

(* [comment removed for export] *)
Theorem B_startup_main :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
         (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream),
    valid_sp sp -> valid_brk B_SEGS brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
    entry_stack_fits sp argv envp -> valid_id uid ->
    forall HOLES : nat -> env -> Fs.Fs -> ShapeAlg.TSet,
      (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') ->
      (forall h E fs', HOLES h E fs' []) ->
      holes_stmt B_SEGS B_T AsanInit.LIMIT (HS_one B_HSm) (SINV0 B_PH sp rdraw brk0 argv envp uid hw) (argH0 B_PH sp rdraw argv envp uid hw) (bv_unsigned sp) HOLES fs ->
      srealizes B_SEGS (init_config B_SEGS AsanUbsan.M.init_pc B_PH sp brk0 mbase rdraw AsanInit.LIMIT
                         (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
                (HOLES 0%nat (E0 B_PH sp rdraw brk0 argv envp uid hw) fs).
Proof.
  intros sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd Hsp Hbrk Hmb Hva Hve Hfit Huid HOLES HA HN MAIN.
  exact (B_chain_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd
           Hsp Hbrk Hva Hve Hfit Huid B_HSm HOLES HA HN MAIN B_chain).
Qed.
