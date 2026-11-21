(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up facts stated over the launch's ProcInput; the larger auxiliary vector and its CONFIG_RSEQ entries; the channel-reader premise; the launch premises; the start-up hand-off tables computed in the build). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.openssl.pem.images Require Import Asan.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_Top.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import A_HS_000 A_C_000 A_HS_001 A_C_001 A_HS_002 A_C_002 A_HS_003 A_C_003 A_HS_004 A_C_004 A_HS_005 A_C_005 A_HS_006 A_C_006 A_HS_007 A_C_007 A_HS_008 A_C_008 A_HS_009 A_C_009 A_HS_010 A_C_010 A_HS_011 A_C_011 A_G_001 A_G_002 A_G_003 A_G_004 A_G_005 A_G_006 A_G_007 A_G_008 A_G_009 A_G_010 A_G_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition A_HSm : acs := A_HSg_011.

(* After level 11 nothing is left: level 11's own table, collected over both kernel builds, is the main
   hand-off.  Kept as a lemma so the flag split below ends in one place. *)
(* [chain] is declared inside AsanChain's Section, so outside it the six section
   arguments are explicit; only the two [acs] indices move. *)
Lemma A_chain_rest : chain A_SEGS A_T AsanInit.LIMIT A_XN0 A_XE0 A_XB0 A_HSg_011 A_HSm.
Proof.
  apply chain_nil.
Qed.

(* BOTH KERNEL BUILDS.  [r] is the run's CONFIG_RSEQ flag, read off the input at the use
   site below and never chosen here, so no kernel field is pinned: levels 0..11 are
   certified at each of the flag's two values, over the SAME plans, each build from its
   own computed tables (the auxv tail differs between the builds), into the one computed
   level-11 table. *)
Lemma A_chain : forall r : Z, 0 <= r <= 1 ->
  chain A_SEGS A_T AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (init_acs_of r A_T) A_HSm.
Proof.
  intros r Hr. assert (Hr01 : r = 0 \/ r = 1) by lia. destruct Hr01 as [-> | ->].
  - eapply chain_cons; [exact A_IT_000_ok | exact A_cert_000_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_001_ok | exact A_cert_001_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_002_ok | exact A_cert_002_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_003_ok | exact A_cert_003_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_004_ok | exact A_cert_004_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_005_ok | exact A_cert_005_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_006_ok | exact A_cert_006_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_007_ok | exact A_cert_007_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_008_ok | exact A_cert_008_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_009_ok | exact A_cert_009_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_010_ok | exact A_cert_010_r0 | reflexivity |].
    eapply chain_cons; [exact A_IT_011_ok | exact A_cert_011_r0 | reflexivity | exact A_chain_rest].
  - eapply chain_cons; [exact A_IT_000_ok | exact A_cert_000_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_001_ok | exact A_cert_001_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_002_ok | exact A_cert_002_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_003_ok | exact A_cert_003_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_004_ok | exact A_cert_004_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_005_ok | exact A_cert_005_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_006_ok | exact A_cert_006_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_007_ok | exact A_cert_007_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_008_ok | exact A_cert_008_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_009_ok | exact A_cert_009_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_010_ok | exact A_cert_010_r1 | reflexivity |].
    eapply chain_cons; [exact A_IT_011_ok | exact A_cert_011_r1 | reflexivity | exact A_chain_rest].
Qed.

(* [comment removed for export] *)
Theorem A_startup_main :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_brk A_SEGS brk0 -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    valid_id (in_uid inp) -> valid_launch inp -> in_channel_reader inp = true ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    forall HOLES : nat -> env -> Fs.Fs -> ShapeAlg.TSet,
      (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') ->
      (forall h E fs', HOLES h E fs' []) ->
      holes_stmt A_SEGS A_T AsanInit.LIMIT (HS_one A_HSm) (SINV0 A_PH Asan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
                 (bv_unsigned sp) HOLES (in_fs inp) ->
      srealizes A_SEGS (init_config A_SEGS Asan.M.init_pc A_PH sp brk0 mbase rdraw AsanInit.LIMIT inp)
                (HOLES 0%nat (E0 sp rdraw brk0 inp) (in_fs inp)).
Proof.
  intros sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau HOLES HA HN MAIN.
  (* the flag is READ OFF the input, never chosen: [A_Top]'s [CHAIN] asks for exactly
     [init_acs_of (rseq_z (kb_rseq (in_kernel inp))) A_T], and [rseq_z_range] says that
     value is 0 or 1, which is all [A_chain] needs. *)
  pose proof (A_chain (rseq_z (kb_rseq (in_kernel inp))) (rseq_z_range _)) as CH.
  eapply A_chain_startup; eassumption.
Qed.
