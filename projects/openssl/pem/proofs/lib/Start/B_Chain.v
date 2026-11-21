(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up facts stated over the launch's ProcInput; the larger auxiliary vector and its CONFIG_RSEQ entries; the channel-reader premise; the launch premises; the start-up hand-off tables computed in the build). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.openssl.pem.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_Top.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import B_HS_000 B_C_000 B_HS_001 B_C_001 B_HS_002 B_C_002 B_HS_003 B_C_003 B_HS_004 B_C_004 B_HS_005 B_C_005 B_HS_006 B_C_006 B_HS_007 B_C_007 B_HS_008 B_C_008 B_HS_009 B_C_009 B_HS_010 B_C_010 B_HS_011 B_C_011 B_G_001 B_G_002 B_G_003 B_G_004 B_G_005 B_G_006 B_G_007 B_G_008 B_G_009 B_G_010 B_G_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition B_HSm : acs := B_HSg_011.

(* After level 11 nothing is left: level 11's own table, collected over both kernel builds, is the main
   hand-off; see the A twin's note. *)
(* [chain] is declared inside AsanChain's Section, so outside it the six section
   arguments are explicit; only the two [acs] indices move. *)
Lemma B_chain_rest : chain B_SEGS B_T AsanInit.LIMIT B_XN0 B_XE0 B_XB0 B_HSg_011 B_HSm.
Proof.
  apply chain_nil.
Qed.

(* BOTH KERNEL BUILDS: levels 0..11 are certified at each value of the run's CONFIG_RSEQ
   flag, over the SAME plans, each build from its own computed tables, into the one computed
   level-11 table, so no kernel field is pinned. *)
Lemma B_chain : forall r : Z, 0 <= r <= 1 ->
  chain B_SEGS B_T AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (init_acs_of r B_T) B_HSm.
Proof.
  intros r Hr. assert (Hr01 : r = 0 \/ r = 1) by lia. destruct Hr01 as [-> | ->].
  - eapply chain_cons; [exact B_IT_000_ok | exact B_cert_000_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_001_ok | exact B_cert_001_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_002_ok | exact B_cert_002_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_003_ok | exact B_cert_003_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_004_ok | exact B_cert_004_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_005_ok | exact B_cert_005_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_006_ok | exact B_cert_006_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_007_ok | exact B_cert_007_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_008_ok | exact B_cert_008_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_009_ok | exact B_cert_009_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_010_ok | exact B_cert_010_r0 | reflexivity |].
    eapply chain_cons; [exact B_IT_011_ok | exact B_cert_011_r0 | reflexivity | exact B_chain_rest].
  - eapply chain_cons; [exact B_IT_000_ok | exact B_cert_000_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_001_ok | exact B_cert_001_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_002_ok | exact B_cert_002_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_003_ok | exact B_cert_003_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_004_ok | exact B_cert_004_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_005_ok | exact B_cert_005_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_006_ok | exact B_cert_006_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_007_ok | exact B_cert_007_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_008_ok | exact B_cert_008_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_009_ok | exact B_cert_009_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_010_ok | exact B_cert_010_r1 | reflexivity |].
    eapply chain_cons; [exact B_IT_011_ok | exact B_cert_011_r1 | reflexivity | exact B_chain_rest].
Qed.

(* [comment removed for export] *)
Theorem B_startup_main :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_brk B_SEGS brk0 -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    valid_id (in_uid inp) -> valid_launch inp -> in_channel_reader inp = true ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    forall HOLES : nat -> env -> Fs.Fs -> ShapeAlg.TSet,
      (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') ->
      (forall h E fs', HOLES h E fs' []) ->
      holes_stmt B_SEGS B_T AsanInit.LIMIT (HS_one B_HSm) (SINV0 B_PH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
                 (bv_unsigned sp) HOLES (in_fs inp) ->
      srealizes B_SEGS (init_config B_SEGS AsanUbsan.M.init_pc B_PH sp brk0 mbase rdraw AsanInit.LIMIT inp)
                (HOLES 0%nat (E0 sp rdraw brk0 inp) (in_fs inp)).
Proof.
  intros sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau HOLES HA HN MAIN.
  (* the flag is READ OFF the input, never chosen; see the A twin. *)
  pose proof (B_chain (rseq_z (kb_rseq (in_kernel inp))) (rseq_z_range _)) as CH.
  eapply B_chain_startup; eassumption.
Qed.
