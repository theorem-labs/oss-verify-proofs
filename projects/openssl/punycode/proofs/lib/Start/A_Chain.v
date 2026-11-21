(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the chain runs over the hand-off tables computed in the build, one chain per value of the run's CONFIG_RSEQ flag up to level 10, met in one table at level 11; the start-up theorem is stated over the run's whole ProcInput with the mmap base and the launch's premises and reads the flag off the input). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_Top.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import A_C_000 A_C_001 A_C_002 A_C_003 A_C_004 A_C_005 A_C_006 A_C_007 A_C_008 A_C_009 A_C_010 A_C_011.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import A_G_000 A_G_001 A_G_002 A_G_003 A_G_004 A_G_005 A_G_006 A_G_007 A_G_008 A_G_009 A_G_010 A_G_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* The hand-off tables are COMPUTED in the build from each level's start state (Start/A_G_*.v), one chain per
   value of the run's CONFIG_RSEQ flag up to level 10; level 11 meets the two chains in one table.  The
   recorded A_HS_* tables are only the fallback a failed collection would hand on, which the certificates
   would then reject. *)
Definition A_HSm : acs := A_HSg_011.

(* the chain at CONFIG_RSEQ value r = 0, from the start state at r = 0 *)
Lemma A_chain_r0 : chain A_SEGS A_T AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (init_acs_of 0 A_T) A_HSm.
Proof.
  eapply chain_cons; [exact A_IT_000_ok | exact A_cert_000_r0 | reflexivity |].
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
  eapply chain_cons; [exact A_IT_011_ok | exact A_cert_011_r0 | reflexivity |].
  apply chain_nil.
Qed.

(* the chain at CONFIG_RSEQ value r = 1, from the start state at r = 1 *)
Lemma A_chain_r1 : chain A_SEGS A_T AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (init_acs_of 1 A_T) A_HSm.
Proof.
  eapply chain_cons; [exact A_IT_000_ok | exact A_cert_000_r1 | reflexivity |].
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
  eapply chain_cons; [exact A_IT_011_ok | exact A_cert_011_r1 | reflexivity |].
  apply chain_nil.
Qed.

(* BOTH KERNEL BUILDS: the run's flag is 0 or 1, and each value has its chain. *)
Lemma A_chain : forall r : Z, 0 <= r <= 1 ->
  chain A_SEGS A_T AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (init_acs_of r A_T) A_HSm.
Proof.
  intros r Hr. assert (Hr01 : r = 0 \/ r = 1) by lia. destruct Hr01 as [-> | ->].
  - exact A_chain_r0.
  - exact A_chain_r1.
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
  (* the flag is read off the input, never chosen: A_Top's [CHAIN] asks for exactly
     [init_acs_of (rseq_z (kb_rseq (in_kernel inp))) A_T] *)
  pose proof (A_chain (rseq_z (kb_rseq (in_kernel inp))) (rseq_z_range _)) as CH.
  eapply A_chain_startup; eassumption.
Qed.
