(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HAPlanImage HAAtable HACheck0 HACheck1 HAArg HAChain HAUsageDefs HAOpenDefs HADirDefs
  C2A0Lit C2A2Lit C2A3Lit S6EndA0 S6EndA2 S6EndA3 C3A0Lit C3A2Lit C3A3Lit FEEndA0 FEEndA2 FEEndA3 C4A0Lit C4A2Lit C4A3Lit FEEndOA0 FEEndOA2 FEEndOA3 C5A0Lit C5A2Lit C5A3Lit FEEndDA0 FEEndDA2 FEEndDA3 HADirA0 HADirA2 HADirA3  C2A1Lit S6EndA1 C3A1Lit FEEndA1 C4A1Lit FEEndOA1 C5A1Lit FEEndDA1 HADirA1
  C2B0Lit C2B2Lit C2B3Lit S6EndB0 S6EndB2 S6EndB3 C3B0Lit C3B2Lit C3B3Lit FEEndB0 FEEndB2 FEEndB3 C4B0Lit C4B2Lit C4B3Lit FEEndOB0 FEEndOB2 FEEndOB3 C5B0Lit C5B2Lit C5B3Lit FEEndDB0 FEEndDB2 FEEndDB3 HADirB0 HADirB2 HADirB3  C2B1Lit S6EndB1 C3B1Lit FEEndB1 C4B1Lit FEEndOB1 C5B1Lit FEEndDB1 HADirB1  C1Thm HAUsage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section Leaf.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable lim : Z.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InStreams.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk HASEGS brk0.
  Hypothesis Hlim : (AsanInit.LIMIT <= lim)%Z.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Let argv1 := nth 1 argv [].
  (* [comment removed for export] *)
  Hypothesis Hargc : length argv = 2%nat.
  Hypothesis Hclass : path_is_dirref argv1 = true.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).

  Definition T98d : env -> Fs.Fs -> TSet := fun _ fs' => T_dir argv1 fs'.
  Lemma T98d_agree : t_agree T98d. Proof. intros E E' fs0 _. reflexivity. Qed.
  Lemma T98d_nil : forall E fs0, T98d E fs0 []. Proof. intros E fs0. left. apply t_emit_has_nil. Qed.

  Lemma T_main_dir : forall E M, SV E M -> T_main T98d E fs = T_dir argv1 fs.
  Proof.
    intros E M HS.
    pose proof (HAArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M HS)) as (_ & _ & _ & H1 & _).
    unfold T_main, usage_shape. cbn [sd]. change (EVar 1) with (EVar V_ARGC). rewrite H1, Hargc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis H_S6_A0 : FXHOLE c2a0_hs10 s6enda0.   Hypothesis H_FE_A0 : FXHOLE c3a0_hs20 feenda0.   Hypothesis H_FEO_A0 : FXHOLE c4a0_hs21 feendoa0.   Hypothesis H_FED_A0 : FXHOLE c5a0_hs23 feendda0.
  Hypothesis H_S6_A2 : FXHOLE c2a2_hs10 s6enda2.   Hypothesis H_FE_A2 : FXHOLE c3a2_hs20 feenda2.   Hypothesis H_FEO_A2 : FXHOLE c4a2_hs21 feendoa2.   Hypothesis H_FED_A2 : FXHOLE c5a2_hs23 feendda2.
  Hypothesis H_S6_A3 : FXHOLE c2a3_hs10 s6enda3.   Hypothesis H_FE_A3 : FXHOLE c3a3_hs20 feenda3.   Hypothesis H_FEO_A3 : FXHOLE c4a3_hs21 feendoa3.   Hypothesis H_FED_A3 : FXHOLE c5a3_hs23 feendda3.
  Hypothesis H_S6_A1 : FXHOLE c2a1_hs10 s6enda1.   Hypothesis H_FE_A1 : FXHOLE c3a1_hs20 feenda1.   Hypothesis H_FEO_A1 : FXHOLE c4a1_hs21 feendoa1.   Hypothesis H_FED_A1 : FXHOLE c5a1_hs23 feendda1.
  Hypothesis H_S6_B0 : FXHOLE c2b0_hs10 s6endb0.   Hypothesis H_FE_B0 : FXHOLE c3b0_hs20 feendb0.   Hypothesis H_FEO_B0 : FXHOLE c4b0_hs21 feendob0.   Hypothesis H_FED_B0 : FXHOLE c5b0_hs23 feenddb0.
  Hypothesis H_S6_B2 : FXHOLE c2b2_hs10 s6endb2.   Hypothesis H_FE_B2 : FXHOLE c3b2_hs20 feendb2.   Hypothesis H_FEO_B2 : FXHOLE c4b2_hs21 feendob2.   Hypothesis H_FED_B2 : FXHOLE c5b2_hs23 feenddb2.
  Hypothesis H_S6_B3 : FXHOLE c2b3_hs10 s6endb3.   Hypothesis H_FE_B3 : FXHOLE c3b3_hs20 feendb3.   Hypothesis H_FEO_B3 : FXHOLE c4b3_hs21 feendob3.   Hypothesis H_FED_B3 : FXHOLE c5b3_hs23 feenddb3.
  Hypothesis H_S6_B1 : FXHOLE c2b1_hs10 s6endb1.   Hypothesis H_FE_B1 : FXHOLE c3b1_hs20 feendb1.   Hypothesis H_FEO_B1 : FXHOLE c4b1_hs21 feendob1.   Hypothesis H_FED_B1 : FXHOLE c5b1_hs23 feenddb1.

  Theorem dir_leaf :
    crz HASEGS (init_config HASEGS Asan.M.init_pc HAPH sp brk0 mbase rdraw lim
                  (inp argv envp fs stdin uid gid hw groups net nofile sigmask))
        (T_dir argv1 fs).
  Proof.
    pose proof (usage_chain sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid T98d T98d_agree T98d_nil
                  H_S6_A0 H_FE_A0 (dir_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A0 H_FED_A0 Hclass)
                  H_S6_A2 H_FE_A2 (dir_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A2 H_FED_A2 Hclass)
                  H_S6_A3 H_FE_A3 (dir_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A3 H_FED_A3 Hclass)
                  H_S6_A1 H_FE_A1 (dir_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A1 H_FED_A1 Hclass)
                  H_S6_B0 H_FE_B0 (dir_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B0 H_FED_B0 Hclass)
                  H_S6_B2 H_FE_B2 (dir_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B2 H_FED_B2 Hclass)
                  H_S6_B3 H_FE_B3 (dir_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B3 H_FED_B3 Hclass)
                  H_S6_B1 H_FE_B1 (dir_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B1 H_FED_B1 Hclass)) as RZ.
    rewrite (T_main_dir _ (FULL0 HAPH sp rdraw argv envp uid hw)) in RZ; [exact RZ|].
    apply SINVm_reblob.
    exact (AsanPlanSound.APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ (init_cs_ok HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask
                  ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid)).
  Qed.
End Leaf.
