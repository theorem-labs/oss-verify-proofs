(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBArg HBChain HBUsageDefs HBOpenDefs HBDirDefs
  BC2A0Lit BC2A2Lit BC2A3Lit BS6EndA0 BS6EndA2 BS6EndA3 BC3A0Lit BC3A2Lit BC3A3Lit BFEEndA0 BFEEndA2 BFEEndA3 BC4A0Lit BC4A2Lit BC4A3Lit BFEEndOA0 BFEEndOA2 BFEEndOA3 BC5A0Lit BC5A2Lit BC5A3Lit BFEEndDA0 BFEEndDA2 BFEEndDA3 HBDirA0 HBDirA2 HBDirA3  BC2A1Lit BS6EndA1 BC3A1Lit BFEEndA1 BC4A1Lit BFEEndOA1 BC5A1Lit BFEEndDA1 HBDirA1
  BC2B0Lit BC2B2Lit BC2B3Lit BS6EndB0 BS6EndB2 BS6EndB3 BC3B0Lit BC3B2Lit BC3B3Lit BFEEndB0 BFEEndB2 BFEEndB3 BC4B0Lit BC4B2Lit BC4B3Lit BFEEndOB0 BFEEndOB2 BFEEndOB3 BC5B0Lit BC5B2Lit BC5B3Lit BFEEndDB0 BFEEndDB2 BFEEndDB3 HBDirB0 HBDirB2 HBDirB3  BC2B1Lit BS6EndB1 BC3B1Lit BFEEndB1 BC4B1Lit BFEEndOB1 BC5B1Lit BFEEndDB1 HBDirB1  BC1Thm HBUsage.
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
    pose proof (HBArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M HS)) as (_ & _ & _ & H1 & _).
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
    crz HASEGS (init_config HASEGS AsanUbsan.M.init_pc HAPH sp brk0 mbase rdraw lim
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
