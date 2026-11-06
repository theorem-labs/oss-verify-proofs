(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HAPlanImage HAAtable HACheck0 HACheck1 HAArg HAChain HAUsageDefs HAOpenDefs HAHdrDefs
  C2A0Lit C2A2Lit C2A3Lit S6EndA0 S6EndA2 S6EndA3 C3A0Lit C3A2Lit C3A3Lit FEEndA0 FEEndA2 FEEndA3 C4A0Lit C4A2Lit C4A3Lit FEEndOA0 FEEndOA2 FEEndOA3 C6A0Lit C6A2Lit C6A3Lit FEEndHA0 FEEndHA2 FEEndHA3 HAHdrA0 HAHdrA2 HAHdrA3  C2A1Lit S6EndA1 C3A1Lit FEEndA1 C4A1Lit FEEndOA1 C6A1Lit FEEndHA1 HAHdrA1
  C2B0Lit C2B2Lit C2B3Lit S6EndB0 S6EndB2 S6EndB3 C3B0Lit C3B2Lit C3B3Lit FEEndB0 FEEndB2 FEEndB3 C4B0Lit C4B2Lit C4B3Lit FEEndOB0 FEEndOB2 FEEndOB3 C6B0Lit C6B2Lit C6B3Lit FEEndHB0 FEEndHB2 FEEndHB3 HAHdrB0 HAHdrB2 HAHdrB3  C2B1Lit S6EndB1 C3B1Lit FEEndB1 C4B1Lit FEEndOB1 C6B1Lit FEEndHB1 HAHdrB1  C1Thm HAUsage.
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
  Variable cont : list byte.
  Hypothesis Hne : argv1 <> [].
  Hypothesis Hsl : path_has_slash argv1 = false.
  Hypothesis Hdr : path_is_dirref argv1 = false.
  Hypothesis Hln : (length argv1 <= 4095)%nat.
  Hypothesis Hlk : fs_lookup fs argv1 = Some cont.
  Let c := content_of argv fs.
  Lemma c_cont : c = cont.
  Proof. subst c argv1. destruct argv as [|a0 [|p [|q r]]]; try discriminate Hargc. cbn in Hlk |- *. rewrite Hlk. reflexivity. Qed.
  Lemma Hlk_c : fs_lookup fs argv1 = Some c. Proof. rewrite c_cont. exact Hlk. Qed.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).

  Definition T98h (lit : list Z) : env -> Fs.Fs -> TSet := fun _ fs' => T_hdr lit argv1 fs'.
  Lemma T98h_agree : forall lit, t_agree (T98h lit). Proof. intros lit E E' fs0 _. reflexivity. Qed.
  Lemma T98h_nil : forall lit E fs0, T98h lit E fs0 []. Proof. intros lit E fs0. left. apply t_emit_has_nil. Qed.
  Lemma T_main_hdr : forall lit E M, SV E M -> T_main (T98h lit) E fs = T_hdr lit argv1 fs.
  Proof.
    intros lit E M HS.
    pose proof (HAArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M HS)) as (_ & _ & _ & H1 & _).
    unfold T_main, usage_shape. cbn [sd]. change (EVar 1) with (EVar V_ARGC). rewrite H1, Hargc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis H_S6_A0 : FXHOLE c2a0_hs10 s6enda0.   Hypothesis H_FE_A0 : FXHOLE c3a0_hs20 feenda0.   Hypothesis H_FEO_A0 : FXHOLE c4a0_hs21 feendoa0.   Hypothesis H_FEH_A0 : FXHOLE c6a0_hs24 feendha0.
  Hypothesis H_S6_A2 : FXHOLE c2a2_hs10 s6enda2.   Hypothesis H_FE_A2 : FXHOLE c3a2_hs20 feenda2.   Hypothesis H_FEO_A2 : FXHOLE c4a2_hs21 feendoa2.   Hypothesis H_FEH_A2 : FXHOLE c6a2_hs24 feendha2.
  Hypothesis H_S6_A3 : FXHOLE c2a3_hs10 s6enda3.   Hypothesis H_FE_A3 : FXHOLE c3a3_hs20 feenda3.   Hypothesis H_FEO_A3 : FXHOLE c4a3_hs21 feendoa3.   Hypothesis H_FEH_A3 : FXHOLE c6a3_hs24 feendha3.
  Hypothesis H_S6_A1 : FXHOLE c2a1_hs10 s6enda1.   Hypothesis H_FE_A1 : FXHOLE c3a1_hs20 feenda1.   Hypothesis H_FEO_A1 : FXHOLE c4a1_hs21 feendoa1.   Hypothesis H_FEH_A1 : FXHOLE c6a1_hs24 feendha1.
  Hypothesis H_S6_B0 : FXHOLE c2b0_hs10 s6endb0.   Hypothesis H_FE_B0 : FXHOLE c3b0_hs20 feendb0.   Hypothesis H_FEO_B0 : FXHOLE c4b0_hs21 feendob0.   Hypothesis H_FEH_B0 : FXHOLE c6b0_hs24 feendhb0.
  Hypothesis H_S6_B2 : FXHOLE c2b2_hs10 s6endb2.   Hypothesis H_FE_B2 : FXHOLE c3b2_hs20 feendb2.   Hypothesis H_FEO_B2 : FXHOLE c4b2_hs21 feendob2.   Hypothesis H_FEH_B2 : FXHOLE c6b2_hs24 feendhb2.
  Hypothesis H_S6_B3 : FXHOLE c2b3_hs10 s6endb3.   Hypothesis H_FE_B3 : FXHOLE c3b3_hs20 feendb3.   Hypothesis H_FEO_B3 : FXHOLE c4b3_hs21 feendob3.   Hypothesis H_FEH_B3 : FXHOLE c6b3_hs24 feendhb3.
  Hypothesis H_S6_B1 : FXHOLE c2b1_hs10 s6endb1.   Hypothesis H_FE_B1 : FXHOLE c3b1_hs20 feendb1.   Hypothesis H_FEO_B1 : FXHOLE c4b1_hs21 feendob1.   Hypothesis H_FEH_B1 : FXHOLE c6b1_hs24 feendhb1.

  #[local] Notation INIT := (init_config HASEGS Asan.M.init_pc HAPH sp brk0 mbase rdraw lim (inp argv envp fs stdin uid gid hw groups net nofile sigmask)).
  Lemma sv_init : SV (reblob (E0 HAPH sp rdraw brk0 argv envp uid hw) argv c) (FULL0 HAPH sp rdraw argv envp uid hw).
  Proof.
    apply SINVm_reblob.
    exact (AsanPlanSound.APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ (init_cs_ok HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask
                  ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid)).
  Qed.

  Theorem hdr_short_leaf : flen cont <= 5 -> crz HASEGS INIT (T_hdr short_lit argv1 fs).
  Proof.
    intros H5. rewrite <- c_cont in H5.
    pose proof (usage_chain sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid (T98h short_lit) (T98h_agree _) (T98h_nil _)
                  H_S6_A0 H_FE_A0 (hdr_short_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A0 H_FEH_A0 Hne Hsl Hdr Hln Hlk_c H5)
                  H_S6_A2 H_FE_A2 (hdr_short_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A2 H_FEH_A2 Hne Hsl Hdr Hln Hlk_c H5)
                  H_S6_A3 H_FE_A3 (hdr_short_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A3 H_FEH_A3 Hne Hsl Hdr Hln Hlk_c H5)
                  H_S6_A1 H_FE_A1 (hdr_short_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A1 H_FEH_A1 Hne Hsl Hdr Hln Hlk_c H5)
                  H_S6_B0 H_FE_B0 (hdr_short_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B0 H_FEH_B0 Hne Hsl Hdr Hln Hlk_c H5)
                  H_S6_B2 H_FE_B2 (hdr_short_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B2 H_FEH_B2 Hne Hsl Hdr Hln Hlk_c H5)
                  H_S6_B3 H_FE_B3 (hdr_short_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B3 H_FEH_B3 Hne Hsl Hdr Hln Hlk_c H5)
                  H_S6_B1 H_FE_B1 (hdr_short_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B1 H_FEH_B1 Hne Hsl Hdr Hln Hlk_c H5)) as RZ.
    rewrite (T_main_hdr short_lit _ (FULL0 HAPH sp rdraw argv envp uid hw)) in RZ; [exact RZ | exact sv_init].
  Qed.

  Theorem hdr_overrun_leaf : 6 <= flen cont -> ION.room cont < 0 -> crz HASEGS INIT (T_hdr overrun_lit argv1 fs).
  Proof.
    intros H6 Hr. rewrite <- c_cont in H6, Hr.
    pose proof (usage_chain sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid (T98h overrun_lit) (T98h_agree _) (T98h_nil _)
                  H_S6_A0 H_FE_A0 (hdr_overrun_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A0 H_FEH_A0 Hne Hsl Hdr Hln Hlk_c H6 Hr)
                  H_S6_A2 H_FE_A2 (hdr_overrun_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A2 H_FEH_A2 Hne Hsl Hdr Hln Hlk_c H6 Hr)
                  H_S6_A3 H_FE_A3 (hdr_overrun_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A3 H_FEH_A3 Hne Hsl Hdr Hln Hlk_c H6 Hr)
                  H_S6_A1 H_FE_A1 (hdr_overrun_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A1 H_FEH_A1 Hne Hsl Hdr Hln Hlk_c H6 Hr)
                  H_S6_B0 H_FE_B0 (hdr_overrun_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B0 H_FEH_B0 Hne Hsl Hdr Hln Hlk_c H6 Hr)
                  H_S6_B2 H_FE_B2 (hdr_overrun_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B2 H_FEH_B2 Hne Hsl Hdr Hln Hlk_c H6 Hr)
                  H_S6_B3 H_FE_B3 (hdr_overrun_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B3 H_FEH_B3 Hne Hsl Hdr Hln Hlk_c H6 Hr)
                  H_S6_B1 H_FE_B1 (hdr_overrun_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B1 H_FEH_B1 Hne Hsl Hdr Hln Hlk_c H6 Hr)) as RZ.
    rewrite (T_main_hdr overrun_lit _ (FULL0 HAPH sp rdraw argv envp uid hw)) in RZ; [exact RZ | exact sv_init].
  Qed.
End Leaf.
