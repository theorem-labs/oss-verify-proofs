(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBArg HBChain HBUsageDefs HBOpenDefs HBHdrDefs
  BC2A0Lit BC2A2Lit BC2A3Lit BS6EndA0 BS6EndA2 BS6EndA3 BC3A0Lit BC3A2Lit BC3A3Lit BFEEndA0 BFEEndA2 BFEEndA3 BC4A0Lit BC4A2Lit BC4A3Lit BFEEndOA0 BFEEndOA2 BFEEndOA3 BC6A0Lit BC6A2Lit BC6A3Lit BFEEndHA0 BFEEndHA2 BFEEndHA3 HBHdrA0 HBHdrA2 HBHdrA3  BC2A1Lit BS6EndA1 BC3A1Lit BFEEndA1 BC4A1Lit BFEEndOA1 BC6A1Lit BFEEndHA1 HBHdrA1
  BC2B0Lit BC2B2Lit BC2B3Lit BS6EndB0 BS6EndB2 BS6EndB3 BC3B0Lit BC3B2Lit BC3B3Lit BFEEndB0 BFEEndB2 BFEEndB3 BC4B0Lit BC4B2Lit BC4B3Lit BFEEndOB0 BFEEndOB2 BFEEndOB3 BC6B0Lit BC6B2Lit BC6B3Lit BFEEndHB0 BFEEndHB2 BFEEndHB3 HBHdrB0 HBHdrB2 HBHdrB3  BC2B1Lit BS6EndB1 BC3B1Lit BFEEndB1 BC4B1Lit BFEEndOB1 BC6B1Lit BFEEndHB1 HBHdrB1  BC1Thm HBUsage.
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
    pose proof (HBArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M HS)) as (_ & _ & _ & H1 & _).
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

  #[local] Notation INIT := (init_config HASEGS AsanUbsan.M.init_pc HAPH sp brk0 mbase rdraw lim (inp argv envp fs stdin uid gid hw groups net nofile sigmask)).
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
