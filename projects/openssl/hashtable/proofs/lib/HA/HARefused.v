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
  C2A0Lit S6EndA0K C3A0Lit C3A0LitK FEEndA0 C4A0Lit FEEndOA0 HAKge1A0 KRA0Lit FEEndRA0 C2A2Lit S6EndA2K C3A2Lit C3A2LitK FEEndA2 C4A2Lit FEEndOA2 HAKge1A2 KRA2Lit FEEndRA2 C2A3Lit S6EndA3K C3A3Lit C3A3LitK FEEndA3 C4A3Lit FEEndOA3 HAKge1A3 KRA3Lit FEEndRA3 C2A1Lit S6EndA1K C3A1Lit C3A1LitK FEEndA1 C4A1Lit FEEndOA1 HAKge1A1 KRA1Lit FEEndRA1 C2B0Lit S6EndB0K C3B0Lit C3B0LitK FEEndB0 C4B0Lit FEEndOB0 HAKge1B0 KRB0Lit FEEndRB0 C2B2Lit S6EndB2K C3B2Lit C3B2LitK FEEndB2 C4B2Lit FEEndOB2 HAKge1B2 KRB2Lit FEEndRB2 C2B3Lit S6EndB3K C3B3Lit C3B3LitK FEEndB3 C4B3Lit FEEndOB3 HAKge1B3 KRB3Lit FEEndRB3 C2B1Lit S6EndB1K C3B1Lit C3B1LitK FEEndB1 C4B1Lit FEEndOB1 HAKge1B1 KRB1Lit FEEndRB1 C1Thm HAUsageK.
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
  Variable stdin : InStreams.      (* [comment removed for export] *)
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
  #[local] Notation PIECE := (piece SV argH ISP fs).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).
  #[local] Notation INIT := (init_config HASEGS Asan.M.init_pc HAPH sp brk0 mbase rdraw lim (inp argv envp fs stdin uid gid hw groups net nofile sigmask)).
  #[local] Notation EINIT := (reblob (E0 HAPH sp rdraw brk0 argv envp uid hw) argv c).
  Lemma sv_init : SV EINIT (FULL0 HAPH sp rdraw argv envp uid hw).
  Proof.
    apply SINVm_reblob.
    exact (AsanPlanSound.APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ (init_cs_ok HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask
                  ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid)).
  Qed.
  Lemma T_main_2 : forall T98 E M, SV E M -> T_main T98 E fs = T98 E fs.
  Proof.
    intros T98 E M HS.
    pose proof (HAArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M HS)) as (_ & _ & _ & H1 & _).
    unfold T_main, usage_shape. cbn [sd]. change (EVar 1) with (EVar V_ARGC). rewrite H1, Hargc. reflexivity.
  Qed.
  Hypothesis H_S6K_A0 : FXHOLE c2a0_hs10 s6enda0k.   Hypothesis H_FE_A0 : FXHOLE c3a0_hs20 feenda0.   Hypothesis H_FEO_A0 : FXHOLE c4a0_hs21 feendoa0.   Hypothesis H_FER_A0 : FXHOLE kra0_hs230 feendra0.
  Hypothesis H_S6K_A2 : FXHOLE c2a2_hs10 s6enda2k.   Hypothesis H_FE_A2 : FXHOLE c3a2_hs20 feenda2.   Hypothesis H_FEO_A2 : FXHOLE c4a2_hs21 feendoa2.   Hypothesis H_FER_A2 : FXHOLE kra2_hs230 feendra2.
  Hypothesis H_S6K_A3 : FXHOLE c2a3_hs10 s6enda3k.   Hypothesis H_FE_A3 : FXHOLE c3a3_hs20 feenda3.   Hypothesis H_FEO_A3 : FXHOLE c4a3_hs21 feendoa3.   Hypothesis H_FER_A3 : FXHOLE kra3_hs230 feendra3.
  Hypothesis H_S6K_A1 : FXHOLE c2a1_hs10 s6enda1k.   Hypothesis H_FE_A1 : FXHOLE c3a1_hs20 feenda1.   Hypothesis H_FEO_A1 : FXHOLE c4a1_hs21 feendoa1.   Hypothesis H_FER_A1 : FXHOLE kra1_hs230 feendra1.
  Hypothesis H_S6K_B0 : FXHOLE c2b0_hs10 s6endb0k.   Hypothesis H_FE_B0 : FXHOLE c3b0_hs20 feendb0.   Hypothesis H_FEO_B0 : FXHOLE c4b0_hs21 feendob0.   Hypothesis H_FER_B0 : FXHOLE krb0_hs230 feendrb0.
  Hypothesis H_S6K_B2 : FXHOLE c2b2_hs10 s6endb2k.   Hypothesis H_FE_B2 : FXHOLE c3b2_hs20 feendb2.   Hypothesis H_FEO_B2 : FXHOLE c4b2_hs21 feendob2.   Hypothesis H_FER_B2 : FXHOLE krb2_hs230 feendrb2.
  Hypothesis H_S6K_B3 : FXHOLE c2b3_hs10 s6endb3k.   Hypothesis H_FE_B3 : FXHOLE c3b3_hs20 feendb3.   Hypothesis H_FEO_B3 : FXHOLE c4b3_hs21 feendob3.   Hypothesis H_FER_B3 : FXHOLE krb3_hs230 feendrb3.
  Hypothesis H_S6K_B1 : FXHOLE c2b1_hs10 s6endb1k.   Hypothesis H_FE_B1 : FXHOLE c3b1_hs20 feendb1.   Hypothesis H_FEO_B1 : FXHOLE c4b1_hs21 feendob1.   Hypothesis H_FER_B1 : FXHOLE krb1_hs230 feendrb1.
  Definition T98r : env -> Fs.Fs -> TSet := fun _ fs' => T_hdr refused_lit argv1 fs'.
  Lemma T98r_agree : t_agree T98r. Proof. intros E E' fs0 _. reflexivity. Qed.
  Lemma T98r_nil : forall E fs0, T98r E fs0 []. Proof. intros E fs0. left. apply t_emit_has_nil. Qed.
  Theorem refused_leaf : 67108864 <= flen cont -> crz HASEGS INIT (T_hdr refused_lit argv1 fs).
  Proof.
    intros HF. rewrite <- c_cont in HF.
    pose proof (usagek_chain sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid T98r T98r_agree T98r_nil
                  H_S6K_A0 H_FE_A0 (refused_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A0 Hne Hsl Hdr Hln Hlk_c H_FER_A0 HF)
                  H_S6K_A2 H_FE_A2 (refused_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A2 Hne Hsl Hdr Hln Hlk_c H_FER_A2 HF)
                  H_S6K_A3 H_FE_A3 (refused_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A3 Hne Hsl Hdr Hln Hlk_c H_FER_A3 HF)
                  H_S6K_A1 H_FE_A1 (refused_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A1 Hne Hsl Hdr Hln Hlk_c H_FER_A1 HF)
                  H_S6K_B0 H_FE_B0 (refused_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B0 Hne Hsl Hdr Hln Hlk_c H_FER_B0 HF)
                  H_S6K_B2 H_FE_B2 (refused_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B2 Hne Hsl Hdr Hln Hlk_c H_FER_B2 HF)
                  H_S6K_B3 H_FE_B3 (refused_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B3 Hne Hsl Hdr Hln Hlk_c H_FER_B3 HF)
                  H_S6K_B1 H_FE_B1 (refused_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B1 Hne Hsl Hdr Hln Hlk_c H_FER_B1 HF)) as RZ.
    rewrite (T_main_2 T98r _ (FULL0 HAPH sp rdraw argv envp uid hw)) in RZ; [exact RZ | exact sv_init].
  Qed.
End Leaf.
