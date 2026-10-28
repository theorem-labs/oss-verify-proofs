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
  BC2A0Lit BS6EndA0K BC3A0Lit BC3A0LitK BFEEndA0 BC4A0Lit BFEEndOA0 HBKge1A0 BC2A2Lit BS6EndA2K BC3A2Lit BC3A2LitK BFEEndA2 BC4A2Lit BFEEndOA2 HBKge1A2 BC2A3Lit BS6EndA3K BC3A3Lit BC3A3LitK BFEEndA3 BC4A3Lit BFEEndOA3 HBKge1A3 BC2A1Lit BS6EndA1K BC3A1Lit BC3A1LitK BFEEndA1 BC4A1Lit BFEEndOA1 HBKge1A1 BC2B0Lit BS6EndB0K BC3B0Lit BC3B0LitK BFEEndB0 BC4B0Lit BFEEndOB0 HBKge1B0 BC2B2Lit BS6EndB2K BC3B2Lit BC3B2LitK BFEEndB2 BC4B2Lit BFEEndOB2 HBKge1B2 BC2B3Lit BS6EndB3K BC3B3Lit BC3B3LitK BFEEndB3 BC4B3Lit BFEEndOB3 HBKge1B3 BC2B1Lit BS6EndB1K BC3B1Lit BC3B1LitK BFEEndB1 BC4B1Lit BFEEndOB1 HBKge1B1 BC1Thm HBUsageK.
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
  #[local] Notation INIT := (init_config HASEGS AsanUbsan.M.init_pc HAPH sp brk0 mbase rdraw lim (inp argv envp fs stdin uid gid hw groups net nofile sigmask)).
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
    pose proof (HBArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M HS)) as (_ & _ & _ & H1 & _).
    unfold T_main, usage_shape. cbn [sd]. change (EVar 1) with (EVar V_ARGC). rewrite H1, Hargc. reflexivity.
  Qed.
  Hypothesis H_S6K_A0 : FXHOLE c2a0_hs10 s6enda0k.   Hypothesis H_FE_A0 : FXHOLE c3a0_hs20 feenda0.   Hypothesis H_FEO_A0 : FXHOLE c4a0_hs21 feendoa0.
  Hypothesis H_S6K_A2 : FXHOLE c2a2_hs10 s6enda2k.   Hypothesis H_FE_A2 : FXHOLE c3a2_hs20 feenda2.   Hypothesis H_FEO_A2 : FXHOLE c4a2_hs21 feendoa2.
  Hypothesis H_S6K_A3 : FXHOLE c2a3_hs10 s6enda3k.   Hypothesis H_FE_A3 : FXHOLE c3a3_hs20 feenda3.   Hypothesis H_FEO_A3 : FXHOLE c4a3_hs21 feendoa3.
  Hypothesis H_S6K_A1 : FXHOLE c2a1_hs10 s6enda1k.   Hypothesis H_FE_A1 : FXHOLE c3a1_hs20 feenda1.   Hypothesis H_FEO_A1 : FXHOLE c4a1_hs21 feendoa1.
  Hypothesis H_S6K_B0 : FXHOLE c2b0_hs10 s6endb0k.   Hypothesis H_FE_B0 : FXHOLE c3b0_hs20 feendb0.   Hypothesis H_FEO_B0 : FXHOLE c4b0_hs21 feendob0.
  Hypothesis H_S6K_B2 : FXHOLE c2b2_hs10 s6endb2k.   Hypothesis H_FE_B2 : FXHOLE c3b2_hs20 feendb2.   Hypothesis H_FEO_B2 : FXHOLE c4b2_hs21 feendob2.
  Hypothesis H_S6K_B3 : FXHOLE c2b3_hs10 s6endb3k.   Hypothesis H_FE_B3 : FXHOLE c3b3_hs20 feendb3.   Hypothesis H_FEO_B3 : FXHOLE c4b3_hs21 feendob3.
  Hypothesis H_S6K_B1 : FXHOLE c2b1_hs10 s6endb1k.   Hypothesis H_FE_B1 : FXHOLE c3b1_hs20 feendb1.   Hypothesis H_FEO_B1 : FXHOLE c4b1_hs21 feendob1.
  (* [comment removed for export] *)
  Variable TT : env -> Fs.Fs -> TSet.
  Hypothesis TT_agree : t_agree TT.
  Hypothesis TT_nil : forall E fs0, TT E fs0 [].
  Hypothesis H_FI_A0 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_a0 k) TT.
  Hypothesis H_FI_A2 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_a2 k) TT.
  Hypothesis H_FI_A3 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_a3 k) TT.
  Hypothesis H_FI_A1 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_a1 k) TT.
  Hypothesis H_FI_B0 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_b0 k) TT.
  Hypothesis H_FI_B2 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_b2 k) TT.
  Hypothesis H_FI_B3 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_b3 k) TT.
  Hypothesis H_FI_B1 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_b1 k) TT.
  Definition T98k : env -> Fs.Fs -> TSet := fun E fs' => t_alt2 (T_cannot argv1 fs') (TT E fs').
  Lemma T98k_agree : t_agree T98k. Proof. intros E E' fs0 Ha. unfold T98k. rewrite (TT_agree E E' fs0 Ha). reflexivity. Qed.
  Lemma T98k_nil : forall E fs0, T98k E fs0 []. Proof. intros E fs0. left. apply t_emit_has_nil. Qed.
  Theorem kge1_leaf : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen cont <= 2 ^ (16 + k) - 1 -> crz HASEGS INIT (t_alt2 (T_cannot argv1 fs) (TT EINIT fs)).
  Proof.
    intros k Hk HF. rewrite <- c_cont in HF.
    pose proof (usagek_chain sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid T98k T98k_agree T98k_nil
                  H_S6K_A0 H_FE_A0 (kge1_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A0 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_A0 k Hk HF))
                  H_S6K_A2 H_FE_A2 (kge1_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A2 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_A2 k Hk HF))
                  H_S6K_A3 H_FE_A3 (kge1_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A3 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_A3 k Hk HF))
                  H_S6K_A1 H_FE_A1 (kge1_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_A1 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_A1 k Hk HF))
                  H_S6K_B0 H_FE_B0 (kge1_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B0 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_B0 k Hk HF))
                  H_S6K_B2 H_FE_B2 (kge1_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B2 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_B2 k Hk HF))
                  H_S6K_B3 H_FE_B3 (kge1_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B3 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_B3 k Hk HF))
                  H_S6K_B1 H_FE_B1 (kge1_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO_B1 Hne Hsl Hdr Hln Hlk_c TT TT_agree TT_nil k Hk HF (H_FI_B1 k Hk HF))) as RZ.
    rewrite (T_main_2 T98k _ (FULL0 HAPH sp rdraw argv envp uid hw)) in RZ; [exact RZ | exact sv_init].
  Qed.
End Leaf.
