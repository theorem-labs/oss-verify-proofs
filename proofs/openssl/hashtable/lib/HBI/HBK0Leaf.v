(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec ShapeLaws.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBArg HBChain HBUsageDefs HBOpenDefs HBHdrDefs
  BC1Thm HBUsage HBTgtGlue HBFullDefs
  BC2A0Lit BS6EndA0 BC3A0Lit BFEEndA0 BC4A0Lit BFEEndOA0 BC7A0Lit HBKge1A0 BC2A2Lit BS6EndA2 BC3A2Lit BFEEndA2 BC4A2Lit BFEEndOA2 BC7A2Lit HBKge1A2 BC2A3Lit BS6EndA3 BC3A3Lit BFEEndA3 BC4A3Lit BFEEndOA3 BC7A3Lit HBKge1A3 BC2A1Lit BS6EndA1 BC3A1Lit BFEEndA1 BC4A1Lit BFEEndOA1 BC7A1Lit HBKge1A1 BC2B0Lit BS6EndB0 BC3B0Lit BFEEndB0 BC4B0Lit BFEEndOB0 BC7B0Lit HBKge1B0 BC2B2Lit BS6EndB2 BC3B2Lit BFEEndB2 BC4B2Lit BFEEndOB2 BC7B2Lit HBKge1B2 BC2B3Lit BS6EndB3 BC3B3Lit BFEEndB3 BC4B3Lit BFEEndOB3 BC7B3Lit HBKge1B3 BC2B1Lit BS6EndB1 BC3B1Lit BFEEndB1 BC4B1Lit BFEEndOB1 BC7B1Lit HBKge1B1.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleA0 BFeHoleA0 BFeHoleOA0 BS6HoleA2 BFeHoleA2 BFeHoleOA2 BS6HoleA3 BFeHoleA3 BFeHoleOA3 BS6HoleA1 BFeHoleA1 BFeHoleOA1 BS6HoleB0 BFeHoleB0 BFeHoleOB0 BS6HoleB2 BFeHoleB2 BFeHoleOB2 BS6HoleB3 BFeHoleB3 BFeHoleOB3 BS6HoleB1 BFeHoleB1 BFeHoleOB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition main25_stmt (hs25 : acs) : Prop :=
  forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs hs25 TT0.

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
  Let c := content_of argv fs.
  Let argv1 := nth 1 argv [].
  Hypothesis Hargc : length argv = 2%nat.
  Variable cont : list byte.
  Hypothesis Hne : argv1 <> [].
  Hypothesis Hsl : path_has_slash argv1 = false.
  Hypothesis Hdr : path_is_dirref argv1 = false.
  Hypothesis Hln : (length argv1 <= 4095)%nat.
  Hypothesis Hlk : fs_lookup fs argv1 = Some cont.
  Hypothesis HK : K0 cont.
  Lemma c_cont : c = cont.
  Proof. subst c argv1. destruct argv as [|a0 [|p [|q r]]]; try discriminate Hargc. cbn in Hlk |- *. rewrite Hlk. reflexivity. Qed.
  Lemma Hlk_c : fs_lookup fs argv1 = Some c. Proof. rewrite c_cont. exact Hlk. Qed.
  Lemma HF_c : 6 <= flen c <= 65535. Proof. rewrite c_cont. exact (proj1 HK). Qed.
  Lemma HR_c : 0 <= ION.room c. Proof. rewrite c_cont. exact (proj2 HK). Qed.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation PIECE := (piece SV argH ISP fs).

  Definition T98 : env -> Fs.Fs -> TSet := fun E fs' => t_alt2 (T_cannot argv1 fs') (TT0 E fs').
  Lemma T98_agree : t_agree T98. Proof. intros E E' fs0 Hag. unfold T98. rewrite (TT0_agree E E' fs0 Hag). reflexivity. Qed.
  Lemma T98_nil : forall E fs0, T98 E fs0 []. Proof. intros E fs0. right. apply TT0_nil. Qed.
  Lemma T_main_T98 : forall E M, SV E M -> T_main T98 E fs = T98 E fs.
  Proof.
    intros E M HS.
    pose proof (HBArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M HS)) as (_ & _ & _ & H1 & _).
    unfold T_main, usage_shape. cbn [sd]. change (EVar 1) with (EVar V_ARGC). rewrite H1, Hargc. reflexivity.
  Qed.
  Lemma sv_init : SV (reblob (E0 HAPH sp rdraw brk0 argv envp uid hw) argv c) (FULL0 HAPH sp rdraw argv envp uid hw).
  Proof.
    apply SINVm_reblob.
    exact (AsanPlanSound.APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ (init_cs_ok HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask
                  ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid)).
  Qed.

  (* [comment removed for export] *)

  Hypothesis HM_A0 : main25_stmt c7a0_hs25.
  Hypothesis HM_A2 : main25_stmt c7a2_hs25.
  Hypothesis HM_A3 : main25_stmt c7a3_hs25.
  Hypothesis HM_A1 : main25_stmt c7a1_hs25.
  Hypothesis HM_B0 : main25_stmt c7b0_hs25.
  Hypothesis HM_B2 : main25_stmt c7b2_hs25.
  Hypothesis HM_B3 : main25_stmt c7b3_hs25.
  Hypothesis HM_B1 : main25_stmt c7b1_hs25.

  Theorem k0_leaf_sec : crz HASEGS (INITA sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask) (T_file argv1 cont fs).
  Proof.
    pose proof (usage_chain sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid T98 T98_agree T98_nil
                  (BS6HoleA0.s6_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA0.fe_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1A0.k0_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOA0.fe_hole_oa0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_A0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))
                  (BS6HoleA2.s6_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA2.fe_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1A2.k0_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOA2.fe_hole_oa2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_A2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))
                  (BS6HoleA3.s6_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA3.fe_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1A3.k0_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOA3.fe_hole_oa3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_A3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))
                  (BS6HoleA1.s6_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA1.fe_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1A1.k0_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOA1.fe_hole_oa1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_A1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))
                  (BS6HoleB0.s6_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB0.fe_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1B0.k0_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOB0.fe_hole_ob0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_B0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))
                  (BS6HoleB2.s6_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB2.fe_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1B2.k0_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOB2.fe_hole_ob2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_B2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))
                  (BS6HoleB3.s6_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB3.fe_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1B3.k0_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOB3.fe_hole_ob3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_B3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))
                  (BS6HoleB1.s6_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB1.fe_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (HBKge1B1.k0_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleOB1.fe_hole_ob1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) Hne Hsl Hdr Hln Hlk_c TT0 TT0_agree TT0_nil HF_c HR_c
                     (HM_B1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit))) as RZ.
    rewrite (T_main_T98 _ (FULL0 HAPH sp rdraw argv envp uid hw)) in RZ; [|exact sv_init].
    eapply crz_conseq; [exact RZ|]. unfold T98, T_file. apply t_alt2_congr_r. rewrite <- c_cont.
    exact (tt0_target HAPH sp rdraw brk0 argv envp uid hw c _ _ fs sv_init HF_c HR_c).
  Qed.
End Leaf.

Theorem k0_leaf : main25_stmt c7a0_hs25 -> main25_stmt c7a2_hs25 -> main25_stmt c7a3_hs25 -> main25_stmt c7a1_hs25 -> main25_stmt c7b0_hs25 -> main25_stmt c7b2_hs25 -> main25_stmt c7b3_hs25 -> main25_stmt c7b1_hs25 -> file_leaf_stmt K0 T_file.
Proof.
  intros MA0 MA2 MA3 MA1 MB0 MB2 MB3 MB1 lim Hlim sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk HK.
  exact (k0_leaf_sec sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk HK MA0 MA2 MA3 MA1 MB0 MB2 MB3 MB1).
Qed.
