(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HAPlanImage HAAtable HACheck0 HACheck1 HAArg HAChain HAUsageDefs HAOpenDefs HASplit
  C1 C1HS C1Cert C1Thm C2AStart
  C2A0Lit C2A2Lit C2A3Lit S6EndA0 S6EndA2 S6EndA3 C3A0Lit C3A2Lit C3A3Lit FEEndA0 FEEndA2 FEEndA3 HAUsageA0 HAUsageA2 HAUsageA3  C2A1Lit S6EndA1 C3A1Lit FEEndA1 HAUsageA1
  C2B0Lit C2B2Lit C2B3Lit S6EndB0 S6EndB2 S6EndB3 C3B0Lit C3B2Lit C3B3Lit FEEndB0 FEEndB2 FEEndB3 HAUsageB0 HAUsageB2 HAUsageB3  C2B1Lit S6EndB1 C3B1Lit FEEndB1 HAUsageB1.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section Usage.
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
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation PIECE := (piece SV argH ISP fs).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).
  Let SVF := SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c.
  Let SVA := SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c.
  Let SV1 := SVm_to1 sp rdraw brk0 argv envp uid hw c.

  (* [comment removed for export] *)
  Variable T98 : env -> Fs.Fs -> TSet.
  Hypothesis T98_agree : t_agree T98.
  Hypothesis T98_nil : forall E fs0, T98 E fs0 [].
  (* [comment removed for export] *)
  Hypothesis H_S6_A0 : FXHOLE c2a0_hs10 s6enda0.   Hypothesis H_FE_A0 : FXHOLE c3a0_hs20 feenda0.   Hypothesis H98_A0 : PIECE c3a0_hs98 T98.
  Hypothesis H_S6_A2 : FXHOLE c2a2_hs10 s6enda2.   Hypothesis H_FE_A2 : FXHOLE c3a2_hs20 feenda2.   Hypothesis H98_A2 : PIECE c3a2_hs98 T98.
  Hypothesis H_S6_A3 : FXHOLE c2a3_hs10 s6enda3.   Hypothesis H_FE_A3 : FXHOLE c3a3_hs20 feenda3.   Hypothesis H98_A3 : PIECE c3a3_hs98 T98.
  Hypothesis H_S6_A1 : FXHOLE c2a1_hs10 s6enda1.   Hypothesis H_FE_A1 : FXHOLE c3a1_hs20 feenda1.   Hypothesis H98_A1 : PIECE c3a1_hs98 T98.
  Hypothesis H_S6_B0 : FXHOLE c2b0_hs10 s6endb0.   Hypothesis H_FE_B0 : FXHOLE c3b0_hs20 feendb0.   Hypothesis H98_B0 : PIECE c3b0_hs98 T98.
  Hypothesis H_S6_B2 : FXHOLE c2b2_hs10 s6endb2.   Hypothesis H_FE_B2 : FXHOLE c3b2_hs20 feendb2.   Hypothesis H98_B2 : PIECE c3b2_hs98 T98.
  Hypothesis H_S6_B3 : FXHOLE c2b3_hs10 s6endb3.   Hypothesis H_FE_B3 : FXHOLE c3b3_hs20 feendb3.   Hypothesis H98_B3 : PIECE c3b3_hs98 T98.
  Hypothesis H_S6_B1 : FXHOLE c2b1_hs10 s6endb1.   Hypothesis H_FE_B1 : FXHOLE c3b1_hs20 feendb1.   Hypothesis H98_B1 : PIECE c3b1_hs98 T98.

  #[local] Notation TM := (T_main T98).
  #[local] Notation TMA := (T_main_agree T98 T98_agree).
  Let UA0 : PIECE c2a0_start TM := usage_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_A0 H_FE_A0 H98_A0.
  Let UA2 : PIECE c2a2_start TM := usage_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_A2 H_FE_A2 H98_A2.
  Let UA3 : PIECE c2a3_start TM := usage_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_A3 H_FE_A3 H98_A3.
  Let UA0all : PIECE c2a_start0 TM := piece_split3 SV argH ISP fs c2a_start0 TM c2a_start0_kr UA0 UA2 UA3.
  Let UA1 : PIECE c2a_start1 TM := usage_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_A1 H_FE_A1 H98_A1.
  Let UB0 : PIECE c2b0_start TM := usage_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_B0 H_FE_B0 H98_B0.
  Let UB2 : PIECE c2b2_start TM := usage_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_B2 H_FE_B2 H98_B2.
  Let UB3 : PIECE c2b3_start TM := usage_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_B3 H_FE_B3 H98_B3.
  Let UB0all : PIECE c2b_start0 TM := piece_split3 SV argH ISP fs c2b_start0 TM c2b_start0_kr UB0 UB2 UB3.
  Let UB1 : PIECE c2b_start1 TM := usage_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit T98 T98_agree T98_nil H_S6_B1 H_FE_B1 H98_B1.

  (* [comment removed for export] *)
  Lemma split_piece : forall cs csa csb, is_ecall_at HASEGS cs = true -> node_brk2 HAT NX0 LIM cs = Some (false, csb, csa) ->
    PIECE csa TM -> PIECE csb TM -> PIECE cs TM.
  Proof.
    intros cs csa csb Hec Hn PA PB E R FULL m HC.
    pose proof (ob1_brk2 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA) as B2.
    refine (proj2 (B2 cs false csb csa E R FULL m (TM E (m_fs m)) (TM E (m_fs m)) HC Hec Hn _ _) eq_refl (t_eq_refl _)).
    - intros _ E' R' FULL' m' [Hag _] HC' Hfs. rewrite (TMA E E' (m_fs m) Hag), <- Hfs. exact (PB E' R' FULL' m' HC').
    - intros E' R' FULL' m' [Hag _] HC' Hfs. rewrite (TMA E E' (m_fs m) Hag), <- Hfs. exact (PA E' R' FULL' m' HC').
  Qed.
  Lemma c1hs0_piece : PIECE c1_hs0 TM. Proof. exact (split_piece c1_hs0 c2a_start0 c2b_start0 c1_hs0_ecall c1_hs0_brk2 UA0all UB0all). Qed.
  Lemma c1hs1_piece : PIECE c1_hs1 TM. Proof. exact (split_piece c1_hs1 c2a_start1 c2b_start1 c1_hs1_ecall c1_hs1_brk2 UA1 UB1). Qed.

  (* [comment removed for export] *)
  Definition HOLES1 (h : nat) (E : env) (fs' : Fs.Fs) : TSet := TM E fs'.
  Lemma c1_holes : holes_stmt HASEGS HAT LIM C1_HS SV argH ISP HOLES1 fs.
  Proof.
    intros h ch Hh E R FULL m HC. unfold HOLES1. destruct h as [|[|h]]; cbn in Hh;
      [diet_injection Hh; exact (c1hs0_piece E R FULL m HC) | diet_injection Hh; exact (c1hs1_piece E R FULL m HC) | discriminate Hh].
  Qed.

  Theorem usage_chain :
    crz HASEGS (init_config HASEGS Asan.M.init_pc HAPH sp brk0 mbase rdraw lim
                  (inp argv envp fs stdin uid gid hw groups net nofile sigmask))
        (TM (reblob (E0 HAPH sp rdraw brk0 argv envp uid hw) argv c) fs).
  Proof.
    rewrite (init_cfg_eq HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Asan.M.init_pc (eq_trans ha_entry_eq (eq_sym hat_entry))).
    pose proof (init_cs_ok HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask
                  ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid) as HC.
    apply (cs_ok_reblob HASEGS HAT HAPH sp rdraw brk0 argv envp uid hw c) in HC; [|exact ha_init_noblob].
    apply cxs_cs_ok_of_aps in HC.
    pose proof (ha0sv_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA C1_HS HOLES1 (fun h => TMA) (fun h => T_main_nil T98 T98_nil) (fun _ _ _ => eq_refl) c1_holes
             C1_IT C1_IT_ok 0%nat true 3000%nat 400000%nat c1_plan (init_acs_of HAT) c1_shape c1_cert _ _ _ _ HC) as RZ.
    unfold c1_shape in RZ. cbn [sd] in RZ. unfold HOLES1 in RZ.
    rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC) in RZ.
    destruct (_ <=? _)%Z in RZ; exact RZ.
  Qed.
End Usage.
