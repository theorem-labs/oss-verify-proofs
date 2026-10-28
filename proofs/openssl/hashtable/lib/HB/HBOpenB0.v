(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheck2 HBArg HBChain HBUsageDefs HBOpenDefs
  BC3B0Lit BC4n BC4l BC4B0Lit BC4nB0Cert BC4lB0Cert BFEEndOB0 BXu BXOB0Cert.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma c4nb0_shape_eq : c4nb0_shape = noent_shape. Proof. reflexivity. Qed.
Lemma c4lb0_shape_eq : c4lb0_shape = toolong_shape. Proof. reflexivity. Qed.

Section OpenB0.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  Let argv1 := nth 1 argv [].
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation PIECE := (piece SV argH ISP fs).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).
  Let SVF := SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c.
  Let SVA := SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c.
  Let SV1 := SVm_to1 sp rdraw brk0 argv envp uid hw c.
  #[local] Notation CHK1 := (ha1_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA).

  (* [comment removed for export] *)
  Lemma vals1_b0 : forall E M, SV E M -> bv_unsigned (edenot E (EVar 7)) = Z.of_nat (length argv1) /\ eb E 2%nat = argv1.
  Proof.
    intros E M H. pose proof (HBArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SV1 E M H)) as (_ & _ & _ & _ & H7 & _ & B2).
    split; [|exact B2]. change (EVar 7) with (EVar V_L1). rewrite H7, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
    assert (Z.of_nat (length argv1) <= 131071); [|lia].
    unfold argv1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl]; [apply (valid_argv_str_len argv 1 Hva Hl) | rewrite nth_overflow by lia; cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Hypothesis H_FE : FXHOLE c4b0_hs21 feendob0.

  Lemma xo_piece_b0 : PIECE feendob0 T_exit2.
  Proof.
    intros E R FULL m HC.
    exact (CHK1 (fun _ : nat => @None acs) (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
             (fun h ch Hh => ltac:(discriminate Hh)) xob0_IT xob0_IT_ok 0%nat true 3000%nat 400000%nat xu_plan feendob0 xob0_shape xob0_cert E R FULL m HC).
  Qed.
  Lemma feo_piece_b0 : PIECE c4b0_hs21 T_exit2.
  Proof. apply (hole_compose SV argH ISP fs c4b0_hs21 feendob0 T_exit2); [vm_compute; lia | intros E E' fs0 _; reflexivity | exact H_FE | exact xo_piece_b0]. Qed.

  (* [comment removed for export] *)
  Section NoEnt.
    Hypothesis Hn : argv1 = [] \/ (path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup fs argv1 = None).
    Lemma c4n_holes_b0 : holes_stmt HASEGS HAT LIM C4B0_HSn SV argH ISP HOLES4 fs.
    Proof.
      intros h ch Hh E R FULL m HC. unfold C4B0_HSn in Hh. unfold HOLES4.
      destruct (Nat.eqb h 21) eqn:HQ21; [apply Nat.eqb_eq in HQ21; subst h; diet_injection Hh; exact (feo_piece_b0 E R FULL m HC) | discriminate Hh].
    Qed.
    Lemma noent_b0 : PIECE c3b0_hs98 (fun _ fs' => T_cannot argv1 fs').
    Proof.
      intros E R FULL m HC.
      pose proof (ha2_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA (ION.iot_simple ION.ONoEnt 32) Hn
                    C4B0_HSn HOLES4 HOLES4_agree HOLES4_nil HOLES4_mod c4n_holes_b0 c4nb0_IT c4nb0_IT_ok 0%nat true 3000%nat 400000%nat
                    c4n_top c3b0_hs98 c4nb0_shape c4nb0_cert E R FULL m HC) as RZ.
      rewrite c4nb0_shape_eq in RZ. eapply crz_conseq; [exact RZ|].
      destruct (vals1_b0 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2]. exact (noent_eval E (m_fs m) argv1 U7 B2).
    Qed.
  End NoEnt.

  (* [comment removed for export] *)
  Section TooLong.
    Hypothesis Hl : (4096 <= length argv1)%nat.
    Lemma c4l_holes_b0 : holes_stmt HASEGS HAT LIM C4B0_HS SV argH ISP HOLES4 fs.
    Proof.
      intros h ch Hh E R FULL m HC. unfold C4B0_HS in Hh. unfold HOLES4.
      destruct (Nat.eqb h 21) eqn:HQ21; [apply Nat.eqb_eq in HQ21; subst h; diet_injection Hh; exact (feo_piece_b0 E R FULL m HC)|].
      destruct (Nat.eqb h 96) eqn:HQ96; [apply Nat.eqb_eq in HQ96; subst h; diet_injection Hh | discriminate Hh].
      (* [comment removed for export] *)
      exfalso. assert (KR : knows_range (kn c4b0_hs96) 7%nat 0 4095 = true) by (vm_compute; reflexivity).
      pose proof (knows_range_sound _ _ _ _ 7%nat 0 4095 KR (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H7.
      destruct (vals1_b0 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 _]. lia.
    Qed.
    Lemma toolong_b0 : PIECE c3b0_hs98 (fun _ fs' => T_cannot argv1 fs').
    Proof.
      intros E R FULL m HC.
      pose proof (ha2_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA (ION.iot_simple ION.OTooLong 32) Hl
                    C4B0_HS HOLES4 HOLES4_agree HOLES4_nil HOLES4_mod c4l_holes_b0 c4lb0_IT c4lb0_IT_ok 0%nat true 3000%nat 400000%nat
                    c4l_top c3b0_hs98 c4lb0_shape c4lb0_cert E R FULL m HC) as RZ.
      rewrite c4lb0_shape_eq in RZ. eapply crz_conseq; [exact RZ|].
      destruct (vals1_b0 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2]. exact (toolong_eval E (m_fs m) argv1 U7 B2 Hl).
    Qed.
  End TooLong.

  Theorem open_fail_b0 :
    (4096 <= length argv1)%nat \/ argv1 = [] \/ (path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup fs argv1 = None) ->
    PIECE c3b0_hs98 (fun _ fs' => T_cannot argv1 fs').
  Proof. intros [Hl | Hn]; [exact (toolong_b0 Hl) | exact (noent_b0 Hn)]. Qed.
End OpenB0.
