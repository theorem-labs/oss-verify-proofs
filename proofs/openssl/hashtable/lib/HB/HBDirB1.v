(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheck2 HBArg HBChain HBUsageDefs HBOpenDefs HBDirDefs
  BC3B1Lit BC4e BC4d1 BC4B1Lit BFEEndOB1 HBOpenB1 BC5B1Lit BC5B1Cert BFEEndDB1 BXu BXDB1Cert.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma c5b1_shape_eq : c5b1_shape = dir_shape1. Proof. reflexivity. Qed.

Section DirB1.
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
  Hypothesis H_FEO : FXHOLE c4b1_hs21 feendob1.
  Hypothesis H_FED : FXHOLE c5b1_hs23 feenddb1.
  Hypothesis Hd : path_is_dirref argv1 = true.

  Lemma xd_piece_b1 : PIECE feenddb1 T_exit2.
  Proof.
    intros E R FULL m HC.
    exact (CHK1 (fun _ : nat => @None acs) (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
             (fun h ch Hh => ltac:(discriminate Hh)) xdb1_IT xdb1_IT_ok 0%nat true 3000%nat 400000%nat xu_plan feenddb1 xdb1_shape xdb1_cert E R FULL m HC).
  Qed.
  Lemma fed_piece_b1 : PIECE c5b1_hs23 T_exit2.
  Proof. apply (hole_compose SV argH ISP fs c5b1_hs23 feenddb1 T_exit2); [vm_compute; lia | intros E E' fs0 _; reflexivity | exact H_FED | exact xd_piece_b1]. Qed.

  Lemma c5_holes_b1 : holes_stmt HASEGS HAT LIM C5B1_HS SV argH ISP HOLES5 fs.
  Proof.
    intros h ch Hh E R FULL m HC. unfold C5B1_HS, C5B1_HS0 in Hh. unfold HOLES5.
    pose proof (dirref_len argv1 Hd) as HL.
    destruct (vals1_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 _].
    destruct (Nat.eqb h 21) eqn:H21.
    { apply Nat.eqb_eq in H21; subst h. diet_injection Hh. cbn [orb]. exact (feo_piece_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO E R FULL m HC). }
    destruct (Nat.eqb h 23) eqn:H23.
    { apply Nat.eqb_eq in H23; subst h. diet_injection Hh. cbn [orb]. exact (fed_piece_b1 E R FULL m HC). }
    exfalso. destruct (Nat.eqb h 94).
    { diet_injection Hh. assert (KR : knows_range (kn c5b1_hs94) 7%nat 3 (2 ^ 64) = true) by (vm_compute; reflexivity).
      pose proof (knows_range_sound _ _ _ _ 7%nat 3 (2 ^ 64) KR (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H7. subst argv1. lia. }
    destruct (Nat.eqb h 95); [|discriminate Hh].
    diet_injection Hh. assert (KR : knows_range (kn c5b1_hs95) 7%nat 0 0 = true) by (vm_compute; reflexivity).
    pose proof (knows_range_sound _ _ _ _ 7%nat 0 0 KR (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H7. subst argv1. lia.
  Qed.

  Theorem dir_b1 : PIECE c3b1_hs98 (fun _ fs' => T_dir argv1 fs').
  Proof.
    intros E R FULL m HC.
    pose proof (ha2_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA (ION.iot_simple ION.ODir 32)
                  (conj Hd (ltac:(pose proof (dirref_len argv1 Hd); lia) : (length argv1 <= 4095)%nat))
                  C5B1_HS HOLES5 HOLES5_agree HOLES5_nil HOLES5_mod c5_holes_b1 c5b1_IT c5b1_IT_ok 0%nat true 3000%nat 400000%nat
                  c4d1_top c3b1_hs98 c5b1_shape c5b1_cert E R FULL m HC) as RZ.
    rewrite c5b1_shape_eq in RZ. eapply crz_conseq; [exact RZ|].
    destruct (vals1_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2].
    exact (dir_eval1 E (m_fs m) argv1 U7 B2 (dirref_len argv1 Hd)).
  Qed.
End DirB1.
