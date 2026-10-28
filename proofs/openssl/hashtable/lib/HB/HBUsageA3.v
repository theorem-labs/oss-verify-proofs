(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBArg HBChain HBUsageDefs
  BC1HS BC2AStart HBSplit BSt3a BC2A3Lit BC2A3Cert BS6EndA3 BC3 BC3A3Lit BC3A3Cert BFEEndA3 BXu BXA3Cert.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma c3a3_shape_eq : c3a3_shape = usage_shape. Proof. reflexivity. Qed.

Section UsageA3.
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
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation PIECE := (piece SV argH ISP fs).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).
  Let SVF := SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c.
  Let SVA := SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c.
  #[local] Notation CHK1 := (ha1_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV (SVm_to1 sp rdraw brk0 argv envp uid hw c) SVF SVA).

  Variable T98 : env -> Fs.Fs -> TSet.
  Hypothesis T98_agree : t_agree T98.
  Hypothesis T98_nil : forall E fs0, T98 E fs0 [].
  (* [comment removed for export] *)
  Hypothesis H_S6 : FXHOLE c2a3_hs10 s6enda3.
  Hypothesis H_FE : FXHOLE c3a3_hs20 feenda3.
  Hypothesis H98 : PIECE c3a3_hs98 T98.

  Lemma x_piece_a3 : PIECE feenda3 T_exit2.
  Proof.
    intros E R FULL m HC.
    exact (CHK1 (fun _ : nat => @None acs) (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
             (fun h ch Hh => ltac:(discriminate Hh)) xa3_IT xa3_IT_ok 0%nat true 3000%nat 400000%nat xu_plan feenda3 xa3_shape xa3_cert E R FULL m HC).
  Qed.
  Lemma fe_piece_a3 : PIECE c3a3_hs20 T_exit2.
  Proof. apply (hole_compose SV argH ISP fs c3a3_hs20 feenda3 T_exit2); [vm_compute; lia | intros E E' fs0 _; reflexivity | exact H_FE | exact x_piece_a3]. Qed.
  Lemma c3_holes_a3 : holes_stmt HASEGS HAT LIM C3A3_HS SV argH ISP (HOLES3 T98) fs.
  Proof.
    intros h ch Hh E R FULL m HC. unfold C3A3_HS in Hh. unfold HOLES3.
    destruct (Nat.eqb h 20) eqn:HQ20; [apply Nat.eqb_eq in HQ20; subst h; diet_injection Hh; exact (fe_piece_a3 E R FULL m HC)|].
    destruct (Nat.eqb h 98) eqn:HQ98; [apply Nat.eqb_eq in HQ98; subst h; diet_injection Hh; exact (H98 E R FULL m HC) | discriminate Hh].
  Qed.
  Lemma c3_piece_a3 : PIECE s6enda3 (T_main T98).
  Proof.
    intros E R FULL m HC. unfold T_main. rewrite <- c3a3_shape_eq.
    exact (CHK1 C3A3_HS (HOLES3 T98) (HOLES3_agree T98 T98_agree) (HOLES3_nil T98 T98_nil) (HOLES3_mod T98) c3_holes_a3 c3a3_IT c3a3_IT_ok 0%nat true 3000%nat 400000%nat
             c3_top s6enda3 c3a3_shape c3a3_cert E R FULL m HC).
  Qed.
  Lemma s6_piece_a3 : PIECE c2a3_hs10 (T_main T98).
  Proof. apply (hole_compose SV argH ISP fs c2a3_hs10 s6enda3 (T_main T98)); [vm_compute; lia | exact (T_main_agree T98 T98_agree) | exact H_S6 | exact c3_piece_a3]. Qed.
  Lemma c2_holes_a3 : holes_stmt HASEGS HAT LIM C2A3_HS SV argH ISP (HOLES2 T98) fs.
  Proof.
    intros h ch Hh E R FULL m HC. unfold C2A3_HS in Hh. unfold HOLES2.
    destruct (Nat.eqb h 10) eqn:HQ10; [apply Nat.eqb_eq in HQ10; subst h; diet_injection Hh; exact (s6_piece_a3 E R FULL m HC) | discriminate Hh].
  Qed.
  Lemma c2a3_shape_eq : c2a3_shape = SHole 10. Proof. reflexivity. Qed.
  Theorem usage_a3 : PIECE c2a3_start (T_main T98).
  Proof.
    intros E R FULL m HC.
    pose proof (CHK1 C2A3_HS (HOLES2 T98) (HOLES2_agree T98 T98_agree) (HOLES2_nil T98 T98_nil) (HOLES2_mod T98) c2_holes_a3 c2a3_IT c2a3_IT_ok 0%nat true 3000%nat 400000%nat
             st3a_plan c2a3_start c2a3_shape c2a3_cert E R FULL m HC) as RZ.
    rewrite c2a3_shape_eq in RZ. exact RZ.
  Qed.
End UsageA3.
