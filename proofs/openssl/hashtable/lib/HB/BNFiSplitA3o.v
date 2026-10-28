(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheckG HBArg HBChain HBUsageDefs HBHop HBParity
  BC7A3Lit BFIaEndA3o BC7m BC7mA3oLit BC7mA3oCert BFIEndA3so.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section FiSplitA3o.
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
  Let SVF := SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c.
  Let SVA := SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c.
  Let SV1 := SVm_to1 sp rdraw brk0 argv envp uid hw c.

  (* [comment removed for export] *)
  Hypothesis H_FIa : fx_hole SV argH ISP fs (with_facts c7a3_hs25 [par_odd]) fiaenda3o.
  Hypothesis H_FIb : fx_hole SV argH ISP fs c7ma3o_hs27 fienda3so.

  Variable PHI : env -> Prop.
  Hypothesis PHI_agree : forall E E', env_agree NX0 E E' -> PHI E -> PHI E'.
  Variable T : env -> Fs.Fs -> TSet.
  Hypothesis T_agree : t_agree T.
  Hypothesis T_nil : forall E fs0, T E fs0 [].
  #[local] Notation SVP := (SVG PHI SV).
  #[local] Notation PIECE := (piece SVP argH ISP fs).

  Let SVP1 : forall E M, SVP E M -> HBArg.SINV1 sp brk0 argv envp rdraw hw uid E M := fun E M H => SV1 E M (proj1 H).
  Let SVPF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SVP E M -> SVP E M' :=
    fun E M M' Hf H => conj (SVF E M M' Hf (proj1 H)) (proj2 H).
  Let SVPA : forall E E' M, env_agree NX0 E E' -> SVP E M -> SVP E' M := fun E E' M Hag H => conj (SVA E E' M Hag (proj1 H)) (PHI_agree E E' Hag (proj2 H)).

  Hypothesis Htail : PIECE fienda3so T.

  Lemma fib_piece : PIECE c7ma3o_hs27 T.
  Proof.
    apply (hole_compose SVP argH ISP fs c7ma3o_hs27 fienda3so T); [vm_compute; lia | exact T_agree | | exact Htail].
    apply (fx_hole_phi sp rdraw argv envp uid hw fs SV NX0 PHI PHI_agree c7ma3o_hs27 fienda3so); [vm_compute; lia | exact H_FIb].
  Qed.

  Lemma mini_holes : holes_stmt HASEGS HAT AsanInit.LIMIT C7mA3o_HS SVP argH ISP (fun _ => T) fs.
  Proof.
    intros h ch Hh E R FULL m HC. unfold C7mA3o_HS in Hh. destruct (Nat.eqb h 27); [|discriminate Hh]. diet_injection Hh. exact (fib_piece E R FULL m HC).
  Qed.

  Lemma mini_piece : PIECE fiaenda3o T.
  Proof.
    intros E R FULL m HC.
    exact (ha1_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SVP SVP1 SVPF SVPA C7mA3o_HS (fun _ => T)
             (fun _ E1 E2 fs0 Hag => T_agree E1 E2 fs0 Hag) (fun _ => T_nil) (fun _ _ _ => eq_refl) mini_holes c7ma3o_IT c7ma3o_IT_ok
             0%nat true 3000%nat 400000%nat c7m_plan fiaenda3o c7ma3o_shape c7ma3o_cert E R FULL m HC).
  Qed.

  Theorem fi_split_a3o : PIECE (with_facts c7a3_hs25 [par_odd]) T.
  Proof.
    apply (hole_compose SVP argH ISP fs (with_facts c7a3_hs25 [par_odd]) fiaenda3o T); [vm_compute; lia | exact T_agree | | exact mini_piece].
    apply (fx_hole_phi sp rdraw argv envp uid hw fs SV NX0 PHI PHI_agree (with_facts c7a3_hs25 [par_odd]) fiaenda3o); [vm_compute; lia | exact H_FIa].
  Qed.
End FiSplitA3o.
