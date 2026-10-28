(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBArg HBChain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition usage_shape : shape := (SCase (EVar 1) 1 (SCase (EVar 3) 63 (SCase (EVar 3) 0 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20))) (SCase (EVar 3) 64 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SCase (EVar 3) 73 (SCase (EVar 3) 66 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SHole 20)))) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)))))) (SCase (EVar 1) 2 (SHole 98) (SCase (EVar 3) 63 (SCase (EVar 3) 0 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20))) (SCase (EVar 3) 64 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SCase (EVar 3) 73 (SCase (EVar 3) 66 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SHole 20)))) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)))))))).

Definition T_exit2 : env -> Fs.Fs -> TSet := fun _ fs' => t_exit (Z_to_bv 64 2) fs'.

Section Holes3.
  Variable T98 : env -> Fs.Fs -> TSet.
  Hypothesis T98_agree : t_agree T98.
  Hypothesis T98_nil : forall E fs0, T98 E fs0 [].
  Definition HOLES3 (h : nat) (E : env) (fs' : Fs.Fs) : TSet :=
    if Nat.eqb (CAP.hole_cls h) 20 then T_exit2 E fs' else if Nat.eqb (CAP.hole_cls h) 98 then T98 E fs' else t_nil.
  Lemma HOLES3_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES3 h E fs0 = HOLES3 h E' fs0.
  Proof. intros h E E' fs0 Hag. unfold HOLES3. destruct (Nat.eqb (CAP.hole_cls h) 20); [reflexivity|]. destruct (Nat.eqb (CAP.hole_cls h) 98); [exact (T98_agree E E' fs0 Hag) | reflexivity]. Qed.
  Lemma HOLES3_nil : forall h E fs0, HOLES3 h E fs0 [].
  Proof. intros h E fs0. unfold HOLES3. destruct (Nat.eqb (CAP.hole_cls h) 20); [apply CXS.t_exit_has_nil|]. destruct (Nat.eqb (CAP.hole_cls h) 98); [apply T98_nil | reflexivity]. Qed.
  Lemma HOLES3_mod : forall h E fs0, HOLES3 h E fs0 = HOLES3 (CAP.hole_cls h) E fs0.
  Proof. intros h E fs0. unfold HOLES3, CAP.hole_cls. rewrite Nat.Div0.mod_mod. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition T_main : env -> Fs.Fs -> TSet := fun E fs' => sd HOLES3 t_nil E fs' usage_shape.
  Lemma T_main_agree : t_agree T_main.
  Proof. intros E E' fs0 Hag. unfold T_main. apply (CXS.sd_agree NX0 HOLES3 HOLES3_agree); [exact Hag | reflexivity]. Qed.
  Lemma T_main_nil : forall E fs0, T_main E fs0 [].
  Proof. intros E fs0. unfold T_main. apply (CXS.sd_has_nil HOLES3 HOLES3_nil). reflexivity. Qed.
  Definition HOLES2 (h : nat) (E : env) (fs' : Fs.Fs) : TSet := if Nat.eqb (CAP.hole_cls h) 10 then T_main E fs' else t_nil.
  Lemma HOLES2_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES2 h E fs0 = HOLES2 h E' fs0.
  Proof. intros h E E' fs0 Hag. unfold HOLES2. destruct (Nat.eqb (CAP.hole_cls h) 10); [exact (T_main_agree E E' fs0 Hag) | reflexivity]. Qed.
  Lemma HOLES2_nil : forall h E fs0, HOLES2 h E fs0 [].
  Proof. intros h E fs0. unfold HOLES2. destruct (Nat.eqb (CAP.hole_cls h) 10); [apply T_main_nil | reflexivity]. Qed.
  Lemma HOLES2_mod : forall h E fs0, HOLES2 h E fs0 = HOLES2 (CAP.hole_cls h) E fs0.
  Proof. intros h E fs0. unfold HOLES2, CAP.hole_cls. rewrite Nat.Div0.mod_mod. reflexivity. Qed.
End Holes3.

Lemma SVm_to1 : forall sp rdraw brk0 argv envp uid hw c E M,
  SINVm HAPH sp rdraw brk0 argv envp uid hw c E M -> HBArg.SINV1 sp brk0 argv envp rdraw hw uid E M.
Proof. intros sp rdraw brk0 argv envp uid hw c E M (H0 & H1 & H2 & _). exact (conj H0 (conj H1 H2)). Qed.

Lemma ha_init_noblob : acs_noblob (init_acs_of HAT) = true.
Proof. vm_compute. reflexivity. Qed.
