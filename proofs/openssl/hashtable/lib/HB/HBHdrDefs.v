(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec FileSim ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBChain HBUsageDefs HBOpenDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition short_lit : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 115; 104; 111; 114; 116; 101; 114; 32; 116; 104; 97; 110; 32; 104; 101; 97; 100; 101; 114; 10].
Definition overrun_lit : list Z := [99; 108; 105; 58; 32; 99; 111; 110; 102; 105; 103; 95; 108; 101; 110; 32; 111; 118; 101; 114; 114; 117; 110; 115; 32; 105; 110; 112; 117; 116; 10].
Definition T_lit (lit : list Z) (fs : Fs.Fs) : TSet := t_emit (map (WriteEv (Z_to_bv 64 2)) (map (Z_to_bv 8) lit)) (t_exit (Z_to_bv 64 2) fs).
Definition T_hdr (lit : list Z) (argv1 : list byte) (fs : Fs.Fs) : TSet := t_alt2 (T_cannot argv1 fs) (T_lit lit fs).

(* [comment removed for export] *)
Definition hdr_alt (lit : list Z) : shape := SAlt2 noent_shape (SEmitP 2 [SPLit lit] (SHole 24)).
Definition hdr_shape0 (lit : list Z) : shape := SCase (EVar 6) 6 (hdr_alt lit) (hdr_alt lit).
Definition hdr_shape1 (lit : list Z) : shape := hdr_alt lit.

(* [comment removed for export] *)
Definition HOLES6 (h : nat) (E : env) (fs' : Fs.Fs) : TSet := if (Nat.eqb (CAP.hole_cls h) 21 || Nat.eqb (CAP.hole_cls h) 24)%bool then T_exit2 E fs' else t_nil.
Lemma HOLES6_mod : forall h E fs0, HOLES6 h E fs0 = HOLES6 (CAP.hole_cls h) E fs0.
Proof. intros h E fs0. unfold HOLES6, CAP.hole_cls. rewrite Nat.Div0.mod_mod. reflexivity. Qed.
Lemma HOLES6_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES6 h E fs0 = HOLES6 h E' fs0.
Proof. intros h E E' fs0 _. reflexivity. Qed.
Lemma HOLES6_nil : forall h E fs0, HOLES6 h E fs0 [].
Proof. intros h E fs0. unfold HOLES6. destruct (Nat.eqb (CAP.hole_cls h) 21 || Nat.eqb (CAP.hole_cls h) 24)%bool; [apply CXS.t_exit_has_nil | reflexivity]. Qed.

Section Eval.
  Variables (E : env) (fs : Fs.Fs) (argv1 : list byte) (lit : list Z).
  Hypothesis U7 : bv_unsigned (edenot E (EVar 7)) = Z.of_nat (length argv1).
  Hypothesis B2 : eb E 2%nat = argv1.
  #[local] Notation X2 := (t_exit (Z_to_bv 64 2) fs).
  Lemma noent6 : t_eq (sd HOLES6 t_nil E fs noent_shape) (T_cannot argv1 fs).
  Proof. exact (noent_eval E fs argv1 U7 B2). Qed.
  Lemma leafL : t_eq (t_emit (Wp E 2 [SPLit lit]) X2) (T_lit lit fs).
  Proof. unfold Wp, T_lit. cbn [flat_map piece_den]. rewrite app_nil_r. apply t_eq_refl. Qed.
  Lemma alt6_eval : t_eq (sd HOLES6 t_nil E fs (hdr_alt lit)) (T_hdr lit argv1 fs).
  Proof. unfold hdr_alt, T_hdr. cbn [sd]. apply t_eq_alt2; [exact noent6 | exact leafL]. Qed.
  Lemma hdr_eval1 : t_eq (sd HOLES6 t_nil E fs (hdr_shape1 lit)) (T_hdr lit argv1 fs).
  Proof. exact alt6_eval. Qed.
  Lemma hdr_eval0 : t_eq (sd HOLES6 t_nil E fs (hdr_shape0 lit)) (T_hdr lit argv1 fs).
  Proof. unfold hdr_shape0. cbn [sd]. destruct (_ <=? _)%Z; exact alt6_eval. Qed.
End Eval.
