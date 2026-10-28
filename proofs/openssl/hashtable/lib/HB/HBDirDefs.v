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

Definition readerr_bytes (argv1 : list byte) : list byte :=
  map (Z_to_bv 8) [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32] ++ argv1 ++ map (Z_to_bv 8) [10].
Definition T_readerr (argv1 : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (map (WriteEv (Z_to_bv 64 2)) (readerr_bytes argv1)) (t_exit (Z_to_bv 64 2) fs).
Definition T_dir (argv1 : list byte) (fs : Fs.Fs) : TSet := t_alt2 (T_cannot argv1 fs) (T_readerr argv1 fs).

(* [comment removed for export] *)
Definition dir_shape0 : shape := (SCase (EVar 7) 0 (SHole 95) (SCase (EVar 7) 2 (SCase (EVar 6) 6 (SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]] (SHole 23))) (SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]] (SHole 23)))) (SHole 94))).
Definition dir_alt : shape :=
  SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21))
        (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]] (SHole 23)).
Definition dir_shape1 : shape := SCase (EVar 7) 0 (SHole 95) (SCase (EVar 7) 2 dir_alt (SHole 94)).

(* [comment removed for export] *)
Definition HOLES5 (h : nat) (E : env) (fs' : Fs.Fs) : TSet := if (Nat.eqb (CAP.hole_cls h) 21 || Nat.eqb (CAP.hole_cls h) 23)%bool then T_exit2 E fs' else t_nil.
Lemma HOLES5_mod : forall h E fs0, HOLES5 h E fs0 = HOLES5 (CAP.hole_cls h) E fs0.
Proof. intros h E fs0. unfold HOLES5, CAP.hole_cls. rewrite Nat.Div0.mod_mod. reflexivity. Qed.
Lemma HOLES5_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES5 h E fs0 = HOLES5 h E' fs0.
Proof. intros h E E' fs0 _. reflexivity. Qed.
Lemma HOLES5_nil : forall h E fs0, HOLES5 h E fs0 [].
Proof. intros h E fs0. unfold HOLES5. destruct (Nat.eqb (CAP.hole_cls h) 21 || Nat.eqb (CAP.hole_cls h) 23)%bool; [apply CXS.t_exit_has_nil | reflexivity]. Qed.

Lemma dirref_len : forall p, path_is_dirref p = true -> (1 <= length p <= 2)%nat.
Proof.
  intros p H. unfold path_is_dirref in H. apply orb_prop in H as [H|H].
  - destruct (list_eq_dec (fun a b : byte => bv_eq_dec _ a b) p dot_path) as [->|Hn]; [cbn; lia | rewrite (path_eqb_neq _ _ Hn) in H; discriminate H].
  - destruct (list_eq_dec (fun a b : byte => bv_eq_dec _ a b) p dotdot_path) as [->|Hn]; [cbn; lia | rewrite (path_eqb_neq _ _ Hn) in H; discriminate H].
Qed.

Section Eval.
  Variables (E : env) (fs : Fs.Fs) (argv1 : list byte).
  Hypothesis U7 : bv_unsigned (edenot E (EVar 7)) = Z.of_nat (length argv1).
  Hypothesis B2 : eb E 2%nat = argv1.
  Hypothesis HL : (1 <= length argv1 <= 2)%nat.
  #[local] Notation X2 := (t_exit (Z_to_bv 64 2) fs).
  Lemma leafR : t_eq (t_emit (Wp E 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]]) X2) (T_readerr argv1 fs).
  Proof. unfold Wp, T_readerr, readerr_bytes. cbn [flat_map piece_den]. rewrite B2, app_nil_r. apply t_eq_refl. Qed.
  Lemma alt_eval : t_eq (sd HOLES5 t_nil E fs dir_alt) (T_dir argv1 fs).
  Proof. unfold dir_alt, T_dir. cbn [sd]. apply t_eq_alt2; [exact (leafA E fs argv1 B2) | exact leafR]. Qed.
  Lemma dir_eval1 : t_eq (sd HOLES5 t_nil E fs dir_shape1) (T_dir argv1 fs).
  Proof.
    unfold dir_shape1. cbn [sd]. rewrite U7.
    destruct (Z.leb_spec (Z.of_nat (length argv1)) 0); [lia|]. destruct (Z.leb_spec (Z.of_nat (length argv1)) 2); [exact alt_eval | lia].
  Qed.
  Lemma dir_eval0 : t_eq (sd HOLES5 t_nil E fs dir_shape0) (T_dir argv1 fs).
  Proof.
    change dir_shape0 with (SCase (EVar 7) 0 (SHole 95) (SCase (EVar 7) 2 (SCase (EVar 6) 6 dir_alt dir_alt) (SHole 94))). cbn [sd]. rewrite U7.
    destruct (Z.leb_spec (Z.of_nat (length argv1)) 0); [lia|]. destruct (Z.leb_spec (Z.of_nat (length argv1)) 2); [|lia].
    destruct (_ <=? _)%Z; exact alt_eval.
  Qed.
End Eval.
