(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBChain HBUsageDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition cannot_bytes (argv1 : list byte) : list byte :=
  map (Z_to_bv 8) [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32] ++ argv1 ++ map (Z_to_bv 8) [10].
Definition T_cannot (argv1 : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (map (WriteEv (Z_to_bv 64 2)) (cannot_bytes argv1)) (t_exit (Z_to_bv 64 2) fs).

Definition noent_shape : shape := (SCase (EVar 7) 63 (SCase (EVar 7) 0 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SHole 21)) (SCase (EVar 7) 62 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SHole 21))))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))).
Definition toolong_shape : shape := (SCase (EVar 7) 4095 (SHole 96) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))).

(* [comment removed for export] *)
Definition HOLES4 (h : nat) (E : env) (fs' : Fs.Fs) : TSet := if Nat.eqb (CAP.hole_cls h) 21 then T_exit2 E fs' else t_nil.
Lemma HOLES4_mod : forall h E fs0, HOLES4 h E fs0 = HOLES4 (CAP.hole_cls h) E fs0.
Proof. intros h E fs0. unfold HOLES4, CAP.hole_cls. rewrite Nat.Div0.mod_mod. reflexivity. Qed.
Lemma HOLES4_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES4 h E fs0 = HOLES4 h E' fs0.
Proof. intros h E E' fs0 _. reflexivity. Qed.
Lemma HOLES4_nil : forall h E fs0, HOLES4 h E fs0 [].
Proof. intros h E fs0. unfold HOLES4. destruct (Nat.eqb (CAP.hole_cls h) 21); [apply CXS.t_exit_has_nil | reflexivity]. Qed.

(* [comment removed for export] *)
Fixpoint knows_range (k : list kentry) (v : nat) (lo hi : Z) : bool :=
  match k with
  | [] => false
  | KRange (EVar w) l h :: r => if (Nat.eqb w v && Z.leb lo l && Z.leb h hi)%bool then true else knows_range r v lo hi
  | _ :: r => knows_range r v lo hi
  end.
Lemma knows_range_sound : forall segs E M k v lo hi, knows_range k v lo hi = true -> know_ok segs E M k -> lo <= bv_unsigned (edenot E (EVar v)) <= hi.
Proof.
  intros segs E M k v lo hi. induction k as [|K r IH]; intros H HK; [discriminate H|].
  inversion HK as [|? ? HK1 HKr]; subst.
  destruct K as [ | | | | |e l h| | | | ]; cbn [knows_range] in H; try (exact (IH H HKr)).
  destruct e as [ |w| | | | | | ]; try (exact (IH H HKr)).
  destruct (Nat.eqb w v && Z.leb lo l && Z.leb h hi)%bool eqn:Hc; [|exact (IH H HKr)].
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Nat.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst. cbn [kentry_ok] in HK1. lia.
Qed.

Section Eval.
  Variables (E : env) (fs : Fs.Fs) (argv1 : list byte).
  Hypothesis U7 : bv_unsigned (edenot E (EVar 7)) = Z.of_nat (length argv1).
  Hypothesis B2 : eb E 2%nat = argv1.
  #[local] Notation LIT := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32].
  #[local] Notation X2 := (t_exit (Z_to_bv 64 2) fs).

  Lemma leafA : t_eq (t_emit (Wp E 2 [SPLit LIT; SPBlob 2; SPLit [10]]) X2) (T_cannot argv1 fs).
  Proof. unfold Wp, T_cannot, cannot_bytes. cbn [flat_map piece_den]. rewrite B2, app_nil_r. apply t_eq_refl. Qed.
  Lemma leafB : t_eq (t_emit (Wp E 2 [SPLit LIT; SPBlob 2; SPLit [10]]) (t_emit (Wp E 2 []) X2)) (T_cannot argv1 fs).
  Proof. eapply t_eq_trans; [apply t_emit_congr; apply t_emit_nil_eq; apply CXS.t_exit_has_nil | exact leafA]. Qed.
  Lemma leafC : t_eq (t_emit (Wp E 2 [SPLit LIT; SPBlob 2]) (t_emit (Wp E 2 [SPLit [10]]) X2)) (T_cannot argv1 fs).
  Proof.
    eapply t_eq_trans; [apply t_eq_sym; apply t_emit_app|]. unfold Wp, T_cannot, cannot_bytes. cbn [flat_map piece_den].
    rewrite B2, !app_nil_r, <- map_app, <- app_assoc. apply t_eq_refl.
  Qed.
  Lemma leaf0 : length argv1 = 0%nat -> t_eq (t_emit (Wp E 2 [SPLit (LIT ++ [10])]) X2) (T_cannot argv1 fs).
  Proof. intros H0. unfold Wp, T_cannot, cannot_bytes. cbn [flat_map piece_den]. destruct argv1; [|discriminate H0]. rewrite app_nil_r. apply t_eq_refl. Qed.

  Lemma noent_eval : t_eq (sd HOLES4 t_nil E fs noent_shape) (T_cannot argv1 fs).
  Proof.
    unfold noent_shape. cbn [sd]. rewrite U7. change (HOLES4 21 E fs) with X2.
    repeat match goal with |- context [(?a <=? ?b)%Z] => destruct (Z.leb_spec a b) end;
      first [exact leafA | exact leafB | exact leafC | apply leaf0; lia].
  Qed.
  Lemma toolong_eval : (4096 <= length argv1)%nat -> t_eq (sd HOLES4 t_nil E fs toolong_shape) (T_cannot argv1 fs).
  Proof.
    intros HL. unfold toolong_shape. cbn [sd]. rewrite U7. change (HOLES4 21 E fs) with X2.
    destruct (Z.leb_spec (Z.of_nat (length argv1)) 4095); [lia | exact leafC].
  Qed.
End Eval.
