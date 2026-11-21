(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflatePsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition arm_psi (M : Z) (arm : AM unit) : Prop :=
  forall w0 s c r, WINV (mkW s c r) -> is_mode s = M -> PPw w0 (mkW s c r) -> PP w0 (arm (mkW s c r)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rules.
  Context {A B : Type}.

  Lemma PP_bind : forall w0 (m : AM A) (f : A -> AM B) w,
    match m w with
    | ARun a w' => PP w0 (f a w')
    | ALeave w' => PPw w0 w'
    | ARet _ w' => True
    end ->
    PP w0 (abind m f w).
  Proof. intros w0 m f w H. unfold abind. destruct (m w); exact H. Qed.

  Lemma PP_ARun : forall w0 (a : A) w', PPw w0 w' -> PP w0 (ARun a w').
  Proof. intros. assumption. Qed.

  Lemma PP_bind_run : forall w0 (m : AM A) (f : A -> AM B) w a w',
    m w = ARun a w' -> PP w0 (f a w') -> PP w0 (abind m f w).
  Proof. intros w0 m f w a w' E H. unfold abind. rewrite E. exact H. Qed.
  Lemma PP_bind_leave : forall w0 (m : AM A) (f : A -> AM B) w w',
    m w = ALeave w' -> PPw w0 w' -> PP w0 (abind m f w).
  Proof. intros w0 m f w w' E H. unfold abind. rewrite E. exact H. Qed.
  Lemma PP_bind_ret : forall w0 (m : AM A) (f : A -> AM B) w rc w',
    m w = ARet rc w' -> PP w0 (abind m f w).
  Proof. intros w0 m f w rc w' E. unfold abind. rewrite E. exact I. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma PP_arm : forall M arm w0 s c r,
    arm_psi M arm -> WINV (mkW s c r) -> is_mode s = M -> PPw w0 (mkW s c r) -> PP w0 (arm (mkW s c r)).
  Proof. intros M arm w0 s c r H. exact (H w0 s c r). Qed.
End Rules.

(* [comment removed for export] *)
Ltac acase2 H :=
  lazymatch goal with
  | |- PP _ (abind (if ?cnd then _ else _) _ _) => destruct cnd eqn:H
  | |- PP _ ((if ?cnd then _ else _) _) => destruct cnd eqn:H
  | |- PP _ (abind (abind _ _) _ _) => rewrite abind_assoc; acase2 H
  end.
Ltac arun2 lem := eapply PP_bind_run; [apply lem|]; cbv beta iota.
Ltac aleave2 :=
  first [ rewrite aleave_eq; cbn [PP]
        | rewrite areturn_eq; cbn [PP]
        | eapply PP_bind_leave; [reflexivity|]
        | eapply PP_bind_ret; reflexivity ].
Ltac arun02 := eapply PP_bind_run; [reflexivity|]; cbv beta iota.
Ltac pstep2 lem := apply PP_bind; rewrite lem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pulled_psi : forall r r', pulled r r' ->
  8 * ir_have r' + ir_bits r' = 8 * ir_have r + ir_bits r /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ 0 <= ir_have r' <= ir_have r.
Proof. intros r r' (k & Hk & _ & Hh & Hh0 & Hb & _ & _ & Hp & Hl & _). rewrite Hh, Hb, Hp, Hl. repeat split; lia. Qed.

(* [comment removed for export] *)
Ltac pend_red :=
  cbv beta iota delta [pend Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].
Ltac pend_red_in H :=
  cbv beta iota delta [pend Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.

(* [comment removed for export] *)
Ltac pend_lit := unfold pend; sacc; pend_red.

(* [comment removed for export] *)
Ltac pulls_psi := repeat match goal with H : pulled ?a ?b |- _ => apply pulled_psi in H end.

(* [comment removed for export] *)
Ltac ppw_open E HQ :=
  eapply (PPw_trans _ _ _ HQ);
  unfold PPw, PSI, PSIr; cbn [w_r w_s]; sacc; unfold PSIW;
  unfold pend; sacc; rewrite ?E; pend_red.
Ltac ppw E HQ := ppw_open E HQ; pulls_psi; lia.

(* [comment removed for export] *)
Lemma PPw_pulled : forall w0 s c r r', PPw w0 (mkW s c r) -> pulled r r' -> PPw w0 (mkW s c r').
Proof.
  intros w0 s c r r' HQ HP. eapply (PPw_trans _ _ _ HQ). apply pulled_psi in HP.
  unfold PPw, PSI, PSIr. cbn [w_r w_s]. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

