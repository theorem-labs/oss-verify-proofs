(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require ZApiL ZHarnessL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD RefInflate_runA RefInflateEqS HarnessSmall ZApiInst ZApiInstL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pend (s : inflate_state) : Z :=
  let m := is_mode s in
  if m =? LENEXT then is_length s + (2 ^ is_extra s - 1)
  else if (m =? DIST) || (m =? DISTEXT) || (m =? MATCH) then is_length s
  else if m =? LIT then 1
  else 0.

(* [comment removed for export] *)
Definition PSIW : Z := 259.

Definition PSIr (r : iregs) : Z := PSIW * (8 * ir_have r + ir_bits r).
Definition PSI (w : iw) : Z := PSIr (w_r w) + pend (w_s w).

(* [comment removed for export] *)
Definition PSIq (avail_in : Z) (s : inflate_state) : Z := PSIW * (8 * avail_in + is_bits s) + pend s.

(* [comment removed for export] *)
Lemma pend_keep : forall s s', is_mode s' = is_mode s -> is_length s' = is_length s -> is_extra s' = is_extra s -> pend s' = pend s.
Proof. intros s s' E1 E2 E3. unfold pend. rewrite E1, E2, E3. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pend_nonneg_INV : forall s, INV s -> 0 <= pend s.
Proof.
  intros s (HC & _ & HM). unfold pend.
  assert (HL : 0 <= is_length s < 2 ^ 32) by (unfold CORE in HC; repeat lazymatch type of HC with _ <= _ < _ => fail | _ /\ _ => apply proj2 in HC end; exact HC).
  destruct (Z.eqb_spec (is_mode s) LENEXT) as [E|NE].
  - rewrite E in HM. unfold MF in HM. cbn in HM. destruct HM as (_ & _ & _ & HE & _).
    pose proof (Z.pow_pos_nonneg 2 (is_extra s) ltac:(lia) ltac:(lia)). lia.
  - destruct (_ || _); [lia|]. destruct (_ =? _); lia.
Qed.

Lemma PSIq_nonneg_INV : forall a s, INV s -> 0 <= a -> 0 <= PSIq a s.
Proof.
  intros a s HI Ha. pose proof (pend_nonneg_INV s HI). destruct HI as (_ & [Hb _] & _). unfold PSIq, PSIW. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PPw (w0 w' : iw) : Prop :=
  ir_put (w_r w0) <= ir_put (w_r w') /\ PSI w' + (ir_put (w_r w') - ir_put (w_r w0)) <= PSI w0.
Definition PP (w0 : iw) {A} (res : ares A) : Prop :=
  match res with
  | ARun _ w' => PPw w0 w'
  | ALeave w' => PPw w0 w'
  | ARet _ _ => True
  end.

Lemma PPw_refl : forall w, PPw w w.
Proof. intros w. unfold PPw. lia. Qed.
Lemma PPw_trans : forall w0 w1 w2, PPw w0 w1 -> PPw w1 w2 -> PPw w0 w2.
Proof. intros w0 w1 w2 [A1 A2] [B1 B2]. unfold PPw. lia. Qed.

Section Stmts.
  Variable iv : ivariant.

  (* [comment removed for export] *)
  Definition psi_step_stmt (flush : Z) : Prop :=
    forall w, WINV w -> PP w (dispatch iv flush w).
End Stmts.

(* [comment removed for export] *)
Definition psi_call_stmt : Prop :=
  forall (s : inflate_state) (zc : ZCall) (ok : bool),
    INV s -> ZC zc ->
    let p := fst (inflate_p (wans ok) s zc Z_NO_FLUSH) in
    zr_rc (snd p) = Z_OK ->
    0 <= zr_consumed (snd p) <= zlength (zc_input zc)
    /\ 1 <= zr_consumed (snd p) + zlength (zr_output (snd p))
    /\ PSIq (zlength (zc_input zc) - zr_consumed (snd p)) (fst p) + zlength (zr_output (snd p)) <= PSIq (zlength (zc_input zc)) s.

(* [comment removed for export] *)
Definition iloopL_total_stmt : Prop :=
  forall (size : Z) (comprc : list Z),
    1 <= size <= ZApiL.ZL_MAX -> zlength comprc = ZApiL.NofL size -> Forall (fun b => 0 <= b < 256) comprc ->
    ZHarnessL.iloopL_pure zinstL (ZApiL.NofL size) comprc (ZApiL.il_init zinstL) <> ZHarnessL.IRLstuck.

(* [comment removed for export] *)
Lemma ZIL_FUEL_enough : forall N, 0 <= N -> PSIW * (8 * N) + N + 1 < ZHarnessL.ZIL_FUEL N.
Proof. intros N HN. unfold PSIW, ZHarnessL.ZIL_FUEL. lia. Qed.
