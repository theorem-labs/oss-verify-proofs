(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Znumtheory.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cpy_n (s : inflate_state) (r : iregs) : Z :=
  let copy := is_length s in
  let copy := if ir_have r <? copy then ir_have r else copy in
  if ir_left r <? copy then ir_left r else copy.

Definition cpy_c (c : icall) (r : iregs) (n : Z) : icall :=
  icset_outbuf c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) n).
Definition cpy_r (r : iregs) (n : Z) : iregs :=
  irset_put (irset_left (irset_next (irset_have r (wrap32 (ir_have r - n))) (ir_next r + n)) (wrap32 (ir_left r - n))) (ir_put r + n).

Lemma arm_COPY_zero : forall s c r, is_length s = 0 -> arm_COPY (mkW s c r) = ARun tt (mkW (iset_mode s TYPE) c r).
Proof. intros s c r H. unfold arm_COPY. mstep1 (@gs_eq inflate_state). rewrite H. cbn [Z.eqb negb]. apply set_mode_eq. Qed.

Lemma arm_COPY_leave : forall s c r, is_length s <> 0 -> cpy_n s r = 0 -> arm_COPY (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros s c r H Hn. unfold arm_COPY. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  mstep1 (@gr_eq iregs). fold (cpy_n s r). rewrite Hn. cbn [Z.eqb]. apply aleave_eq.
Qed.

Lemma arm_COPY_run : forall s c r, is_length s <> 0 -> cpy_n s r <> 0 ->
  arm_COPY (mkW s c r) = ARun tt (mkW (iset_length s (wrap32 (is_length s - cpy_n s r))) (cpy_c c r (cpy_n s r)) (cpy_r r (cpy_n s r))).
Proof.
  intros s c r H Hn. unfold arm_COPY. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  mstep1 (@gr_eq iregs). fold (cpy_n s r). rewrite (proj2 (Z.eqb_neq _ _) Hn).
  mstep1 uc_eq. mstep1 ur_eq. rewrite us_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sxu_le : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 <= szwrap 32 y mod 2 ^ 64 <-> x <= y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.
Lemma sxu_lt : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 < szwrap 32 y mod 2 ^ 64 <-> x < y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

(* [comment removed for export] *)

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Section ArmCOPY.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_COPY_ : forall flush w, is_mode (w_s w) = COPY_ -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_COPY : forall flush w, is_mode (w_s w) = COPY -> arm_ok flush w = true -> leave_okb (w_s w) = true.

  (* [comment removed for export] *)
  Definition cpy_m1 (s : inflate_state) (r : iregs) : Z := if ir_have r <=? is_length s then ir_have r else is_length s.
  Definition cpy_m (s : inflate_state) (r : iregs) : Z := if ir_left r <? cpy_m1 s r then ir_left r else cpy_m1 s r.

End ArmCOPY.
