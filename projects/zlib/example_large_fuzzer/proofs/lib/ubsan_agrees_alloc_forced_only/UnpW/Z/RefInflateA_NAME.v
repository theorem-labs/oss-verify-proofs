(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint scan_k (input : arr) (next have : Z) (k : nat) (copy : Z) : Z * Z :=
  match k with
  | O => (copy, 0)
  | S k' => let len := arr_get input (next + copy) in
            let copy' := copy + 1 in
            if negb (len =? 0) && (copy' <? have) then scan_k input next have k' copy' else (copy', len)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nl_s1 (s : inflate_state) (c : icall) (r : iregs) (copy : Z) : inflate_state :=
  if hcrc_on s then iset_check s (icrc32_upd (is_check s) (arr_slice (ic_input c) (ir_next r) copy)) else s.
Definition nl_r2 (r : iregs) (copy : Z) : iregs :=
  irset_next (irset_have r (wrap32 (ir_have r - copy))) (ir_next r + copy).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sxu_le : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 <= szwrap 32 y mod 2 ^ 64 <-> x <= y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.
Lemma sxu_lt : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 < szwrap 32 y mod 2 ^ 64 <-> x < y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).
Local Ltac byte_side :=
  match goal with
  | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- 0 <= arr_get (ic_input ?c) ?i => exact (proj1 (Rinb i ltac:(lia)))
  | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- arr_get (ic_input ?c) ?i < 256 => exact (proj2 (Rinb i ltac:(lia)))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac lreg_in := cbn; repeat (first [ left; reflexivity | right ]).

Section ArmNAME.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_COMMENT : forall flush w, is_mode (w_s w) = COMMENT -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_NAME : forall flush w, is_mode (w_s w) = NAME -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  (* [comment removed for export] *)
  Hypothesis OK_COMMENT_HCRC : forall flush s c r r', is_mode s = COMMENT -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode s HCRC) c r') = true.
  Hypothesis OK_COMMENT_HCRCc : forall flush s c r ck r', is_mode s = COMMENT -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check s ck) HCRC) c r') = true.
  Hypothesis OK_NAME_COMMENT : forall flush s c r r', is_mode s = NAME -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s 0) COMMENT) c r') = true.
  Hypothesis OK_NAME_COMMENTc : forall flush s c r ck r', is_mode s = NAME -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length (iset_check s ck) 0) COMMENT) c r') = true.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition nm_s3 (s1 : inflate_state) : inflate_state := iset_mode (iset_length s1 0) COMMENT.
End ArmNAME.
