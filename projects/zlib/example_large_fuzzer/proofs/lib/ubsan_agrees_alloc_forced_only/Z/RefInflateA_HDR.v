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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_EXTRA.
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
Definition hcrc2 (s : inflate_state) (hold : Z) : inflate_state :=
  if hcrc_on s then iset_check s (icrc32_upd (is_check s) [wrap8 hold; wrap8 (Z.shiftr hold 8)]) else s.
Definition hcrc4 (s : inflate_state) (hold : Z) : inflate_state :=
  if hcrc_on s then iset_check s (icrc32_upd (is_check s) [wrap8 hold; wrap8 (Z.shiftr hold 8); wrap8 (Z.shiftr hold 16); wrap8 (Z.shiftr hold 24)]) else s.
(* [comment removed for export] *)
Definition r00 (r1 : iregs) : iregs := irset_bits (irset_hold r1 0) 0.

(* [comment removed for export] *)
Lemma NEEDBITS_k_run : forall k n s c r s1 c1 r1,
  NEEDBITS_k k n (mkW s c r) = ARun tt (mkW s1 c1 r1) -> s1 = s /\ c1 = c.
Proof.
  induction k as [|k IH]; intros n s c r s1 c1 r1 HN.
  - cbn in HN. unfold aret in HN. split; congruence.
  - rewrite NEEDBITS_k_S in HN. destruct (ir_bits r <? n); [| split; congruence]. destruct (ir_have r =? 0); [congruence | exact (IH _ _ _ _ _ _ _ HN)].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)

Local Ltac inl6 H := cbn in H; destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].

Section ArmHDR.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_TIME : forall flush w, is_mode (w_s w) = TIME -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_OS : forall flush w, is_mode (w_s w) = OS -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_EXLEN : forall flush w, is_mode (w_s w) = EXLEN -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  (* [comment removed for export] *)
  Hypothesis OK_TIME_OS : forall flush s c r r', is_mode s = TIME -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode s OS) c r') = true.
  Hypothesis OK_TIME_OSc : forall flush s c r ck r', is_mode s = TIME -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check s ck) OS) c r') = true.
  Hypothesis OK_OS_EXLEN : forall flush s c r r', is_mode s = OS -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode s EXLEN) c r') = true.
  Hypothesis OK_OS_EXLENc : forall flush s c r ck r', is_mode s = OS -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check s ck) EXLEN) c r') = true.
  Hypothesis OK_OS_NAME : forall flush s c r r', is_mode s = OS -> Z.land (is_flags s) 1024 = 0 -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s 0) NAME) c r') = true.
  Hypothesis OK_OS_NAMEc : forall flush s c r ck r', is_mode s = OS -> Z.land (is_flags s) 1024 = 0 -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length (iset_check s ck) 0) NAME) c r') = true.
  Hypothesis OK_EXLEN_NAME : forall flush s c r r', is_mode s = EXLEN -> Z.land (is_flags s) 1024 = 0 -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s 0) NAME) c r') = true.
  Hypothesis OK_EXLEN_EXTRA : forall flush s c r l r', is_mode s = EXLEN -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s l) EXTRA) c r') = true.
  Hypothesis OK_EXLEN_EXTRAc : forall flush s c r ck l r', is_mode s = EXLEN -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check (iset_length s l) ck) EXTRA) c r') = true.
End ArmHDR.
