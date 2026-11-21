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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCtx.
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

Section ArmFor.
  Variable iv : ivariant.
Variable flush : Z.
  Definition arm_for (m : Z) : AM unit :=
    if m =? HEAD then arm_HEAD iv
    else if m =? FLAGS then arm_FLAGS
    else if m =? TIME then arm_TIME
    else if m =? OS then arm_OS
    else if m =? EXLEN then arm_EXLEN
    else if m =? EXTRA then arm_EXTRA
    else if m =? NAME then arm_NAME
    else if m =? COMMENT then arm_COMMENT
    else if m =? HCRC then arm_HCRC
    else if m =? DICTID then arm_DICTID iv flush
    else if m =? DICT then arm_DICT iv flush
    else if m =? TYPE then arm_TYPE iv flush
    else if m =? TYPEDO then arm_TYPEDO iv flush
    else if m =? STORED then arm_STORED iv flush
    else if m =? COPY_ then arm_COPY_
    else if m =? COPY then arm_COPY
    else if m =? TABLE then arm_TABLE iv flush
    else if m =? LENLENS then arm_LENLENS iv flush
    else if m =? CODELENS then arm_CODELENS iv flush
    else if m =? LEN_ then arm_LEN_ iv
    else if m =? LEN then arm_LEN iv
    else if m =? LENEXT then arm_LENEXT iv
    else if m =? DIST then arm_DIST iv
    else if m =? DISTEXT then arm_DISTEXT iv
    else if m =? MATCH then arm_MATCH iv
    else if m =? LIT then arm_LIT
    else if m =? CHECK then arm_CHECK
    else if m =? LENGTH then arm_LENGTH
    else if m =? DONE then arm_DONE
    else if m =? BAD then arm_BAD
    else if m =? MEM then arm_MEM
    else arm_SYNC.

End ArmFor.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition jt_entry (i : Z) : Z := nth (Z.to_nat i) arm_pcs 0.

Section Dispatch.

End Dispatch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.
  Variable arm_ok : Z -> iw -> bool.

  (* [comment removed for export] *)
  Definition mstep (flush : Z) (w : iw) : iw + (istop * iw) :=
    match dispatch ivar_ref flush w with
    | ARun _ w' => inl w'
    | ALeave w' => inr (SLeave, w')
    | ARet rc w' => inr (SRet rc, w')
    end.

End Loop.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
