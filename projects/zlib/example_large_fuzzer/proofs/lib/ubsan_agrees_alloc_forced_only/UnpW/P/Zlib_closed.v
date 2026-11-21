(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZApiL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Zlib_iface Zl_iface Z_irep Zl_zrd Zl_infl_closed Zl_defl_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition zRL : zrepsL :=
  mkZrepsL zr_dL zr_iL zr_dL_frame zr_iL_frame zr_dL_stream zr_iL_stream.
Definition zR : zrepsL := zRL.

(* [comment removed for export] *)
Theorem zlib_closed : zlib_okL zRL.
Proof.
  destruct (zlib_okL_defl zRL eq_refl) as (DI & DD & DP & DE).
  destruct (zlib_infl_closedL zRL eq_refl) as (II & INF & IE).
  unfold zlib_okL. repeat split; assumption.
Qed.

End WithCeiling0.

(* [comment removed for export] *)
Theorem zlib_closed_all : forall (CE__ : Ceiling) (RN__ : RunRnd), @zlib_okL CE__ RN__ (@zRL CE__).
Proof. intros. apply zlib_closed. Qed.
