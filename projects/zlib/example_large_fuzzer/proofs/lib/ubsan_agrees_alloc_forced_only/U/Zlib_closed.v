(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prog ZApiL ZInstL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Zlib_iface Zl_iface Z_irep Zg_zlib_iface Zl_zrd Zl_infl_closed Zl_defl_closed Zg_zlib_infl_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition zRL : zrepsL :=
  mkZrepsL zr_dL zr_iL zr_dL_frame zr_iL_frame zr_dL_stream zr_iL_stream.
Definition zR : zrepsL := zRL.

(* [comment removed for export] *)
Definition INFLG_stmt : Prop :=
  forall R : zreps, zr_i R = zr_i_def -> inflateInit_stmt R /\ inflate_stmtG R /\ inflateEnd_stmt R.

(* [comment removed for export] *)
Theorem zlib_closed_of : INFLG_stmt -> zlib_okL zRL.
Proof.
  intros INFLG.
  destruct (zlib_okL_defl zRL eq_refl) as (DI & DD & DP & DE).
  destruct (zlib_infl_closedL_of INFLG zRL eq_refl) as (II & INF & IE).
  unfold zlib_okL. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Theorem zlib_closed : zlib_okL zRL.
Proof. exact (zlib_closed_of zlib_infl_closedG). Qed.

End WithCeiling0.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem zlib_closed_all : forall (CE__ : Ceiling) (RN__ : RunRnd), @zlib_okL CE__ RN__ (@zRL CE__).
Proof. intros. apply zlib_closed. Qed.
