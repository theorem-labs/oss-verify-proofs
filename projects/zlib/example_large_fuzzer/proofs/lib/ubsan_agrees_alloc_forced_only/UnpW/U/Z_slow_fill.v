(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FILL.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmt.

End FILL.
