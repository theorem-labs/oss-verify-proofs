(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad CMonad Stdio Driver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section DriverC.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> M St unit.
Variable run : Z -> list Z -> MC St Z.
Variable alloc_count : M St Z.

Definition main_model (argv : list (list Z)) : MC St Z :=
  if negb (Z.of_nat (length argv) =? 2) then
    clift (io_diag io (DUsage (nth 0 argv [])) ;;; mret 2)
  else
    cmbind (clift (read_all io drv_malloc drv_free read_stage (nth 1 argv [])))
      (fun ra =>
         match ra with
         | RdExit => cmret 2
         | RdDone buf content =>
             let len := zlength content in
             if len <? HDR_MIN then clift (io_diag io DShortHdr ;;; drv_free buf ;;; mret 2)
             else
               let cfg_word := le16 content in
               let count_allocs := Z.testbit cfg_word 15 in
               let config_len := Z.land cfg_word 0x7fff in
               if len <? HDR_MIN + config_len then clift (io_diag io DCfgOverrun ;;; drv_free buf ;;; mret 2)
               else
                 let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
                 let payload := skipn (Z.to_nat (6 + config_len)) content in
                 let cfg := if 0 <? config_len then znth content 2 else 0 in
                 cmbind (clift (alloc_init bitmap)) (fun _ =>
                 cmbind (run cfg payload) (fun status =>
                 cmbind (clift (if count_allocs then
                                  n <- alloc_count ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
                                else mret status)) (fun status' =>
                 cmbind (clift (drv_free buf)) (fun _ =>
                 cmret status'))))
         end).

Definition exit_model (code : Z) : MC St Empty_set := clift (Driver.exit_model io code).

End DriverC.
