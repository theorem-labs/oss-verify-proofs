(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition MAX_INPUT : Z := 67108864.
Definition READ_CAP : Z := 65536.
Definition HDR_MIN : Z := 6.
Definition COUNT_MAX : Z := 251.

Section Driver.
Context {St ptr : Type}.
Variable io_diag : diag_msg -> M St unit.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> M St unit.
Variable run : Z -> list Z -> M St Z.
Variable alloc_count : M St Z.

Inductive rd_result : Type :=
| RdExit
| RdDone (buf : ptr) (content : list Z).

Record rd_st := mkRd { rd_buf : ptr; rd_cap : Z; rd_content : list Z }.

Definition u8s_of_bytes (bs : list byte) : list Z := map bv_unsigned bs.

Definition read_loop_body (fd : Z) (path : list Z) (st : rd_st) : M St (rd_st + rd_result) :=
let len := zlength (rd_content st) in

g <- (if len =? rd_cap st then
if MAX_INPUT <=? rd_cap st then
io_diag DTooBig ;;; mret None
else
nb <- drv_malloc (rd_cap st * 2) ;;
match nb with
| None => io_diag DOom ;;; mret None
| Some nb' => drv_free (rd_buf st) ;;;
mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
end
else mret (Some st)) ;;
match g with
| None => mret (inr RdExit)
| Some st1 =>
let want := rd_cap st1 - len in
let cnt := if READ_CAP <? want then READ_CAP else want in
a <- msys (NRead fd read_stage cnt) (dec_read read_stage cnt) ;;
match a with
| RdErr _ => io_diag (DReadError path) ;;; mret (inr RdExit)
| RdData bs =>
if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
end
end.

Definition READ_FUEL : nat := Z.to_nat (MAX_INPUT + 16).

Definition read_all (path : list Z) : M St rd_result :=
r <- msys (NOpen (map (Z_to_bv 8) path)) dec_open ;;
match r with
| SErr _ => io_diag (DCannotOpen path) ;;; mret RdExit
| SVal fd =>
b <- drv_malloc 65536 ;;
match b with
| None => io_diag DOom ;;; mret RdExit
| Some buf =>
res <- mloop READ_FUEL (read_loop_body fd path) (mkRd buf 65536 []) ;;
match res with
| RdExit => mret RdExit
| RdDone buf' content => _ <- msys (NClose fd) dec_close ;; mret (RdDone buf' content)
end
end
end.

Definition le16 (l : list Z) : Z := znth l 0 + znth l 1 * 256.
Definition le32 (l : list Z) : Z := znth l 0 + znth l 1 * 2^8 + znth l 2 * 2^16 + znth l 3 * 2^24.

Definition main_model (argv : list (list Z)) : M St Z :=
if negb (Z.of_nat (length argv) =? 2) then
io_diag (DUsage (nth 0 argv [])) ;;; mret 2
else
ra <- read_all (nth 1 argv []) ;;
match ra with
| RdExit => mret 2
| RdDone buf content =>
let len := zlength content in
if len <? HDR_MIN then io_diag DShortHdr ;;; drv_free buf ;;; mret 2
else
let cfg_word := le16 content in
let count_allocs := Z.testbit cfg_word 15 in
let config_len := Z.land cfg_word 0x7fff in
if len <? HDR_MIN + config_len then io_diag DCfgOverrun ;;; drv_free buf ;;; mret 2
else
let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
let payload := skipn (Z.to_nat (6 + config_len)) content in
let cfg := if 0 <? config_len then znth content 2 else 0 in
alloc_init bitmap ;;;
status <- run cfg payload ;;
status' <- (if count_allocs then
n <- alloc_count ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
else mret status) ;;
drv_free buf ;;;
mret status'
end.

End Driver.
