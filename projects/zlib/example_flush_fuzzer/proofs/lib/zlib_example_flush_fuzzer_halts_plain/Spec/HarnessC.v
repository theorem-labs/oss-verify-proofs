(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool String.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad CMonad Stdio.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ExFlushIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition KMAX : Z := 1048576.
Definition DSTATE_N : Z := 5968.
Definition DBLK_N : Z := 65536.
Definition ISTATE_N : Z := 7176.
Definition WIN_N : Z := 32768.
Definition MSG_DEFLATEEND : list Z := str "deflateEnd".
Definition MSG_INFLATE : list Z := str "inflate".
Definition MSG_INFLATESYNC : list Z := str "inflateSync".
Definition MSG_SHOULD : list Z := str "inflate should report DATA_ERROR or Z_STREAM_END" ++ [10].
Definition zconv_pieces (e : Z) : list (list Z) :=
  if e =? 0 then [ []; [48]; [] ] else if e <? 0 then [ [45]; fmt_u (- e) ] else [ []; fmt_u e ].
Definition pieces_zerr (msg : list Z) (e : Z) : list (list Z) :=
  [ []; []; msg; str " error: "; [] ] ++ zconv_pieces e ++ [ [10] ].

Definition fuzz_skip (n : Z) : bool := (n <=? 3) || (KMAX <? n).

Section HarnessC.
Context {St ptr : Type}.
Variable FM : flush_model.
Variable malloc : Z -> M St (option ptr).
Variable free : ptr -> M St unit.
Variable fresh : St -> St -> ptr -> bool.

Definition creq (n : Z) : M St ptr :=
  r <- malloc n ;; match r with Some p => mret p | None => munr end.
Definition zreq (n : Z) : M St ptr :=
  s0 <- mget ;; r <- malloc n ;;
  match r with
  | None => munr
  | Some p => s1 <- mget ;; if fresh s0 s1 p then mret p else munr
  end.

Definition diag_zerr (msg : list Z) (e : Z) : M St unit := stderr_fprintf (pieces_zerr msg e).

Definition test_flush_m (d : list Z) (n : Z) : M St Z :=
  s <- zreq DSTATE_N ;; w <- zreq DBLK_N ;; pv <- zreq DBLK_N ;; hd <- zreq DBLK_N ;; pb <- zreq DBLK_N ;;
  free pb ;;; free hd ;;; free pv ;;; free w ;;; free s ;;;
  if fm_busy FM d then diag_zerr MSG_DEFLATEEND ZE_DATA_ERROR ;;; mret (CLEN n)
  else mret (fm_tot FM d).

Definition inflate_end (p : ptr) (w : option ptr) : M St unit :=
  match w with Some wd => free wd ;;; free p | None => free p end.

Definition finish_sync (p : ptr) (w : option ptr) (rc : Z) : M St unit :=
  if (rc =? ZE_DATA_ERROR) || (rc =? ZE_STREAM_END) then inflate_end p w
  else stderr_fwrite MSG_SHOULD.

Definition test_sync_m (c : list Z) (clen n : Z) : M St unit :=
  p <- zreq ISTATE_N ;;
  match fm_i1 FM c n with
  | I1_E e => diag_zerr MSG_INFLATE e
  | I1_OK =>
      match fm_is FM c clen n with
      | IS_E e => diag_zerr MSG_INFLATESYNC e
      | IS_OK =>
          match fm_i2 FM c clen n with
          | I2_R rc => finish_sync p None rc
          | I2_W => wd <- zreq WIN_N ;; finish_sync p (Some wd) (fm_i2b FM c clen n)
          end
      end
  end.

Definition fuzz_one_m (d : list Z) : M St Z :=
  let n := zlength d in
  if fuzz_skip n then mret 0
  else cp <- creq (CLEN n) ;; up <- creq n ;;
       clen <- test_flush_m d n ;;
       test_sync_m (fm_compr FM d) clen n ;;;
       free cp ;;; free up ;;; mret 0.

Definition fuzz_one (d : list Z) : MC St Z := clift (fuzz_one_m d).


End HarnessC.
