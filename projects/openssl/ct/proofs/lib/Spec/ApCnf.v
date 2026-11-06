(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState ApErr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Definition SZ_CNF_NAME : Z := 27.      (* [comment removed for export] *)
Definition SZ_CONF : Z := 48.          (* [comment removed for export] *)
Definition SZ_MUTEX : Z := 40.         (* [comment removed for export] *)
Definition SZ_LHASH : Z := 104.        (* [comment removed for export] *)
Definition SZ_LH_BUCKETS : Z := 128.   (* [comment removed for export] *)
Definition CNF_PRINTED : Z := 45.      (* [comment removed for export] *)

Section Cnf.
Context {ptr : Type}.
Local Notation AM := (@AM ptr) (only parsing).

(* [comment removed for export] *)
Definition ossl_issetugid : AM unit :=
  u <- asys SyGetuid ;;
  e <- asys SyGeteuid ;;
  if u mod 4294967296 =? e mod 4294967296 then asys SyGetgid ;;; asys SyGetegid ;;; aret tt else aret tt.

(* [comment removed for export] *)
Definition ossl_init_added_api : AM unit :=
  s <- aget ;;
  match as_cnf s with
  | Some _ => aret tt
  | None =>
      (* [comment removed for export] *)
      err_set_mark ;;;
      (* [comment removed for export] *)
      ossl_issetugid ;;;
      fname <- amalloc SZ_CNF_NAME ;;                       (* [comment removed for export] *)
      conf <- amalloc SZ_CONF ;;                            (* [comment removed for export] *)
      (* [comment removed for export] *)
      asys SyOpenCnf ;;;                                    (* [comment removed for export] *)
      err_raise_data RS_fopen_sys CNF_PRINTED ;;;           (* [comment removed for export] *)
      err_raise RS_no_such_file ;;;                         (* [comment removed for export] *)
      (* [comment removed for export] *)
      c <- err_peek_last_error ;;
      (if err_get_reason c =? BIO_R_NO_SUCH_FILE then err_raise RS_conf_no_file else aunr) ;;;
      (* [comment removed for export] *)
      c <- err_peek_last_error ;;
      (if err_get_reason c =? CONF_R_NO_SUCH_FILE then aret tt else aunr) ;;;
      afree fname ;;;                                       (* [comment removed for export] *)
      afree conf ;;;                                        (* [comment removed for export] *)
      err_pop_to_mark ;;;                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      lock <- amalloc SZ_MUTEX ;;
      lh <- amalloc SZ_LHASH ;;
      b <- amalloc SZ_LH_BUCKETS ;;
      amodify (set_cnf (Some (lock, lh, b)))
  end.

End Cnf.
