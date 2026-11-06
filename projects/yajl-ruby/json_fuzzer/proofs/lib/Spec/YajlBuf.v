(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope yprog_scope.

Inductive buf_state : Type := BS_ok | BS_alloc_failed | BS_overflow.

Definition buf_state_code (s : buf_state) : Z :=
  match s with BS_ok => 0 | BS_alloc_failed => 1 | BS_overflow => 2 end.

Definition buf_state_ok (s : buf_state) : bool :=
  match s with BS_ok => true | _ => false end.

Record ybuf : Type := mkBuf {
  yb_state : buf_state;
  yb_len   : Z;
  yb_used  : Z;
  yb_data  : option yptr;
  yb_bytes : list Z
}.

Definition YAJL_BUF_INIT_SIZE : Z := 2048.
Definition SIZEOF_YAJL_BUF_T : Z := 32.

(* [comment removed for export] *)
Definition ybuf_zero : ybuf := mkBuf BS_ok 0 0 None [].

(* [comment removed for export] *)
Definition ybuf_alloc : yprog (option yptr) := ymalloc SIZEOF_YAJL_BUF_T.

(* [comment removed for export] *)
Definition ybuf_free (blk : yptr) (b : ybuf) : yprog unit :=
  match yb_data b with
  | Some d => yfree (Some d) ;;; yfree (Some blk)
  | None => yfree (Some blk)
  end.

(* [comment removed for export] *)
Definition ybuf_set_error (b : ybuf) (err : buf_state) : yprog ybuf :=
  yfree (yb_data b) ;;; YRet (mkBuf err 0 0 None []).

(* [comment removed for export] *)
Fixpoint ens_need_loop (fuel : nat) (want need used : Z) : Z :=
  match fuel with
  | O => need
  | S f => if (need - used <=? want) && (0 <? need)
           then ens_need_loop f want (need * 2) used
           else need
  end.
Definition ENS_FUEL : nat := 64%nat.

(* [comment removed for export] *)
Definition ybuf_ensure_available (b : ybuf) (want : Z) : yprog ybuf :=
  match yb_state b with
  | BS_ok =>
      first <- match yb_data b with
               | None =>
                   r <- ymalloc YAJL_BUF_INIT_SIZE ;;
                   match r with
                   | None =>
                       (* [comment removed for export] *)
                       b' <- ybuf_set_error (mkBuf BS_ok YAJL_BUF_INIT_SIZE (yb_used b) None (yb_bytes b))
                                            BS_overflow ;;
                       YRet (inr b')
                   | Some d => YRet (inl (mkBuf BS_ok YAJL_BUF_INIT_SIZE (yb_used b) (Some d) (yb_bytes b)))
                   end
               | Some _ => YRet (inl b)
               end ;;
      match first with
      | inr b' => YRet b'
      | inl b1 =>
          if want =? 0 then YRet b1 else
          let need := ens_need_loop ENS_FUEL want (yb_len b1) (yb_used b1) in
          if (need <? yb_used b1) || (need =? 0)
          then ybuf_set_error b1 BS_overflow
          else if negb (need =? yb_len b1) then
            r <- yrealloc (yb_data b1) need ;;
            match r with
            | None => ybuf_set_error (mkBuf BS_ok (yb_len b1) (yb_used b1) None (yb_bytes b1)) BS_overflow
            | Some d => YRet (mkBuf BS_ok need (yb_used b1) (Some d) (yb_bytes b1))
            end
          else YRet b1
      end
  | _ => YRet b
  end.

(* [comment removed for export] *)
Definition ybuf_append (b : ybuf) (src : list Z) : yprog ybuf :=
  b1 <- ybuf_ensure_available b (zlength src) ;;
  match yb_state b1 with
  | BS_ok =>
      if 0 <? zlength src
      then YRet (mkBuf BS_ok (yb_len b1) (yb_used b1 + zlength src) (yb_data b1) (yb_bytes b1 ++ src))
      else YRet b1
  | _ => YRet b1
  end.

(* [comment removed for export] *)
Definition ybuf_clear (b : ybuf) : yprog ybuf :=
  match yb_state b with
  | BS_ok => YRet (mkBuf BS_ok (yb_len b) 0 (yb_data b) [])
  | _ => YAbort
  end.

(* [comment removed for export] *)
Definition ybuf_err (b : ybuf) : bool := negb (buf_state_ok (yb_state b)).

(* [comment removed for export] *)
Definition ybuf_data_chk (b : ybuf) : yprog (option yptr) :=
  match yb_state b with BS_ok => YRet (yb_data b) | _ => YAbort end.
Definition ybuf_len_chk (b : ybuf) : yprog Z :=
  match yb_state b with BS_ok => YRet (yb_used b) | _ => YAbort end.
