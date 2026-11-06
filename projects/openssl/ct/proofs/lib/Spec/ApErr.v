(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record rsite : Type := mkRS { rs_flen : Z; rs_fnlen : Z; rs_line : Z; rs_code : Z }.

Definition ERR_PACK (lib reason : Z) : Z := Z.lor (Z.shiftl (Z.land lib 255) 23) (Z.land reason 8388607).
Definition ERR_SYSTEM_FLAG : Z := 2147483648.
(* [comment removed for export] *)
Definition err_get_reason (code : Z) : Z :=
  if negb (Z.land code ERR_SYSTEM_FLAG =? 0) then Z.land code 2147483647 else Z.land code 8388607.

Definition ERR_LIB_SYS : Z := 2.  Definition ERR_LIB_ASN1 : Z := 13.  Definition ERR_LIB_CONF : Z := 14.  Definition ERR_LIB_BIO : Z := 32.
Definition BIO_R_NO_SUCH_FILE : Z := 128.  Definition CONF_R_NO_SUCH_FILE : Z := 114.  Definition ENOENT : Z := 2.

(* [comment removed for export] *)
Definition RS_hdr_too_long : rsite := mkRS 23 16 105 (ERR_PACK ERR_LIB_ASN1 123).
Definition RS_too_long     : rsite := mkRS 23 16 95 (ERR_PACK ERR_LIB_ASN1 155).
Definition RS_too_small    : rsite := mkRS 23 16 56 (ERR_PACK ERR_LIB_ASN1 224).     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RS_zero_content : rsite := mkRS 20 9 160 (ERR_PACK ERR_LIB_ASN1 222).
Definition RS_ill_padding  : rsite := mkRS 20 9 193 (ERR_PACK ERR_LIB_ASN1 221).
(* [comment removed for export] *)
Definition RS_inv_obj_a    : rsite := mkRS 23 21 260 (ERR_PACK ERR_LIB_ASN1 216).
Definition RS_inv_obj_b    : rsite := mkRS 23 21 290 (ERR_PACK ERR_LIB_ASN1 216).
(* [comment removed for export] *)
Definition RS_fopen_sys    : rsite := mkRS 22 13 73 (Z.lor ERR_SYSTEM_FLAG ENOENT).    (* [comment removed for export] *)
Definition RS_no_such_file : rsite := mkRS 22 13 81 (ERR_PACK ERR_LIB_BIO BIO_R_NO_SUCH_FILE).
(* [comment removed for export] *)
Definition RS_conf_no_file : rsite := mkRS 23 9 179 (ERR_PACK ERR_LIB_CONF CONF_R_NO_SUCH_FILE).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Err.
Context {ptr : Type}.
Local Notation ST := (ap_st ptr) (only parsing).
Local Notation AM := (@AM ptr) (only parsing).

Definition ring_next (i : nat) : nat := Nat.modulo (S i) ERR_NUM.
Definition ring_prev (i : nat) : nat := match i with O => 15%nat | S j => j end.

(* [comment removed for export] *)
Definition err_clear_data (i : nat) (deall : bool) : AM unit :=
  s <- aget ;;
  if negb (Z.land (get_dflags i s) ERR_TXT_MALLOCED =? 0) then
    if deall then
      afree_opt (option_map fst (get_data i s)) ;;;
      amodify (fun s => set_dflags i 0 (set_data i None s))
    else
      match get_data i s with
      | Some _ => amodify (set_dflags i ERR_TXT_MALLOCED)
      | None => aret tt                                   (* [comment removed for export] *)
      end
  else amodify (fun s => set_dflags i 0 (set_data i None s)).

(* [comment removed for export] *)
Definition free_file_slot (i : nat) : AM unit :=
  s <- aget ;; afree_opt (option_map fst (get_file i s)) ;;; amodify (set_file i None).
Definition free_func_slot (i : nat) : AM unit :=
  s <- aget ;; afree_opt (option_map fst (get_func i s)) ;;; amodify (set_func i None).

(* [comment removed for export] *)
Definition err_clear (i : nat) (deall : bool) : AM unit :=
  err_clear_data i deall ;;;
  amodify (fun s => set_line i (-1) (set_buf i 0 (set_marks i 0 s))) ;;;
  free_file_slot i ;;;
  free_func_slot i.

(* [comment removed for export] *)
Definition err_new : AM unit :=
  s <- aget ;;
  let top := ring_next (as_top s) in
  let bot := if Nat.eqb top (as_bottom s) then ring_next (as_bottom s) else as_bottom s in
  amodify (fun s => set_bottom bot (set_top top s)) ;;;
  err_clear top false.

(* [comment removed for export] *)
Definition err_set_debug (rs : rsite) : AM unit :=
  s <- aget ;;
  let i := as_top s in
  free_file_slot i ;;;
  pf <- amalloc (rs_flen rs) ;;
  amodify (fun s => set_line i (rs_line rs) (set_file i (Some (pf, rs_flen rs)) s)) ;;;
  free_func_slot i ;;;
  pn <- amalloc (rs_fnlen rs) ;;
  amodify (set_func i (Some (pn, rs_fnlen rs))).

(* [comment removed for export] *)
Definition err_set_error (rs : rsite) : AM unit :=
  s <- aget ;;
  let i := as_top s in
  err_clear_data i false ;;;
  amodify (set_buf i (rs_code rs)).

(* [comment removed for export] *)
Definition err_set_error_data (rs : rsite) (printed : Z) : AM unit :=
  s <- aget ;;
  let i := as_top s in
  let old := get_data i s in
  let buf := option_map fst old in
  let buf_size := match old with Some (_, sz) => sz | None => 0 end in
  amodify (fun s => set_dflags i 0 (set_data i None s)) ;;;
  (* [comment removed for export] *)
  ' (buf, buf_size) <- (if buf_size <? ERR_MAX_DATA_SIZE
                        then (b <- arealloc_opt buf ERR_MAX_DATA_SIZE ;; aret (Some b, ERR_MAX_DATA_SIZE))
                        else aret (buf, buf_size)) ;;
  match buf with
  | None => aunr                                              (* [comment removed for export] *)
  | Some b =>
      let printed := if (printed <? 0) || (buf_size <=? printed) then 0 else printed in
      (* [comment removed for export] *)
      b2 <- areallocS b (printed + 1) ;;
      err_clear_data i false ;;;
      amodify (set_buf i (rs_code rs)) ;;;
      (* [comment removed for export] *)
      s <- aget ;;
      (if negb (Z.land (get_dflags i s) ERR_TXT_MALLOCED =? 0) then afree_opt (option_map fst (get_data i s)) else aret tt) ;;;
      amodify (fun s => set_dflags i (Z.lor ERR_TXT_MALLOCED ERR_TXT_STRING) (set_data i (Some (b2, printed + 1)) s))
  end.

Definition err_raise (rs : rsite) : AM unit := err_new ;;; err_set_debug rs ;;; err_set_error rs.
Definition err_raise_data (rs : rsite) (printed : Z) : AM unit := err_new ;;; err_set_debug rs ;;; err_set_error_data rs printed.

(* [comment removed for export] *)
Fixpoint err_clear_slots (i : nat) (n : nat) {struct n} : AM unit :=
  match n with
  | O => aret tt
  | S n' => err_clear i false ;;; err_clear_slots (S i) n'
  end.
Definition err_clear_error : AM unit :=
  err_clear_slots 0 ERR_NUM ;;; amodify (fun s => set_bottom 0%nat (set_top 0%nat s)).

(* [comment removed for export] *)
Definition err_set_mark : AM unit :=
  s <- aget ;;
  if Nat.eqb (as_bottom s) (as_top s) then aret tt
  else amodify (set_marks (as_top s) (get_marks (as_top s) s + 1)).

(* [comment removed for export] *)
Fixpoint err_pop_loop (n : nat) {struct n} : AM unit :=
  match n with
  | O => aret tt
  | S n' =>
      s <- aget ;;
      if Nat.eqb (as_bottom s) (as_top s) then aret tt
      else if negb (get_marks (as_top s) s =? 0) then aret tt
      else err_clear (as_top s) false ;;; amodify (fun s => set_top (ring_prev (as_top s)) s) ;;; err_pop_loop n'
  end.
Definition err_pop_to_mark : AM unit :=
  err_pop_loop ERR_NUM ;;;
  s <- aget ;;
  if Nat.eqb (as_bottom s) (as_top s) then aret tt
  else amodify (set_marks (as_top s) (get_marks (as_top s) s - 1)).

(* [comment removed for export] *)
Definition err_peek_last_error : AM Z :=
  s <- aget ;;
  if Nat.eqb (as_bottom s) (as_top s) then aret 0 else aret (get_buf (as_top s) s).

End Err.
