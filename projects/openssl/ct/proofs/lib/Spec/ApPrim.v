(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState ApParse ApErr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Definition SZ_ASN1_STRING : Z := 24.
Definition V_ASN1_INTEGER : Z := 2.
Definition V_ASN1_OCTET_STRING : Z := 4.
Definition V_ASN1_ENUMERATED : Z := 10.

Record astr (ptr : Type) : Type := mkStr { str_blk : ptr; str_data : option (ptr * Z) }.
Arguments mkStr {ptr}.
Arguments str_blk {ptr}.
Arguments str_data {ptr}.

(* [comment removed for export] *)
Inductive ibuf_res : Type := IbZero | IbPad | IbOk (r : Z).

Definition c2i_ibuf_len (d : list Z) (p plen : Z) : ibuf_res :=
  if plen =? 0 then IbZero
  else if plen =? 1 then IbOk 1
  else
    let b0 := znth d p in
    let neg := Z.land b0 128 in
    let pad := if b0 =? 0 then 1
               else if b0 =? 255 then (if forallb (fun b => b =? 0) (firstn (Z.to_nat (plen - 1)) (skipn (Z.to_nat (p + 1)) d)) then 0 else 1)
               else 0 in
    if negb (pad =? 0) && (neg =? Z.land (znth d (p + 1)) 128) then IbPad
    else IbOk (plen - pad).

Section Prim.
Context {ptr : Type}.
Local Notation AM := (@AM ptr) (only parsing).

(* [comment removed for export] *)
Definition asn1_string_free (s : option (astr ptr)) : AM unit :=
  match s with
  | None => aret tt
  | Some st => afree_opt (option_map fst (str_data st)) ;;; afree (str_blk st)
  end.

(* [comment removed for export] *)
Definition d2i_prim (d : list Z) (op totlen utype : Z) : AM (option (astr ptr)) :=
  let g := get_object d op totlen in
  match go_err g with
  | Some _ => aunr                                                   (* [comment removed for export] *)
  | None =>
      let cont := go_p g in
      let plen := go_len g in
      if utype =? V_ASN1_OCTET_STRING then
        (* [comment removed for export] *)
        blk <- amalloc SZ_ASN1_STRING ;;
        (if plen =? 0 then aret (Some (mkStr blk None))
         else dp <- amalloc plen ;; aret (Some (mkStr blk (Some (dp, plen)))))
      else
        (* [comment removed for export] *)
        match c2i_ibuf_len d cont plen with
        | IbZero => err_raise RS_zero_content ;;; aret None
        | IbPad => err_raise RS_ill_padding ;;; aret None
        | IbOk r =>
            blk <- amalloc SZ_ASN1_STRING ;;                         (* [comment removed for export] *)
            dp <- amalloc r ;;                                       (* [comment removed for export] *)
            aret (Some (mkStr blk (Some (dp, r))))
        end
  end.

End Prim.
