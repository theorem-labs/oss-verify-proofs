(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState
  ApBase ApState ApFmt ApParse ApErr ApCnf ApBn ApObj ApPrim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Definition SZ_BIO : Z := 128.
Definition SZ_PREFIX_CTX : Z := 16.
Definition ASN1_PARSE_MAXDEPTH : Z := 128.

(* [comment removed for export] *)
Definition slice (d : list Z) (p len : Z) : list Z := firstn (Z.to_nat len) (skipn (Z.to_nat p) d).

(* [comment removed for export] *)
Definition is_string_tag (tag : Z) : bool :=
  (tag =? 19) || (tag =? 20) || (tag =? 22) || (tag =? 26) || (tag =? 18) || (tag =? 12) || (tag =? 23) || (tag =? 24).

Section Parse.
Context {ptr : Type}.
Local Notation AM := (@AM ptr) (only parsing).
Variable d : list Z.

(* [comment removed for export] *)
Definition print_info (offset depth hl len j : Z) : AM unit :=
  let inf := j =? 33 in                                              (* [comment removed for export] *)
  let n := hdr_len offset depth hl len inf in
  if (n <=? 0) || (128 <=? n) then aunr                              (* [comment removed for export] *)
  else
    bio <- amalloc SZ_BIO ;;                                         (* [comment removed for export] *)
    ctx <- amalloc SZ_PREFIX_CTX ;;                                  (* [comment removed for export] *)
    pre <- amalloc (n + 1) ;;                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    afree pre ;;; afree ctx ;;; afree bio.

(* [comment removed for export] *)
Definition prim_content (o : aobj ptr) (tag op hl len : Z) : AM (aobj ptr) :=
  let p := op + hl in
  if is_string_tag tag then aret o
  else if tag =? 6 then
    (* [comment removed for export] *)
    let g := get_object d op (len + hl) in
    match go_err g with
    | Some _ => aunr                                                 (* [comment removed for export] *)
    | None =>
        if negb (go_tag g =? 6) then aunr                            (* [comment removed for export] *)
        else
          ' (o', ok) <- c2i_asn1_object o (slice d (go_p g) (go_len g)) ;;
          (if ok then i2a_asn1_object o' else aret tt) ;;;           (* [comment removed for export] *)
          aret o'
    end
  else if tag =? 4 then
    s <- d2i_prim d op (len + hl) V_ASN1_OCTET_STRING ;;             (* [comment removed for export] *)
    asn1_string_free s ;;; aret o
  else if tag =? 2 then
    s <- d2i_prim d op (len + hl) V_ASN1_INTEGER ;; asn1_string_free s ;;; aret o
  else if tag =? 10 then
    s <- d2i_prim d op (len + hl) V_ASN1_ENUMERATED ;; asn1_string_free s ;;; aret o
  else aret o.                                                       (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint parse2 (fuel : nat) (p length offset depth : Z) {struct fuel} : AM (Z * Z) :=
  match fuel with
  | O => aunr
  | S f =>
      if ASN1_PARSE_MAXDEPTH <? depth then aret (0, p)               (* [comment removed for export] *)
      else ploop f p length offset depth p (p + length) ONone
  end
with ploop (fuel : nat) (p length offset depth pp0 tot : Z) (o : aobj ptr) {struct fuel} : AM (Z * Z) :=
  match fuel with
  | O => aunr
  | S f =>
      if length <=? 0 then asn1_object_free o ;;; aret (1, p)         (* [comment removed for export] *)
      else
        let op := p in
        let g := get_object d op length in
        match go_err g with
        | Some GeTooSmall => aunr                                    (* [comment removed for export] *)
        | Some GeHdr => err_raise RS_hdr_too_long ;;; asn1_object_free o ;;; aret (0, go_p g)      (* [comment removed for export] *)
        | Some GeTooLong => err_raise RS_too_long ;;; asn1_object_free o ;;; aret (0, go_p g)
        | None =>
            let p := go_p g in
            let hl := p - op in
            let length := length - hl in
            let len := go_len g in
            let j := go_ret g in
            let tag := go_tag g in
            let xclass := go_cls g in
            print_info (offset + (op - pp0)) depth hl len j ;;;
            if negb (Z.land j V_ASN1_CONSTRUCTED =? 0) then
              (* [comment removed for export] *)
              if length <? len then asn1_object_free o ;;; aret (0, p)
              else if (j =? 33) && (len =? 0) then
                ' (ok, p') <- kids_inf f p tot offset depth pp0 ;;
                if ok then ploop f p' (length - (p' - p)) offset depth pp0 tot o            (* [comment removed for export] *)
                else asn1_object_free o ;;; aret (0, p')
              else
                ' (ok, p') <- kids_def f p (p + len) len offset depth pp0 ;;
                if ok then ploop f p' (length - len) offset depth pp0 tot o
                else asn1_object_free o ;;; aret (0, p')
            else if negb (xclass =? 0) then
              ploop f (p + len) (length - len) offset depth pp0 tot o                   (* [comment removed for export] *)
            else
              o' <- prim_content o tag op hl len ;;
              let p := p + len in
              if tag =? 0 then asn1_object_free o' ;;; aret (2, p)                        (* [comment removed for export] *)
              else ploop f p (length - len) offset depth pp0 tot o'
        end
  end
with kids_inf (fuel : nat) (p tot offset depth pp0 : Z) {struct fuel} : AM (bool * Z) :=
  match fuel with
  | O => aunr
  | S f =>
      ' (r, p') <- parse2 f p (tot - p) (offset + (p - pp0)) (depth + 1) ;;
      if r =? 0 then aret (false, p')
      else if (r =? 2) || (tot <=? p') then aret (true, p')
      else kids_inf f p' tot offset depth pp0
  end
with kids_def (fuel : nat) (p ep tmp offset depth pp0 : Z) {struct fuel} : AM (bool * Z) :=
  match fuel with
  | O => aunr
  | S f =>
      if p <? ep then
        ' (r, p') <- parse2 f p tmp (offset + (p - pp0)) (depth + 1) ;;
        if r =? 0 then aret (false, p')
        else kids_def f p' ep (tmp - (p' - p)) offset depth pp0
      else aret (true, p)
  end.

End Parse.

Definition ap_fuel (d : list Z) : nat := (3 * (length d + 200))%nat.

(* [comment removed for export] *)
Definition ap_bytes (d : list Z) : list Z := map u8 d.
Definition ap_one {ptr} (ls : ap_ls ptr) (d : list Z) : aprog ptr (ap_ls ptr * Z) :=
  apbind ((parse2 (ap_bytes d) (ap_fuel d) 0 (zlength d) 0 0 ;;; err_clear_error) (st_of_ls ls))
         (fun r => ARet (ls_of_st (snd r), 0)).

Lemma ap_bytes_id d : Forall (fun b => 0 <= b < 256) d -> ap_bytes d = d.
Proof.
  intros H. unfold ap_bytes. induction H as [|b l Hb HF IH]; [reflexivity|]. cbn. rewrite IH. f_equal. unfold u8. apply Z.mod_small. exact Hb.
Qed.
