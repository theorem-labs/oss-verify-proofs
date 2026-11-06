(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApObjTab ApBase ApState ApFmt ApErr ApCnf ApBn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Definition SZ_ASN1_OBJECT : Z := 40.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint bytes_cmp (a b : list Z) : Z :=
  match a, b with
  | x :: a', y :: b' => if x =? y then bytes_cmp a' b' else x - y
  | _, _ => 0
  end.

(* [comment removed for export] *)
Definition obj_cmp (key : list Z) (entry : list Z) : Z :=
  let c := zlength key - zlength entry in
  if c =? 0 then bytes_cmp key entry else c.

Definition tab_entry (i : Z) : Z * list Z * Z := nth (Z.to_nat i) ap_obj_table (0, [], 0).

(* [comment removed for export] *)
Fixpoint obj_bsearch_loop (fuel : nat) (key : list Z) (l h : Z) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      if l <? h then
        let i := l + (h - l) / 2 in
        let '(nid, content, lnlen) := tab_entry i in
        let c := obj_cmp key content in
        if c <? 0 then obj_bsearch_loop fuel' key l i
        else if 0 <? c then obj_bsearch_loop fuel' key (i + 1) h
        else Some (nid, lnlen)
      else None
  end.

Definition OBJ_BSEARCH_FUEL : nat := 32%nat.
Definition obj_lookup (key : list Z) : option (Z * Z) := obj_bsearch_loop OBJ_BSEARCH_FUEL key 0 NUM_OBJ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive aobj (ptr : Type) : Type :=
| ONone
| OStatic (nid lnlen : Z)
| ODyn (blk : ptr) (data : ptr) (alloc : Z) (content : list Z).
Arguments ONone {ptr}.
Arguments OStatic {ptr} nid lnlen.
Arguments ODyn {ptr} blk data alloc content.

Section Obj.
Context {ptr : Type}.
Local Notation AM := (@AM ptr) (only parsing).

(* [comment removed for export] *)
Definition asn1_object_free (o : aobj ptr) : AM unit :=
  match o with
  | ODyn blk data _ _ => afree data ;;; afree blk       (* [comment removed for export] *)
  | _ => aret tt
  end.

(* [comment removed for export] *)
Definition ossl_obj_obj2nid (key : list Z) : AM (option (Z * Z)) :=
  match obj_lookup key with
  | Some e => aret (Some e)
  | None => ossl_init_added_api ;;; aret None                (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition c2i_asn1_object (o : aobj ptr) (content : list Z) : AM (aobj ptr * bool) :=
  let len := zlength content in
  if (len <=? 0) || (2147483647 <? len) || negb (Z.land (znth content (len - 1)) 128 =? 0) then
    err_raise RS_inv_obj_a ;;; aret (o, false)
  else
    r <- ossl_obj_obj2nid content ;;
    match r with
    | Some (nid, lnlen) =>
        asn1_object_free o ;;;                                 (* [comment removed for export] *)
        aret (OStatic nid lnlen, true)
    | None =>
        (* [comment removed for export] *)
        if (fix bad (prev_cont : bool) (bs : list Z) {struct bs} : bool :=
              match bs with
              | [] => false
              | c :: bs' => ((c =? 128) && negb prev_cont) || bad (negb (Z.land c 128 =? 0)) bs'
              end) false content
        then err_raise RS_inv_obj_b ;;; aret (o, false)
        else
          ' (blk, data, alloc) <- match o with
                                  | ODyn blk data alloc _ => aret (blk, Some data, alloc)
                                  | _ => b <- amalloc SZ_ASN1_OBJECT ;; aret (b, None, 0)     (* [comment removed for export] *)
                                  end ;;
          (* [comment removed for export] *)
          ' (data, alloc) <- match data with
                             | None => d <- amalloc len ;; aret (d, len)
                             | Some d => match o with
                                         | ODyn _ _ _ prev => if zlength prev <? len then (afree d ;;; d' <- amalloc len ;; aret (d', len))
                                                              else aret (d, alloc)
                                         | _ => aunr
                                         end
                             end ;;
          aret (ODyn blk data alloc content, true)
    end.

End Obj.

(* [comment removed for export] *)
Definition obj2txt_bn {ptr} (content : list Z) : @AM ptr Z :=
  abt (tbind (obj2txt_num (tree_ops ptr) content abs0) (fun p => TRet (fst p))).

Section Obj2.
Context {ptr : Type}.
Local Notation AM := (@AM ptr) (only parsing).

Definition obj_obj2txt (o : aobj ptr) : AM Z :=
  match o with
  | ONone => aret 0                                           (* [comment removed for export] *)
  | OStatic nid lnlen => aret lnlen                           (* [comment removed for export] *)
  | ODyn _ _ _ content =>
      r <- ossl_obj_obj2nid content ;;
      match r with
      | Some (_, lnlen) => aret lnlen
      | None => if 586 <? zlength content then aret (-1) else obj2txt_bn content
      end
  end.

(* [comment removed for export] *)
Definition i2a_asn1_object (o : aobj ptr) : AM unit :=
  match o with
  | ONone => aret tt                                          (* [comment removed for export] *)
  | _ =>
      i <- obj_obj2txt o ;;
      if 79 <? i then
        p <- amalloc (i + 1) ;;
        obj_obj2txt o ;;;
        afree p
      else aret tt
  end.

End Obj2.
