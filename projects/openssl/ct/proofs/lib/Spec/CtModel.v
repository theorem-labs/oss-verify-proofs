(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState ApErr ApParse CtSizes CtWire CtTime.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record bufm (ptr : Type) : Type := mkBuf { bm_len : Z; bm_data : option (ptr * Z); bm_bytes : list Z }.
Arguments mkBuf {ptr}. Arguments bm_len {ptr}. Arguments bm_data {ptr}. Arguments bm_bytes {ptr}.
Definition bm_max {ptr} (b : bufm ptr) : Z := match bm_data b with Some (_, m) => m | None => 0 end.
Definition buf0 {ptr} : bufm ptr := mkBuf 0 None [].

(* [comment removed for export] *)
Record octet (ptr : Type) : Type := mkOct { os_blk : ptr; os_data : option (ptr * Z); os_len : Z; os_bytes : list Z }.
Arguments mkOct {ptr}. Arguments os_blk {ptr}. Arguments os_data {ptr}. Arguments os_len {ptr}. Arguments os_bytes {ptr}.

Section Model.
Context {ptr : Type}.
Local Notation AM := (@AM ptr) (only parsing).
Local Notation ST := (ap_st ptr) (only parsing).

(* [comment removed for export] *)
Definition tlen_fail (e : go_errk) : AM unit :=
  match e with
  | GeHdr => err_raise RS_hdr_too_long
  | GeTooLong => err_raise RS_too_long
  | GeTooSmall => aunr                                   (* [comment removed for export] *)
  end ;;; err_raise RS_tlen_bad_hdr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIMIT_BEFORE_EXPANSION : Z := 1610612732.    (* [comment removed for export] *)

Definition buf_grow_clean (b : bufm ptr) (len : Z) : AM (bufm ptr) :=
  if len <=? bm_len b then aret (mkBuf len (bm_data b) (bm_bytes b))
  else if len <=? bm_max b then aret (mkBuf len (bm_data b) (bm_bytes b))
  else if LIMIT_BEFORE_EXPANSION <? len then aunr          (* [comment removed for export] *)
  else
    let n := (len + 3) / 3 * 4 in
    (* [comment removed for export] *)
    q <- amalloc n ;;
    afree_opt (option_map fst (bm_data b)) ;;;
    aret (mkBuf len (Some (q, n)) (bm_bytes b)).

(* [comment removed for export] *)
Definition collect_data (d : list Z) (b : bufm ptr) (p plen : Z) : AM (bufm ptr * Z) :=
  b' <- buf_grow_clean b (bm_len b + plen) ;;          (* [comment removed for export] *)
  aret (mkBuf (bm_len b') (bm_data b') (bm_bytes b ++ slice d p plen), p + plen).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint collect (fuel : nat) (d : list Z) (b : bufm ptr) (p len : Z) (inf : bool) (depth : Z) {struct fuel}
  : AM (bufm ptr * option Z) :=
  match fuel with
  | O => aunr
  | S f =>
    if len <=? 0 then
      (if inf then err_raise RS_coll_miss_eoc ;;; aret (b, None) else aret (b, Some p))
    else if (2 <=? len) && (znth d p =? 0) && (znth d (p + 1) =? 0) then
      (* [comment removed for export] *)
      (if inf then aret (b, Some (p + 2)) else err_raise RS_coll_unexp_eoc ;;; aret (b, None))
    else
      let g := get_object d p len in
      match go_err g with
      | Some e => tlen_fail e ;;; err_raise RS_coll_nested ;;; aret (b, None)
      | None =>
          let p1 := go_p g in
          let ininf := Z.testbit (go_ret g) 0 in
          let cst := negb (Z.land (go_ret g) 32 =? 0) in
          let plen := if ininf then len - (p1 - p) else go_len g in
          if cst then
            if 5 <=? depth then err_raise RS_coll_nest_str ;;; aret (b, None)
            else
              ' (b1, r) <- collect f d b p1 plen ininf (depth + 1) ;;
              match r with
              | None => aret (b1, None)
              | Some p2 => collect f d b1 p2 (len - (p2 - p)) inf depth
              end
          else
            ' (b1, p2) <- (if plen =? 0 then aret (b, p1) else collect_data d b p1 plen) ;;
            collect f d b1 p2 (len - (p2 - p)) inf depth
      end
  end.

Definition ct_fuel (d : list Z) : nat := (2 * length d + 16)%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition d2i_octet (d : list Z) (len : Z) : AM (option (octet ptr)) :=
  if len <=? 0 then err_raise RS_td_small ;;; aret None                                     (* [comment removed for export] *)
  else
    let g := get_object d 0 len in                                                        (* [comment removed for export] *)
    match go_err g with
    | Some e => tlen_fail e ;;; err_raise RS_prim_nested ;;; aret None
    | None =>
        (* [comment removed for export] *)
        if negb (go_tag g =? V_ASN1_OCTET_STRING) || negb (go_cls g =? 0)
        then err_raise RS_tlen_wrong_tag ;;; err_raise RS_prim_nested ;;; aret None
        else
          let p := go_p g in
          let inf := Z.testbit (go_ret g) 0 in
          let cst := negb (Z.land (go_ret g) 32 =? 0) in
          let plen := if inf then len - p else go_len g in
          if cst then
            ' (b, r) <- collect (ct_fuel d) d buf0 p plen inf 0 ;;
            match r with
            | None => afree_opt (option_map fst (bm_data b)) ;;; aret None                     (* [comment removed for export] *)
            | Some _ =>
                let l := bm_len b in
                b2 <- buf_grow_clean b (l + 1) ;;                                             (* [comment removed for export] *)
                blk <- amalloc SZ_ASN1_STRING ;;                                              (* [comment removed for export] *)
                aret (Some (mkOct blk (bm_data b2) l (firstn (Z.to_nat l) (bm_bytes b2))))   (* [comment removed for export] *)
            end
          else
            blk <- amalloc SZ_ASN1_STRING ;;                                                  (* [comment removed for export] *)
            dp <- amalloc_crypto plen ;;                                                      (* [comment removed for export] *)
            aret (Some (mkOct blk (option_map (fun q => (q, plen)) dp) plen (slice d p plen)))
    end.

(* [comment removed for export] *)
Definition octet_free (o : octet ptr) : AM unit := afree_opt (option_map fst (os_data o)) ;;; afree (os_blk o).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sct_free (s : sctr ptr) : AM unit :=
  afree_opt (sc_logid s) ;;; afree_opt (option_map fst (sc_ext s)) ;;; afree_opt (option_map fst (sc_sig s)) ;;;
  afree_opt (option_map fst (sc_blob s)) ;;; afree (sc_blk s).

(* [comment removed for export] *)
Fixpoint scts_free (l : list (sctr ptr)) : AM unit :=
  match l with [] => aret tt | s :: t => sct_free s ;;; scts_free t end.
Definition sk_free_all (k : skr ptr) : AM unit :=
  scts_free (sk_items k) ;;; afree_opt (option_map fst (sk_data k)) ;;; afree (sk_blk k).

(* [comment removed for export] *)
Definition o2i_sct_signature (s : sctr ptr) (c : list Z) (p len : Z) : AM (sctr ptr * Z) :=
  if negb (sc_version s =? 0) then err_raise RS_sig_version ;;; aret (s, -1)           (* [comment removed for export] *)
  else if len <=? 4 then err_raise RS_sig_len4 ;;; aret (s, -1)
  else
    let s := set_algs (byte c p) (byte c (p + 1)) s in
    if sct_nid s =? NID_undef then err_raise RS_sig_nid ;;; aret (s, -1)
    else
      let siglen := u16be c (p + 2) in
      let rem := len - 4 in
      if rem <? siglen then err_raise RS_sig_overrun ;;; aret (s, -1)
      else
        (* [comment removed for export] *)
        afree_opt (option_map fst (sc_sig s)) ;;;
        s' <- (if 0 <? siglen then q <- amalloc siglen ;; aret (set_sig (Some (q, siglen)) s) else aret (set_sig None s)) ;;
        aret (s', len - (rem - siglen)).

(* [comment removed for export] *)
Definition o2i_sct (c : list Z) (p len : Z) : AM (option (sctr ptr)) :=
  if (len =? 0) || (MAX_SCT_SIZE <? len) then err_raise RS_sct_len ;;; aret None       (* [comment removed for export] *)
  else
    blk <- amalloc SZ_SCT ;;                                                              (* [comment removed for export] *)
    let s := set_version (byte c p) (sct_new blk) in
    if byte c p =? 0 then
      if len <? 43 then err_raise RS_sct_43 ;;; sct_free s ;;; aret None
      else
        let len := len - 43 in
        let p := p + 1 in
        lg <- amalloc CT_V1_HASHLEN ;;                                                    (* [comment removed for export] *)
        let s := set_logid (Some lg) s in
        let p := p + CT_V1_HASHLEN in
        let s := set_ts (u64be c p) s in
        let p := p + 8 in
        let len2 := u16be c p in
        let p := p + 2 in
        if len <? len2 then err_raise RS_sct_ext ;;; sct_free s ;;; aret None
        else
          s <- (if 0 <? len2 then e <- amalloc len2 ;; aret (set_ext (Some (e, len2)) len2 s) else aret (set_ext None 0 s)) ;;
          let p := p + len2 in
          let len := len - len2 in
          ' (s, r) <- o2i_sct_signature s c p len ;;
          if r <=? 0 then err_raise RS_sct_sig ;;; sct_free s ;;; aret None
          else aret (Some s)                                                              (* [comment removed for export] *)
    else
      q <- amalloc len ;;                                                                 (* [comment removed for export] *)
      aret (Some (set_blob (Some (q, len)) s)).

(* [comment removed for export] *)
Definition sk_push (k : skr ptr) (s : sctr ptr) : AM (skr ptr) :=
  let num := sk_num k in
  let want := Z.max (num + 1) SK_MIN_NODES in
  match sk_data k with
  | None => q <- amalloc (8 * want) ;; aret (mkSK (sk_blk k) (Some (q, want)) (sk_items k ++ [s]))     (* [comment removed for export] *)
  | Some (q, na) =>
      if want <=? na then aret (mkSK (sk_blk k) (Some (q, na)) (sk_items k ++ [s]))
      else
        let cur := sk_grow SK_GROW_FUEL na want in
        q' <- arealloc q (8 * cur) ;;                                                              (* [comment removed for export] *)
        aret (mkSK (sk_blk k) (Some (q', cur)) (sk_items k ++ [s]))
  end.

(* [comment removed for export] *)
Fixpoint o2i_loop (fuel : nat) (c : list Z) (k : skr ptr) (p ll : Z) {struct fuel} : AM (option (skr ptr)) :=
  match fuel with
  | O => aunr
  | S f =>
    if ll <=? 0 then aret (Some k)
    else if ll <? 2 then err_raise RS_list_lt2 ;;; sk_free_all k ;;; aret None
    else
      let sct_len := u16be c p in
      let p := p + 2 in
      let ll := ll - 2 in
      if (sct_len =? 0) || (ll <? sct_len) then err_raise RS_list_sctlen ;;; sk_free_all k ;;; aret None
      else
        let ll := ll - sct_len in
        r <- o2i_sct c p sct_len ;;
        match r with
        | None => sk_free_all k ;;; aret None
        | Some s => k' <- sk_push k s ;; o2i_loop f c k' (p + sct_len) ll
        end
  end.

(* [comment removed for export] *)
Definition o2i_sct_list (c : list Z) (len : Z) : AM (option (skr ptr)) :=
  if (len <? 2) || (MAX_SCT_LIST_SIZE <? len) then err_raise RS_list_len ;;; aret None
  else
    let ll := u16be c 0 in
    if negb (ll =? len - 2) then err_raise RS_list_mismatch ;;; aret None
    else
      kb <- amalloc SZ_STACK ;;                                                            (* [comment removed for export] *)
      o2i_loop (Z.to_nat len) c (mkSK kb None []) 2 ll.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition timestamp_print (ts : Z) : AM unit :=
  gen <- amalloc SZ_ASN1_STRING ;;                                                        (* [comment removed for export] *)
  if printable ts then
    dp <- amalloc SZ_GEN_DATA ;;                                                          (* [comment removed for export] *)
    dp' <- areallocI dp SZ_GENSTR ;;                                                      (* [comment removed for export] *)
    afree dp' ;;; afree gen                                                               (* [comment removed for export] *)
  else
    afree gen.                                                                            (* [comment removed for export] *)

Definition sct_print (s : sctr ptr) : AM unit :=
  if sc_version s =? 0 then timestamp_print (sc_ts s) else aret tt.

Fixpoint scts_print (l : list (sctr ptr)) : AM unit :=
  match l with [] => aret tt | s :: t => sct_print s ;;; scts_print t end.
Definition sct_list_print (k : skr ptr) : AM unit := scts_print (sk_items k).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint i2o_len_pass (l : list (sctr ptr)) (acc : Z) : AM (option Z) :=
  match l with
  | [] => aret (Some acc)
  | s :: t => if sct_complete s then i2o_len_pass t (acc + 2 + i2o_sct_len s)
              else err_raise RS_i2o_notset ;;; err_raise RS_i2o_list ;;; aret None      (* [comment removed for export] *)
  end.

Definition i2d_sct_list (k : skr ptr) : AM unit :=
  r <- i2o_len_pass (sk_items k) 2 ;;
  match r with
  | None => aret tt                                                                       (* [comment removed for export] *)
  | Some len2 =>
      if MAX_SCT_LIST_SIZE <? len2 then err_raise RS_i2o_list ;;; aret tt                 (* [comment removed for export] *)
      else
        data <- amalloc len2 ;;                                                           (* [comment removed for export] *)
        oct <- amalloc SZ_ASN1_STRING ;;                                                  (* [comment removed for export] *)
        der <- amalloc (der_hl len2 + len2) ;;                                            (* [comment removed for export] *)
        afree data ;;; afree oct ;;;                                                      (* [comment removed for export] *)
        afree der                                                                         (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ct_call (d : list Z) : AM Z :=
  r <- d2i_octet d (zlength d) ;;
  match r with
  | None => aret tt
  | Some os =>
      k <- o2i_sct_list (os_bytes os) (os_len os) ;;
      octet_free os ;;;
      match k with
      | None => aret tt
      | Some k =>
          bio <- amalloc SZ_BIO ;;                                                        (* [comment removed for export] *)
          sct_list_print k ;;;
          afree bio ;;;                                                                   (* [comment removed for export] *)
          i2d_sct_list k ;;;
          sk_free_all k                                                                   (* [comment removed for export] *)
      end
  end ;;;
  err_clear_error ;;;
  aret 0.

End Model.

(* [comment removed for export] *)
Definition ct_bytes (d : list Z) : list Z := map u8 d.
Definition ct_one {ptr} (ls : ap_ls ptr) (d : list Z) : aprog ptr (ap_ls ptr * Z) :=
  apbind (ct_call (ct_bytes d) (st_of_ls ls)) (fun r => ARet (ls_of_st (snd r), fst r)).

Lemma ct_bytes_id d : Forall (fun b => 0 <= b < 256) d -> ct_bytes d = d.
Proof.
  intros H. unfold ct_bytes. induction H as [|b l Hb HF IH]; [reflexivity|]. cbn. rewrite IH. f_equal. unfold u8. apply Z.mod_small. exact Hb.
Qed.
