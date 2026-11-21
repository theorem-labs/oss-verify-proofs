(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia String.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL ZApiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition CK_FILE : list Z := str "/work/targets/zlib-compress_fuzzer/compress_fuzzer.c".
Definition CK_FUNC : list Z := str "check_compress_level".
Definition CK_EXPR1 : list Z := str "dataLen == uncomprLen".
Definition CK_EXPR2 : list Z := str "0 == memcmp(data, uncompr, dataLen)".
Definition CK_LINE1 : Z := 43.
Definition CK_LINE2 : Z := 44.

Definition pieces_check (expr : list Z) (line : Z) : list (list Z) :=
  [ str "Assertion failed: "; []; []; expr; str " ("; []; []; CK_FILE; str ": "; []; []; CK_FUNC; str ": "; []; []; Zdecimal line;
    str ")" ++ [10] ].
Definition msg_check (expr : list Z) (line : Z) : list Z := List.concat (pieces_check expr line).
Local Close Scope string_scope.

Inductive ckfail : Type := CK1 | CK2.
Definition ck_pieces (k : ckfail) : list (list Z) :=
  match k with CK1 => pieces_check CK_EXPR1 CK_LINE1 | CK2 => pieces_check CK_EXPR2 CK_LINE2 end.
Definition ck_msg (k : ckfail) : list Z := List.concat (ck_pieces k).

Definition sel_level (d8 : list Z) : Z := znth d8 0 mod 10.
Definition sel_cm (d8 : list Z) : Z := let c := znth d8 1 mod 5 in if c =? 4 then 8 else c.
Definition sel_flags (d8 : list Z) : Z := Z.land (znth d8 2) 32.

Definition zhdr_word (cm flags : Z) : Z :=
  let h := Z.lor (Z.shiftl (8 + Z.shiftl flags 4) 8) (Z.shiftl cm 6) in h + (31 - h mod 31).
Definition zhdr_bytes (cm flags : Z) : list Z :=
  [ Z.shiftr (zhdr_word cm flags) 8 mod 256; zhdr_word cm flags mod 256 ].

Definition bufC (bs : list Z) (n : Z) : list Z := firstn (Z.to_nat n) (bs ++ zrepeat 0 (n - zlength bs)).

Section HarnessC.
Variable za : zapiC.

Record c2L : Type := mkC2L { c2_ds : DSC za; c2_left : Z; c2_slen : Z; c2_rest : list Z; c2_ain : Z; c2_aout : Z; c2_orev : list Z }.

Definition c2_refill (x : c2L) : Z * Z * Z * Z :=
  let '(ao, lf) := if c2_aout x =? 0 then (let a := if ZC_UMAX <? c2_left x then ZC_UMAX else c2_left x in (a, c2_left x - a))
                   else (c2_aout x, c2_left x) in
  let '(ai, sl) := if c2_ain x =? 0 then (let a := if ZC_UMAX <? c2_slen x then ZC_UMAX else c2_slen x in (a, c2_slen x - a))
                   else (c2_ain x, c2_slen x) in
  (ao, lf, ai, sl).
Definition c2_flush (sl : Z) : Z := if sl =? 0 then Z_FINISH else Z_NO_FLUSH.

Definition c_step_ok (ai ao : Z) (ds ds' : DSC za) (consumed : Z) (bs : list Z) : bool :=
  (0 <=? consumed) && (consumed <=? ai) && (zlength bs <=? ao) && (dc_total_out za ds' =? dc_total_out za ds + zlength bs).

Definition c2_stepP (x : c2L) : c2L + option (c2L * Z) :=
  let '(ao, lf, ai, sl) := c2_refill x in
  let '(ds', consumed, bs, rc) := dc_deflate za (ztake ai (c2_rest x)) (c2_ds x) ao (c2_flush sl) in
  if c_step_ok ai ao (c2_ds x) ds' consumed bs then
    let x' := mkC2L ds' lf sl (zdrop consumed (c2_rest x)) (ai - consumed) (ao - zlength bs) (rev_append bs (c2_orev x)) in
    if rc =? Z_OK then inl x' else inr (Some (x', rc))
  else inr None.

Definition C2_FUEL (N slen : Z) : Z := N + slen + 2.

Definition c2_x0 (N : Z) (src : list Z) (level : Z) : c2L := mkC2L (dc_init za level) N (zlength src) src 0 0 [].
Definition c2_loop (N : Z) (src : list Z) (level : Z) : option (c2L * Z) :=
  iterZL (C2_FUEL N (zlength src)) c2_stepP (fun _ => None) (c2_x0 N src level).

Definition c2_pure (N : Z) (src : list Z) (level : Z) : option (list Z * Z * Z) :=
  match c2_loop N src level with
  | None => None
  | Some (x, err) =>
      let out := rev_append (c2_orev x) [] in
      let tout := dc_total_out za (c2_ds x) in
      if (tout =? zlength out) && (tout <=? N)
      then Some (out, tout, if err =? Z_STREAM_END then Z_OK else err)
      else None
  end.

Definition c2_final (N : Z) (src : list Z) (level : Z) : option (DSC za) :=
  match c2_loop N src level with Some (x, _) => Some (c2_ds x) | None => None end.

Record u2L : Type := mkU2L { u2_is : ISC za; u2_left : Z; u2_len : Z; u2_rest : list Z; u2_ain : Z; u2_aout : Z; u2_orev : list Z }.

Definition u2_refill (x : u2L) : Z * Z * Z * Z :=
  let '(ao, lf) := if u2_aout x =? 0 then (let a := if ZC_UMAX <? u2_left x then ZC_UMAX else u2_left x in (a, u2_left x - a))
                   else (u2_aout x, u2_left x) in
  let '(ai, ln) := if u2_ain x =? 0 then (let a := if ZC_UMAX <? u2_len x then ZC_UMAX else u2_len x in (a, u2_len x - a))
                   else (u2_ain x, u2_len x) in
  (ao, lf, ai, ln).

Definition u2_inp (x : u2L) : list Z := let '(_, _, ai, _) := u2_refill x in ztake ai (u2_rest x).
Definition u2_ao (x : u2L) : Z := let '(ao, _, _, _) := u2_refill x in ao.
Definition u2_wants (x : u2L) : bool := ic_wants_window za (u2_inp x) (u2_is x) (u2_ao x).

Definition u_step_ok (ai ao : Z) (consumed : Z) (bs : list Z) (rc : Z) : bool :=
  (zlength bs <=? ao) && (negb (rc =? Z_OK) || ((0 <=? consumed) && (consumed <=? ai))).

Definition u2_stepP (ok : bool) (x : u2L) : u2L + option (u2L * Z) :=
  let '(ao, lf, ai, ln) := u2_refill x in
  let '(is', consumed, bs, rc) := ic_inflate za (ztake ai (u2_rest x)) (u2_is x) ao ok in
  if u_step_ok ai ao consumed bs rc then
    let x' := mkU2L is' lf ln (zdrop consumed (u2_rest x)) (ai - consumed) (ao - zlength bs) (rev_append bs (u2_orev x)) in
    if rc =? Z_OK then inl x' else inr (Some (x', rc))
  else inr None.

Definition U2_FUEL (dlen slen : Z) : Z := dlen + slen + 4.

Definition u2_x0 (dlen : Z) (src : list Z) : u2L := mkU2L (ic_init za) dlen (zlength src) src 0 0 [].
Definition u2_loop (dlen : Z) (src : list Z) : option (u2L * Z) :=
  iterZL (U2_FUEL dlen (zlength src)) (u2_stepP true) (fun _ => None) (u2_x0 dlen src).

(* zlib 1.4, O7: Z_BUF_ERROR becomes Z_DATA_ERROR iff all input
   was consumed (unused input len + avail_in = 0); 1.3.1: iff room was left. ZTargetC.uncompress2M returns
   this code; the harness (oss-fuzz #16582) tests it for Z_MEM_ERROR. *)
Definition u2_rc (err : Z) (x : u2L) : Z :=
  if err =? Z_STREAM_END then Z_OK
  else if err =? Z_NEED_DICT then Z_DATA_ERROR
  else if (err =? Z_BUF_ERROR) && (u2_len x + u2_ain x =? 0) then Z_DATA_ERROR
  else err.

(* zlib 1.4: *destLen := dlen - (left + avail_out),
   the room the calls did not use (1.3.1 wrote total_out).  [u2_room_step] below keeps left + avail_out + |output|
   = dlen at every step and every rc, so this length is the output's length at every exit. *)
Definition u2_result (dlen : Z) (x : u2L) (err : Z) : list Z * Z * Z :=
  (rev_append (u2_orev x) [], dlen - (u2_left x + u2_aout x), u2_rc err x).

Definition u2_pure (dlen : Z) (src : list Z) : option (list Z * Z * Z) :=
  match u2_loop dlen src with
  | None => None
  | Some (x, err) => Some (u2_result dlen x err)
  end.

Lemma u2_zlength_rev_append : forall (l a : list Z), zlength (rev_append l a) = zlength l + zlength a.
Proof. intros l a. unfold zlength. rewrite rev_append_rev, length_app, length_rev. lia. Qed.

(** One step of the uncompress loop moves room from [left] to [avail_out] (the refill) and from [avail_out] to the
    output (the call's bytes, at most its room by [u_step_ok]), whatever the call's rc. *)
Lemma u2_refill_room : forall x ao lf ai ln, u2_refill x = (ao, lf, ai, ln) -> ao + lf = u2_left x + u2_aout x.
Proof.
  intros x ao lf ai ln H. unfold u2_refill in H. revert H.
  destruct (Z.eqb_spec (u2_aout x) 0) as [E|E];
    [destruct (ZC_UMAX <? u2_left x)|];
    destruct (u2_ain x =? 0); try destruct (ZC_UMAX <? u2_len x);
    cbv beta iota zeta; intros H; injection H; intros; subst; lia.
Qed.

Lemma u2_room_step : forall ok x x',
  (u2_stepP ok x = inl x' \/ exists e, u2_stepP ok x = inr (Some (x', e))) ->
  u2_left x' + u2_aout x' + zlength (u2_orev x') = u2_left x + u2_aout x + zlength (u2_orev x).
Proof.
  intros ok x x' H. unfold u2_stepP in H.
  destruct (u2_refill x) as [[[ao lf] ai] ln] eqn:ER.
  pose proof (u2_refill_room x ao lf ai ln ER) as HR.
  destruct (ic_inflate za (ztake ai (u2_rest x)) (u2_is x) ao ok) as [[[is' consumed] bs] rc].
  destruct (u_step_ok ai ao consumed bs rc); [|destruct H as [H|(e & H)]; discriminate H].
  destruct (rc =? Z_OK); destruct H as [H|(e & H)]; try discriminate H;
    injection H; intros; subst; cbn [u2_left u2_aout u2_orev]; rewrite u2_zlength_rev_append; lia.
Qed.

Inductive houtC : Type :=
| HC_ret
| HC_exit (k : ckfail)
| HC_stuck.

Definition check_level_pure (data : list Z) (n cl level : Z) : option (ckfail + unit) :=
  match c2_pure cl data level with
  | None => None
  | Some (cout, clen, _) =>

      match u2_pure n (norm8 cout) with
      | None => None
      | Some (uout, ulen, _) =>
          if negb (n =? ulen) then Some (inl CK1)
          else if negb (zlist_eqb data (norm8 (bufC uout n))) then Some (inl CK2)
          else Some (inr tt)
      end
  end.

Definition check_decompress_pure (data : list Z) (cl cm flags : Z) : option unit :=
  match u2_pure cl (zhdr_bytes cm flags ++ data) with
  | None => None
  | Some _ => Some tt
  end.

Definition harness_outC (d : list Z) : houtC :=
  let size := zlength d in
  if (size <? ZC_MIN) || (ZC_MAX <? size) then HC_ret
  else
    let d8 := norm8 d in
    let data := zdrop 3 d8 in
    let n := size - 3 in
    let cl := zc_bound za n in
    match check_level_pure data n cl (sel_level d8) with
    | None => HC_stuck
    | Some (inl k) => HC_exit k
    | Some (inr _) =>
        match check_decompress_pure data cl (sel_cm d8) (sel_flags d8) with
        | None => HC_stuck
        | Some _ => HC_ret
        end
    end.

Definition harness_exitC (d : list Z) : option (list Z) :=
  match harness_outC d with HC_exit k => Some (ck_msg k) | _ => None end.

Definition ZBC_MAX : Z := 2 * ZC_MAX.

Definition u2_reach (dlen : Z) (src : list Z) (x : u2L) : Prop :=
  exists k, iterNL k (u2_stepP true) (u2_x0 dlen src) = inl x.

Record zapiC_ok : Prop := mkZapiCOk {

  zo_sizesC : Forall (fun n => 0 < n <= 65536)
                     [zc_dstate za; zc_dwin za; zc_dprev za; zc_dhead za; zc_dpend za; zc_isize za; zc_wsize za];
  zo_boundC : forall n, 1 <= n <= ZC_MAX -> n < zc_bound za n <= ZBC_MAX;

  zo_c2C : forall N src level, 0 <= N <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    0 <= level <= 9 -> c2_pure N src level <> None;

  zo_u2C : forall dlen src, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    u2_pure dlen src <> None;

  zo_u2twoC : forall dlen src x1 ok, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    u2_stepP true (u2_x0 dlen src) = inl x1 -> exists r, u2_stepP ok x1 = inr r;

  zo_nomemC : forall dlen src x, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    u2_reach dlen src x -> u2_wants x = true ->
    exists x', u2_stepP false x = inr (Some (x', Z_MEM_ERROR))
}.

Lemma c2_pure_post : forall N src level out tout rc,
  c2_pure N src level = Some (out, tout, rc) -> tout = zlength out /\ tout <= N.
Proof.
  intros N src level out tout rc. unfold c2_pure. destruct (c2_loop N src level) as [[x err]|]; [| intros H; discriminate H].
  destruct (Z.eqb_spec (dc_total_out za (c2_ds x)) (zlength (rev_append (c2_orev x) []))) as [E1|E1]; cbn [andb]; [| intros H; discriminate H].
  destruct (Z.leb_spec (dc_total_out za (c2_ds x)) N) as [E2|E2]; [| intros H; discriminate H].
  intros H. injection H as <- <- _. split; [exact E1 | exact E2].
Qed.

Definition c2_reach (N : Z) (src : list Z) (level : Z) (x : c2L) : Prop :=
  exists k, iterNL k c2_stepP (c2_x0 N src level) = inl x.

Lemma c2_reach_x0 : forall N src level, c2_reach N src level (c2_x0 N src level).
Proof. intros. exists O. reflexivity. Qed.

Lemma c2_reach_step : forall N src level x x', c2_reach N src level x -> c2_stepP x = inl x' -> c2_reach N src level x'.
Proof.
  intros N src level x x' [k Hk] Hs. exists (k + 1)%nat. rewrite iterNL_add, Hk. cbn [iterNL]. rewrite Hs. reflexivity.
Qed.

Lemma u2_reach_x0 : forall dlen src, u2_reach dlen src (u2_x0 dlen src).
Proof. intros dlen src. exists O. reflexivity. Qed.

Lemma u2_reach_step : forall dlen src x x', u2_reach dlen src x -> u2_stepP true x = inl x' -> u2_reach dlen src x'.
Proof.
  intros dlen src x x' [k Hk] Hs. exists (k + 1)%nat. rewrite iterNL_add, Hk. cbn [iterNL]. rewrite Hs. reflexivity.
Qed.

Definition u2_after (n : nat) (x : u2L) : option (u2L * Z) :=
  match iterNL n (u2_stepP true) x with inl _ => None | inr r => r end.

Lemma u2_loop_after : forall dlen src, u2_loop dlen src = u2_after (Z.to_nat (U2_FUEL dlen (zlength src))) (u2_x0 dlen src).
Proof. intros dlen src. unfold u2_loop, u2_after. rewrite iterZL_nat. destruct (iterNL _ _ _) as [a|r]; reflexivity. Qed.

Lemma u2_after_S : forall n x, u2_after (S n) x = match u2_stepP true x with inl x' => u2_after n x' | inr r => r end.
Proof. intros n x. unfold u2_after. cbn [iterNL]. destruct (u2_stepP true x) as [x'|r]; reflexivity. Qed.

Lemma sel_level_range : forall d8, 0 <= sel_level d8 <= 9.
Proof. intros d8. unfold sel_level. pose proof (Z.mod_pos_bound (znth d8 0) 10 ltac:(lia)). lia. Qed.

Lemma zhdr_bytes_ok : forall cm flags, Forall (fun b => 0 <= b < 256) (zhdr_bytes cm flags) /\ zlength (zhdr_bytes cm flags) = 2.
Proof.
  intros cm flags. unfold zhdr_bytes. split; [| reflexivity].
  constructor; [apply Z.mod_pos_bound; lia|]. constructor; [apply Z.mod_pos_bound; lia|]. constructor.
Qed.

End HarnessC.
