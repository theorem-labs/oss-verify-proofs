(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Inductive xev : Type :=
| XE (e : ev)
| XMremap (addr old_len new_len flags : Z).

Definition MX (R : Type) := stree xev Z R.

Fixpoint xlift {R} (t : M R) : MX R :=
  match t with
  | SRet r => SRet r
  | SVis e k => SVis (XE e) (fun z => xlift (k z))
  end.

Lemma xlift_ret {R} (r : R) : xlift (SRet r) = SRet r.
Proof. reflexivity. Qed.
Lemma xlift_vis {R} e (k : Z -> M R) : xlift (SVis e k) = SVis (XE e) (fun z => xlift (k z)).
Proof. reflexivity. Qed.

Lemma xlift_sbind {R S} (t : M R) (f : R -> M S) :
  steq (xlift (sbind t f)) (sbind (xlift t) (fun r => xlift (f r))).
Proof. induction t as [r|e k IH]; cbn; [apply steq_refl|]. constructor. intros a. apply IH. Qed.

Definition xbad_answer {R} (bail : MX R) : MX R := SVis (XE (EUndef UBadAnswer)) (fun _ => bail).
Definition xguard {R} (tag : Z) (c : bool) (k : MX R) (bail : MX R) : MX R :=
  if c then k else SVis (XE (EUndef (UAssert tag))) (fun _ => bail).

(* [comment removed for export] *)
Fixpoint xfollow {R} (t : MX R) (ans : list Z) : option R :=
  match t, ans with
  | SRet r, _ => Some r
  | SVis (XE (EUndef _)) _, _ => None
  | SVis _ k, a :: ans' => xfollow (k a) ans'
  | SVis _ _, [] => None
  end.

(* [comment removed for export] *)
Section XRUN.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Variable pupd : O -> ev -> Z -> O.
Definition xpsel (o : O) (e : xev) : option Z :=
  match e with XE (EPeek p c h) => Some (pans o p c h) | _ => None end.
Definition xpupd (o : O) (e : xev) (z : Z) : O :=
  match e with XE e' => pupd o e' z | XMremap _ _ _ _ => o end.
Definition xprun {R} (o : O) (t : MX R) : MX (O * R) := eruns xpsel xpupd o t.

Lemma xprun_ret {R} o (r : R) : xprun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
Lemma xprun_peek {R} o p c h (k : Z -> MX R) :
  xprun o (SVis (XE (EPeek p c h)) k) = xprun (pupd o (EPeek p c h) (pans o p c h)) (k (pans o p c h)).
Proof. reflexivity. Qed.
Lemma xprun_vis {R} o (e : xev) (k : Z -> MX R) :
  match e with XE (EPeek _ _ _) => False | _ => True end ->
  xprun o (SVis e k) = SVis e (fun z => xprun (xpupd o e z) (k z)).
Proof. intros He. destruct e as [e|]; [destruct e|]; try reflexivity. destruct He. Qed.

(* [comment removed for export] *)
Lemma xprun_xlift {R} : forall (t : M R) o,
  steq (xprun o (xlift t)) (xlift (prun pans pupd o t)).
Proof.
  induction t as [r|e k IH]; intros o; cbn -[xpsel psel].
  - apply steq_refl.
  - unfold prun. cbn [eruns xlift]. change (psel pans o e) with (xpsel o (XE e)).
    destruct (xpsel o (XE e)) as [a|] eqn:E.
    + cbn. apply IH.
    + cbn. constructor. intros a. apply IH.
Qed.
End XRUN.
End RC__1.
Arguments xpsel {O} pans o e.
Arguments xpupd {O} pupd o e z.
Arguments xprun {O} pans pupd {R} o t.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma xfollow_xlift {R} : forall (t : M R) ans, xfollow (xlift t) ans = follow t ans.
Proof.
  induction t as [r|e k IH]; intros ans; cbn; [destruct ans; reflexivity|].
  destruct e; destruct ans; cbn; try reflexivity; apply IH.
Qed.

Lemma xfollow_steq {R} : forall (t1 t2 : MX R) ans, steq t1 t2 -> xfollow t1 ans = xfollow t2 ans.
Proof.
  intros t1 t2 ans H; revert ans; induction H as [r|e k1 k2 Hk IH]; intros ans; [reflexivity|].
  destruct e as [e|]; [destruct e|]; destruct ans; cbn; try reflexivity; apply IH.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SYS_mremap : Z := 216.
Definition MREMAP_MAYMOVE : Z := 1.
Definition PTRDIFF_MAX : Z := 2^63 - 1.

(* [comment removed for export] *)
Definition mremap_answer_ok (live : list (Z * Z)) (old old_len new_len r : Z) : bool :=
  is_errno_form r
  || ((r =? old) && ((new_len <? old_len)
                     || ((old + new_len <=? alloc_ceiling) && ranges_free live (old + old_len) (new_len - old_len))))
  || (negb (r =? old) && (0 <? r) && (r mod PGSZ =? 0) && (r + new_len <=? alloc_ceiling)
      && ranges_free live r new_len).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition shadow_trunc (len : Z) (sh : shadow) : shadow :=
  mkShadow (filter (fun kv : Z * (Z * N) => kv.1 <? len) (r_cells sh))
           (filter (fun kv : Z * list (Z * N) => kv.1 * 16 <? len) (r_hav sh))
           (filter (fun kv : Z * N => kv.1 * 4096 <? len) (r_havp sh)).

(* [comment removed for export] *)
Definition remap_region (rid : N) (g : aptr) (newbase needed : Z) (st : mstate) : mstate :=
  let st1 := upd_region rid (fun r => mkRegion (r_kind r) newbase needed) st in
  let st2 := upd_shadow rid (shadow_trunc needed) st1 in
  upd_meta g (m_set_maplen (needed / 4096)) st2.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition realloc_hdr (st : mstate) (p : aptr) : M (option (aptr * Z * Z)) :=
  let bail := ret (@None (aptr * Z * Z)) in
  get_meta st p (fun g _ idx =>
    let mr := get_meta_rec st g in
    match slot_start mr idx with
    | None => SVis (EUndef UBadPtr) (fun _ => bail)
    | Some start =>
      let e := aadd start (get_stride mr - IB) in
      get_nominal_size st p e (fun old_size => ret (Some (g, idx, old_size))) bail
    end) bail.

(* [comment removed for export] *)
Definition realloc_move (st : mstate) (p : aptr) (n : Z) : MX (mstate * optr) :=
  ' (st1, r) <-- xlift (malloc st n) ;;
  match r with
  | None => SRet (st1, None)
  | Some q => st2 <-- xlift (free st1 (Some p)) ;; SRet (st2, Some q)
  end.

(* [comment removed for export] *)
Definition realloc_big_tail (st : mstate) (gmem : aptr) (base idx needed n : Z) : mstate * optr :=
  let p := aadd gmem (UNIT + base) in
  let e := aadd gmem (needed - IB) in
  (havoc p n (set_size p e n idx (wr8 e 0 st)), Some p).

Definition realloc (st0 : mstate) (p : optr) (n : Z) : MX (mstate * optr) :=
  match p with
  | None => xlift (malloc st0 n)
  | Some p =>
    if size_overflows n then SRet (st0, None) else
    let st := set_tick (N.succ (s_tick st0)) st0 in
    h <-- xlift (realloc_hdr st p) ;;
    match h with
    | None => SRet (st, None)                      (* [comment removed for export] *)
    | Some (g, idx, old_size) =>
      let mr := get_meta_rec st g in
      let stride := get_stride mr in
      let start := slot_start' mr idx in
      let e := aadd start (stride - IB) in
      let avail := snd e - snd p in
      if (n <=? avail) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) then
        (* [comment removed for export] *)
        SRet (havoc p n (set_size p e n idx st), Some p)
      else if (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n) then
        xguard 70 (m_sizeclass mr =? 63) (
          let base := snd p - snd start in
          let needed := round_up_pg (n + base + UNIT + IB) in
          let maplen4096 := m_maplen mr * 4096 in
          let gmem := default (0%N, 0) (m_mem mr) in
          if maplen4096 =? needed then
            (* [comment removed for export] *)
            SRet (realloc_big_tail st gmem base idx needed n)
          else if PTRDIFF_MAX <=? needed then
            (* [comment removed for export] *)
            realloc_move st p n
          else
            SVis (XMremap (conc st gmem) maplen4096 needed MREMAP_MAYMOVE) (fun r =>
              if negb (mremap_answer_ok (live_ranges st) (conc st gmem) maplen4096 needed r)
              then xbad_answer (SRet (st, None))
              else if is_err r then realloc_move st p n        (* [comment removed for export] *)
              else (* [comment removed for export] *)
                SRet (realloc_big_tail (remap_region (fst gmem) g r needed st) gmem base idx needed n)))
          (SRet (st, None))
      else realloc_move st p n
    end
  end.
End RC__2.
