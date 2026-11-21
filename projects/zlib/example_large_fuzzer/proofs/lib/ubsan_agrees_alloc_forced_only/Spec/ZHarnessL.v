(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia String.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim ZApi ZHarness ZApiL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint iterPL {A B : Type} (p : positive) (step : A -> A + B) (a : A) : A + B :=
  match p with
  | xH => step a
  | xO q => match iterPL q step a with inl a' => iterPL q step a' | r => r end
  | xI q => match step a with
             | inl a' => match iterPL q step a' with inl a'' => iterPL q step a'' | r => r end
             | r => r
             end
  end.
Definition iterZL {A B : Type} (n : Z) (step : A -> A + B) (dflt : A -> B) (a : A) : B :=
  match n with
  | Zpos p => match iterPL p step a with inl a' => dflt a' | inr b => b end
  | _ => dflt a
  end.

(* [comment removed for export] *)
Fixpoint iterNL {A B : Type} (n : nat) (step : A -> A + B) (a : A) : A + B :=
  match n with
  | O => inl a
  | S k => match step a with inl a' => iterNL k step a' | r => r end
  end.

Lemma iterNL_add : forall {A B} n m (step : A -> A + B) a,
  iterNL (n + m) step a = match iterNL n step a with inl a' => iterNL m step a' | r => r end.
Proof.
  induction n as [|n IH]; intros m step a; cbn; [reflexivity|].
  destruct (step a) as [a'|b]; [apply IH| reflexivity].
Qed.

Lemma iterPL_nat : forall {A B} p (step : A -> A + B) a, iterPL p step a = iterNL (Pos.to_nat p) step a.
Proof.
  induction p as [q IH|q IH|]; intros step a.
  - cbn [iterPL]. rewrite Pos2Nat.inj_xI. cbn [iterNL]. destruct (step a) as [a'|b]; [|reflexivity].
    replace (2 * Pos.to_nat q)%nat with (Pos.to_nat q + Pos.to_nat q)%nat by lia.
    rewrite iterNL_add, IH. destruct (iterNL _ _ _); [apply IH|reflexivity].
  - cbn [iterPL]. rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat q)%nat with (Pos.to_nat q + Pos.to_nat q)%nat by lia.
    rewrite iterNL_add, IH. destruct (iterNL _ _ _); [apply IH|reflexivity].
  - cbn [iterPL]. change (Pos.to_nat 1) with 1%nat. cbn [iterNL]. destruct (step a); reflexivity.
Qed.

Lemma iterZL_nat : forall {A B} n (step : A -> A + B) dflt a,
  iterZL n step dflt a = match iterNL (Z.to_nat n) step a with inl a' => dflt a' | inr b => b end.
Proof. intros A B n step dflt a. destruct n; cbn [iterZL Z.to_nat iterNL]; try reflexivity. rewrite iterPL_nat. reflexivity. Qed.

(* [comment removed for export] *)
Local Open Scope string_scope.
Definition NL_deflateInit : list Z := str "deflateInit".
Definition NL_deflate1 : list Z := str "deflate large 1".
Definition NL_deflate2 : list Z := str "deflate large 2".
Definition NL_deflate3 : list Z := str "deflate large 3".
Definition NL_deflateEnd : list Z := str "deflateEnd".
Definition NL_inflateInit : list Z := str "inflateInit".
Definition NL_inflate : list Z := str "large inflate".
Definition NL_inflateEnd : list Z := str "inflateEnd".
Definition MSGL_GREEDY : list Z := str "deflate not greedy" ++ [10].
Definition MSGL_FINISH : list Z := str "deflate large should report Z_STREAM_END" ++ [10].
(* [comment removed for export] *)
Definition msgl_bad (tout : Z) : list Z := str "bad large inflate: " ++ Zdecimal tout ++ [10].
Local Close Scope string_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HarnessL.
Variable za : zapiL.

(* [comment removed for export] *)
Inductive dexitL : Type :=
| DXL_ok                         (* [comment removed for export] *)
| DXL_err (what : list Z) (rc : Z)   (* [comment removed for export] *)
| DXL_greedy                     (* [comment removed for export] *)
| DXL_finish.                    (* [comment removed for export] *)

Definition dexitL_msg (e : dexitL) : list Z :=
  match e with DXL_ok => [] | DXL_err w rc => msg_err w rc | DXL_greedy => MSGL_GREEDY | DXL_finish => MSGL_FINISH end.

(* [comment removed for export] *)
Record dphL : Type := mkDPL { dp_ds : DSL za; dp_orev : list Z; dp_n : Z; dp_in : list Z }.

Definition dp_after (x : dphL) (ds' : DSL za) (consumed : Z) (bs : list Z) (inp : list Z) : dphL :=
  mkDPL ds' (rev_append bs (dp_orev x)) (dp_n x + zlength bs) (zdrop consumed inp).

(* [comment removed for export] *)
Definition d_callL (N flush : Z) (inp : list Z) (x : dphL) : dphL * Z :=
  let '(ds', consumed, bs, rc) := dl_deflate za inp (dp_ds x) (N - dp_n x) flush in (dp_after x ds' consumed bs inp, rc).
(* [comment removed for export] *)
Definition p_callL (N level strategy : Z) (x : dphL) : dphL * Z :=
  let '(ds', consumed, bs, rc) := dl_params za (dp_in x) (dp_ds x) (N - dp_n x) level strategy in (dp_after x ds' consumed bs (dp_in x), rc).

(* [comment removed for export] *)
Definition tdeflL (N : Z) : dphL * dexitL * option Z * bool :=
  let zeros := zrepeat 0 N in
  let x0 := mkDPL (dl_init9 za) [] 0 [] in
  let '(x1, rc1) := d_callL N Z_NO_FLUSH zeros x0 in
  if negb (rc1 =? Z_OK) then (x1, DXL_err NL_deflate1 rc1, None, false)
  else if negb (zlength (dp_in x1) =? 0) then (x1, DXL_greedy, None, false)
  else
    let '(x2, _) := p_callL N Z_NO_COMPRESSION Z_DEFAULT_STRATEGY x1 in
    let diff := dp_n x2 in
    let comprc := rev_append (dp_orev x2) [] in
    let '(x3, rc3) := d_callL N Z_NO_FLUSH comprc x2 in
    if negb (rc3 =? Z_OK) then (x3, DXL_err NL_deflate2 rc3, Some diff, false)
    else
      let '(x4, _) := p_callL N Z_BEST_COMPRESSION Z_FILTERED x3 in
      let '(x5, rc5) := d_callL N Z_NO_FLUSH zeros x4 in
      if negb (rc5 =? Z_OK) then (x5, DXL_err NL_deflate3 rc5, Some diff, false)
      else
        let '(x6, rc6) := d_callL N Z_FINISH (dp_in x5) x5 in
        if negb (rc6 =? Z_STREAM_END) then (x6, DXL_finish, Some diff, false)
        else
          let rc := dl_end za (dp_ds x6) in
          (x6, (if rc =? Z_OK then DXL_ok else DXL_err NL_deflateEnd rc), Some diff, true).

(* [comment removed for export] *)
Definition comprL (x : dphL) (N : Z) : list Z := let out := rev_append (dp_orev x) [] in firstn (Z.to_nat N) (out ++ zrepeat 0 (N - zlength out)).

Lemma comprL_length : forall x N, 0 <= N -> zlength (comprL x N) = N.
Proof.
  intros x N HN. unfold comprL, zlength, zrepeat. rewrite length_firstn, length_app, repeat_length.
  unfold zlength. lia.
Qed.
Definition test_large_deflate_pure (N : Z) : list Z * dexitL * option Z * bool :=
  let '(r, ended) := tdeflL N in let '(r2, od) := r in let '(x, e) := r2 in (comprL x N, e, od, ended).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition i_callL (N : Z) (comprc : list Z) (is : ISL za) (ok : bool) : ISL za * list Z * Z :=
  let '(is', _, bs, rc) := il_inflate za (zdrop (il_total_in za is) comprc) is N ok in (is', bs, rc).
Definition i_wantsL (N : Z) (comprc : list Z) (is : ISL za) : bool :=
  il_wants_window za (zdrop (il_total_in za is) comprc) is N.

Inductive iresL : Type :=
| IRLdone (is : ISL za)      (* [comment removed for export] *)
| IRLerr (rc : Z)            (* [comment removed for export] *)
| IRLstuck.                  (* [comment removed for export] *)

Definition il_stepP (N : Z) (comprc : list Z) (is : ISL za) : ISL za + iresL :=
  let '(is', bs, rc) := i_callL N comprc is true in
  if rc =? Z_STREAM_END then inr (IRLdone is')
  else if rc =? Z_OK then inl is'
  else inr (IRLerr rc).

(* [comment removed for export] *)
Definition ZIL_FUEL (N : Z) : Z := 2100 * N + 10000.

Definition iloopL_pure (N : Z) (comprc : list Z) (is : ISL za) : iresL :=
  iterZL (ZIL_FUEL N) (il_stepP N comprc) (fun _ => IRLstuck) is.

(* [comment removed for export] *)
Definition test_large_inflate_msg (N : Z) (comprc : list Z) (diff : Z) : list Z :=
  match iloopL_pure N (norm8 comprc) (il_init za) with
  | IRLerr rc => msg_err NL_inflate rc
  | IRLdone is => if il_end za is =? Z_OK
                  then (if il_total_out za is =? 2 * N + diff then [] else msgl_bad (il_total_out za is))
                  else msg_err NL_inflateEnd (il_end za is)
  | IRLstuck => []
  end.

(* [comment removed for export] *)
Definition harness_callL (size diff : Z) : list Z * Z :=
  if (size <? 1) || (ZL_MAX <? size) then ([], diff)
  else
    let N := NofL size in
    let '(r, _) := test_large_deflate_pure N in let '(r2, od) := r in let '(comprc, de) := r2 in
    let diff' := match od with Some d => d | None => diff end in
    (dexitL_msg de ++ test_large_inflate_msg N comprc diff', diff').

(* [comment removed for export] *)
Fixpoint harness_msgsL_from (size : Z) (calls : nat) (diff : Z) : list (list Z) :=
  match calls with
  | O => []
  | S k => let '(m, diff') := harness_callL size diff in m :: harness_msgsL_from size k diff'
  end.
Definition harness_msgsL (size : Z) (calls : nat) : list (list Z) := harness_msgsL_from size calls 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cint (v : Z) : Prop := - 2^31 <= v < 2^31.

Record zapiL_ok : Prop := mkZapiLOk {
  (* [comment removed for export] *)
  zo_iinitL : il_total_in za (il_init za) = 0 /\ il_total_out za (il_init za) = 0;
  (* [comment removed for export] *)
  zo_sizesL : Forall (fun n => 0 < n <= 65536)
                     [zl_dstate za; zl_dwin za; zl_dprev za; zl_dhead za; zl_dpend za; zl_isize za; zl_wsize za];
  (* [comment removed for export] *)
  zo_drcL : forall inp x aout flush, cint (snd (dl_deflate za inp x aout flush));
  zo_dendL : forall x, cint (dl_end za x);
  zo_ircL : forall inp x aout ok, cint (snd (il_inflate za inp x aout ok));
  zo_iendL : forall x, cint (il_end za x);
  (* [comment removed for export] *)
  zo_nomemL : forall inp x aout, il_wants_window za inp x aout = true ->
    snd (il_inflate za inp x aout false) = Z_MEM_ERROR
    /\ snd (fst (il_inflate za inp x aout false)) = snd (fst (il_inflate za inp x aout true));
  (* [comment removed for export] *)
  zo_inflateL : forall size comprc, 1 <= size <= ZL_MAX -> zlength comprc = NofL size -> Forall (fun b => 0 <= b < 256) comprc ->
    match iloopL_pure (NofL size) comprc (il_init za) with
    | IRLstuck => False
    | IRLdone is => 0 <= il_total_out za is < 2^64
    | IRLerr _ => True
    end
}.

End HarnessL.

Arguments IRLdone {za}.
Arguments IRLerr {za}.
Arguments IRLstuck {za}.
