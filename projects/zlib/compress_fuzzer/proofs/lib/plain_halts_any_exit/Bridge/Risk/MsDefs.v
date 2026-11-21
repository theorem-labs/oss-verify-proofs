(** * Bridge.Risk.MsDefs — the definitions risk item (b) is stated with (group R).

    Kept apart from [RiskIface] so the proof files can import them and
    [RiskIface] can re-export the proofs without a cycle; [RiskIface]
    re-exports every name here (same constants). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk Trees Deflate.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module RD := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Deflate.
Module RT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Trees.
Module RC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Chunk.

(** RT's hash chains point strictly below [strstart] (or are NIL): every
    [head] slot of the hash table and every [prev] slot of the window. *)
Definition ms_chain_ok (g : RC.DeflGeom) (l : RD.LSt) : Prop :=
  (forall i, 0 <= i < RC.dg_hash_size g ->
     0 <= RD.ls_head l i /\ (RD.ls_head l i = RD.NIL \/ RD.ls_head l i < RD.ls_strstart l))
  /\ (forall i, 0 <= i < RC.dg_w_size g ->
     0 <= RD.ls_prev l i /\ (RD.ls_prev l i = RD.NIL \/ RD.ls_prev l i < RD.ls_strstart l)).

(** The [prev] half: all [longest_match] walks. *)
Definition ms_prev_ok (g : RC.DeflGeom) (l : RD.LSt) : Prop :=
  forall i, 0 <= i < RC.dg_w_size g ->
    0 <= RD.ls_prev l i /\ (RD.ls_prev l i = RD.NIL \/ RD.ls_prev l i < RD.ls_strstart l).

(** The state facts the chain invariant needs to survive a trip (window
    slide, the inserts of fill_window and of the match loops); all hold
    from [deflateInit2] on. *)
Record ms_inv (s : RD.DSt) : Prop := {
  mi_chain : ms_chain_ok (RD.d_cfg s) (RD.d_ls s);
  mi_wsize : 512 <= RC.dg_w_size (RD.d_cfg s) <= 32768;
  mi_maxdist : RC.dg_max_dist (RD.d_cfg s) = RC.dg_w_size (RD.d_cfg s) - RC.MIN_LOOKAHEAD;
  mi_winsize : RD.ls_windowsize (RD.d_ls s) = 2 * RC.dg_w_size (RD.d_cfg s);
  mi_str : 0 <= RD.ls_strstart (RD.d_ls s);
  mi_look : 0 <= RD.ls_lookahead (RD.d_ls s);
  mi_room : RD.ls_strstart (RD.d_ls s) + RD.ls_lookahead (RD.d_ls s) <= RD.ls_windowsize (RD.d_ls s);
  mi_ins : 0 <= RD.ls_insert (RD.d_ls s) <= RD.ls_strstart (RD.d_ls s);
  (** added 2026-10-20: the hash and window masks (an [insert_string]
      outside [[0, hash_size)] would put an unconstrained value in [prev]) *)
  mi_wmask : RC.dg_w_mask (RD.d_cfg s) = RC.dg_w_size (RD.d_cfg s) - 1;
  mi_hmask : 1 <= RC.dg_hash_size (RD.d_cfg s) /\ RC.dg_hash_mask (RD.d_cfg s) = RC.dg_hash_size (RD.d_cfg s) - 1 }.

(** deflate_fast: at the top of a trip no match is pending. *)
Definition ms_fast_inv (s : RD.DSt) : Prop :=
  RD.ls_matchlen (RD.d_ls s) < RC.MIN_MATCH /\ RD.ls_prevlen (RD.d_ls s) < RC.MIN_MATCH.

(** deflate_slow: at the top of a trip a pending match (found one trip
    earlier, at [strstart - 1]) is no longer than [lookahead + 1] (the slow
    clause of [IFuelDefl.fuel_deflate_slow]) and is live. *)
Definition ms_slow_inv (s : RD.DSt) : Prop :=
  (RD.ls_matchlen (RD.d_ls s) < RC.MIN_MATCH \/ RD.ls_matchlen (RD.d_ls s) <= RD.ls_lookahead (RD.d_ls s) + 1)
  /\ (RC.MIN_MATCH <= RD.ls_matchlen (RD.d_ls s) ->
      2 <= RD.ls_strstart (RD.d_ls s) - RD.ls_matchstart (RD.d_ls s) <= RC.dg_max_dist (RD.d_cfg s) + 1).

(** The trip's states as [df_body] / [ds_body] name them, from the post-fill
    state [p0] (verbatim lets, so [change] matches them). *)
Definition df_l1 (p0 : RD.DSt) : RD.LSt :=
  let g := RD.d_cfg p0 in
  let ph := if Z.leb RC.MIN_MATCH (RD.ls_lookahead (RD.d_ls p0))
            then RD.insert_string g (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)
            else (RD.NIL, RD.d_ls p0) in
  let hash_head := fst ph in
  let l0 := snd ph in
  if negb (Z.eqb hash_head RD.NIL) && (Z.leb (RD.ls_strstart l0 - hash_head) (RC.dg_max_dist g))
  then let r := RD.longest_match g l0 hash_head in
       RD.setL_matchstart (snd r) (RD.setL_matchlen (fst r) l0)
  else l0.

Definition ds_l2 (p0 : RD.DSt) : RD.LSt :=
  let g := RD.d_cfg p0 in
  let ph := if Z.leb RC.MIN_MATCH (RD.ls_lookahead (RD.d_ls p0))
            then RD.insert_string g (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)
            else (RD.NIL, RD.d_ls p0) in
  let hash_head := fst ph in
  let l0 := snd ph in
  let l1 := RD.setL_matchlen (RC.MIN_MATCH - 1)
              (RD.setL_prevmatch (RD.ls_matchstart l0) (RD.setL_prevlen (RD.ls_matchlen l0) l0)) in
  if negb (Z.eqb hash_head RD.NIL)
     && (Z.ltb (RD.ls_prevlen l1) (RC.dg_max_lazy_match g))
     && (Z.leb (RD.ls_strstart l1 - hash_head) (RC.dg_max_dist g)) then
    let r := RD.longest_match g l1 hash_head in
    let l1a := RD.setL_matchstart (snd r) (RD.setL_matchlen (fst r) l1) in
    if (Z.leb (RD.ls_matchlen l1a) 5)
       && ((Z.eqb (RC.dg_strategy g) RT.Z_FILTERED)
           || ((Z.eqb (RD.ls_matchlen l1a) RC.MIN_MATCH)
               && (Z.ltb RD.TOO_FAR (RD.ls_strstart l1a - RD.ls_matchstart l1a))))
    then RD.setL_matchlen (RC.MIN_MATCH - 1) l1a else l1a
  else l1.

(** The state a trip leaves, whatever it returns. *)
Definition step_state (r : RD.DsStep) : RD.DSt :=
  match r with RD.DsCont s' => s' | RD.DsRet _ s' => s' | RD.DsBreak s' => s' end.
