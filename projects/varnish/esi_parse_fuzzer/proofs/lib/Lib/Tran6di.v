(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Zify PreOmega.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import LiaTwx2 MState Mem Cells Frame Step Arr Tac Bytes.
#[global] Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition regn (key B S : Z) : Prop := True.
Definition regn_lit (B S : Z) : Prop := True.
Definition rdj (B S lo hi : Z) : Prop := B + S <= lo \/ hi <= B.
Definition rdj_no (B S lo hi : Z) : Prop := True.
Definition tf_reg_found (B S : Z) : Prop := True.
Definition tf_cached : Prop := True.      (* [comment removed for export] *)
Lemma rdj_use : forall B S lo hi a n, rdj B S lo hi -> B <= a -> a + n <= B + S -> a + n <= lo \/ hi <= a.
Proof. unfold rdj. intros B S lo hi a n [H|H] H1 H2; [left|right]; lia. Qed.

(* [comment removed for export] *)
Ltac2 tf_clear_props () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Bool.and (LiaTwx2.zt_is_local id) (LiaTwx2.zt_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac tf_clear_props := ltac2:(Control.enter tf_clear_props).
(* [comment removed for export] *)
Ltac tf_lia :=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Ltac tf_cfree_lia := solve [ tf_clear_props; Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac tf_thin := idtac.
Ltac tf_slow := slia.           (* [comment removed for export] *)
Ltac tf_slow_all := slia.
Ltac tf_apart B lo := fail.     (* [comment removed for export] *)
Ltac tf_skip a := fail.
Ltac tf_sizes := simpl_sizes.
Ltac tf_same := first [ tf_cfree_lia | tf_lia | tf_thin; tf_slow ].   (* [comment removed for export] *)
Ltac tf_regions := idtac.       (* [comment removed for export] *)
Ltac tf_dbg_rd B S lo hi := idtac.

(* [comment removed for export] *)
Ltac tf_base t := lazymatch t with ?x + _ => tf_base x | ?x - _ => tf_base x | _ => t end.
(* [comment removed for export] *)
Ltac tf_closed t := lazymatch t with ?x + ?y => tf_closed x; tf_closed y | ?x - ?y => tf_closed x; tf_closed y | ?x * ?y => tf_closed x; tf_closed y | Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Ltac tf_same_base t1 t2 :=
  let b1 := tf_base t1 in let b2 := tf_base t2 in
  first [ constr_eq b1 b2 | (tf_closed b1; tf_closed b2) ].
(* [comment removed for export] *)
Ltac tf_rd_solve B lo := unfold rdj; first [ solve [ tf_apart B lo; first [ tf_cfree_lia | tf_lia ] ] | tf_lia ].
(* [comment removed for export] *)
Ltac tf_region_used segs m key :=
  match goal with
  | H : rw_cells segs m ?a _ |- _ => lazymatch a with context [key] => idtac end
  | H : ro_cells segs m ?a _ |- _ => lazymatch a with context [key] => idtac end
  | H : bytes_at segs m ?a _ |- _ => lazymatch a with context [key] => idtac end
  | H : stk segs m ?a _ |- _ => lazymatch a with context [key] => idtac end
  end.
Ltac tf_lit_used segs m :=
  match goal with
  | H : rw_cells segs m ?a _ |- _ => tf_closed a
  | H : ro_cells segs m ?a _ |- _ => tf_closed a
  | H : bytes_at segs m ?a _ |- _ => tf_closed a
  end.
Ltac tf_build_one segs m lo hi :=
  repeat match goal with
  | R : regn ?key ?B ?S |- _ =>
      lazymatch goal with
      | _ : rdj B S lo hi |- _ => fail
      | _ : rdj_no B S lo hi |- _ => fail
      | _ => idtac end;
      tf_region_used segs m key;
      tf_dbg_rd B S lo hi;
      first [ assert (rdj B S lo hi) by (tf_rd_solve B lo) | pose proof (I : rdj_no B S lo hi) ]
  | R : regn_lit ?B ?S |- _ =>
      lazymatch goal with
      | _ : rdj B S lo hi |- _ => fail
      | _ : rdj_no B S lo hi |- _ => fail
      | _ => idtac end;
      tf_lit_used segs m;
      first [ assert (rdj B S lo hi) by (tf_rd_solve B lo) | pose proof (I : rdj_no B S lo hi) ]
  end.
Ltac tf_build segs m W :=
  lazymatch W with
  | (?lo, ?hi) :: ?W' => tf_build_one segs m lo hi; tf_build segs m W'
  | _ => idtac
  end.
Ltac tf_cleanup :=
  repeat match goal with
  | H : rdj _ _ _ _ |- _ => clear H | H : rdj_no _ _ _ _ |- _ => clear H
  | H : regn _ _ _ |- _ => clear H | H : regn_lit _ _ |- _ => clear H | H : tf_cached |- _ => clear H end.

Lemma tf_notin_mono : forall a lo hi lo' hi', ~ (lo' <= a < hi') -> lo' <= lo -> hi <= hi' -> ~ (lo <= a < hi).
Proof. intros; lia. Qed.

(* [comment removed for export] *)
Ltac tf_direct1 :=
  lazymatch goal with
  | |- True => exact I
  | |- ?a + ?n <= ?lo \/ ?hi <= ?a =>
      first [ tf_cfree_lia
            | let B := tf_base a in solve [ tf_apart B lo; first [ tf_cfree_lia | tf_lia ] ]
            | tf_lia
            | tf_thin; tf_slow ]
  | |- _ => tf_thin; tf_slow
  end.
Ltac tf_direct := repeat (lazymatch goal with |- _ /\ _ => split end); tf_direct1.

(* [comment removed for export] *)
Ltac tf_incl1 :=
  lazymatch goal with
  | |- True => exact I
  | |- ~ (?lo <= ?x < ?hi) =>
      first [ assumption
            | multimatch goal with H : ~ (?lo' <= x < ?hi') |- _ =>
                tf_same_base lo lo'; apply (tf_notin_mono x lo hi lo' hi' H); first [ tf_cfree_lia | tf_lia ] end
            | tf_slow_all ]
  | |- _ => tf_slow_all
  end.
Ltac tf_incl :=
  repeat match goal with H : (~ (_ <= _ < _)) /\ _ |- _ => let H1 := fresh H in destruct H as [H1 H] end;
  repeat (lazymatch goal with |- _ /\ _ => split end); tf_incl1.

(* [comment removed for export] *)
Ltac tf_conj1 B S a n I1 I2 :=
  lazymatch goal with
  | |- True => exact I
  | |- a + n <= ?lo \/ ?hi <= a =>
      first [ match goal with RD : rdj B S lo hi |- _ => exact (rdj_use B S lo hi a n RD I1 I2) end
            | lazymatch goal with
              | _ : rdj_no B S lo hi |- _ => tf_same
              | _ => first [ tf_cfree_lia | tf_thin; tf_slow ]
              end ]
  | |- _ => tf_thin; tf_slow
  end.
Ltac tf_conjs B S a n I1 I2 :=
  lazymatch goal with
  | |- _ /\ _ => split; [ tf_conj1 B S a n I1 I2 | tf_conjs B S a n I1 I2 ]
  | |- _ => tf_conj1 B S a n I1 I2
  end.
Ltac tf_is_lit a := tf_closed a.

(* [comment removed for export] *)
Ltac tf_with_region B S a n :=
  let I1 := fresh "INS" in let I2 := fresh "INS" in
  assert (I1 : B <= a) by (first [ tf_cfree_lia | tf_lia ]);
  assert (I2 : a + n <= B + S) by (first [ tf_cfree_lia | tf_lia ]);
  pose proof (I : tf_reg_found B S).
Ltac tf_region_find a n :=
  tryif tf_skip a then fail else
  match goal with
  | R : regn ?key ?B ?S |- _ => lazymatch a with context [key] => idtac end; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
(* [comment removed for export] *)
Ltac tf_side :=
  lazymatch goal with
  | |- disjoint_from ?W ?a ?n =>
      (let E := fresh "Esz" in eassert (E : n = _) by (tf_sizes; reflexivity); try rewrite E; clear E);
      cbn [disjoint_from];
      lazymatch goal with
      | _ : tf_cached |- (?a' + ?n' <= _ \/ _ <= _) /\ _ =>
          tryif tf_region_find a' n'
          then (lazymatch goal with F : tf_reg_found ?B ?S |- _ =>
                  lazymatch goal with I1 : B <= a', I2 : a' + n' <= B + S |- _ => tf_conjs B S a' n' I1 I2 end end)
          else (tf_thin; tf_slow_all)
      | |- (_ + _ <= _ \/ _ <= _) /\ _ => tf_direct
      | |- _ => tf_thin; tf_slow_all
      end
  end.

(* [comment removed for export] *)
Definition tf_seen (P : Prop) : Prop := P.
Definition tf_count (n : nat) : Prop := True.
Ltac tf_count_cells segs m :=
  pose proof (I : tf_count 0);
  repeat match goal with
  | H : rw_cells segs m _ _ |- _ => let T := type of H in change T with (tf_seen T) in H; tf_bump
  | H : ro_cells segs m _ _ |- _ => let T := type of H in change T with (tf_seen T) in H; tf_bump
  | H : bytes_at segs m _ _ |- _ => let T := type of H in change T with (tf_seen T) in H; tf_bump
  end;
  repeat match goal with H : tf_seen ?T |- _ => change (tf_seen T) with T in H end
with tf_bump := lazymatch goal with C : tf_count ?n |- _ => clear C; pose proof (I : tf_count (S n)) end.
Ltac tf_threshold := constr:(16%nat).
Ltac tf_maybe_cache segs m W :=
  tf_count_cells segs m;
  lazymatch goal with C : tf_count ?n |- _ =>
    clear C;
    let t := tf_threshold in
    let big := eval cbv in (Nat.leb t n) in
    lazymatch big with
    | true => tf_regions; tf_build segs m W; pose proof (I : tf_cached)
    | false => idtac
    end end.
(* [comment removed for export] *)
Ltac tf_transport segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : rw_cells segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  | H : u8arr segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  | H : bytes_at segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  end;
  tf_maybe_cache segs m W;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | tf_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | tf_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | tf_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | tf_side ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; tf_incl | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end;
  tf_cleanup.

(* [comment removed for export] *)
Ltac tf_open segs MU := lazymatch type of MU with munch ?W ?m _ => tf_regions; tf_build segs m W; pose proof (I : tf_cached) end.
Ltac tf_close := tf_cleanup.
Ltac tf_xfer H M WMH :=
  lazymatch type of M with munch ?W ?mi ?mc =>
  lazymatch type of H with
  | ro_cells ?segs _ ?A ?cs => apply (ro_cells_transport segs W mi mc A cs) in H; [| exact M| tf_side]
  | bytes_at ?segs _ ?A ?bs => apply (bytes_at_transport segs W mi mc A bs) in H; [| exact M| tf_side]
  | rw_cells ?segs _ ?A ?cs => apply (rw_cells_transport segs W mi mc A cs) in H; [| exact M| exact WMH| tf_side]
  end end.
