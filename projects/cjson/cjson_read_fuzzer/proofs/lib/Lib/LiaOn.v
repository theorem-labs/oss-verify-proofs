(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaTuning.
Module SepM.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaTuning.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Definition Sep (P : Prop) : Prop := P.

Lemma sep_bigM : forall a b c d : Z, a <= b \/ c <= d -> a - b <= 73786976294838206464 -> c - d <= 73786976294838206464 ->
  exists s : Z, 0 <= s <= 1 /\ a <= b + s * 73786976294838206464 /\ c <= d + (1 - s) * 73786976294838206464.
Proof. intros a b c d [H|H] H0 H1; [exists 0| exists 1]; lia. Qed.

(* [comment removed for export] *)
Ltac sepM_lia := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.

Ltac sepM1 H :=
  lazymatch type of H with
  | ?a <= ?b \/ ?c <= ?d =>
      let s := fresh "sMsel" in let SM := fresh "SMf" in
      destruct (sep_bigM a b c d H ltac:(sepM_lia) ltac:(sepM_lia)) as (s & SM);
      change (a <= b \/ c <= d) with (Sep (a <= b \/ c <= d)) in H
  end.

Ltac sepM := repeat match goal with H : ?a <= ?b \/ ?c <= ?d |- _ => sepM1 H end.

(* [comment removed for export] *)
Ltac sep_unhide := repeat match goal with H : Sep _ |- _ => unfold Sep in H end.
Ltac sep_hide H := lazymatch type of H with ?P => change (Sep P) in H end.
End SepM.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2.
Import SepM.

Module LiaOnL2.
Import Ltac2.
Ltac2 cut_tolerant (l : Ltac1.t) : unit :=
  let ids := match Ltac1.to_list l with Some x => x | None => [l] end in
  let ids := List.map_filter (fun x => Ltac1.to_ident x) ids in
  Control.enter (fun () =>
    let hs := List.map (fun h => let (id, _, _) := h in id) (Control.hyps ()) in
    let present := List.filter (fun id => List.exist (Ident.equal id) hs) ids in
    Std.keep present).
End LiaOnL2.

(* [comment removed for export] *)
Ltac cut_unhide := repeat match goal with H : Sep _ |- _ => unfold Sep in H end.
Tactic Notation "cut_to" ne_ident_list(l) := let f := ltac2:(l |- LiaOnL2.cut_tolerant l) in f l; cut_unhide.
Ltac cut_all := let x := fresh "cutI" in pose proof I as x; clear - x; clear x.

Tactic Notation "lia_on" ne_ident_list(l) := let f := ltac2:(l |- LiaOnL2.cut_tolerant l) in first [ solve [ f l; cut_unhide; lia ] | lia ].
Tactic Notation "nia_on" ne_ident_list(l) := let f := ltac2:(l |- LiaOnL2.cut_tolerant l) in first [ solve [ f l; cut_unhide; nia ] | nia ].
Tactic Notation "cut_on" "[" ne_ident_list(l) "]" tactic3(tac) := let f := ltac2:(l |- LiaOnL2.cut_tolerant l) in first [ solve [ f l; cut_unhide; tac ] | tac ].
Ltac lia_on0 := first [ solve [ cut_all; lia ] | lia ].
Tactic Notation "cut_on0" tactic3(tac) := first [ solve [ cut_all; tac ] | tac ].

(* [comment removed for export] *)
Ltac no_H3 := idtac; lazymatch goal with H3 : (_ < 100 \/ _)%Z |- _ => fail | _ => lia end.
Goal forall a b c : Z, (a < b)%Z -> (b < c)%Z -> (c < 100 \/ c > 3)%Z -> (a < c)%Z.
Proof. intros a b c H1 H2 H3. Fail no_H3. cut_on [H1 H2] no_H3. Qed.
Goal forall a b c : Z, (a < b)%Z -> (b < c)%Z -> (c < 100 \/ c > 3)%Z -> (a < c)%Z.
Proof. intros a b c H1 H2 H3. lia_on H1 H2. Qed.
Goal forall a b c : Z, (a < b)%Z -> (b < c)%Z -> (c < 100 \/ c > 3)%Z -> (a < c /\ a < b)%Z.
Proof. intros a b c H1 H2 H3. split; cut_on [H1 Hmissing H2] no_H3. Qed.
Goal forall a b c : Z, (a < b)%Z -> (b < c)%Z -> (c < 100 \/ c > 3)%Z -> (a < c /\ a < b)%Z.
Proof. intros a b c H1 H2 H3. split; lia_on H1 Hmissing H2. Qed.
Goal forall a b c : Z, (a < b)%Z -> (b < c)%Z -> (c < 100 \/ c > 3)%Z -> (a < c)%Z.
Proof. intros a b c H1 H2 H3. cut_on [H1 H2] nia. Qed.
Goal forall a b c : Z, (a < b)%Z -> (b < c)%Z -> (c < 100 \/ c > 3)%Z -> (a < c)%Z.
Proof. intros a b c H1 H2 H3. first [ (cut_to H1; lia) | (cut_to H1 H2 Hx; lia) ]. Qed.
Goal forall a b c : Z, (a < b)%Z -> (b < c)%Z -> (c < 100 \/ c > 3)%Z -> (a < a + 1)%Z.
Proof. intros a b c H1 H2 H3. cut_on0 no_H3. Qed.
Goal forall a b c : Z, (a < b)%Z -> (b <= c \/ c + 5 <= a)%Z -> (c < 100 \/ c > 3)%Z -> (c < b -> c + 5 <= a)%Z.
Proof. intros a b c H1 H2 H3 H4. sepM. cut_on [H1 H2 H4] no_H3. Qed.
