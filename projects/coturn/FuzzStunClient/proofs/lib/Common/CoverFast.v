(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StreamSim WsegFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Cover.
Variable P : Segment -> bool.

(* [comment removed for export] *)
Definition cover1 (seg : Segment) (w : Z * Z) : bool * list (Z * Z) :=
  let base := Z.of_N (seg_base seg) in
  let top := base + Z.of_N (seg_size seg) in
  let ilo := Z.max (fst w) base in
  let ihi := Z.min (snd w) top in
  if Z.ltb ilo ihi then
    ((P seg && bytes_ok (seg_bytes seg) (Z.to_N (ilo - base)) (Z.to_nat (ihi - ilo)))%bool,
     (if Z.ltb (fst w) ilo then [(fst w, ilo)] else []) ++ (if Z.ltb ihi (snd w) then [(ihi, snd w)] else []))
  else (true, [w]).

Fixpoint cover_ws (seg : Segment) (ws : list (Z * Z)) : bool * list (Z * Z) :=
  match ws with
  | [] => (true, [])
  | w :: r => let (o1, l1) := cover1 seg w in let (o2, l2) := cover_ws seg r in ((o1 && o2)%bool, l1 ++ l2)
  end.

Fixpoint cover (segs : list Segment) (ws : list (Z * Z)) : bool :=
  match segs with
  | [] => forallb (fun w : Z * Z => Z.leb (snd w) (fst w)) ws
  | seg :: rest => let (ok, out) := cover_ws seg ws in (ok && cover rest out)%bool
  end.

Definition inside (seg : Segment) (x : Z) : Prop :=
  Z.of_N (seg_base seg) <= x < Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Definition byte_def (seg : Segment) (x : Z) : Prop :=
  exists b, segment_byte_at (seg_bytes seg) (Z.to_N (x - Z.of_N (seg_base seg))) = Some b.

Lemma cover1_spec : forall seg w ok out, cover1 seg w = (ok, out) -> ok = true ->
  forall x, fst w <= x < snd w ->
    (inside seg x /\ P seg = true /\ byte_def seg x)
    \/ (~ inside seg x /\ exists w', In w' out /\ fst w' <= x < snd w').
Proof.
  intros seg [lo hi] ok out H Hok x Hx. unfold cover1 in H. cbn [fst snd] in *. cbv zeta in H.
  set (base := Z.of_N (seg_base seg)) in *. set (top := base + Z.of_N (seg_size seg)) in *.
  destruct (Z.ltb (Z.max lo base) (Z.min hi top)) eqn:Hi.
  - apply Z.ltb_lt in Hi. injection H as <- <-. apply andb_prop in Hok. destruct Hok as [HP Hb].
    destruct (Z_lt_ge_dec x (Z.max lo base)) as [Hl|Hl].
    + right. split; [unfold inside; fold base; lia|].
      exists (lo, Z.max lo base). split; [|cbn [fst snd]; lia].
      apply in_or_app. left. destruct (Z.ltb lo (Z.max lo base)) eqn:E; [left; reflexivity|apply Z.ltb_ge in E; lia].
    + destruct (Z_lt_ge_dec x (Z.min hi top)) as [Hh|Hh].
      * left. split; [unfold inside; fold base; fold top; lia|]. split; [exact HP|].
        destruct (bytes_ok_sound _ _ _ Hb (Z.to_nat (x - Z.max lo base)) ltac:(lia)) as [b Hbb].
        exists b. rewrite <- Hbb. f_equal. fold base. lia.
      * right. split; [unfold inside; fold base; fold top; lia|].
        exists (Z.min hi top, hi). split; [|cbn [fst snd]; lia].
        apply in_or_app. right. destruct (Z.ltb (Z.min hi top) hi) eqn:E; [left; reflexivity|apply Z.ltb_ge in E; lia].
  - apply Z.ltb_ge in Hi. injection H as <- <-. right. split; [unfold inside; fold base; fold top; lia|].
    exists (lo, hi). split; [left; reflexivity|cbn [fst snd]; lia].
Qed.

Lemma cover_ws_spec : forall seg ws ok out, cover_ws seg ws = (ok, out) -> ok = true ->
  forall w x, In w ws -> fst w <= x < snd w ->
    (inside seg x /\ P seg = true /\ byte_def seg x)
    \/ (~ inside seg x /\ exists w', In w' out /\ fst w' <= x < snd w').
Proof.
  intros seg. induction ws as [|w0 r IH]; intros ok out H Hok w x Hin Hx; [destruct Hin|].
  cbn [cover_ws] in H. destruct (cover1 seg w0) as [o1 l1] eqn:E1. destruct (cover_ws seg r) as [o2 l2] eqn:E2.
  injection H as <- <-. apply andb_prop in Hok. destruct Hok as [Ho1 Ho2].
  destruct Hin as [<-|Hin].
  - destruct (cover1_spec _ _ _ _ E1 Ho1 x Hx) as [A|[A [w' [B C]]]]; [left; exact A|].
    right. split; [exact A|]. exists w'. split; [apply in_or_app; left; exact B|exact C].
  - destruct (IH _ _ eq_refl Ho2 w x Hin Hx) as [A|[A [w' [B C]]]]; [left; exact A|].
    right. split; [exact A|]. exists w'. split; [apply in_or_app; right; exact B|exact C].
Qed.

Theorem cover_sound : forall segs ws, cover segs ws = true ->
  forall w x, In w ws -> fst w <= x < snd w ->
  exists seg, find_segment segs x 1 = Some seg /\ P seg = true /\ byte_def seg x.
Proof.
  induction segs as [|seg rest IH]; intros ws H w x Hin Hx; cbn [cover] in H.
  - pose proof (proj1 (forallb_forall _ _) H w Hin) as E. apply Z.leb_le in E. lia.
  - destruct (cover_ws seg ws) as [ok out] eqn:E. apply andb_prop in H. destruct H as [Hok Hrest].
    cbn [find_segment]. cbv zeta.
    destruct (cover_ws_spec _ _ _ _ E Hok w x Hin Hx) as [[Hi [HP Hb]]|[Hni [w' [Hin' Hx']]]].
    + unfold inside in Hi.
      assert (T : (Z.leb (Z.of_N (seg_base seg)) x && Z.leb (x + 1) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool = true)
        by (apply andb_true_intro; split; apply Z.leb_le; lia).
      rewrite T. exists seg. split; [reflexivity|]. split; [exact HP|exact Hb].
    + unfold inside in Hni.
      assert (F : (Z.leb (Z.of_N (seg_base seg)) x && Z.leb (x + 1) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool = false).
      { destruct (Z.leb (Z.of_N (seg_base seg)) x) eqn:A; [|reflexivity].
        destruct (Z.leb (x + 1) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))) eqn:B; [|reflexivity].
        apply Z.leb_le in A, B. exfalso. apply Hni. lia. }
      rewrite F. exact (IH out Hrest w' x Hin' Hx').
Qed.
End Cover.

(* [comment removed for export] *)
Definition range_cover (P : Segment -> bool) (segs : list Segment) (lo : Z) (n : nat) : bool :=
  (Z.leb 0 lo && Z.leb (lo + Z.of_nat n) (2 ^ 64) && cover P segs [(lo, lo + Z.of_nat n)])%bool.

Lemma range_cover_sound : forall P segs lo n, range_cover P segs lo n = true ->
  forall x, lo <= x < lo + Z.of_nat n ->
  0 <= x < 2 ^ 64 /\ exists seg, find_segment segs x 1 = Some seg /\ P seg = true /\ byte_def seg x.
Proof.
  intros P segs lo n H x Hx. unfold range_cover in H.
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2.
  split; [lia|]. exact (cover_sound P segs _ H3 (lo, lo + Z.of_nat n) x ltac:(left; reflexivity) Hx).
Qed.
