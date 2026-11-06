(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module HeapOp.

Definition iv : Type := (Z * Z)%type.
Definition in_iv (v : iv) (a : Z) : Prop := fst v <= a < fst v + snd v.
Definition in_ivs (l : list iv) (a : Z) : Prop := Exists (fun v => in_iv v a) l.

Lemma in_ivs_cons : forall v l a, in_ivs (v :: l) a <-> in_iv v a \/ in_ivs l a.
Proof. intros v l a. unfold in_ivs. rewrite Exists_cons. tauto. Qed.
Lemma in_ivs_app : forall l1 l2 a, in_ivs (l1 ++ l2) a <-> in_ivs l1 a \/ in_ivs l2 a.
Proof. intros. unfold in_ivs. rewrite Exists_app. tauto. Qed.
Lemma in_ivs_In : forall l a, in_ivs l a <-> exists v, In v l /\ in_iv v a.
Proof. intros. unfold in_ivs. rewrite Exists_exists. tauto. Qed.

Fixpoint ins (v : iv) (l : list iv) : list iv :=
  match l with
  | [] => [v]
  | w :: l' => if fst v <=? fst w then v :: l else w :: ins v l'
  end.
Fixpoint isort (l : list iv) : list iv :=
  match l with [] => [] | v :: l' => ins v (isort l') end.

Lemma ins_In : forall v l x, In x (ins v l) <-> v = x \/ In x l.
Proof.
  induction l as [|w l IH]; intros x; cbn.
  - tauto.
  - destruct (fst v <=? fst w); cbn; [tauto|]. rewrite IH. tauto.
Qed.
Lemma isort_In : forall l x, In x (isort l) <-> In x l.
Proof. induction l as [|v l IH]; intros x; cbn; [tauto|]. rewrite ins_In, IH. tauto. Qed.

Definition starts_sorted (l : list iv) : Prop := Sorted.StronglySorted (fun a b => fst a <= fst b) l.

Lemma ins_sorted : forall v l, starts_sorted l -> starts_sorted (ins v l).
Proof.
  induction l as [|w l IH]; intros S; cbn.
  - constructor; constructor.
  - inversion S as [|w' l' Sl Fw]; subst.
    destruct (Z.leb_spec (fst v) (fst w)).
    + constructor; [exact S|]. constructor; [cbn beta; lia|]. eapply Forall_impl; [|exact Fw]. cbn beta. intros; lia.
    + constructor; [apply IH; exact Sl|]. apply Forall_forall. intros x Hx. apply ins_In in Hx. destruct Hx as [<-|Hx]; [cbn beta; lia|].
      exact (proj1 (Forall_forall _ _) Fw x Hx).
Qed.
Lemma isort_sorted : forall l, starts_sorted (isort l).
Proof. induction l; cbn; [constructor| apply ins_sorted; assumption]. Qed.

Fixpoint gaps (top cur : Z) (l : list iv) : list iv :=
  match l with
  | [] => [(cur, top - cur)]
  | v :: l' => (if cur <? fst v then [(cur, Z.min (fst v) top - cur)] else []) ++ gaps top (Z.max cur (fst v + snd v)) l'
  end.

Lemma gaps_spec : forall top l cur a, starts_sorted l ->
  (in_ivs (gaps top cur l) a <-> (cur <= a < top /\ ~ in_ivs l a)).
Proof.
  intros top l. induction l as [|v l IH]; intros cur a S; cbn [gaps].
  - unfold in_ivs at 1. rewrite Exists_cons, Exists_nil. unfold in_iv; cbn [fst snd].
    split; [intros [H|[]]| intros [H _]; left]; try split; try lia. intros X. inversion X.
  - inversion S as [|v' l' Sl Fv]; subst.
    rewrite in_ivs_app, (IH _ a Sl), in_ivs_cons.
    assert (LATER : in_ivs l a -> fst v <= a).
    { intros H. apply in_ivs_In in H as (w & Hw & Ha). pose proof (proj1 (Forall_forall _ _) Fv w Hw) as LE. cbn beta in LE.
      unfold in_iv in Ha. lia. }
    assert (HD : in_ivs (if cur <? fst v then [(cur, Z.min (fst v) top - cur)] else []) a <-> cur <= a < Z.min (fst v) top).
    { destruct (Z.ltb_spec cur (fst v)).
      - unfold in_ivs. rewrite Exists_cons, Exists_nil. unfold in_iv. cbn [fst snd].
        split; [intros [H'|[]]; lia| intros; left; lia].
      - unfold in_ivs. rewrite Exists_nil. split; [intros []| intros; lia]. }
    rewrite HD. unfold in_iv. split.
    + intros [H|[H1 H2]].
      * split; [lia|]. intros [X|X]; [lia|]. apply LATER in X. lia.
      * split; [lia|]. intros [X|X]; [lia|]. exact (H2 X).
    + intros [H N]. destruct (Z.lt_ge_cases a (fst v)); [left; lia| right].
      split; [|intros X; apply N; right; exact X].
      assert (~ (fst v <= a < fst v + snd v)) by (intros X; apply N; left; exact X). lia.
Qed.

Definition complement (l : list iv) : list iv := gaps two64 0 (isort l).

Lemma complement_spec : forall l a, in_ivs (complement l) a <-> (0 <= a < two64 /\ ~ in_ivs l a).
Proof.
  intros l a. unfold complement. rewrite (gaps_spec two64 (isort l) 0 a (isort_sorted l)).
  assert (E : in_ivs (isort l) a <-> in_ivs l a).
  { rewrite !in_ivs_In. split; intros (v & Hv & Ha); exists v; split; try exact Ha.
    - exact (proj1 (isort_In l v) Hv).
    - exact (proj2 (isort_In l v) Hv). }
  rewrite E. tauto.
Qed.

Definition K_STACK : Z := 0.
Definition K_BLOCK : Z := 1.
Definition K_SUB   : Z := 2.

Record window := Win { w_lo : Z; w_len : Z; w_kind : Z }.
Definition w_iv (w : window) : iv := (w_lo w, w_len w).
Definition in_ws (ws : list window) (a : Z) : Prop := in_ivs (map w_iv ws) a.

Definition heap_ws (ws : list window) : list window := List.filter (fun w => negb (w_kind w =? K_STACK)) ws.

Definition K_GHOST : Z := 7.
Definition AW_BAND : Z := 2 ^ 48.
Definition aw_tied (w : window) : Prop := (w_kind w = K_STACK /\ w_lo w < AW_BAND) \/ K_GHOST <= w_kind w.

Definition C24_LO : Z := 5881.
Definition C24_HI : Z := 7936.
Definition c24 (n : Z) : Prop := C24_LO <= n <= C24_HI.

Fixpoint decode_windows (n : nat) (l : list word) : option (list window * list word) :=
  match n with
  | O => Some ([], l)
  | S n' => match l with
            | a :: b :: c :: r =>
                match decode_windows n' r with
                | Some (ws, rest) => Some (Win (bv_unsigned a) (bv_unsigned b) (bv_unsigned c) :: ws, rest)
                | None => None
                end
            | _ => None
            end
  end.

Definition decode (dargs : list word) : option (Z * word * list window * list word) :=
  match dargs with
  | md :: aw :: nw :: r =>
      match decode_windows (Z.to_nat (bv_unsigned nw)) r with
      | Some (ws, ca) => Some (bv_unsigned md, aw, ws, ca)
      | None => None
      end
  | _ => None
  end.

Definition blocks := list iv.
Definition iv_eq_dec (x y : iv) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition in_user (LB : blocks) (a : Z) : Prop := in_ivs LB a.

Definition ghost_apart (ws : list window) : Prop :=
  forall w w', In w ws -> In w' ws -> K_GHOST <= w_kind w -> w_kind w' = K_BLOCK -> forall a, in_iv (w_iv w) a -> ~ in_iv (w_iv w') a.

Definition heap_kind (w : window) : Prop := K_BLOCK <= w_kind w < K_GHOST.
Definition wins_keep (LB : blocks) (ws ws' : list window) : Prop :=
  (forall w, aw_tied w -> (In w ws' <-> In w ws)) /\
  (forall w, In w ws -> ~ In w ws' -> heap_kind w -> 0 < w_len w ->
             exists o, In o LB /\ in_iv o (w_lo w) /\
                       (~ c24 (snd o) \/ exists w', In w' ws' /\ heap_kind w' /\ 0 < w_len w' /\ in_iv o (w_lo w'))) /\
  (forall w', In w' ws' -> ~ In w' ws -> w_kind w' = K_BLOCK ->
              forall w, In w ws' -> K_GHOST <= w_kind w -> forall a, in_iv (w_iv w) a -> ~ in_iv (w_iv w') a).

Lemma wins_keep_refl : forall LB ws, wins_keep LB ws ws.
Proof. intros LB ws. split; [tauto|]. split; [intros w H N; contradiction| intros w' H N; contradiction]. Qed.

Lemma wins_keep_same : forall LB ws ws', (forall w, In w ws' <-> In w ws) -> wins_keep LB ws ws'.
Proof.
  intros LB ws ws' H. split; [intros w _; exact (H w)|]. split.
  - intros w H1 N. exfalso. apply N. apply H. exact H1.
  - intros w' H1 N. exfalso. apply N. apply H. exact H1.
Qed.

Lemma wins_keep_intro : forall LB ws ws',
  (forall w, In w ws' -> In w ws \/ (~ aw_tied w /\ (w_kind w = K_BLOCK ->
       forall g, In g ws' -> K_GHOST <= w_kind g -> forall a, in_iv (w_iv g) a -> ~ in_iv (w_iv w) a))) ->
  (forall w, In w ws -> In w ws' \/ (~ aw_tied w /\ (heap_kind w -> 0 < w_len w ->
       exists o, In o LB /\ in_iv o (w_lo w) /\
                 (~ c24 (snd o) \/ exists w', In w' ws' /\ heap_kind w' /\ 0 < w_len w' /\ in_iv o (w_lo w'))))) ->
  wins_keep LB ws ws'.
Proof.
  intros LB ws ws' NEW OLD. split; [| split].
  - intros w T. split; intros H.
    + destruct (NEW w H) as [H0|[N _]]; [exact H0| exfalso; exact (N T)].
    + destruct (OLD w H) as [H0|[N _]]; [exact H0| exfalso; exact (N T)].
  - intros w H N K P. destruct (OLD w H) as [H0|[_ EV]]; [exfalso; exact (N H0)| exact (EV K P)].
  - intros w' H N K g Hg KG a Ha. destruct (NEW w' H) as [H0|[_ AP]]; [exfalso; exact (N H0)| exact (AP K g Hg KG a Ha)].
Qed.

Lemma wins_keep_app : forall LB ws new, (forall w, In w new -> ~ aw_tied w /\ w_kind w <> K_BLOCK) -> wins_keep LB ws (ws ++ new).
Proof.
  intros LB ws new H. apply wins_keep_intro.
  - intros w Hw. apply in_app_or in Hw as [Hw|Hw]; [left; exact Hw| right]. destruct (H w Hw) as [T NB]. split; [exact T|]. intros K. exfalso. exact (NB K).
  - intros w Hw. left. apply in_or_app. left. exact Hw.
Qed.

Section Worlds.
Variable segs : list Segment.
Variable IMGX : list iv.

Record alloc_world := AW {

  aw_holds : word -> blocks -> list window -> (word -> option byte) -> Model -> Prop;

  aw_dep : blocks -> (word -> option byte) -> Model -> Z -> Prop;
  aw_ceiling : Model -> Z;
  aw_frame : forall A LB ws m m' mo, aw_holds A LB ws m mo ->
      (forall a, 0 <= a < two64 -> aw_dep LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
      (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
      aw_holds A LB ws m' mo /\ (forall a, aw_dep LB m' mo a <-> aw_dep LB m mo a);

  aw_keep : forall A LB ws ws' m mo, aw_holds A LB ws m mo -> wins_keep LB ws ws' -> aw_holds A LB ws' m mo;

  aw_ghost_apart : forall A LB ws m mo, aw_holds A LB ws m mo -> ghost_apart ws;
  aw_dep_ok : forall A LB ws m mo a, aw_holds A LB ws m mo -> aw_dep LB m mo a ->
      0 <= a < aw_ceiling mo /\ ~ in_user LB a /\ ~ in_ivs IMGX a;
  aw_blocks_ok : forall A LB ws m mo b, aw_holds A LB ws m mo -> In b LB ->
      0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= aw_ceiling mo /\ aw_ceiling mo < two64 /\
      (forall a, in_iv b a -> ~ in_ivs IMGX a);

  aw_user_ok : forall A LB ws m mo b a, aw_holds A LB ws m mo -> In b LB -> in_iv b a ->
      m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None;

  aw_blocks_disj : forall A LB ws m mo b b' a, aw_holds A LB ws m mo -> In b LB -> In b' LB -> fst b <> fst b' ->
      in_iv b a -> ~ in_iv b' a;

  aw_ceiling_small : forall mo, aw_ceiling mo <= Mem.two62Z;

  aw_blocks_lo : forall A LB ws m mo b, aw_holds A LB ws m mo -> In b LB -> 4096 <= fst b
}.

Record client_world := CW {
  cw_holds : Z -> list word -> blocks -> list window -> (word -> option byte) -> Prop;

  cw_frame : forall md ca LB ws m m', cw_holds md ca LB ws m ->
      (forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
      cw_holds md ca LB ws m';

  cw_grow : forall md ca LB ws m b n, cw_holds md ca LB ws m ->
      (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
      cw_holds md ca ((b, n) :: LB) (ws ++ [Win b n K_BLOCK]) m;

  cw_free : forall md ca LB ws m b n ws', cw_holds md ca LB ws m -> In (Win b n K_BLOCK) ws ->
      (forall w, In w ws' <-> In w ws /\ w <> Win b n K_BLOCK) ->
      cw_holds md ca (remove iv_eq_dec (b, n) LB) ws' m
}.

Record client_ghost_laws (C : client_world) (shad : Z -> Z) (kt : Z) := CGL {
  cg_twin_grow : forall md ca LB ws m b0 n0 n, cw_holds C md ca LB ws m ->
      In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
      (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) ->
      cw_holds C md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n kt]) m;
  cg_ghost_grow : forall md ca LB ws m b n kd, cw_holds C md ca LB ws m -> K_GHOST <= kd -> kd <> kt ->
      (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
      cw_holds C md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m;
  cg_ghost_free : forall md ca LB ws m b n kd ws', cw_holds C md ca LB ws m -> K_GHOST <= kd -> In (Win b n kd) ws ->
      (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) ->
      cw_holds C md ca (remove iv_eq_dec (b, n) LB) ws' m
}.
End Worlds.

Section Table.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable A : alloc_world segs IMGX.
Variable C : client_world.

Definition OPID : int := 1%uint63.

Definition window_wf (LB : blocks) (ceil : Z) (w : window) : Prop :=
  0 <= w_lo w /\ 0 <= w_len w /\ w_lo w + w_len w <= two64 /\
  ((w_kind w = K_STACK /\ ceil <= w_lo w)
   \/ (w_kind w = K_BLOCK /\ In (w_iv w) LB)
   \/ (K_SUB <= w_kind w /\ exists b, In b LB /\ forall a, in_iv (w_iv w) a -> in_iv b a)).
Definition windows_wf (ws : list window) (LB : blocks) (ceil : Z) : Prop := Forall (window_wf LB ceil) ws.

Definition heap_holds (dargs : list word) (m : word -> option byte) (mo : Model) : Prop :=
  exists md aw ws ca LB, decode dargs = Some (md, aw, ws, ca) /\
    aw_holds segs IMGX A aw LB ws m mo /\ windows_wf ws LB (aw_ceiling segs IMGX A mo) /\ cw_holds C md ca LB ws m.

Definition to_lohi (v : iv) : Z * Z := (fst v, fst v + snd v).
Definition heap_fp (dargs : list word) : list (Z * Z) :=
  match decode dargs with
  | Some (_, _, ws, _) => map to_lohi (complement (IMGX ++ map w_iv ws))
  | None => []
  end.

Lemma fp_spec : forall dargs md aw ws ca a, decode dargs = Some (md, aw, ws, ca) ->
  (Exists (fun p => fst p <= a < snd p) (heap_fp dargs) <-> (0 <= a < two64 /\ ~ in_ivs IMGX a /\ ~ in_ws ws a)).
Proof.
  intros dargs md aw ws ca a D. unfold heap_fp. rewrite D.
  transitivity (in_ivs (complement (IMGX ++ map w_iv ws)) a).
  - unfold in_ivs. split.
    + intros H. apply Exists_exists in H as (p & Hp & Ha). apply in_map_iff in Hp as (v & <- & Hv).
      apply Exists_exists. exists v. split; [exact Hv|]. unfold in_iv, to_lohi in *. cbn [fst snd] in Ha. lia.
    + intros H. apply Exists_exists in H as (v & Hv & Ha). apply Exists_exists. exists (to_lohi v).
      split; [apply in_map; exact Hv|]. unfold in_iv, to_lohi in *. cbn [fst snd]. lia.
  - rewrite complement_spec. unfold in_ws. rewrite in_ivs_app. tauto.
Qed.

Lemma heap_frame : forall dargs m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (heap_fp dargs) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  heap_holds dargs m mo -> heap_holds dargs m' mo.
Proof.
  intros dargs m m' mo AG DM (md & aw & ws & ca & LB & D & HA & WF & HC).
  assert (INFP : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws ws a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
  { intros a Ha I W. apply AG; [exact Ha|]. apply (proj2 (fp_spec dargs md aw ws ca a D)). tauto. }

  assert (NOTW : forall a, 0 <= a < aw_ceiling segs IMGX A mo ->
            (forall w, In w ws -> w_kind w <> K_STACK -> ~ in_iv (w_iv w) a) -> ~ in_ws ws a).
  { intros a Ha H X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
    - unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
    - exact (H w Hw ltac:(rewrite K; discriminate) Hin).
    - exact (H w Hw ltac:(unfold K_SUB, K_STACK in *; lia) Hin). }
  exists md, aw, ws, ca, LB. split; [exact D|]. split; [| split; [exact WF|]].
  - unshelve refine (proj1 (aw_frame segs IMGX A aw LB ws m m' mo HA _ DM)).
    intros a Ha Hd. destruct (aw_dep_ok segs IMGX A aw LB ws m mo a HA Hd) as (C1 & NU & NI).
    apply INFP; [exact Ha| exact NI|]. apply NOTW; [exact C1|].
    intros w Hw NK Hin. pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
    + exact (NK K).
    + apply NU. unfold in_user. apply in_ivs_In. exists (w_iv w). auto.
    + apply NU. unfold in_user. apply in_ivs_In. exists b. auto.
  - apply (cw_frame C md ca LB ws m m' HC).
    intros a Ha U NH. apply in_ivs_In in U as (b & Hb & Hin).
    destruct (aw_blocks_ok segs IMGX A aw LB ws m mo b HA Hb) as (B1 & B2 & B3 & B4 & B5).
    apply INFP; [exact Ha| exact (B5 a Hin)|]. apply NOTW; [unfold in_iv in Hin; lia|].
    intros w Hw NK Hw'. apply NH. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [|exact Hw'].
    apply in_map. apply filter_In. split; [exact Hw|]. destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity].
Qed.

Definition heap_optable : optable :=
  plain_optable (fun id dargs m mo => if PrimInt63.eqb id OPID then heap_holds dargs m mo else False)
          (fun id dargs => if PrimInt63.eqb id OPID then heap_fp dargs else [])
          (fun id args m m' model AG DM H =>
             match PrimInt63.eqb id OPID as b
               return ((forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (if b then heap_fp args else []) ->
                                   m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
                       (if b then heap_holds args m model else False) -> (if b then heap_holds args m' model else False))
             with
             | true => fun AG H => heap_frame args m m' model AG DM H
             | false => fun _ H => H
             end AG H).

End Table.

End HeapOp.
