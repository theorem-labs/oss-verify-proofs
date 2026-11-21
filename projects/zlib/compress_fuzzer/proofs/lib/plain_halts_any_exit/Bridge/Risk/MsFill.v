(** * Bridge.Risk.MsFill — RT's [fill_window] keeps the hash-chain and
    window invariants (group R).

    [fi g l]: the hash chains lie below [strstart] ([MsKit.chain_below]),
    [0 <= strstart], [0 <= lookahead], [strstart + lookahead <=
    window_size = 2 * w_size], [0 <= insert <= strstart].  One trip of
    fill_window's loop ([fw_step]) keeps it: a window slide moves
    [strstart], [match_start] and every chain entry down by [w_size]
    together; the read only appends bytes the window has room for; the
    re-hash ([fw_seed] / [fw_insert]) inserts positions below [strstart].
    [lookahead] never falls and [strstart - match_start],
    [match_length], [prev_length] are unchanged. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Chunk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require Import MsKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition fi (g : DeflGeom) (l : LSt) : Prop :=
  chain_below g l (ls_strstart l) /\ 0 <= ls_strstart l /\ 0 <= ls_lookahead l
  /\ ls_strstart l + ls_lookahead l <= ls_windowsize l /\ ls_windowsize l = 2 * dg_w_size g
  /\ 0 <= ls_insert l <= ls_strstart l.

(** What fill_window keeps (or moves in step). *)
Definition fw_same (l l' : LSt) : Prop :=
  ls_lookahead l <= ls_lookahead l' /\ ls_matchlen l' = ls_matchlen l /\ ls_prevlen l' = ls_prevlen l
  /\ ls_strstart l' - ls_matchstart l' = ls_strstart l - ls_matchstart l
  /\ ls_windowsize l' = ls_windowsize l.

Lemma fw_same_refl : forall l, fw_same l l.
Proof. intros l. unfold fw_same. repeat split; lia. Qed.

Lemma fw_same_trans : forall a b c, fw_same a b -> fw_same b c -> fw_same a c.
Proof. intros a b c (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold fw_same. repeat split; lia. Qed.

Ltac ls_red :=
  cbn [ls_window ls_prev ls_head ls_insh ls_blockstart ls_matchlen ls_prevmatch ls_matchavail ls_strstart
       ls_matchstart ls_lookahead ls_prevlen ls_insert ls_highwater ls_windowsize
       setL_window setL_prev setL_head setL_insh setL_blockstart setL_matchlen setL_prevmatch setL_matchavail
       setL_strstart setL_matchstart setL_lookahead setL_prevlen setL_insert setL_highwater setL_windowsize] in *.

(* ------------------------------------------------------------------------- *)
(* fw_insert / fw_seed                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma fw_insert_step : forall f g str l,
  fw_insert (S f) g str l
  = if Z.eqb (ls_insert l) 0 then l
    else let l4 := setL_insert (ls_insert (snd (insert_string g str l)) - 1) (snd (insert_string g str l)) in
         if Z.ltb (ls_lookahead l4 + ls_insert l4) MIN_MATCH then l4 else fw_insert f g (str + 1) l4.
Proof. reflexivity. Qed.

(** Everything [fw_insert] leaves alone. *)
Definition FV2 (l : LSt) :=
  (ls_window l, ls_blockstart l, ls_matchlen l, ls_prevmatch l, ls_matchavail l, ls_strstart l,
   ls_matchstart l, ls_lookahead l, ls_prevlen l, ls_highwater l, ls_windowsize l).

Lemma fw_insert_inv : forall n g str l, cfg_ok g ->
  chain_below g l (ls_strstart l) -> str + ls_insert l = ls_strstart l -> 0 <= ls_insert l -> 0 <= str ->
  ls_strstart l <= 65536 ->
  let l' := fw_insert n g str l in
  chain_below g l' (ls_strstart l') /\ 0 <= ls_insert l' <= ls_insert l /\ FV2 l' = FV2 l.
Proof.
  induction n as [|n IH]; intros g str l Hc Hch Hsi Hi0 Hs0 Hs64 l'; subst l'.
  { cbn [fw_insert]. split; [exact Hch|]. split; [lia | reflexivity]. }
  rewrite fw_insert_step. destruct (Z.eqb_spec (ls_insert l) 0) as [I0|I0];
    [split; [exact Hch|]; split; [lia | reflexivity]|].
  cbv zeta.
  destruct (insert_chain g str l (ls_strstart l) Hc Hch ltac:(lia)) as [Ch _].
  pose proof (LV_insert g str l) as EV.
  set (l3 := snd (insert_string g str l)) in *. clearbody l3.
  unfold LV in EV. repeat (apply pair_equal_spec in EV as [EV ?]).
  rewrite Z.max_l in Ch by lia.
  set (l4 := setL_insert (ls_insert l3 - 1) l3).
  assert (Ch4 : chain_below g l4 (ls_strstart l4)).
  { apply (chain_frame g g l3 l4); try reflexivity. subst l4. ls_red. congruence. }
  assert (FV4 : FV2 l4 = FV2 l) by (subst l4; unfold FV2; ls_red; congruence).
  assert (I4 : ls_insert l4 = ls_insert l - 1) by (subst l4; ls_red; congruence).
  clearbody l4.
  destruct (_ <? _); [split; [exact Ch4|]; split; [lia | exact FV4]|].
  assert (S4 : ls_strstart l4 = ls_strstart l) by (unfold FV2 in FV4; repeat (apply pair_equal_spec in FV4 as [FV4 ?]); congruence).
  destruct (IH g (str + 1) l4 Hc Ch4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (C5 & I5 & F5).
  split; [exact C5|]. split; [lia|]. congruence.
Qed.

Lemma fw_seed_inv : forall g l, cfg_ok g -> chain_below g l (ls_strstart l) ->
  0 <= ls_insert l <= ls_strstart l -> ls_strstart l <= 65536 ->
  let l' := fw_seed g l in
  chain_below g l' (ls_strstart l') /\ 0 <= ls_insert l' <= ls_insert l /\ FV2 l' = FV2 l.
Proof.
  intros g l Hc Hch Hi Hs l'. subst l'. unfold fw_seed. destruct (_ <=? _); [| split; [exact Hch|]; split; [lia | reflexivity]].
  cbv zeta.
  set (l1 := setL_insh _ l).
  assert (Ch1 : chain_below g l1 (ls_strstart l1)) by (apply (chain_frame g g l l1); reflexivity || exact Hch).
  assert (F1 : FV2 l1 = FV2 l) by reflexivity.
  assert (I1 : ls_insert l1 = ls_insert l) by reflexivity.
  assert (S1 : ls_strstart l1 = ls_strstart l) by reflexivity.
  clearbody l1.
  destruct (fw_insert_inv (Z.to_nat (ls_insert l) + 1) g (ls_strstart l - ls_insert l) l1 Hc Ch1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (C2 & I2 & F2).
  split; [exact C2|]. split; [lia | congruence].
Qed.

(* ------------------------------------------------------------------------- *)
(* read_buf and one trip                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma rb_len : forall wrap size st, 0 <= size -> 0 <= zlen (fst (read_buf wrap size st)) <= size.
Proof.
  intros wrap size st Hs. unfold read_buf. cbv zeta.
  destruct (Z.ltb_spec size (zlen (zs_in st))) as [H|H]; cbv beta iota.
  - destruct (Z.eqb_spec size 0) as [E|E]; cbn [fst]; [unfold zlen; cbn [length Z.of_nat]; lia|].
    unfold zlen in *. rewrite length_map, length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. lia.
  - destruct (Z.eqb_spec (zlen (zs_in st)) 0) as [E|E]; cbn [fst]; [unfold zlen; cbn [length Z.of_nat]; lia|].
    unfold zlen in *. rewrite length_map, length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.

Lemma u32_id : forall v, 0 <= v < 4294967296 -> u32 v = v.
Proof. intros v H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma FV2_fields : forall a b, FV2 b = FV2 a ->
  ls_matchlen b = ls_matchlen a /\ ls_strstart b = ls_strstart a /\ ls_matchstart b = ls_matchstart a
  /\ ls_lookahead b = ls_lookahead a /\ ls_prevlen b = ls_prevlen a /\ ls_windowsize b = ls_windowsize a.
Proof.
  intros a b E. unfold FV2 in E. repeat (apply pair_equal_spec in E as [E ?]). repeat split; assumption.
Qed.

(** fw_step's slide stage, verbatim. *)
Definition fw_p (g : DeflGeom) (l : LSt) : LSt * Z :=
  let wsize := dg_w_size g in
  let more0 := u32 (ls_windowsize l - ls_lookahead l - ls_strstart l) in
  if Z.leb (wsize + dg_max_dist g) (ls_strstart l) then
    let l1 := setL_window (win_move 0 wsize (wsize - more0) (ls_window l)) l in
    let l2 := setL_matchstart (ls_matchstart l1 - wsize) l1 in
    let l3 := setL_strstart (ls_strstart l2 - wsize) l2 in
    let l4 := setL_blockstart (ls_blockstart l3 - wsize) l3 in
    let l5 := if Z.ltb (ls_strstart l4) (ls_insert l4) then setL_insert (ls_strstart l4) l4 else l4 in
    (slide_hash g l5, more0 + wsize)
  else (l, more0).

Lemma fw_step_eq : forall g wrap l st,
  fw_step g wrap l st =
  (let p := fw_p g l in
   let l' := fst p in let more := snd p in
   if Z.eqb (zlen (zs_in st)) 0 then (true, l', st)
   else
     let r := read_buf wrap more st in
     let dat := fst r in let st' := snd r in
     let l6 := setL_window (win_blit dat (ls_strstart l' + ls_lookahead l') (ls_window l')) l' in
     let l7 := setL_lookahead (ls_lookahead l6 + zlen dat) l6 in
     (false, fw_seed g l7, st')).
Proof. reflexivity. Qed.

Lemma fw_p_inv : forall g l, cfg_ok g -> fi g l ->
  let p := fw_p g l in
  fi g (fst p) /\ fw_same l (fst p) /\ ls_lookahead (fst p) = ls_lookahead l
  /\ snd p = ls_windowsize (fst p) - ls_lookahead (fst p) - ls_strstart (fst p).
Proof.
  intros g l Hc Hf p. subst p. pose proof Hf as (Hch & Hs & Hl & Hr & Hw & Hi).
  pose proof Hc as (Hws & Hmd & _). unfold fw_p. cbv zeta.
  rewrite u32_id by lia.
  destruct (Z.leb_spec (dg_w_size g + dg_max_dist g) (ls_strstart l)) as [Hsl|Hsl]; cbn [fst snd].
  - set (l4 := setL_blockstart _ (setL_strstart _ (setL_matchstart _ (setL_window _ l)))).
    assert (E4 : ls_strstart l4 = ls_strstart l - dg_w_size g /\ ls_insert l4 = ls_insert l
                 /\ ls_lookahead l4 = ls_lookahead l /\ ls_matchstart l4 = ls_matchstart l - dg_w_size g
                 /\ ls_matchlen l4 = ls_matchlen l /\ ls_prevlen l4 = ls_prevlen l /\ ls_windowsize l4 = ls_windowsize l
                 /\ ls_head l4 = ls_head l /\ ls_prev l4 = ls_prev l)
      by (subst l4; ls_red; repeat split; reflexivity).
    clearbody l4.
    destruct E4 as (S4 & I4 & L4 & M4 & ML4 & P4 & W4 & H4 & V4).
    set (l5 := if ls_strstart l4 <? ls_insert l4 then setL_insert (ls_strstart l4) l4 else l4).
    assert (E5 : ls_strstart l5 = ls_strstart l4 /\ 0 <= ls_insert l5 <= ls_strstart l5
                 /\ ls_lookahead l5 = ls_lookahead l4 /\ ls_matchstart l5 = ls_matchstart l4
                 /\ ls_matchlen l5 = ls_matchlen l4 /\ ls_prevlen l5 = ls_prevlen l4 /\ ls_windowsize l5 = ls_windowsize l4
                 /\ ls_head l5 = ls_head l4 /\ ls_prev l5 = ls_prev l4).
    { subst l5. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
      destruct (Z.ltb_spec (ls_strstart l4) (ls_insert l4)); ls_red; repeat split; try reflexivity; lia. }
    clearbody l5.
    destruct E5 as (S5 & I5 & L5 & M5 & ML5 & P5 & W5 & H5 & V5).
    assert (C5 : chain_below g l5 (ls_strstart l)) by (apply (chain_frame g g l l5); try reflexivity; congruence || exact Hch).
    pose proof (slide_chain g l5 (ls_strstart l) Hc ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia) C5) as C6.
    assert (Q : ls_strstart (slide_hash g l5) = ls_strstart l5 /\ ls_lookahead (slide_hash g l5) = ls_lookahead l5
                /\ ls_matchstart (slide_hash g l5) = ls_matchstart l5 /\ ls_matchlen (slide_hash g l5) = ls_matchlen l5
                /\ ls_prevlen (slide_hash g l5) = ls_prevlen l5 /\ ls_insert (slide_hash g l5) = ls_insert l5
                /\ ls_windowsize (slide_hash g l5) = ls_windowsize l5) by (repeat split; reflexivity).
    destruct Q as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    unfold fi, fw_same. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q7.
    replace (ls_strstart l5) with (ls_strstart l - dg_w_size g) by lia.
    unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
    split; [split; [exact C6 | repeat split; lia] |]. repeat split; lia.
  - split; [exact Hf|]. split; [apply fw_same_refl|]. split; reflexivity.
Qed.

Lemma fw_step_inv : forall g wrap l st, cfg_ok g -> fi g l ->
  let l' := snd (fst (fw_step g wrap l st)) in
  fi g l' /\ fw_same l l'.
Proof.
  intros g wrap l st Hc Hf l'. subst l'. rewrite fw_step_eq. cbv zeta.
  destruct (fw_p_inv g l Hc Hf) as (F1 & S1 & L1 & M1).
  destruct (fw_p g l) as [l1 more]. cbn [fst snd] in *.
  destruct (zlen (zs_in st) =? 0); cbn [fst snd]; [split; assumption|].
  pose proof F1 as (Hch & Hs & Hl & Hr & Hw & Hi). pose proof Hc as (Hws & _).
  pose proof (rb_len wrap more st ltac:(lia)) as R.
  set (dat := fst (read_buf wrap more st)) in *. clearbody dat.
  set (l7 := setL_lookahead _ (setL_window _ l1)).
  assert (E7 : ls_strstart l7 = ls_strstart l1 /\ ls_lookahead l7 = ls_lookahead l1 + zlen dat
               /\ ls_insert l7 = ls_insert l1 /\ ls_matchstart l7 = ls_matchstart l1
               /\ ls_matchlen l7 = ls_matchlen l1 /\ ls_prevlen l7 = ls_prevlen l1 /\ ls_windowsize l7 = ls_windowsize l1
               /\ ls_head l7 = ls_head l1 /\ ls_prev l7 = ls_prev l1)
    by (subst l7; ls_red; repeat split; reflexivity).
  clearbody l7. destruct E7 as (S7 & L7 & I7 & M7 & ML7 & P7 & W7 & H7 & V7).
  assert (C7 : chain_below g l7 (ls_strstart l7)) by (rewrite S7; apply (chain_frame g g l1 l7); try reflexivity; congruence || exact Hch).
  destruct (fw_seed_inv g l7 Hc C7 ltac:(lia) ltac:(lia)) as (C8 & I8 & F8).
  destruct (FV2_fields _ _ F8) as (ML8 & S8 & M8 & L8 & P8 & W8).
  destruct S1 as (A1 & A2 & A3 & A4 & A5).
  unfold fi, fw_same. rewrite ML8, S8, M8, L8, P8, W8.
  split; [split; [rewrite <- S8; exact C8 | repeat split; lia] | repeat split; lia].
Qed.

Lemma fw_loop_inv : forall n g wrap l st, cfg_ok g -> fi g l ->
  let l' := fst (fw_loop n g wrap l st) in fi g l' /\ fw_same l l'.
Proof.
  induction n as [|n IH]; intros g wrap l st Hc Hf l'; subst l'.
  { cbn [fw_loop fst]. split; [exact Hf | apply fw_same_refl]. }
  cbn [fw_loop]. pose proof (fw_step_inv g wrap l st Hc Hf) as P. cbv zeta in P.
  destruct (fw_step g wrap l st) as [[brk l1] st1]. cbn [fst snd] in P. destruct P as [F1 S1].
  destruct brk; cbn [fst]; [split; assumption|].
  destruct (_ && _); cbn [fst]; [| split; assumption].
  destruct (IH g wrap l1 st1 Hc F1) as [F2 S2]. split; [exact F2 | exact (fw_same_trans _ _ _ S1 S2)].
Qed.

Lemma fw_highwater_fields : forall l,
  ls_head (fw_highwater l) = ls_head l /\ ls_prev (fw_highwater l) = ls_prev l
  /\ ls_strstart (fw_highwater l) = ls_strstart l /\ ls_lookahead (fw_highwater l) = ls_lookahead l
  /\ ls_insert (fw_highwater l) = ls_insert l /\ ls_matchstart (fw_highwater l) = ls_matchstart l
  /\ ls_matchlen (fw_highwater l) = ls_matchlen l /\ ls_prevlen (fw_highwater l) = ls_prevlen l
  /\ ls_windowsize (fw_highwater l) = ls_windowsize l.
Proof.
  intros l. unfold fw_highwater. cbv zeta.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); ls_red; repeat split; reflexivity.
Qed.

Theorem fill_window_inv : forall g wrap l st, cfg_ok g -> fi g l ->
  let l' := fst (fill_window g wrap l st) in fi g l' /\ fw_same l l'.
Proof.
  intros g wrap l st Hc Hf l'. subst l'. unfold fill_window. cbv zeta. cbn [fst].
  destruct (fw_loop_inv (Z.to_nat (zlen (zs_in st)) + 2) g wrap l st Hc Hf) as [F1 S1].
  set (l1 := fst (fw_loop _ g wrap l st)) in *. clearbody l1.
  destruct (fw_highwater_fields l1) as (H1 & V1 & S2 & L2 & I2 & M2 & ML2 & P2 & W2).
  pose proof F1 as (Hch & Hs & Hl & Hr & Hw & Hi). destruct S1 as (A1 & A2 & A3 & A4 & A5).
  unfold fi, fw_same. rewrite S2, L2, I2, M2, ML2, P2, W2.
  split; [split; [apply (chain_frame g g l1); try reflexivity; assumption | repeat split; lia] | repeat split; lia].
Qed.
