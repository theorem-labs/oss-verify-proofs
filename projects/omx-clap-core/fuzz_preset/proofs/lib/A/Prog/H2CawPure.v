(* fuzz_preset, image A: PURE (machine-free) lemmas about preset's JSON grammar model (lib/Spec/PjGrammar.v), for the
   walk of check_as_written (fuzz_preset.c:333-349, 519-536). Lane WalkH2H5.H2Caw. No function is proved here (rule
   24): these are model lemmas the walk cites.
   - the rest of a successful reading is a suffix of its input (jrv / jrl at any strtod model, and prhex_V of
     lib/A/PRH_FnEx.v), stated as `skipn (length x - length r) x = r`;
   - ck_read (lib/A/PRH_FnCheck.v) in terms of prhex_V 0: a tree exactly when the value reading succeeds and only
     whitespace follows;
   - the inlined ex_ws loop (fuzz_preset.c:103-107): one step of PjGrammar.skip over skipn i x, its end and its length;
   - the machine's whitespace test (A 0x81fb8-0x81fec): the mask 0x100002600 shifted right by c, low bit, for
     c <= 32, and no byte above 32 is whitespace. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnEx PRH_FnCheck.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

(* ---- suffixes ---- *)

Lemma cawp_sfx_trans : forall x y z : list Z,
  (exists p, x = p ++ y) -> (exists q, y = q ++ z) -> exists p, x = p ++ z.
Proof. intros x y z [p ->] [q ->]. exists (p ++ q). apply app_assoc. Qed.

Lemma cawp_sfx_cons : forall b (y z : list Z), (exists p, y = p ++ z) -> exists p, b :: y = p ++ z.
Proof. intros b y z [p ->]. exists (b :: p). reflexivity. Qed.

Lemma cawp_skip_sfx : forall x, exists p, x = p ++ PjGrammar.skip x.
Proof.
  induction x as [|b r IH]; cbn [PjGrammar.skip].
  - exists []. reflexivity.
  - destruct (PjGrammar.ws b).
    + apply cawp_sfx_cons. exact IH.
    + exists []. reflexivity.
Qed.

Lemma cawp_tl_sfx : forall x : list Z, exists p, x = p ++ tl x.
Proof. intros [|b r]; [exists []|exists [b]]; reflexivity. Qed.

Lemma cawp_skipn_sfx : forall k (x : list Z), exists p, x = p ++ skipn k x.
Proof. intros k x. exists (firstn k x). symmetry. apply firstn_skipn. Qed.

Lemma cawp_string_sfx : forall z ok s r t ok', PjGrammar.jr_string z ok = (Some (s, r), t, ok') ->
  exists p, z = p ++ r.
Proof.
  intros z ok s r t ok' H. pose proof (PjGrammar.jr_string_spec z ok) as Hs. rewrite H in Hs.
  cbv beta iota in Hs. destruct Hs as (q & _ & Hd & _ & _).
  destruct (PjGrammar.decode_stop z s r Hd) as (q' & _ & Hr & _). rewrite Hr.
  apply cawp_skipn_sfx.
Qed.

Lemma cawp_lit_sfx : forall w v x ok u r t ok', PjGrammar.lit w v x ok = (Some (u, r), t, ok') ->
  exists p, x = p ++ r.
Proof.
  intros w v x ok u r t ok' H. unfold PjGrammar.lit in H.
  destruct (PjGrammar.prefixb w x); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
  unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r. apply cawp_skipn_sfx.
Qed.

Lemma cawp_number_sfx : forall sm x ok u r t ok', PjGrammar.jr_number sm x ok = (Some (u, r), t, ok') ->
  exists p, x = p ++ r.
Proof.
  intros sm x ok u r t ok' H. unfold PjGrammar.jr_number in H. cbv beta zeta in H.
  destruct (skipn _ x) as [|c z] eqn:Ez; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  destruct (negb (PjGrammar.digit c)); cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  destruct ((c =? 48) && _); cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  destruct (PjGrammar.span PjGrammar.numch z) as [a r'] eqn:Es. cbv beta iota in H.
  apply PjGrammar.jbind_some in H as (a0 & t1 & ok1 & t2 & _ & H & _). cbv beta in H.
  destruct (PjGrammar.whole sm _); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
  unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r.
  apply (cawp_sfx_trans x (c :: z) r').
  - rewrite <- Ez. apply cawp_skipn_sfx.
  - apply cawp_sfx_cons. rewrite (PjGrammar.span_app _ _ _ _ Es). exists a. reflexivity.
Qed.

Lemma cawp_name_sfx : forall o y ok nm y1 t ok', PjGrammar.jr_name o y ok = (Some (nm, y1), t, ok') ->
  exists p, y = p ++ y1.
Proof.
  intros o y ok nm y1 t ok' H. unfold PjGrammar.jr_name in H. destruct o; cbv beta iota in H.
  - pose proof (cawp_skip_sfx y) as Hy.
    destruct (PjGrammar.skip y) as [|b z]; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
    destruct (b =? 34); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
    apply PjGrammar.jbind_some in H as ([nm0 r] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
    pose proof (cawp_string_sfx _ _ _ _ _ _ Hs) as Hz.
    pose proof (cawp_skip_sfx r) as Hr.
    destruct (PjGrammar.skip r) as [|c r1]; cbv beta iota in H.
    + apply PjGrammar.jbind_some in H as (? & ? & ? & ? & _ & H & _). cbv beta in H.
      unfold PjGrammar.jrefuse in H. discriminate.
    + destruct (c =? 58); cbv beta iota in H.
      * unfold PjGrammar.jret in H. injection H as _ Hy1 _ _. subst y1.
        apply (cawp_sfx_trans y (b :: z) r1); [exact Hy|]. apply cawp_sfx_cons.
        apply (cawp_sfx_trans z r r1); [exact Hz|]. apply (cawp_sfx_trans r (c :: r1) r1); [exact Hr|].
        exists [c]. reflexivity.
      * apply PjGrammar.jbind_some in H as (? & ? & ? & ? & _ & H & _). cbv beta in H.
        unfold PjGrammar.jrefuse in H. discriminate.
  - unfold PjGrammar.jret in H. injection H as _ Hy1 _ _. subst y1. exists []. reflexivity.
Qed.

Lemma cawp_cont_sfx : forall loop d o x ok v r t ok',
  (forall o' n cap acc y ok1 v1 r1 t1 ok2, loop (S d) o' n cap acc y ok1 = (Some (v1, r1), t1, ok2) ->
     exists p, y = p ++ r1) ->
  PjGrammar.jr_cont loop d o x ok = (Some (v, r), t, ok') -> exists p, x = p ++ r.
Proof.
  intros loop d o x ok v r t ok' HL H. unfold PjGrammar.jr_cont in H. cbv beta in H.
  destruct (Nat.ltb PjGrammar.MAXD (S d)); cbv beta iota zeta in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  assert (Hx : exists p, x = p ++ PjGrammar.skip (tl x)).
  { apply (cawp_sfx_trans x (tl x)); [apply cawp_tl_sfx|apply cawp_skip_sfx]. }
  destruct (PjGrammar.skip (tl x)) as [|c r0]; cbv beta iota in H.
  - exact (cawp_sfx_trans _ _ _ Hx (HL _ _ _ _ _ _ _ _ _ _ H)).
  - destruct (c =? PjGrammar.closer o); cbv beta iota in H.
    + unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r.
      apply (cawp_sfx_trans x (c :: r0) r0); [exact Hx|]. exists [c]. reflexivity.
    + exact (cawp_sfx_trans _ _ _ Hx (HL _ _ _ _ _ _ _ _ _ _ H)).
Qed.

Lemma cawp_suffix_fuel : forall sm f,
  (forall d x ok v r t ok', PjGrammar.jrv sm f d x ok = (Some (v, r), t, ok') -> exists p, x = p ++ r) /\
  (forall d o n cap acc y ok v r t ok', PjGrammar.jrl sm f d o n cap acc y ok = (Some (v, r), t, ok') ->
     exists p, y = p ++ r).
Proof.
  intros sm f. induction f as [|f [IHv IHl]].
  - split; intros; cbn [PjGrammar.jrv PjGrammar.jrl] in *; unfold PjGrammar.jrefuse in *; discriminate.
  - split.
    + intros d x ok v r t ok' H. cbn [PjGrammar.jrv] in H.
      pose proof (cawp_skip_sfx x) as Hx.
      destruct (PjGrammar.skip x) as [|b y]; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
      apply (cawp_sfx_trans x (b :: y) r); [exact Hx|].
      destruct (b =? 123); cbv beta iota in H.
      { exact (cawp_cont_sfx _ _ _ _ _ _ _ _ _ (IHl (S d)) H). }
      destruct (b =? 91); cbv beta iota in H.
      { exact (cawp_cont_sfx _ _ _ _ _ _ _ _ _ (IHl (S d)) H). }
      destruct (b =? 34); cbv beta iota in H.
      { apply PjGrammar.jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
        unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r.
        apply cawp_sfx_cons. exact (cawp_string_sfx _ _ _ _ _ _ Hs). }
      destruct (b =? 116); cbv beta iota in H; [exact (cawp_lit_sfx _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota in H; [exact (cawp_lit_sfx _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota in H; [exact (cawp_lit_sfx _ _ _ _ _ _ _ _ H)|].
      exact (cawp_number_sfx _ _ _ _ _ _ _ H).
    + intros d o n cap acc y ok v r t ok' H. cbn [PjGrammar.jrl] in H.
      apply PjGrammar.jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply PjGrammar.jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply PjGrammar.jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      apply (cawp_sfx_trans y y1 r); [exact (cawp_name_sfx _ _ _ _ _ _ _ En)|].
      apply (cawp_sfx_trans y1 r0 r); [exact (IHv _ _ _ _ _ _ _ Ev)|].
      pose proof (cawp_skip_sfx r0) as Hr0.
      destruct (PjGrammar.skip r0) as [|c r1]; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
      apply (cawp_sfx_trans r0 (c :: r1) r); [exact Hr0|].
      apply (cawp_sfx_trans (c :: r1) r1 r); [exists [c]; reflexivity|].
      destruct (c =? 44); cbv beta iota in H; [exact (IHl _ _ _ _ _ _ _ _ _ _ _ H)|].
      destruct (c =? PjGrammar.closer o); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
      unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r. exists []. reflexivity.
Qed.

(* the rest of a value reading is a suffix of its input, at any strtod model *)
Lemma cawp_jrv_suffix : forall sm f d x ok v r t ok',
  PjGrammar.jrv sm f d x ok = (Some (v, r), t, ok') -> exists p, x = p ++ r.
Proof. intros sm f. exact (proj1 (cawp_suffix_fuel sm f)). Qed.

(* the rest of a member-list reading is a suffix of its input, at any strtod model *)
Lemma cawp_jrl_suffix : forall sm f d o n cap acc y ok v r t ok',
  PjGrammar.jrl sm f d o n cap acc y ok = (Some (v, r), t, ok') -> exists p, y = p ++ r.
Proof. intros sm f. exact (proj2 (cawp_suffix_fuel sm f)). Qed.

Lemma cawp_skipn_app : forall p r : list Z, skipn (length p) (p ++ r) = r.
Proof. induction p as [|a p IH]; intros r; [reflexivity|exact (IH r)]. Qed.

Lemma cawp_V_sfx : forall d x v r, PRH_FnEx.prhex_V d x = Some (v, r) -> exists p, x = p ++ r.
Proof.
  intros d x v r H. unfold PRH_FnEx.prhex_V, PjGrammar.jr_value in H.
  destruct (PjGrammar.jrv ReaderRes.jr_strtod _ _ x []) as [[res t] ok'] eqn:E. cbn [fst] in H. subst res.
  exact (cawp_jrv_suffix _ _ _ _ _ _ _ _ _ E).
Qed.

(* ex_value's rest pointer: the rest r is the last length r bytes of x *)
Lemma caw_V_suffix : forall d x v r, PRH_FnEx.prhex_V d x = Some (v, r) ->
  skipn (length x - length r)%nat x = r.
Proof.
  intros d x v r H. destruct (cawp_V_sfx d x v r H) as [p ->].
  rewrite length_app. replace (length p + length r - length r)%nat with (length p) by lia.
  apply cawp_skipn_app.
Qed.

Lemma caw_V_len : forall d x v r, PRH_FnEx.prhex_V d x = Some (v, r) -> (length r <= length x)%nat.
Proof. intros d x v r H. destruct (cawp_V_sfx d x v r H) as [p ->]. rewrite length_app. lia. Qed.

(* ---- ck_read through prhex_V 0 ---- *)

Lemma caw_read_V : forall x t, PRH_FnCheck.ck_read x = Some t <->
  exists r, PRH_FnEx.prhex_V 0 x = Some (t, r) /\ PjGrammar.skip r = [].
Proof.
  intros x t. unfold PRH_FnCheck.ck_read, PRH_FnEx.prhex_V, PjGrammar.json_read, PjGrammar.jr_run. cbv beta.
  change (Z.to_nat 0) with 0%nat.
  destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 x []) as [[[[t' r]|] tr] ok']; cbn [fst].
  - split.
    + intros H. exists r. destruct (PjGrammar.skip r) as [|b r1]; [|discriminate H].
      injection H as ->. split; reflexivity.
    + intros (r0 & H & Hs). injection H as -> ->. rewrite Hs. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros (r0 & H & _). discriminate H.
Qed.

Lemma caw_read_none_V : forall x, PRH_FnCheck.ck_read x <> None ->
  exists t r, PRH_FnEx.prhex_V 0 x = Some (t, r) /\ PjGrammar.skip r = [].
Proof.
  intros x H. destruct (PRH_FnCheck.ck_read x) as [t|] eqn:E; [|contradiction].
  exists t. exact (proj1 (caw_read_V x t) E).
Qed.

(* ---- the inlined ex_ws loop (fuzz_preset.c:103-107) ---- *)

Lemma cawp_skipn_nth : forall i (x : list Z), (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
  induction i as [|i IH]; intros [|b x] H; cbn [length] in H; try lia.
  - reflexivity.
  - exact (IH x ltac:(lia)).
Qed.

Lemma caw_skip_cons : forall i x, (i < length x)%nat ->
  PjGrammar.skip (skipn i x) =
  if PjGrammar.ws (nth i x 0) then PjGrammar.skip (skipn (S i) x) else skipn i x.
Proof. intros i x H. rewrite (cawp_skipn_nth i x H). reflexivity. Qed.

Lemma caw_skip_end : forall x, PjGrammar.skip (skipn (length x) x) = [].
Proof. induction x as [|b x IH]; [reflexivity|exact IH]. Qed.

Lemma caw_skip_len : forall i x, (length (PjGrammar.skip (skipn i x)) <= length x - i)%nat.
Proof.
  intros i x. pose proof (PjGrammar.skip_len (skipn i x)) as H. rewrite length_skipn in H. exact H.
Qed.

(* ---- the machine's whitespace test (A 0x81fb8-0x81fec: mask 0x100002600, c <= 32) ---- *)

Lemma caw_ws_mask : forall c, 0 <= c <= 32 ->
  Z.land (Z.shiftr 4294977024 c) 1 = if PjGrammar.ws c then 1 else 0.
Proof.
  intros c Hc.
  replace c with (Z.of_nat (Z.to_nat c)) by lia.
  assert (Hn : (Z.to_nat c <= 32)%nat) by lia.
  revert Hn. generalize (Z.to_nat c) as n. intros n Hn. clear Hc.
  do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma caw_ws_big : forall c, 32 < c -> PjGrammar.ws c = false.
Proof.
  intros c Hc. unfold PjGrammar.ws.
  rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 10)),
    (proj2 (Z.eqb_neq c 13)) by lia.
  reflexivity.
Qed.
