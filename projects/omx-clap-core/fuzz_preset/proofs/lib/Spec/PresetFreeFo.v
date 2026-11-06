(* omx-clap-core/fuzz_preset: pj_free's list of a tree read back from the writer's text.

   PresetReqAt.fo u is the list of requests pj_free (src/preset_file.c:334-350) frees for a tree u, in its order;
   the run model frees each tree read back from the writer's text with HBulk (fo t) (PresetReqAt.round_trip,
   rw_evs). PresetReqAt.pj_frees sm ok x is that list for the tree the reader builds from the text x (jfv over x).
   pj_frees_wdoc: on the writer's text wdoc t p of a tree t with pj_wf sm t, the reading succeeds with u = t and
   the two lists are EQUAL (same blocks, same order). rd_blocks_wdoc: the reader's live blocks after that reading
   are fo t up to Permutation (with PresetReqAtNoMiss.pj_frees_blocks).

   Why pj_wf. The reader sizes a string or key block by the escaped span of the text (src/preset_file.c:127
   `out = malloc((size_t)(o - p) + 1);`, PjGrammar.jr_string's jalloc (S q)); fo sizes it by the writer's escape of
   the decoded string, |flat_map ech s| + 1. On the writer's own text of a pj_wf tree the span is that escape
   (PjRoundTrip.jr_string_ech). Without pj_wf they differ: t = JNum (the text "\u0041") 0 is written as that
   text and read back as u = JStr "A", pj_frees [23] and fo u [18].

   The proof follows PjRoundTrip.rt_value (the reader's result on wdoc t p): fv_value is its jfv twin, and uses
   rt_value for the jrv calls jfv and jfl make.

   THE ORDER OF THE LIVE LIST. rd_blocks keeps the live list newest first (PresetReqAt.hstep: HMal n puts n in
   front, HRe m n puts n in front and drops the FIRST entry of value m). So a container's kids / keys block sits at
   its LAST grow (a grow from capacity 0 is HMal, PresetReqAt.rd_hev), and a realloc of m drops the newest live
   entry of size m, which is the container's own array only when no newer block of that size is live. In
   [0,[1],2,2,2,2,2,2,2] the inner array's kids block (464) is newer than the outer's (464): the outer's grow at
   item 8 drops the inner's entry (ex_nest below). Neither tblk u, rev (tblk u), fo u, nor tblk with each array at
   its last grow is then the live list. rd_blocks_wdoc_trace gives the order there is: the live list of the reading
   is the live list of ttrace u, the reader's trace computed from u alone (PjRoundTrip.ttrace, G9_trace).

   THE ACCEPTED ARM. pj_frees_acc: when the reading of x under the grant oracle ok is accepted, pj_free's list
   is the one of the reading with every allocation granted, pj_frees sm [] x. jfv / jfl take ok through grow,
   jr_name and jrv as jrv / jrl do, and each of those gives on an accepted call what it gives under []
   (PjGrammar.agrees_some), so acc_fuel follows jrl's binds (PjGrammar.jbind_some).

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ fo, member by member *)

Definition fom (m : list Z * jv) : list Z := fo (snd m) ++ [Z.of_nat (S (length (flat_map ech (fst m)))) + HEAD].

Lemma fo_arr : forall items, fo (JArr items) = concat (map fo items) ++ arrz false (capf 0 0 (length items)).
Proof. intros items. rewrite <- ncap_eq. reflexivity. Qed.

Lemma fo_obj : forall ms, fo (JObj ms) = concat (map fom ms) ++ arrz true (capf 0 0 (length ms)).
Proof. intros ms. rewrite <- ncap_eq. reflexivity. Qed.

(* ================================================================ jfv / jfl, one step *)

Lemma jfv_ws : forall sm f d z X ok, forallb ws z = true -> jfv sm f d (z ++ X) ok = jfv sm f d X ok.
Proof.
  intros sm [|f] d z X ok H; [reflexivity|]. cbn [jfv].
  rewrite (skip_ws_app z X H), (jrv_ws sm (S f) d z X ok H). reflexivity.
Qed.

Lemma jfv_arr : forall sm f d X ok, jfv sm (S f) d (91 :: X) ok = jf_cont (jfl sm f) d false (91 :: X) ok.
Proof. reflexivity. Qed.

Lemma jfv_obj : forall sm f d X ok, jfv sm (S f) d (123 :: X) ok = jf_cont (jfl sm f) d true (123 :: X) ok.
Proof. reflexivity. Qed.

(* a value that is not a container: jfv keeps the one block of the reader's trace *)
Lemma jfv_leaf : forall sm f d x ok,
  match skip x with b :: _ => (b =? 123) = false /\ (b =? 91) = false | [] => False end ->
  jfv sm (S f) d x ok = lf (snd (fst (jrv sm (S f) d x ok))).
Proof.
  intros sm f d x ok. cbn [jfv]. destruct (skip x) as [|b y]; intros H; [contradiction|].
  destruct H as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

Lemma jf_cont_empty : forall loop d o b0 X r ok, (S d <= MAXD)%nat -> skip X = closer o :: r ->
  jf_cont loop d o (b0 :: X) ok = [].
Proof.
  intros loop d o b0 X r ok H1 H2. unfold jf_cont.
  rewrite (proj2 (Nat.ltb_ge MAXD (S d))) by lia. cbn [tl]. rewrite H2. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma jf_cont_items : forall loop d o b0 X b r ok, (S d <= MAXD)%nat -> skip X = b :: r -> b <> closer o ->
  jf_cont loop d o (b0 :: X) ok = loop (S d) o 0%nat 0%nat [] (skip X) ok.
Proof.
  intros loop d o b0 X b r ok H1 H2 H3. unfold jf_cont.
  rewrite (proj2 (Nat.ltb_ge MAXD (S d))) by lia. cbn [tl]. rewrite H2.
  rewrite (proj2 (Z.eqb_neq b (closer o)) H3). reflexivity.
Qed.

(* one slot of a container, every allocation granted: a comma follows, or the last slot *)
Lemma jfl_next : forall sm f d o n cap af y nm y1 tn u r tv r1,
  jr_name o y [] = (Some (nm, y1), tn, []) -> jfv sm f d y1 [] = fo u ->
  jrv sm f d y1 [] = (Some (u, r), tv, []) -> skip r = 44 :: r1 ->
  jfl sm (S f) d o n cap af y [] = jfl sm f d o (S n) (gcap n cap) (af ++ fo u ++ lf tn) r1 [].
Proof.
  intros sm f d o n cap af y nm y1 tn u r tv r1 Hn Hf Hv Hs.
  cbn [jfl]. rewrite grow_all. cbv beta iota zeta. rewrite Hn. cbv beta iota zeta.
  rewrite Hf, Hv. cbv beta iota zeta. rewrite Hs. reflexivity.
Qed.

Lemma jfl_last : forall sm f d o n cap af y nm y1 tn u r tv c r1,
  jr_name o y [] = (Some (nm, y1), tn, []) -> jfv sm f d y1 [] = fo u ->
  jrv sm f d y1 [] = (Some (u, r), tv, []) -> skip r = c :: r1 -> c <> 44 ->
  jfl sm (S f) d o n cap af y [] = (af ++ fo u ++ lf tn) ++ arrz o (gcap n cap).
Proof.
  intros sm f d o n cap af y nm y1 tn u r tv c r1 Hn Hf Hv Hs Hc.
  cbn [jfl]. rewrite grow_all. cbv beta iota zeta. rewrite Hn. cbv beta iota zeta.
  rewrite Hf, Hv. cbv beta iota zeta. rewrite Hs. cbv beta iota zeta.
  rewrite (proj2 (Z.eqb_neq c 44) Hc). reflexivity.
Qed.

Local Ltac fin := try unfold fom; cbn [map concat fst snd lf length capf]; rewrite ?app_nil_r, <- ?app_assoc;
  reflexivity.

(* ================================================================ the writer's text, read back *)

(* jfv on the writer's text of t, followed by y: fo t *)
Definition Fv (sm : list Z -> Z * Z) (t : jv) : Prop := forall p dw d, (depth t + d <= MAXD)%nat -> forall y f, safe y ->
  (2 * length (concat (wvpieces t p dw) ++ y) + 1 <= f)%nat ->
  jfv sm f d (concat (wvpieces t p dw) ++ y) [] = fo t.

Lemma lead_leaf : forall sm t p dw y, good sm t -> (forall items, t <> JArr items) -> (forall ms, t <> JObj ms) ->
  match skip (concat (wvpieces t p dw) ++ y) with b :: _ => (b =? 123) = false /\ (b =? 91) = false | [] => False end.
Proof.
  intros sm t p dw y Hg Ha Ho. destruct t as [| | | txt bits | s | items | ms].
  1-3: cbn; split; reflexivity.
  - destruct Hg as [(sg & c & a & -> & Hsg & Hc & _) _].
    assert (Hc1 : 48 <= c <= 57) by (unfold digit in Hc; zr; lia).
    destruct Hsg as [-> | ->]; cbn [wvpieces concat app skip]; rewrite ws_false by lia; cbv beta iota;
      split; apply Z.eqb_neq; lia.
  - cbn [wvpieces]. rewrite wstr_eq. cbn [app skip]. rewrite ws_false by lia. cbv beta iota.
    split; apply Z.eqb_neq; lia.
  - exfalso. exact (Ha items eq_refl).
  - exfalso. exact (Ho ms eq_refl).
Qed.

Lemma fo_arr_loop : forall sm p dw d y r u af n cap z f,
  Forall (fun v => Qv sm v /\ Fv sm v /\ (depth v + S d <= MAXD)%nat) (u :: r) -> forallb ws z = true ->
  (2 * length (z ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93%Z :: y) + 2
     <= f)%nat ->
  jfl sm f (S d) false n cap af
    (z ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y) [] =
    af ++ concat (map fo (u :: r)) ++ arrz false (capf n cap (length (u :: r))).
Proof.
  intros sm p dw d y r. induction r as [|u' r' IH]; intros u af n cap z f HF Hz Hf.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Qu [Fu Du]] _].
    cbn [wgo_arr concat app] in *.
    pose proof (Qu p (dw + 1) (S d) Du (concat (wind p dw) ++ 93 :: y) f (wind_safe p dw y 93 eq_refl)) as Ev.
    lapply Ev; [clear Ev; intro Ev|lens].
    pose proof (Fu p (dw + 1) (S d) Du (concat (wind p dw) ++ 93 :: y) f (wind_safe p dw y 93 eq_refl)) as Ef.
    lapply Ef; [clear Ef; intro Ef|lens].
    assert (Es : skip (concat (wind p dw) ++ 93 :: y) = 93 :: y)
      by (rewrite skip_ws_app by apply wind_ws; reflexivity).
    assert (Hf1 : jfv sm f (S d) (z ++ concat (wvpieces u p (dw + 1)) ++ concat (wind p dw) ++ 93 :: y) [] = fo u)
      by (rewrite jfv_ws by exact Hz; exact Ef).
    assert (Hv1 : jrv sm f (S d) (z ++ concat (wvpieces u p (dw + 1)) ++ concat (wind p dw) ++ 93 :: y) [] =
      (Some (u, concat (wind p dw) ++ 93 :: y), ttrace u, [])) by (rewrite jrv_ws by exact Hz; exact Ev).
    rewrite (jfl_last sm f (S d) false n cap af _ [] _ [] u _ _ 93 y eq_refl Hf1 Hv1 Es ltac:(lia)).
    fin.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Qu [Fu Du]] HF'].
    rewrite (arr_next p dw 0 u' r') in *. cbn [app] in *. rewrite <- !app_assoc in *.
    set (R := 44 :: concat (wind p (dw + 1)) ++ concat (wvpieces u' p (dw + 1)) ++ concat (wgo_arr p dw 1 r') ++
         concat (wind p dw) ++ 93 :: y) in *.
    pose proof (Qu p (dw + 1) (S d) Du R f eq_refl) as Ev.
    lapply Ev; [clear Ev; intro Ev|unfold R in *; lens].
    pose proof (Fu p (dw + 1) (S d) Du R f eq_refl) as Ef.
    lapply Ef; [clear Ef; intro Ef|unfold R in *; lens].
    pose proof (IH u' (af ++ fo u ++ []) (S n) (gcap n cap) (concat (wind p (dw + 1))) f HF' (wind_ws _ _)) as Etr.
    lapply Etr; [clear Etr; intro Etr|unfold R in *; lens].
    assert (Hf1 : jfv sm f (S d) (z ++ concat (wvpieces u p (dw + 1)) ++ R) [] = fo u)
      by (rewrite jfv_ws by exact Hz; exact Ef).
    assert (Hv1 : jrv sm f (S d) (z ++ concat (wvpieces u p (dw + 1)) ++ R) [] = (Some (u, R), ttrace u, []))
      by (rewrite jrv_ws by exact Hz; exact Ev).
    rewrite (jfl_next sm f (S d) false n cap af _ [] _ [] u R _ _ eq_refl Hf1 Hv1 eq_refl).
    refine (eq_trans Etr _). fin.
Qed.

Lemma fo_obj_loop : forall sm p dw d y r k u af n cap z f,
  Forall (fun m => strok (fst m) /\ Qv sm (snd m) /\ Fv sm (snd m) /\ (depth (snd m) + S d <= MAXD)%nat) ((k, u) :: r) ->
  forallb ws z = true ->
  (2 * length (z ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_obj p dw 1 r) ++
     concat (wind p dw) ++ 125%Z :: y) + 2 <= f)%nat ->
  jfl sm f (S d) true n cap af
    (z ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_obj p dw 1 r) ++
     concat (wind p dw) ++ 125 :: y) [] =
    af ++ concat (map fom ((k, u) :: r)) ++ arrz true (capf n cap (length ((k, u) :: r))).
Proof.
  intros sm p dw d y r. induction r as [|[k' u'] r' IH]; intros k u af n cap z f HF Hz Hf.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Sk [Qu [Fu Du]]] _]. cbn [fst snd] in Sk, Qu, Fu, Du.
    cbn [wgo_obj concat app] in *.
    pose proof (jr_name_rt p z k (concat (wvpieces u p (dw + 1)) ++ concat (wind p dw) ++ 125 :: y) Hz Sk) as En.
    pose proof (Qu p (dw + 1) (S d) Du (concat (wind p dw) ++ 125 :: y) f (wind_safe p dw y 125 eq_refl)) as Ev.
    lapply Ev; [clear Ev; intro Ev|lens].
    pose proof (Fu p (dw + 1) (S d) Du (concat (wind p dw) ++ 125 :: y) f (wind_safe p dw y 125 eq_refl)) as Ef.
    lapply Ef; [clear Ef; intro Ef|lens].
    assert (Es : skip (concat (wind p dw) ++ 125 :: y) = 125 :: y)
      by (rewrite skip_ws_app by apply wind_ws; reflexivity).
    assert (Hf1 : jfv sm f (S d) ((if p then [32] else []) ++ concat (wvpieces u p (dw + 1)) ++ concat (wind p dw) ++
      125 :: y) [] = fo u) by (rewrite jfv_ws by apply sp_ws; exact Ef).
    assert (Hv1 : jrv sm f (S d) ((if p then [32] else []) ++ concat (wvpieces u p (dw + 1)) ++ concat (wind p dw) ++
      125 :: y) [] = (Some (u, concat (wind p dw) ++ 125 :: y), ttrace u, []))
      by (rewrite jrv_ws by apply sp_ws; exact Ev).
    rewrite (jfl_last sm f (S d) true n cap af _ k _ _ u _ _ 125 y En Hf1 Hv1 Es ltac:(lia)).
    fin.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Sk [Qu [Fu Du]]] HF']. cbn [fst snd] in Sk, Qu, Fu, Du.
    rewrite (obj_next p dw 0 k' u' r') in *. cbn [app] in *. rewrite <- !app_assoc in *.
    set (R := 44 :: concat (wind p (dw + 1)) ++ concat (spieces k') ++ wsep p ++ concat (wvpieces u' p (dw + 1)) ++
         concat (wgo_obj p dw 1 r') ++ concat (wind p dw) ++ 125 :: y) in *.
    pose proof (jr_name_rt p z k (concat (wvpieces u p (dw + 1)) ++ R) Hz Sk) as En.
    pose proof (Qu p (dw + 1) (S d) Du R f eq_refl) as Ev.
    lapply Ev; [clear Ev; intro Ev|unfold R in *; lens].
    pose proof (Fu p (dw + 1) (S d) Du R f eq_refl) as Ef.
    lapply Ef; [clear Ef; intro Ef|unfold R in *; lens].
    pose proof (IH k' u' (af ++ fo u ++ [Z.of_nat (S (length (flat_map ech k))) + HEAD]) (S n) (gcap n cap)
      (concat (wind p (dw + 1))) f HF' (wind_ws _ _)) as Etr.
    lapply Etr; [clear Etr; intro Etr|unfold R in *; lens].
    assert (Hf1 : jfv sm f (S d) ((if p then [32] else []) ++ concat (wvpieces u p (dw + 1)) ++ R) [] = fo u)
      by (rewrite jfv_ws by apply sp_ws; exact Ef).
    assert (Hv1 : jrv sm f (S d) ((if p then [32] else []) ++ concat (wvpieces u p (dw + 1)) ++ R) [] =
      (Some (u, R), ttrace u, [])) by (rewrite jrv_ws by apply sp_ws; exact Ev).
    rewrite (jfl_next sm f (S d) true n cap af _ k _ _ u R _ _ En Hf1 Hv1 eq_refl).
    refine (eq_trans Etr _). fin.
Qed.

Lemma fv_value : forall sm t, good sm t -> Fv sm t.
Proof.
  intros sm t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind';
    intros Hg p dw d Hd y f Hy Hf.
  1-5: pose proof (rt_value sm _ Hg p dw d Hd y f Hy Hf) as Q; (destruct f as [|f]; [lia|]);
    match goal with |- jfv _ _ _ (concat (wvpieces ?t _ _) ++ _) _ = _ =>
      pose proof (lead_leaf sm t p dw y Hg ltac:(intros ? ?; discriminate) ltac:(intros ? ?; discriminate)) as L;
      rewrite (jfv_leaf sm f d (concat (wvpieces t p dw) ++ y) [] L)
    end;
    rewrite Q; reflexivity.
  - rewrite fo_arr. apply good_arr in Hg.
    assert (HF : Forall (fun v => Qv sm v /\ Fv sm v /\ (depth v + S d <= MAXD)%nat) items).
    { rewrite Forall_forall in *. intros v Hv. split; [exact (rt_value sm v (Hg v Hv))|].
      split; [exact (IH v Hv (Hg v Hv))|]. pose proof (depth_item items v Hv). lia. }
    clear IH.
    assert (HD : (S d <= MAXD)%nat) by (cbn [depth] in Hd; lia).
    destruct f as [|f]; [lia|].
    rewrite arr_text in *. rewrite jfv_arr.
    destruct items as [|u r].
    + rewrite (jf_cont_empty (jfl sm f) d false 91 _ y []); [| exact HD | reflexivity]. reflexivity.
    + cbv beta iota in *. rewrite arr_first in *. rewrite <- !app_assoc in *.
      apply Forall_cons_iff in Hg as [Gu _].
      destruct (first_byte sm u p (dw + 1) Gu) as (b & U' & EU & Hb1 & Hb2 & _).
      assert (Hs : skip (concat (wind p (dw + 1)) ++ concat (wvpieces u p (dw + 1)) ++
          concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y) =
        concat (wvpieces u p (dw + 1)) ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y).
      { rewrite skip_ws_app by apply wind_ws. exact (skip_head _ _ b U' EU Hb1). }
      rewrite (jf_cont_items (jfl sm f) d false 91 _ b (U' ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y) []);
        [| exact HD | rewrite Hs, EU; reflexivity | exact Hb2].
      rewrite Hs.
      pose proof (fo_arr_loop sm p dw d y r u [] 0%nat 0%nat [] f HF eq_refl) as E.
      lapply E; [clear E; intro E|lens].
      refine (eq_trans E _). reflexivity.
  - rewrite fo_obj. apply good_obj in Hg.
    assert (HF : Forall (fun m => strok (fst m) /\ Qv sm (snd m) /\ Fv sm (snd m) /\ (depth (snd m) + S d <= MAXD)%nat) ms).
    { rewrite Forall_forall in *. intros [k v] Hv. destruct (Hg (k, v) Hv) as [H1 H2].
      split; [exact H1|]. split; [exact (rt_value sm v H2)|]. split; [exact (IH (k, v) Hv H2)|].
      pose proof (depth_member ms k v Hv). cbn [snd]. lia. }
    clear IH.
    assert (HD : (S d <= MAXD)%nat) by (cbn [depth] in Hd; lia).
    destruct f as [|f]; [lia|].
    rewrite obj_text in *. rewrite jfv_obj.
    destruct ms as [|[k u] r].
    + rewrite (jf_cont_empty (jfl sm f) d true 123 _ y []); [| exact HD | reflexivity]. reflexivity.
    + cbv beta iota in *. rewrite obj_first in *. rewrite <- !app_assoc in *.
      assert (Hs : skip (concat (wind p (dw + 1)) ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++
          concat (wgo_obj p dw 1 r) ++ concat (wind p dw) ++ 125 :: y) =
        concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++
          concat (wgo_obj p dw 1 r) ++ concat (wind p dw) ++ 125 :: y).
      { rewrite skip_ws_app by apply wind_ws. exact (skip_head _ _ 34 _ (wstr_eq k) eq_refl). }
      rewrite (jf_cont_items (jfl sm f) d true 123 _ 34 ((flat_map ech k ++ [34]) ++ wsep p ++
          concat (wvpieces u p (dw + 1)) ++ concat (wgo_obj p dw 1 r) ++ concat (wind p dw) ++ 125 :: y) []);
        [| exact HD | rewrite Hs, wstr_eq; reflexivity | cbn; lia].
      rewrite Hs.
      pose proof (fo_obj_loop sm p dw d y r k u [] 0%nat 0%nat [] f HF eq_refl) as E.
      lapply E; [clear E; intro E|lens].
      refine (eq_trans E _). reflexivity.
Qed.

(* ================================================================ the statements *)

(* pj_free's list of the tree the reader builds from the writer's text of t: fo t, as a list *)
Theorem pj_frees_wdoc_t : forall sm t p, pj_wf sm t -> pj_frees sm [] (wdoc t p) = fo t.
Proof.
  intros sm t p Hw. destruct (wf_good sm t Hw) as [Hg Hd].
  assert (Hdoc : wdoc t p = concat (wvpieces t p 0) ++ (if p then [10] else [])).
  { unfold wdoc, wdpieces. rewrite concat_app. destruct p; reflexivity. }
  unfold pj_frees. rewrite Hdoc.
  exact (fv_value sm t Hg p 0 0%nat ltac:(lia) (if p then [10] else [])
    (S (2 * length (concat (wvpieces t p 0) ++ (if p then [10] else []))))
    ltac:(destruct p; [exact eq_refl|exact I]) ltac:(lia)).
Qed.

(* in jr_run's shape: the reading of wdoc t p succeeds with the tree u; pj_free's list is fo u *)
Theorem pj_frees_wdoc : forall sm t p u tr, pj_wf sm t -> jr_run sm (wdoc t p) [] = (Some u, tr) ->
  pj_frees sm [] (wdoc t p) = fo u.
Proof.
  intros sm t p u tr Hw E. pose proof (G9 sm t Hw p) as G. unfold json_read in G. rewrite E in G.
  cbn [fst] in G. injection G as Hu. subst u. exact (pj_frees_wdoc_t sm t p Hw).
Qed.

(* the reader's live blocks after that reading: fo t, up to Permutation *)
Theorem rd_blocks_wdoc : forall sm t p, pj_wf sm t -> Permutation (rd_blocks (rtr sm [] (wdoc t p))) (fo t).
Proof.
  intros sm t p Hw. rewrite <- (pj_frees_wdoc_t sm t p Hw). apply Permutation_sym. apply pj_frees_blocks.
Qed.

(* the live list IN ORDER: the replay of ttrace u, the trace computed from u alone *)
Theorem rd_blocks_wdoc_trace : forall sm t p u tr, pj_wf sm t -> jr_run sm (wdoc t p) [] = (Some u, tr) ->
  rd_blocks (rtr sm [] (wdoc t p)) = rd_blocks (ttrace u).
Proof.
  intros sm t p u tr Hw E. pose proof (G9 sm t Hw p) as G. unfold json_read in G. rewrite E in G.
  cbn [fst] in G. injection G as Hu. subst u. unfold rtr. rewrite (G9_trace sm t Hw p). reflexivity.
Qed.

(* ================================================================ by computation, the build's strtod *)

(* strings with escapes the writer uses (quote, backslash, \n, \t, U+0001, U+001F) and does not (233, slash), an
   escaped key, a number, a literal, an empty key, nested *)
Definition ex_t : jv :=
  JObj [([34; 92], JArr [JStr [10; 1; 233]; JNum [49; 101; 53] (snd (ReaderRes.jr_strtod [49; 101; 53])); JTrue]);
        ([], JStr [47; 9; 31])].

Example pj_frees_wdoc_t_ex : pj_frees ReaderRes.jr_strtod [] (wdoc ex_t true) = fo ex_t.
Proof. vm_compute. reflexivity. Qed.

Example pj_frees_wdoc_ex :
  jr_run ReaderRes.jr_strtod (wdoc ex_t false) [] = (Some ex_t, ttrace ex_t) /\
  pj_frees ReaderRes.jr_strtod [] (wdoc ex_t false) = fo ex_t.
Proof. vm_compute. split; reflexivity. Qed.

Example rd_blocks_wdoc_ex :
  let a := rd_blocks (rtr ReaderRes.jr_strtod [] (wdoc ex_t true)) in
  forallb (fun z => Nat.eqb (count_occ Z.eq_dec a z) (count_occ Z.eq_dec (fo ex_t) z)) (a ++ fo ex_t) = true.
Proof. vm_compute. reflexivity. Qed.

(* [0,[1],2,2,2,2,2,2,2]: the outer kids block (912) sits at its last grow, before item 8; that grow dropped the
   inner array's 464 entry (the newest of value 464), so the 464 left is the outer's old entry, at the list's end *)
Definition ex_nest : jv :=
  JArr (JNum [48] (snd (ReaderRes.jr_strtod [48])) :: JArr [JNum [49] (snd (ReaderRes.jr_strtod [49]))] ::
        repeat (JNum [50] (snd (ReaderRes.jr_strtod [50]))) 7).

Example rd_blocks_wdoc_trace_ex :
  rd_blocks (rtr ReaderRes.jr_strtod [] (wdoc ex_nest true)) = rd_blocks (ttrace ex_nest) /\
  rd_blocks (ttrace ex_nest) = [18; 912; 18; 18; 18; 18; 18; 18; 18; 18; 464] /\
  tblk ex_nest = [912; 18; 464; 18; 18; 18; 18; 18; 18; 18; 18].
Proof. vm_compute. split; [|split]; reflexivity. Qed.

(* ================================================================ HBulk's list matters only up to Permutation *)

(* The ledger removes a pj_free's requests one by one (PresetReqAt.hstep, rmall); removing the first z and the first
   y gives the same list in either order, so the state after a HBulk, and whether it hits, depend on its list only up
   to Permutation. A walk that frees a tree's blocks F in its own order may therefore stand for the model's
   HBulk L whenever map size F is a Permutation of L (e.g. PresetReqAtNoMiss.pj_frees_blocks, rd_blocks_wdoc). *)

Lemma rm1_comm : forall x y s, rm1 x (rm1 y s) = rm1 y (rm1 x s).
Proof.
  intros x y s. induction s as [|z r IH]; [reflexivity|].
  cbn [rm1]. destruct (z =? y) eqn:Ey, (z =? x) eqn:Ex.
  - apply Z.eqb_eq in Ey, Ex. subst. reflexivity.
  - cbn [rm1]. rewrite Ey. reflexivity.
  - cbn [rm1]. rewrite Ex. reflexivity.
  - cbn [rm1]. rewrite Ex, Ey. rewrite IH. reflexivity.
Qed.

Lemma rmall_perm_eq : forall L L' s, Permutation L L' -> rmall L s = rmall L' s.
Proof.
  intros L L' s H. revert s. unfold rmall.
  induction H as [| z l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; intros s; cbn [fold_left].
  - reflexivity.
  - apply IH.
  - rewrite rm1_comm. reflexivity.
  - rewrite IH1. apply IH2.
Qed.

Lemma subm_perm_l : forall a a' b, Permutation a a' -> subm a b -> subm a' b.
Proof.
  intros a a' b Ha (d & Hd). exists d. apply (Permutation_trans Hd). apply Permutation_app_tail. exact Ha.
Qed.

Theorem hbulk_perm : forall L L' s es, Permutation L L' ->
  hlive_from s (HBulk L :: es) = hlive_from s (HBulk L' :: es) /\
  (okf s (HBulk L :: es) <-> okf s (HBulk L' :: es)).
Proof.
  intros L L' s es H. unfold hlive_from. cbn [fold_left okf hits hstep].
  rewrite (rmall_perm_eq L L' s H). split; [reflexivity|].
  split; intros (Hh & Hr); split; try exact Hr.
  - exact (subm_perm_l L L' s H Hh).
  - exact (subm_perm_l L' L s (Permutation_sym H) Hh).
Qed.

Example hbulk_perm_ex :
  hlive_from [464; 80; 18; 18; 7] [HBulk [18; 18; 464; 80]] = hlive_from [464; 80; 18; 18; 7] [HBulk [18; 18; 80; 464]] /\
  hlive_from [464; 80; 18; 18; 7] [HBulk [18; 18; 80; 464]] = [7].
Proof. vm_compute. split; reflexivity. Qed.

(* ================================================================ the accepted arm *)

Lemma cont_acc : forall (loop : nat -> bool -> nat -> nat -> list (list Z * jv) -> list Z -> M (jv * list Z))
  (floop : nat -> bool -> nat -> nat -> list Z -> list Z -> list bool -> list Z) d o x ok a t ok',
  (forall d' o' n cap acc af y ok1 a1 t1 ok1', loop d' o' n cap acc y ok1 = (Some a1, t1, ok1') ->
     floop d' o' n cap af y ok1 = floop d' o' n cap af y []) ->
  jr_cont loop d o x ok = (Some a, t, ok') -> jf_cont floop d o x ok = jf_cont floop d o x [].
Proof.
  intros loop floop d o x ok a t ok' H E. unfold jr_cont in E. unfold jf_cont.
  revert E. destruct (Nat.ltb MAXD (S d)); intros E; [unfold jrefuse in E; cbv beta in E; discriminate E|].
  cbv zeta in *. revert E. destruct (skip (tl x)) as [|c r]; intros E.
  - eapply H. exact E.
  - revert E. destruct (c =? closer o); intros E; [reflexivity|]. eapply H. exact E.
Qed.

(* an accepted jrv / jrl under ok: jfv / jfl under ok are as under [] *)
Lemma acc_fuel : forall sm f,
  (forall d x ok a t ok', jrv sm f d x ok = (Some a, t, ok') -> jfv sm f d x ok = jfv sm f d x []) /\
  (forall d o n cap acc af y ok a t ok', jrl sm f d o n cap acc y ok = (Some a, t, ok') ->
     jfl sm f d o n cap af y ok = jfl sm f d o n cap af y []).
Proof.
  intros sm f. induction f as [|f [IHv IHl]].
  - split.
    + intros d x ok a t ok' E. cbn [jrv] in E. unfold jrefuse in E. cbv beta in E. discriminate E.
    + intros d o n cap acc af y ok a t ok' E. cbn [jrl] in E. unfold jrefuse in E. cbv beta in E. discriminate E.
  - split.
    + intros d x ok a t ok' E.
      pose proof (agrees_some _ _ ok a t ok' (proj1 (agrees_fuel sm (S f)) d x) E) as [E0 _].
      pose proof E as Ec.
      cbn [jfv]. cbn [jrv] in E.
      revert E. destruct (skip x) as [|b y]; intros E; [reflexivity|].
      cbv beta iota in E. revert E.
      destruct (b =? 123) eqn:E1; [|destruct (b =? 91) eqn:E2]; intros E.
      * exact (cont_acc (jrl sm f) (jfl sm f) d true (b :: y) ok a t ok' IHl E).
      * exact (cont_acc (jrl sm f) (jfl sm f) d false (b :: y) ok a t ok' IHl E).
      * rewrite Ec, E0. reflexivity.
    + intros d o n cap acc af y ok a t ok' E.
      cbn [jrl] in E.
      apply jbind_some in E as (cap1 & tg & ok1 & t2 & Eg & E2 & _). cbv beta in E2.
      apply jbind_some in E2 as ([nm y1] & tn & ok2 & t3 & En & E3 & _). cbv beta iota in E3.
      apply jbind_some in E3 as ([v r] & tv & ok3 & t4 & Ev & E4 & _). cbv beta iota in E4.
      pose proof (agrees_some _ _ _ _ _ _ (agrees_grow o n cap) Eg) as [Eg0 _].
      pose proof (agrees_some _ _ _ _ _ _ (agrees_jr_name o y) En) as [En0 _].
      pose proof (agrees_some _ _ _ _ _ _ (proj1 (agrees_fuel sm f) d y1) Ev) as [Ev0 _].
      cbn [jfl]. rewrite Eg, Eg0. cbv beta iota zeta. rewrite En, En0. cbv beta iota zeta.
      rewrite (IHv d y1 ok2 _ _ _ Ev). rewrite Ev, Ev0. cbv beta iota zeta.
      revert E4. destruct (skip r) as [|c r1]; intros E4; [reflexivity|].
      revert E4. destruct (c =? 44); intros E4; [|reflexivity].
      exact (IHl _ _ _ _ _ _ _ _ _ _ _ E4).
Qed.

(* the accepted arm, keyed on the reading's own grants: pj_free's list is the one of the reading with every
   allocation granted *)
Theorem pj_frees_acc : forall sm x ok t r, jr_run sm x ok = (Some t, r) -> pj_frees sm ok x = pj_frees sm [] x.
Proof.
  intros sm x ok t r E. rewrite jr_run_eq in E. unfold pj_frees.
  destruct (jr_value sm 0 x ok) as [[[[u y]|] tr] ok'] eqn:Ev; cbn [fst post] in E; [|discriminate E].
  unfold jr_value in Ev. exact (proj1 (acc_fuel sm _) 0%nat x ok _ _ _ Ev).
Qed.

(* {"a":[1,2]}: 6 calls (the object's kids and keys, the key, the array's kids, two numbers). okk 6 refuses a 7th
   call there is not: the reading is accepted and pj_free's list is the one under []; okk 5 refuses the last call. *)
Definition ex_acc : list Z := [123; 34; 97; 34; 58; 91; 49; 44; 50; 93; 125].

Example pj_frees_acc_ex :
  ncalls ReaderRes.jr_strtod ex_acc = 6%nat /\
  match jr_run ReaderRes.jr_strtod ex_acc (okk 6) with (Some _, _) => True | (None, _) => False end /\
  pj_frees ReaderRes.jr_strtod (okk 6) ex_acc = [18; 18; 464; 18; 464; 80] /\
  pj_frees ReaderRes.jr_strtod [] ex_acc = [18; 18; 464; 18; 464; 80] /\
  fst (jr_run ReaderRes.jr_strtod ex_acc (okk 5)) = None.
Proof. vm_compute. split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; reflexivity. Qed.

(* ================================================================ jfv / jfl: the fuel does not matter once it covers x *)

(* The twins of PjGrammar.fuel_mono / jr_value_fuel / jr_items_fuel for pj_free's list: with fuel at least 2 |x| + 1
   (a value) or 2 |y| + 2 (a container's items), more fuel gives the same list. A walk that composes parse_value and
   parse_items across a nested call meets the grammar's fuel shift, and these let it state each list at the call's own
   fuel (PRH_FnParse's tparse_items_specX, :132: jf_cont (jfl sm (2 * length x + 2)) d o x ok). *)

Local Ltac jf_dstr := repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  end.

Lemma jf_fuel_mono : forall sm f,
  (forall d x f' ok, (2 * length x + 1 <= f)%nat -> (f <= f')%nat -> jfv sm f' d x ok = jfv sm f d x ok) /\
  (forall d o n cap af y f' ok, (2 * length y + 2 <= f)%nat -> (f <= f')%nat ->
     jfl sm f' d o n cap af y ok = jfl sm f d o n cap af y ok).
Proof.
  intros sm. induction f as [|f [IHv IHl]].
  - split; intros; lia.
  - split.
    + intros d x f' ok H1 H2. destruct f' as [|f']; [lia|]. cbn [jfv].
      pose proof (skip_len x) as Hs.
      destruct (skip x) as [|b y] eqn:Ex; [reflexivity|].
      cbn [length] in Hs.
      assert (Hc : forall o, jf_cont (jfl sm f') d o (b :: y) ok = jf_cont (jfl sm f) d o (b :: y) ok).
      { intros o. unfold jf_cont. cbn [tl]. destruct (Nat.ltb MAXD (S d)); [reflexivity|].
        pose proof (skip_len y) as Hy.
        destruct (skip y) as [|c r] eqn:Ey.
        - apply IHl; cbn [length]; lia.
        - destruct (c =? closer o); [reflexivity|]. apply IHl; lia. }
      destruct (b =? 123); [apply Hc|].
      destruct (b =? 91); [apply Hc|].
      rewrite (proj1 (fuel_mono sm (S f)) d x (S f') ok) by lia. reflexivity.
    + intros d o n cap af y f' ok H1 H2. destruct f' as [|f']; [lia|]. cbn [jfl].
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1]; [|reflexivity]. cbv beta iota.
      pose proof (jr_name_spec o y ok1) as Hn.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2] eqn:En; [|reflexivity]. cbv beta iota.
      assert (Hy1 : (length y1 <= length y)%nat) by (destruct o; cbv iota in Hn; jf_dstr; subst; lia).
      rewrite (IHv d y1 f' ok2) by lia.
      rewrite (proj1 (fuel_mono sm f) d y1 f' ok2) by lia.
      pose proof (proj1 (spec_fuel sm f) d y1 ok2) as Hv.
      destruct (jrv sm f d y1 ok2) as [[[[v r]|] tv] ok3] eqn:Ev; [|reflexivity]. cbv beta iota.
      unfold vspec in Hv. cbn [fst snd] in Hv. destruct Hv as (_ & _ & Hv).
      destruct (Hv v r eq_refl) as (Hr & _ & _).
      pose proof (skip_len r) as Hsr.
      destruct (skip r) as [|c r1] eqn:Er; [reflexivity|]. cbn [length] in Hsr.
      destruct (c =? 44); [|reflexivity].
      rewrite (IHl d o (S n) cap1 _ r1 f' ok3) by lia.
      reflexivity.
Qed.

Lemma jfv_fuel : forall sm f d x ok, (2 * length x + 1 <= f)%nat -> jfv sm f d x ok = jfv sm (S (2 * length x)) d x ok.
Proof. intros sm f d x ok H. apply (proj1 (jf_fuel_mono sm (S (2 * length x)))); lia. Qed.

Lemma jf_items_fuel : forall sm f d o x ok, (2 * length x + 2 <= f)%nat ->
  jf_cont (jfl sm f) d o x ok = jf_cont (jfl sm (2 * length x + 2)) d o x ok.
Proof.
  intros sm f d o x ok H. unfold jf_cont.
  destruct (Nat.ltb MAXD (S d)); [reflexivity|].
  pose proof (skip_len (tl x)) as Hs.
  assert (Ht : (length (tl x) <= length x)%nat) by (destruct x; cbn [tl length]; lia).
  destruct (skip (tl x)) as [|c r] eqn:Ey.
  - apply (proj2 (jf_fuel_mono sm (2 * length x + 2))); cbn [length]; lia.
  - destruct (c =? closer o); [reflexivity|].
    apply (proj2 (jf_fuel_mono sm (2 * length x + 2))); lia.
Qed.

(* pj_frees at a larger fuel, and a container's list at its call's fuel and at the canonical one *)
Example jf_fuel_ex :
  jfv ReaderRes.jr_strtod 40 0 ex_acc [] = pj_frees ReaderRes.jr_strtod [] ex_acc /\
  jf_cont (jfl ReaderRes.jr_strtod 30) 0 true ex_acc [] =
    jf_cont (jfl ReaderRes.jr_strtod (2 * length ex_acc + 2)) 0 true ex_acc [].
Proof. vm_compute. split; reflexivity. Qed.
