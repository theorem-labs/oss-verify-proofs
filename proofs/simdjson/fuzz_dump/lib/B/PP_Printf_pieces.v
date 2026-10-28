(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import PrintfModelA PrintfFormatsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Printf_mlib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  ITree.impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> ITree.impl segs atn t Q' ms.
Proof.
  intros segs node R atn t. induction t as [r|n k IH|kc IHc]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. exact (HQ r).
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
  - destruct H as [z H]. exists z. eapply IHc; [exact H | exact HQ].
Qed.
Lemma implM_post_evt : forall segs {St A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  Monad.implM segs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt segs (Q' a s') ms') -> Monad.implM segs c s Q' ms.
Proof.
  intros segs St A c s Q Q' ms H HQ. unfold Monad.implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I | apply HQ].
Qed.

Section Outs.
  Variable segs : list Segment.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
  Local Notation implM := (Monad.implM segs).

  Fixpoint outsk {B} (ps : list (list Z)) (k : M St B) : M St B :=
    match ps with
    | [] => k
    | p :: ps' => OUT p ;;; outsk ps' k
    end.

  Lemma outsk_app : forall {B} ps qs (k : M St B), outsk (ps ++ qs) k = outsk ps (outsk qs k).
  Proof. induction ps as [|p ps IH]; intros qs k; [reflexivity|]. cbn [outsk app]. rewrite IH. reflexivity. Qed.

  Lemma outsk_mono : forall {B} ps (k1 k2 : M St B) Q,
    (forall s ms, implM k1 s Q ms -> implM k2 s Q ms) ->
    forall s ms, implM (outsk ps k1) s Q ms -> implM (outsk ps k2) s Q ms.
  Proof.
    induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
    eapply implM_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
  Qed.

  Lemma mpad_outs : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
    pad_pieces c w l fl = Some pp ->
    implM (mbind (mpad OUT c w l fl) K) s Q ms -> implM (outsk pp (K tt)) s Q ms.
  Proof.
    intros B c w l fl pp K s Q ms P H. unfold mpad, pad_pieces in *.
    destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
    - inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H.
    - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [outsk].
      eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
  Qed.

  Lemma out_outs : forall {B} p (K : unit -> M St B) s Q ms,
    implM (mbind (OUT p) K) s Q ms -> implM (outsk [p] (K tt)) s Q ms.
  Proof. intros B p K s Q ms H. cbn [outsk]. eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'. Qed.

  Lemma conv_tail_outs : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
    tail_pieces cnt fl w p prefix body = Some (ps, r) ->
    implM (mbind (conv_tail OUT cnt fl w p prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt fl w p prefix body ps r K s Q ms T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta in H.
    destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
    destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
    destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
    destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
    destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
    destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
    inversion T; subst. clear T.
    match goal with |- implM (outsk ?L (K ?rr)) _ _ _ =>
      replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
        by (rewrite ?outsk_app; cbn [outsk]; rewrite ?outsk_app; cbn [outsk]; reflexivity) end.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P1) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s1 ms1 H.
    apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x2 s2 ms2 H.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P2) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s3 ms3 H.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P3) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s4 ms4 H.
    apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x5 s5 ms5 H.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P4) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s6 ms6 H.
    apply implM_ret_l_rev in H. exact H.
  Qed.

  Lemma conv_int_outs : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
    int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
    implM (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
    destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
    destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs; eassumption.
  Qed.

  Lemma conv_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
    conv_pieces cnt d a = Some (ps, r) ->
    implM (mbind (conv OUT OUTFP cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
    destruct a as [str| |i|u|u|dd].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outs; eassumption.
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
      eapply conv_tail_outs; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outs; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
    - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
      destruct (d_t d =? 117); [|discriminate]. eapply conv_int_outs; eassumption.
    - discriminate.
  Qed.

  Lemma printf_loop_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
    printf_pieces_loop fuel s args cnt = Some (ps, r) ->
    implM (mbind (printf_loop OUT OUTFP fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
  Proof.
    induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms P H; [discriminate|].
    cbn [printf_pieces_loop] in P. cbn [printf_loop] in H.
    destruct s as [|c s1]; [discriminate|].
    destruct (c =? 0). { inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H. }
    cbv zeta in P. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
    destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
    destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
    destruct (0 <? zlength lit).
    - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
      destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
      inversion P; subst. clear P. cbn [outsk].
      apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      eapply IH; [exact R | exact H'].
    - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P.
      match goal with |- implM (outsk ?L (k ?rr)) _ _ _ =>
        replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
      cbn [outsk].
      apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      apply implM_assoc_rev in H'. apply (conv_outs _ _ _ _ _ _ _ _ _ C) in H'.
      eapply outsk_mono; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
  Qed.

  Theorem printf_model_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
    printf_pieces fmt args = Some (ps, r) ->
    implM (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
  Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loop_outs; [exact P | exact H]. Qed.
End Outs.

Ltac lhs_cbvs := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces] in l in change l with l' end.
Lemma zlength_nonneg' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma conv_pieces_s : forall cnt s, 0 <= cnt -> zlength s < INT_MAX - cnt ->
  conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} (PA_s s)
  = Some ([[]; s], cnt + zlength s).
Proof.
  intros cnt s Hc Hs. pose proof (zlength_nonneg' s) as H0.
  unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_PTR Pos.eqb andb Z.ltb Z.compare].
  replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; lia).
  unfold tail_pieces. cbv zeta. rewrite firstn_all2 by (unfold zlength; lia).
  change (zlength (@nil Z)) with 0.
  replace (Z.max (zlength s) (zlength s)) with (zlength s) by lia.
  replace (INT_MAX - 0 <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.max 0 (0 + zlength s)) with (zlength s) by lia.
  replace (INT_MAX - cnt <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces.
  replace (zlength s <=? 0 + zlength s) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ].
  reflexivity.
Qed.

Lemma ppl_unfold : forall fuel s args cnt,
  printf_pieces_loop (S fuel) s args cnt =
    match s with
    | [] => None
    | c :: _ =>
      if c =? 0 then Some ([], cnt) else
      let lit := lit_run s in
      let l := zlength lit in
      let s1 := skipn (Datatypes.length lit) s in
      match s1 with
      | [] => None
      | c1 :: s2 =>
        if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
        else if 0 <? l then
          (if INT_MAX - cnt <? l then None
           else match printf_pieces_loop fuel s1 args (cnt + l) with Some (ps, r) => Some (lit :: ps, r) | None => None end)
        else
          match parse_dir s2, args with
          | Some (d, s3), a :: args' =>
              match conv_pieces cnt d a with
              | Some (ps1, cnt') =>
                  match printf_pieces_loop fuel s3 args' cnt' with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end
              | None => None
              end
          | _, _ => None
          end
      end
    end.
Proof. reflexivity. Qed.

Lemma ppl_noargs_shift_gen : forall fuel s c0 ps r,
  printf_pieces_loop fuel s [] c0 = Some (ps, r) ->
  c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_pieces_loop fuel s [] (c0 + k) = Some (ps, r + k)).
Proof.
  induction fuel as [|fuel IH]; intros s c0 ps r P; [discriminate|].
  rewrite ppl_unfold in P. setoid_rewrite ppl_unfold.
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. split; [lia|]. intros k _ _. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg' lit).
  destruct (0 <? zlength lit).
  - destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) [] (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. destruct (IH _ _ _ _ R) as [LE SH].
    split; [lia|]. intros k Hk Hr.
    replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; discriminate.
Qed.

Lemma ppl_noargs_shift : forall fuel s cnt ps r,
  printf_pieces_loop fuel s [] 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
  printf_pieces_loop fuel s [] cnt = Some (ps, cnt + r).
Proof.
  intros fuel s cnt ps r P Hc Hr. destruct (ppl_noargs_shift_gen _ _ _ _ _ P) as [_ SH].
  rewrite <- (Z.add_0_l cnt). rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma lit_run_app : forall lit rest,
  Forall (fun c => c <> 0 /\ c <> 37) lit ->
  match rest with [] => True | c1 :: _ => c1 = 0 \/ c1 = 37 end ->
  lit_run (lit ++ rest) = lit.
Proof.
  induction lit as [|c lit IH]; intros rest HF HR; cbn.
  - destruct rest as [|c1 r]; [reflexivity|]. cbn. destruct HR as [-> | ->]; reflexivity.
  - apply Forall_cons_iff in HF. destruct HF as [[H0 H37] HF].
    replace ((c =? 0) || (c =? 37))%bool with false.
    2:{ symmetry. apply Bool.orb_false_intro; apply Z.eqb_neq; assumption. }
    f_equal. apply IH; assumption.
Qed.

Lemma ppl_lit_cons : forall fuel lit c1 s2 args cnt,
  lit <> [] -> Forall (fun c => c <> 0 /\ c <> 37) lit ->
  (c1 = 0 \/ (c1 = 37 /\ match s2 with [] => False | c2 :: _ => c2 <> 37 end)) ->
  zlength lit <= INT_MAX - cnt ->
  printf_pieces_loop (S fuel) (lit ++ c1 :: s2) args cnt
  = match printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit) with
    | Some (ps, r) => Some (lit :: ps, r) | None => None end.
Proof.
  intros fuel lit c1 s2 args cnt NE HF HC HL.
  rewrite ppl_unfold. destruct lit as [|c0 lit']; [contradiction|]. cbn [app].
  pose proof HF as HF0. apply Forall_cons_iff in HF. destruct HF as [[H0 H37] HF].
  replace (c0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  cbv zeta.
  change (c0 :: lit' ++ c1 :: s2) with ((c0 :: lit') ++ c1 :: s2).
  rewrite (lit_run_app (c0 :: lit') (c1 :: s2) HF0 ltac:(cbn; lia)).
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app].
  replace ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool with false.
  2:{ symmetry. destruct HC as [-> | [-> HS]]; [reflexivity|]. cbn [Z.eqb Pos.eqb andb]. destruct s2 as [|c2 ?]; [contradiction|]. apply Z.eqb_neq. exact HS. }
  replace (0 <? zlength (c0 :: lit')) with true by (symmetry; apply Z.ltb_lt; unfold zlength; cbn; lia).
  replace (INT_MAX - cnt <? zlength (c0 :: lit')) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Ltac ppl_step := rewrite ppl_unfold; match goal with |- ?l = _ => let l' := eval cbv -[printf_pieces_loop conv_pieces] in l in change l with l' end.

Lemma printf_pieces_emit0 : printf_pieces FMT_emit [PA_i 0] = Some (pieces_emit_0, 2).
Proof. vm_compute. reflexivity. Qed.

Lemma printf_pieces_usage : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_usage) with 17%nat.
  ppl_step. ppl_step. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 15 [32; 73; 78; 80; 85; 84; 10; 0] (7 + zlength s) [[32; 73; 78; 80; 85; 84; 10]] 7 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_usage. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_cannot_open : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_cannot_open) with 21%nat.
  ppl_step. ppl_step. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 19 [10; 0] (17 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_cannot_open. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_read_error : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_read_error) with 23%nat.
  ppl_step. ppl_step. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 21 [10; 0] (19 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_read_error. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_too_big : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.

Lemma printf_pieces_unreached : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_unreached [PA_s s] = Some (pieces_precond_reached s, 34 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_unreached) with 37%nat.
  ppl_step. ppl_step. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 35 [10; 0] (33 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_precond_reached. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_precond : forall x fn, zlength x < 2^20 -> zlength fn < 2^20 ->
  printf_pieces FMT_precond [PA_s x; PA_s fn] = Some (pieces_precond_fail x fn, 25 + zlength x + zlength fn).
Proof.
  intros x fn Hx Hf. pose proof (zlength_nonneg' x) as H0. pose proof (zlength_nonneg' fn) as H1. unfold printf_pieces.
  change (Datatypes.length FMT_precond) with 30%nat.
  ppl_step. ppl_step. rewrite conv_pieces_s by (unfold INT_MAX; lia).
  change [39; 32; 110; 111; 116; 32; 116; 114; 117; 101; 32; 97; 116; 32; 37; 115; 10; 0]
    with ([39; 32; 110; 111; 116; 32; 116; 114; 117; 101; 32; 97; 116; 32] ++ 37 :: [115; 10; 0]).
  rewrite ppl_lit_cons; [ | discriminate | repeat (constructor; [lia|]); apply Forall_nil | right; split; [reflexivity | cbn; lia] | replace (zlength [39; 32; 110; 111; 116; 32; 116; 114; 117; 101; 32; 97; 116; 32]) with 14 by reflexivity; unfold INT_MAX; lia ].
  change (zlength [39; 32; 110; 111; 116; 32; 116; 114; 117; 101; 32; 97; 116; 32]) with 14.
  remember (10 + zlength x + 14) as c1 eqn:Ec1.
  ppl_step. rewrite conv_pieces_s by (unfold INT_MAX; lia).
  rewrite (ppl_noargs_shift 26 [10; 0] (c1 + zlength fn) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
  unfold pieces_precond_fail. subst c1. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma tail_pieces_plain : forall cnt p body, 0 <= cnt -> 1 <= zlength body -> p <= zlength body -> cnt + zlength body <= INT_MAX ->
  tail_pieces cnt 0 0 p [] body = Some ([[]; body], cnt + zlength body).
Proof.
  intros cnt p body Hc Hb Hp HI. unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  replace (Z.max p (zlength body)) with (zlength body) by lia.
  replace (INT_MAX - 0 <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.max 0 (0 + zlength body)) with (zlength body) by lia.
  replace (INT_MAX - cnt <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces.
  replace (zlength body <=? 0 + zlength body) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ]. reflexivity.
Qed.
Lemma tail_pieces_zero1 : forall cnt, 0 <= cnt -> cnt + 1 <= INT_MAX ->
  tail_pieces cnt 0 0 1 [] [] = Some ([[]; [48]; []], cnt + 1).
Proof.
  intros cnt Hc HI. unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  change (Z.max 1 0) with 1. change (Z.max 0 (0 + 1)) with 1.
  replace (INT_MAX - 0 <? 1) with false by reflexivity.
  replace (INT_MAX - cnt <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces. cbn. reflexivity.
Qed.

Lemma conv_pieces_zu : forall cnt u, 0 <= cnt -> 0 <= u < 2^64 -> cnt + 21 <= INT_MAX ->
  conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 117; d_ty := T_SIZET |} (PA_z u)
  = Some ((if u =? 0 then [[]; [48]; []] else [[]; dec_digits u]), cnt + (if u =? 0 then 1 else zlength (dec_digits u))).
Proof.
  intros cnt u Hc Hu HI. pose proof (dec_digits_zlength u) as DL.
  destruct (Z.eqb_spec u 0) as [->|NZ].
  - unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_SIZET Pos.eqb andb Z.ltb Z.compare].
    unfold int_pieces. cbn [andb Z.eqb]. rewrite dec_digits_0. change (zlength (@nil Z)) with 0.
    change (Z.max (-1) (0 + 1)) with 1. apply tail_pieces_zero1; lia.
  - replace (u =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.land LEFT_ADJ negb T_SIZET Pos.eqb andb Z.ltb Z.compare].
    change (117 =? 117) with true. change (T_SIZET =? T_SIZET) with true. cbn [negb andb]. cbv iota. cbv beta iota.
    unfold int_pieces. cbn [andb].
    replace (u =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    pose proof (dec_digits_nz u ltac:(lia)) as NE.
    assert (L1 : 1 <= zlength (dec_digits u)) by (destruct (dec_digits u); [contradiction | unfold zlength; cbn; lia]).
    rewrite Z.add_0_r. change (20 =? 20) with true. change (0 =? 0) with true. cbv iota. cbv beta iota.
    rewrite tail_pieces_plain by lia. reflexivity.
Qed.

Lemma conv_pieces_sn : forall cnt, 0 <= cnt -> cnt + 6 <= INT_MAX ->
  conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} PA_sn
  = Some ([[]; NULLSTR], cnt + 6).
Proof.
  intros cnt Hc HI.
  unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_PTR Pos.eqb andb Z.ltb Z.compare].
  change (zlength NULLSTR) with 6 in *. change (INT_MAX <=? 6) with false. cbv iota.
  change (firstn (Z.to_nat 6) NULLSTR) with NULLSTR.
  rewrite (tail_pieces_plain cnt 6 NULLSTR) by (change (zlength NULLSTR) with 6; lia). reflexivity.
Qed.

Lemma printf_pieces_msg_gen : forall (a1 : parg) (f : list Z) n msg,
  (a1 = PA_s f \/ (a1 = PA_sn /\ f = NULLSTR)) ->
  zlength f < 2^20 -> 0 <= n < 2^64 -> zlength msg < 2^20 ->
  printf_pieces FMT_msg [a1; PA_z n; PA_s msg]
  = Some (pieces_msg f n msg, zlength f + 1 + (if n =? 0 then 1 else zlength (dec_digits n)) + 2 + zlength msg).
Proof.
  intros a1 f n msg Ha Hf Hn Hm. pose proof (zlength_nonneg' f) as H0. pose proof (zlength_nonneg' msg) as H1.
  pose proof (dec_digits_zlength n) as DL.
  unfold printf_pieces. change (Datatypes.length FMT_msg) with 11%nat.
  ppl_step.
  assert (C1 : conv_pieces 0 {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} a1 = Some ([[]; f], 0 + zlength f)).
  { destruct Ha as [-> | [-> ->]]; [apply conv_pieces_s; unfold INT_MAX; lia | apply conv_pieces_sn; unfold INT_MAX; lia]. }
  cbv delta [T_PTR] in C1. rewrite C1. clear C1.
  remember (0 + zlength f) as c1 eqn:Ec1.
  change [58; 37; 122; 117; 58; 32; 37; 115; 0] with ([58] ++ 37 :: [122; 117; 58; 32; 37; 115; 0]).
  rewrite ppl_lit_cons; [ | discriminate | repeat (constructor; [lia|]); apply Forall_nil | right; split; [reflexivity | cbn; lia] | change (zlength [58]) with 1; unfold INT_MAX; lia ].
  change (zlength [58]) with 1.
  remember (c1 + 1) as c2 eqn:Ec2.
  ppl_step. pose proof (conv_pieces_zu c2 n ltac:(lia) Hn ltac:(unfold INT_MAX; lia)) as C2. cbv delta [T_SIZET] in C2. rewrite C2. clear C2.
  remember (if n =? 0 then [[]; [48]; []] else [[]; dec_digits n]) as P2 eqn:EP2.
  remember (if n =? 0 then 1 else zlength (dec_digits n)) as l2 eqn:El2.
  assert (Hl2 : 0 <= l2 <= 20) by (subst l2; destruct (n =? 0); lia).
  remember (c2 + l2) as c3 eqn:Ec3.
  change [58; 32; 37; 115; 0] with ([58; 32] ++ 37 :: [115; 0]).
  rewrite ppl_lit_cons; [ | discriminate | repeat (constructor; [lia|]); apply Forall_nil | right; split; [reflexivity | cbn; lia] | change (zlength [58; 32]) with 2; unfold INT_MAX; lia ].
  change (zlength [58; 32]) with 2.
  remember (c3 + 2) as c4 eqn:Ec4.
  ppl_step. pose proof (conv_pieces_s c4 msg ltac:(lia) ltac:(unfold INT_MAX; lia)) as C3. cbv delta [T_PTR] in C3. rewrite C3. clear C3.
  rewrite (ppl_noargs_shift 6 [0] (c4 + zlength msg) [] 0 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
  cbn [app]. unfold pieces_msg. subst c4 c3 c2 c1.
  f_equal. f_equal; [|lia]. subst P2. destruct (n =? 0); reflexivity.
Qed.

Lemma pass1_ok_emit : pass1_ok FMT_emit = true. Proof. reflexivity. Qed.
Lemma pass1_ok_usage : pass1_ok FMT_usage = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_cannot_open : pass1_ok FMT_cannot_open = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_read_error : pass1_ok FMT_read_error = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_too_big : pass1_ok FMT_too_big = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_precond : pass1_ok FMT_precond = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_unreached : pass1_ok FMT_unreached = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_msg : pass1_ok FMT_msg = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_s : forall fmt s, In fmt [FMT_usage; FMT_cannot_open; FMT_read_error; FMT_unreached] ->
  fp_calls (Datatypes.length fmt) fmt [PA_s s] = [].
Proof. intros fmt s [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity. Qed.
Lemma fp_calls_emit : forall i, fp_calls (Datatypes.length FMT_emit) FMT_emit [PA_i i] = [].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma fp_calls_too_big : fp_calls (Datatypes.length FMT_too_big) FMT_too_big [PA_u 67108864] = [].
Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_precond : forall x fn, fp_calls (Datatypes.length FMT_precond) FMT_precond [PA_s x; PA_s fn] = [].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma fp_calls_msg : forall f n msg, fp_calls (Datatypes.length FMT_msg) FMT_msg [PA_s f; PA_z n; PA_s msg] = [].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma fp_calls_msg_null : forall n msg, fp_calls (Datatypes.length FMT_msg) FMT_msg [PA_sn; PA_z n; PA_s msg] = [].
Proof. intros. vm_compute. reflexivity. Qed.
