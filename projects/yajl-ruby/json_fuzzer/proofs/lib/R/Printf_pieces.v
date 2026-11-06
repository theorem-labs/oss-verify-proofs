(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  ITree.impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> ITree.impl segs atn t Q' ms.
Proof.
  intros segs node R atn t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. exact (HQ r).
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
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

  (* [comment removed for export] *)
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
    destruct a as [str|i|u|dd].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outs; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outs; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End RC__1.
Ltac lhs_cbvs := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces] in l in change l with l' end.
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zlength_nonneg' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

End RC__2.
Ltac ppl_step := rewrite ppl_unfold; match goal with |- ?l = _ => let l' := eval cbv -[printf_pieces_loop conv_pieces] in l in change l with l' end.

Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma digits_aux_S : forall f b d y acc,
  digits_aux (S f) b d y acc = if y =? 0 then acc else digits_aux f b d (y / b) (d (y mod b) :: acc).
Proof. reflexivity. Qed.
Lemma digits_aux_len : forall f b d y acc, (length acc <= length (digits_aux f b d y acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros b d y acc; [cbn; lia|]. rewrite digits_aux_S.
  destruct (y =? 0); [cbn; lia|]. specialize (IH b d (y / b) (d (y mod b) :: acc)). cbn [length] in IH. lia.
Qed.
Lemma dec_digits_nonnil : forall x, x <> 0 -> (1 <= length (dec_digits x) <= 20)%nat.
Proof.
  intros x Hx. unfold dec_digits. change 20%nat with (S 19) at 1. rewrite digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. pose proof (digits_aux_len 19 10 (fun v => 48 + v) (x / 10) [48 + x mod 10]) as L. cbn [length] in L. lia.
Qed.

Definition cnt_emit_d (rc : Z) : Z :=
  if rc =? 0 then 2 else if rc <? 0 then zlength (dec_digits ((- rc) mod 2^64)) + 2 else zlength (dec_digits rc) + 1.

Lemma conv_pieces_emit_d : forall rc cnt, -2^31 <= rc < 2^31 -> 0 <= cnt <= 1000 ->
  conv_pieces cnt (mkDir 0 0 (-1) false 100 T_INT) (PA_i rc) =
  Some (if rc =? 0 then [[]; [48]; []] else if rc <? 0 then [[45]; dec_digits ((- rc) mod 2^64)] else [[]; dec_digits rc],
        cnt + cnt_emit_d rc - 1).
Proof.
  intros rc cnt Hrc Hc. unfold conv_pieces, cnt_emit_d. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota. change (negb (T_INT =? T_INT)) with false. cbv iota.
  change (Z.land 0 MARK_POS =? 0) with true. change (Z.land 0 PAD_POS =? 0) with true. cbn [negb].
  unfold INTMAX_MAX.
  assert (TP : forall cnt' (prefix body : list Z), 0 <= cnt' <= 1000 -> (length prefix <= 1)%nat -> (length body <= 20)%nat ->
    tail_pieces cnt' 0 0 (Z.max (-1) (zlength body + (if zlength body =? 0 then 1 else 0))) prefix body
    = Some ((if zlength body =? 0 then [prefix; [48]; []] else [prefix; body]), cnt' + zlength prefix + Z.max 1 (zlength body))).
  { clear. intros cnt' prefix body Hc Hp Hb. unfold tail_pieces, pad_pieces. unfold zlength in *.
    pose proof (Nat2Z.is_nonneg (length prefix)) as P0.
    replace (negb (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)) with false by reflexivity.
    replace (negb (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0)) with true by reflexivity.
    replace (negb (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0)) with true by reflexivity.
    cbn [orb].
    destruct (Z.eqb_spec (Z.of_nat (length body)) 0) as [B0|B1].
    - destruct body as [|bb body']; [| exfalso; cbn [length] in B0; lia]. cbn [length]. change (Z.of_nat 0) with 0. replace (Z.max (-1) (0 + 1)) with 1 by lia. rewrite (Z.max_l 1 0) by lia.
      destruct (Z.ltb_spec (INT_MAX - Z.of_nat (length prefix)) 1); [unfold INT_MAX in *; exfalso; lia|].
      replace (Z.max 0 (Z.of_nat (length prefix) + 1)) with (Z.of_nat (length prefix) + 1) by lia.
      destruct (Z.ltb_spec (INT_MAX - cnt') (Z.of_nat (length prefix) + 1)); [unfold INT_MAX in *; exfalso; lia|].
      rewrite !Z.leb_refl. change (1 <=? 0) with false. change (256 <=? 1 - 0) with false. cbv iota.
      change (zrepeat 48 (1 - 0)) with [48]. cbn [app]. f_equal. f_equal. lia.
    - replace (Z.max (-1) (Z.of_nat (length body) + 0)) with (Z.of_nat (length body)) by lia. rewrite Z.max_id.
      destruct (Z.ltb_spec (INT_MAX - Z.of_nat (length prefix)) (Z.of_nat (length body))); [unfold INT_MAX in *; exfalso; lia|].
      replace (Z.max 0 (Z.of_nat (length prefix) + Z.of_nat (length body))) with (Z.of_nat (length prefix) + Z.of_nat (length body)) by lia.
      destruct (Z.ltb_spec (INT_MAX - cnt') (Z.of_nat (length prefix) + Z.of_nat (length body))); [unfold INT_MAX in *; exfalso; lia|].
      rewrite !Z.leb_refl. cbv iota. cbn [app]. f_equal. f_equal. lia. }
  destruct (Z.eqb_spec rc 0) as [->|NZ].
  - change (0 mod 2^64) with 0. change (9223372036854775807 <? 0) with false. cbv iota.
    unfold int_pieces. cbn [andb]. change (dec_digits 0) with (@nil Z).
    pose proof (TP cnt [] [] Hc ltac:(cbn; lia) ltac:(cbn; lia)) as E.
    change (zlength (@nil Z)) with 0 in *. change (if 0 =? 0 then 1 else 0) with 1 in E. change (0 =? 0) with true in E. cbv iota in E.
    change ((0 =? 0) && (-1 =? 0)) with false. change (if 0 =? 0 then 1 else 0) with 1. cbv iota.
    rewrite E. f_equal. f_equal. lia.
  - destruct (Z.ltb_spec rc 0) as [NEG|POS].
    + assert (EM : rc mod 2^64 = rc + 2^64) by (rewrite <- (Z.mod_add rc 1 (2^64)) by lia; replace (rc + 1 * 2^64) with (rc + 2^64) by lia; apply Z.mod_small; lia). rewrite EM.
      destruct (Z.ltb_spec 9223372036854775807 (rc + 2^64)); [|exfalso; lia].
      replace (- (rc + 2^64)) with (-rc + (-1) * 2^64) by lia. rewrite Z.mod_add by lia.
      rewrite (Z.mod_small (-rc)) by lia.
      pose proof (dec_digits_nonnil (-rc) ltac:(lia)) as L.
      unfold int_pieces. cbn [andb].
      replace (- rc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      pose proof (TP cnt [45] (dec_digits (-rc)) Hc ltac:(cbn; lia) ltac:(lia)) as E.
      replace (zlength (dec_digits (- rc)) =? 0) with false in E by (symmetry; apply Z.eqb_neq; unfold zlength; lia).
      rewrite E. f_equal. f_equal. unfold zlength in *. cbn [length]. lia.
    + rewrite (Z.mod_small rc) by lia.
      destruct (Z.ltb_spec 9223372036854775807 rc); [exfalso; lia|].
      pose proof (dec_digits_nonnil rc ltac:(lia)) as L.
      unfold int_pieces. cbn [andb].
      replace (rc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      pose proof (TP cnt [] (dec_digits rc) Hc ltac:(cbn; lia) ltac:(lia)) as E.
      replace (zlength (dec_digits rc) =? 0) with false in E by (symmetry; apply Z.eqb_neq; unfold zlength; lia).
      rewrite E. f_equal. f_equal. unfold zlength in *. cbn [length]. lia.
Qed.

Lemma cnt_emit_d_range : forall rc, -2^31 <= rc < 2^31 -> 2 <= cnt_emit_d rc <= 22.
Proof.
  intros rc H. unfold cnt_emit_d, zlength. destruct (Z.eqb_spec rc 0); [lia|].
  destruct (Z.ltb_spec rc 0).
  - replace (- rc mod 2^64) with (-rc) by (symmetry; apply Z.mod_small; lia).
    pose proof (dec_digits_nonnil (-rc) ltac:(lia)). lia.
  - pose proof (dec_digits_nonnil rc ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma printf_pieces_emit : forall rc, -2^31 <= rc < 2^31 ->
  printf_pieces FMT_emit [PA_i rc] = Some (pieces_emit_d rc, cnt_emit_d rc).
Proof.
  intros rc Hrc. pose proof (cnt_emit_d_range rc Hrc) as HB. unfold printf_pieces.
  change (Datatypes.length FMT_emit) with 4%nat.
  ppl_step. change Printf_model.T_INT with T_INT. rewrite conv_pieces_emit_d by lia. cbv beta iota.
  remember (cnt_emit_d rc) as K eqn:EK.
  rewrite (ppl_noargs_shift 3 [10; 0] (0 + K - 1) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
  unfold pieces_emit_d. replace (0 + K - 1 + 1) with K by lia.
  destruct (rc =? 0); [reflexivity|]. destruct (rc <? 0); reflexivity.
Qed.

Lemma printf_pieces_usage : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_usage) with 17%nat.
  ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 15 [32; 73; 78; 80; 85; 84; 10; 0] (7 + zlength s) [[32; 73; 78; 80; 85; 84; 10]] 7 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_usage. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_cannot_open : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_cannot_open) with 21%nat.
  ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 19 [10; 0] (17 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_cannot_open. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_read_error : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_read_error) with 23%nat.
  ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 21 [10; 0] (19 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_read_error. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_too_big : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.

Lemma pass1_ok_emit : pass1_ok FMT_emit = true. Proof. reflexivity. Qed.
Lemma pass1_ok_usage : pass1_ok FMT_usage = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_cannot_open : pass1_ok FMT_cannot_open = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_read_error : pass1_ok FMT_read_error = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_too_big : pass1_ok FMT_too_big = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_s : forall fmt s, In fmt [FMT_emit; FMT_usage; FMT_cannot_open; FMT_read_error] ->
  fp_calls (Datatypes.length fmt) fmt [PA_s s] = [].
Proof. intros fmt s [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity. Qed.
Lemma fp_calls_too_big : fp_calls (Datatypes.length FMT_too_big) FMT_too_big [PA_u 67108864] = [].
Proof. vm_compute. reflexivity. Qed.
End RC__3.
