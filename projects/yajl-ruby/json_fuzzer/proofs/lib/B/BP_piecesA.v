(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages ExecA ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_pieces.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BP_mlibA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma implA_post_evtA : forall segs {node R} (atn : (acc -> Prop) -> node -> machine_state -> Prop) P (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  implA segs atn P t Q ms -> (forall r ms', Q r ms' -> evtA segs P (Q' r) ms') -> implA segs atn P t Q' ms.
Proof.
  intros segs node R atn P t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evtA_cut; [exact H|]. exact (HQ r).
  - eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
Qed.
Lemma implMA_post_evt : forall segs P {St A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implMA segs P c s Q ms -> (forall a s' ms', Q a s' ms' -> evtA segs P (Q' a s') ms') -> implMA segs P c s Q' ms.
Proof.
  intros segs P St A c s Q Q' ms H HQ. unfold implMA in *. eapply implA_post_evtA; [exact H|].
  intros [|[a s']] ms'; cbn; [intros _; apply evtA_done; exact I | apply HQ].
Qed.

Section OutsA.
  Variable segs : list Segment.
  Variable P : acc -> Prop.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
  Local Notation implMA := (MonadA.implMA segs P).

  Lemma outsk_monoA : forall {B} ps (k1 k2 : M St B) Q,
    (forall s ms, implMA k1 s Q ms -> implMA k2 s Q ms) ->
    forall s ms, implMA (outsk OUT ps k1) s Q ms -> implMA (outsk OUT ps k2) s Q ms.
  Proof.
    induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
    eapply implMA_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
  Qed.

  Lemma mpad_outsA : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
    pad_pieces c w l fl = Some pp ->
    implMA (mbind (mpad OUT c w l fl) K) s Q ms -> implMA (outsk OUT pp (K tt)) s Q ms.
  Proof.
    intros B c w l fl pp K s Q ms PP H. unfold mpad, pad_pieces in *.
    destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
    - inversion PP; subst. cbn [outsk]. apply implMA_ret_l_rev in H. exact H.
    - destruct (256 <=? w - l); [discriminate|]. inversion PP; subst. cbn [outsk].
      eapply implMA_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
  Qed.

  Lemma out_outsA : forall {B} p (K : unit -> M St B) s Q ms,
    implMA (mbind (OUT p) K) s Q ms -> implMA (outsk OUT [p] (K tt)) s Q ms.
  Proof. intros B p K s Q ms H. cbn [outsk]. eapply implMA_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'. Qed.

  Lemma conv_tail_outsA : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
    tail_pieces cnt fl w p prefix body = Some (ps, r) ->
    implMA (mbind (conv_tail OUT cnt fl w p prefix body) K) s Q ms -> implMA (outsk OUT ps (K r)) s Q ms.
  Proof.
    intros B cnt fl w p prefix body ps r K s Q ms T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta in H.
    destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
    destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
    destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
    destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
    destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
    destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
    inversion T; subst. clear T.
    match goal with |- implMA (outsk OUT ?L (K ?rr)) _ _ _ =>
      replace (outsk OUT L (K rr)) with (outsk OUT p1 (OUT prefix ;;; outsk OUT p2 (outsk OUT p3 (OUT body ;;; outsk OUT p4 (K rr)))))
        by (rewrite ?outsk_app; cbn [outsk]; rewrite ?outsk_app; cbn [outsk]; reflexivity) end.
    apply implMA_assoc_rev in H. apply (mpad_outsA _ _ _ _ _ _ _ _ _ P1) in H. cbv beta in H.
    eapply outsk_monoA; [|exact H]. clear H. cbv beta. intros s1 ms1 H.
    apply implMA_assoc_rev in H. eapply implMA_bind_ext; [|exact H]. clear H. cbv beta. intros x2 s2 ms2 H.
    apply implMA_assoc_rev in H. apply (mpad_outsA _ _ _ _ _ _ _ _ _ P2) in H. cbv beta in H.
    eapply outsk_monoA; [|exact H]. clear H. cbv beta. intros s3 ms3 H.
    apply implMA_assoc_rev in H. apply (mpad_outsA _ _ _ _ _ _ _ _ _ P3) in H. cbv beta in H.
    eapply outsk_monoA; [|exact H]. clear H. cbv beta. intros s4 ms4 H.
    apply implMA_assoc_rev in H. eapply implMA_bind_ext; [|exact H]. clear H. cbv beta. intros x5 s5 ms5 H.
    apply implMA_assoc_rev in H. apply (mpad_outsA _ _ _ _ _ _ _ _ _ P4) in H. cbv beta in H.
    eapply outsk_monoA; [|exact H]. clear H. cbv beta. intros s6 ms6 H.
    apply implMA_ret_l_rev in H. exact H.
  Qed.

  Lemma conv_int_outsA : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
    int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
    implMA (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implMA (outsk OUT ps (K r)) s Q ms.
  Proof.
    intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
    destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
    destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outsA; eassumption.
  Qed.

  Lemma conv_outsA : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
    conv_pieces cnt d a = Some (ps, r) ->
    implMA (mbind (conv OUT OUTFP cnt d a) K) s Q ms -> implMA (outsk OUT ps (K r)) s Q ms.
  Proof.
    intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
    destruct a as [str|i|u|dd].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outsA; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outsA; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outsA; eassumption.
    - discriminate.
  Qed.

  Lemma printf_loop_outsA : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
    printf_pieces_loop fuel s args cnt = Some (ps, r) ->
    implMA (mbind (printf_loop OUT OUTFP fuel s args cnt) k) st Q ms -> implMA (outsk OUT ps (k r)) st Q ms.
  Proof.
    induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms PP H; [discriminate|].
    cbn [printf_pieces_loop] in PP. cbn [printf_loop] in H.
    destruct s as [|c s1]; [discriminate|].
    destruct (c =? 0). { inversion PP; subst. cbn [outsk]. apply implMA_ret_l_rev in H. exact H. }
    cbv zeta in PP. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
    destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
    destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
    destruct (0 <? zlength lit).
    - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
      destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
      inversion PP; subst. clear PP. cbn [outsk].
      apply implMA_assoc_rev in H. eapply implMA_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      eapply IH; [exact R | exact H'].
    - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion PP; subst. clear PP.
      match goal with |- implMA (outsk OUT ?L (k ?rr)) _ _ _ =>
        replace (outsk OUT L (k rr)) with (outsk OUT [[]] (outsk OUT ps1 (outsk OUT ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
      cbn [outsk].
      apply implMA_assoc_rev in H. eapply implMA_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      apply implMA_assoc_rev in H'. apply (conv_outsA _ _ _ _ _ _ _ _ _ C) in H'.
      eapply outsk_monoA; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
  Qed.

  Theorem printf_model_outsA : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
    printf_pieces fmt args = Some (ps, r) ->
    implMA (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implMA (outsk OUT ps (k r)) st Q ms.
  Proof. intros B fmt args ps r k st Q ms PP H. eapply printf_loop_outsA; [exact PP | exact H]. Qed.
End OutsA.
End RC__1.
