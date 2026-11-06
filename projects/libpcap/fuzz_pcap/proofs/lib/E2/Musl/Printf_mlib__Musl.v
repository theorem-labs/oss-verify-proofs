(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Printf_mlib.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section ImplLaws.
  Variable segs : list Segment.
  Context {node : Type}.
  Variable atn : node -> machine_state -> Prop.
  Variable npk : node -> option (machine_state -> resp).

  Local Notation impl := (ITree.impl segs atn npk).
  Local Notation bind := (ITree.bind node).

  #[using="Type"] Lemma impl_bind_ext : forall {A B} (t : itree node A) (f g : A -> itree node B) Q ms,
    (forall r ms', impl (f r) Q ms' -> impl (g r) Q ms') ->
    impl (bind t f) Q ms -> impl (bind t g) Q ms.
  Proof. intros A B t f g Q ms Hfg H. eapply ITree.impl_bind_cong; [exact Hfg| exact H]. Qed.

  #[using="Type"] Lemma impl_bind_assoc : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind t (fun x => bind (f x) g)) Q ms -> impl (bind (bind t f) g) Q ms.
  Proof. intros A B C t f g Q ms H. apply ITree.impl_bind_assoc. exact H. Qed.

  #[using="Type"] Lemma impl_bind_assoc_rev : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind (bind t f) g) Q ms -> impl (bind t (fun x => bind (f x) g)) Q ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q ms H; cbn [bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(h & Hh & Hk)].
      + left. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
      + right. exists h. split; [exact Hh|]. apply IH. apply Hk.
  Qed.

  (* [comment removed for export] *)
  Inductive teq {A} : itree node A -> itree node A -> Prop :=
  | teq_ret : forall r, teq (Ret r) (Ret r)
  | teq_vis : forall n k k', (forall x, teq (k x) (k' x)) -> teq (Vis n k) (Vis n k').

  #[using="Type"] Lemma impl_teq : forall {A} (t t' : itree node A) Q ms, teq t t' -> impl t Q ms -> impl t' Q ms.
  Proof.
    intros A t t' Q ms H. revert ms. induction H as [r|n k k' Hk IH]; intros ms Hi; cbn in *.
    - exact Hi.
    - eapply evt_mono; [exact Hi|]. intros ms1 [[Hat HK]|(h & Hh & HK)].
      + left. split; [exact Hat|]. intros rsp. apply IH. apply HK.
      + right. exists h. split; [exact Hh|]. apply IH. apply HK.
  Qed.
End ImplLaws.

Section MonadLaws.
  Variable segs : list Segment.
  Context {St : Type}.
  Local Notation implM := (Monad.implM segs).
  Local Open Scope mspec_scope.

  #[using="Type"] Lemma implM_assoc : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
    implM (mbind a (fun x => mbind (b x) k)) s Q ms -> implM (mbind (mbind a b) k) s Q ms.
  Proof.
    intros A B C a b k s Q ms H. unfold Monad.implM, mbind, ebind in *.
    apply impl_bind_assoc.
    eapply impl_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *.
    - exact Hx.
    - exact Hx.
  Qed.

  #[using="Type"] Lemma implM_assoc_rev : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
    implM (mbind (mbind a b) k) s Q ms -> implM (mbind a (fun x => mbind (b x) k)) s Q ms.
  Proof.
    intros A B C a b k s Q ms H. unfold Monad.implM, mbind, ebind in *.
    apply impl_bind_assoc_rev in H.
    eapply impl_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *.
    - exact Hx.
    - exact Hx.
  Qed.

  #[using="Type"] Lemma implM_ret_l : forall {A B} (v : A) (k : A -> M St B) s Q ms,
    implM (k v) s Q ms -> implM (mbind (mret v) k) s Q ms.
  Proof. intros. exact H. Qed.

  #[using="Type"] Lemma implM_ret_l_rev : forall {A B} (v : A) (k : A -> M St B) s Q ms,
    implM (mbind (mret v) k) s Q ms -> implM (k v) s Q ms.
  Proof. intros. exact H. Qed.

  #[using="Type"] Lemma implM_unr_l : forall {A B} (k : A -> M St B) s Q ms, implM (mbind munr k) s Q ms.
  Proof. intros. apply implM_unr. Qed.

  #[using="Type"] Lemma implM_get_l : forall {B} (k : St -> M St B) s Q ms,
    implM (k s) s Q ms -> implM (mbind mget k) s Q ms.
  Proof. intros. exact H. Qed.

  #[using="Type"] Lemma implM_put_l : forall {B} (s' : St) (k : unit -> M St B) s Q ms,
    implM (k tt) s' Q ms -> implM (mbind (mput s') k) s Q ms.
  Proof. intros. exact H. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implM_bind_ext : forall {A B} (a : M St A) (f g : A -> M St B) s Q ms,
    (forall x s' ms', implM (f x) s' Q ms' -> implM (g x) s' Q ms') ->
    implM (mbind a f) s Q ms -> implM (mbind a g) s Q ms.
  Proof.
    intros A B a f g s Q ms Hfg H. unfold Monad.implM, mbind, ebind in *.
    eapply impl_bind_ext; [|exact H]. intros [|[x s1]] ms' Hx; cbn in *; [exact Hx|].
    apply Hfg. exact Hx.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implM_if_false : forall {A} (c : bool) (x y : M St A) s Q ms,
    c = false -> implM y s Q ms -> implM (if c then x else y) s Q ms.
  Proof. intros A c x y s Q ms -> H. exact H. Qed.
  #[using="Type"] Lemma implM_if_true : forall {A} (c : bool) (x y : M St A) s Q ms,
    c = true -> implM x s Q ms -> implM (if c then x else y) s Q ms.
  Proof. intros A c x y s Q ms -> H. exact H. Qed.
End MonadLaws.

(* [comment removed for export] *)
Ltac massoc :=
  repeat lazymatch goal with
  | |- Monad.implM _ (mbind (mbind _ _) _) _ _ _ => apply implM_assoc
  | |- Monad.implM _ (mbind (mret _) _) _ _ _ => apply implM_ret_l
  end.
End Printf_mlib.

(* [comment removed for export] *)
Module Printf_pieces.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (npk : node -> option (machine_state -> resp)) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  ITree.impl segs atn npk t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> ITree.impl segs atn npk t Q' ms.
Proof.
  intros segs node R atn npk t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. exact (HQ r).
  - eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(h & Hh & Hk)].
    + left. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
    + right. exists h. split; [exact Hh|]. eapply IH; [apply Hk | exact HQ].
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
  Local Notation implM := (Monad.implM segs).

  (* [comment removed for export] *)
  Fixpoint outsk {B} (ps : list (list Z)) (k : M St B) : M St B :=
    match ps with
    | [] => k
    | p :: ps' => OUT p ;;; outsk ps' k
    end.

  #[using="Type"] Lemma outsk_app : forall {B} ps qs (k : M St B), outsk (ps ++ qs) k = outsk ps (outsk qs k).
  Proof. induction ps as [|p ps IH]; intros qs k; [reflexivity|]. cbn [outsk app]. rewrite IH. reflexivity. Qed.

  #[using="Type"] Lemma outsk_mono : forall {B} ps (k1 k2 : M St B) Q,
    (forall s ms, implM k1 s Q ms -> implM k2 s Q ms) ->
    forall s ms, implM (outsk ps k1) s Q ms -> implM (outsk ps k2) s Q ms.
  Proof.
    induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
    eapply implM_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
  Qed.

  #[using="Type"] Lemma mpad_outs : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
    pad_pieces c w l fl = Some pp ->
    implM (mbind (mpad OUT c w l fl) K) s Q ms -> implM (outsk pp (K tt)) s Q ms.
  Proof.
    intros B c w l fl pp K s Q ms P H. unfold mpad, pad_pieces in *.
    destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
    - inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H.
    - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [outsk].
      eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
  Qed.

  #[using="Type"] Lemma out_outs : forall {B} p (K : unit -> M St B) s Q ms,
    implM (mbind (OUT p) K) s Q ms -> implM (outsk [p] (K tt)) s Q ms.
  Proof. intros B p K s Q ms H. cbn [outsk]. eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'. Qed.

  #[using="Type"] Lemma conv_tail_outs : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
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

  #[using="Type"] Lemma conv_int_outs : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
    int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
    implM (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
    destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
    destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs; eassumption.
  Qed.

  #[using="Type"] Lemma conv_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
    conv_pieces cnt d a = Some (ps, r) ->
    implM (mbind (conv OUT cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
    destruct a as [str|i|u|zu].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outs; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outs; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
    - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
      destruct (d_t d =? 117); [|discriminate]. eapply conv_int_outs; eassumption.
  Qed.

  #[using="Type"] Lemma printf_loop_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
    printf_pieces_loop fuel s args cnt = Some (ps, r) ->
    implM (mbind (printf_loop OUT fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
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

  #[using="Type"] Theorem printf_model_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
    printf_pieces fmt args = Some (ps, r) ->
    implM (mbind (printf_model OUT fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
  Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loop_outs; [exact P | exact H]. Qed.
End Outs.

End Printf_pieces.

(* [comment removed for export] *)
Module Printf_zfacts.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import Printf_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma Zrange_forallb : forall (P : Z -> bool) (lo : Z) (n : nat),
  forallb P (map (fun k => lo + Z.of_nat k) (seq 0 n)) = true ->
  forall c, lo <= c < lo + Z.of_nat n -> P c = true.
Proof.
  intros P lo n H c Hc. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat (c - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Notation M64 := 18446744073709551615.

(* [comment removed for export] *)
Lemma digit_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
  Bool.eqb (Z.land (c + -48) M64 <=? 9) (is_digit c) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma digit_test : forall c, 0 <= c < 256 -> (Z.land (c + -48) M64 <= 9 <-> is_digit c = true).
Proof.
  intros c Hc. pose proof (digit_testb c ltac:(cbn; lia)) as E.
  destruct (Z.leb_spec0 (Z.land (c + -48) M64) 9); destruct (is_digit c); cbn in E; try discriminate.
  all: split; intros; first [reflexivity | assumption | discriminate | lia].
Qed.
Lemma digit_range : forall c, is_digit c = true <-> 48 <= c <= 57.
Proof. intros c. unfold is_digit. rewrite andb_true_iff, !Z.leb_le. lia. Qed.

(* [comment removed for export] *)
Lemma sp_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
  Bool.eqb (Z.land (c + -32) M64 <? 32) ((32 <=? c) && (c <? 64)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma sp_test : forall c, 0 <= c < 256 -> (Z.land (c + -32) M64 < 32 <-> 32 <= c < 64).
Proof.
  intros c Hc. pose proof (sp_testb c ltac:(cbn; lia)) as E.
  destruct (Z.ltb_spec0 (Z.land (c + -32) M64) 32); destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in E; try discriminate; lia.
Qed.

(* [comment removed for export] *)
Definition flagw (c : Z) : Z := Z.land (bv_swrap 32 (Z.shiftl 1 ((c + -32) mod 32))) M64.

Lemma flag_noneb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
  Bool.eqb (Z.land (flagw c) 75913 =? 0) (match flag_bit c with None => true | Some _ => false end) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_none : forall c, 32 <= c < 64 -> (Z.land (flagw c) 75913 = 0 <-> flag_bit c = None).
Proof.
  intros c Hc. pose proof (flag_noneb c ltac:(cbn; lia)) as E.
  destruct (Z.eqb_spec (Z.land (flagw c) 75913) 0); destruct (flag_bit c); cbn in E; try discriminate.
  all: split; intros; first [reflexivity | assumption | discriminate | congruence | lia].
Qed.
Lemma flag_someb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
  match flag_bit c with None => true | Some b => (flagw c =? b) && (0 <=? b) && (b <? 131072) end = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_some : forall c b, 32 <= c < 64 -> flag_bit c = Some b -> flagw c = b /\ 0 <= b < 131072.
Proof.
  intros c b Hc Hb. pose proof (flag_someb c ltac:(cbn; lia)) as E. rewrite Hb in E.
  rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. lia.
Qed.
Lemma flag_bit_range : forall c, flag_bit c <> None -> 32 <= c < 64.
Proof.
  intros c H. unfold flag_bit in H.
  destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in H; try lia; exfalso; apply H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_bound17 : forall a b, 0 <= a < 131072 -> 0 <= b < 131072 -> 0 <= Z.lor a b < 131072.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  change 131072 with (2^17) in *.
  destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma parse_flags_cons_some : forall c s fl b, flag_bit c = Some b -> parse_flags (c :: s) fl = parse_flags s (Z.lor fl b).
Proof. intros c s fl b H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_cons_none : forall c s fl, flag_bit c = None -> parse_flags (c :: s) fl = (fl, c :: s).
Proof. intros c s fl H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_range : forall s fl, 0 <= fl < 131072 -> 0 <= fst (parse_flags s fl) < 131072.
Proof.
  induction s as [|c s IH]; intros fl Hfl; cbn; [exact Hfl|].
  destruct (flag_bit c) as [b|] eqn:E; [|exact Hfl].
  apply IH. pose proof (flag_some c b (flag_bit_range c ltac:(congruence)) E) as [_ Hb]. apply lor_bound17; lia.
Qed.

(* [comment removed for export] *)
Lemma getint_cons_digit : forall c s i, is_digit c = true ->
  getint (c :: s) i = if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None else getint s (10 * i + (c - 48)).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_cons_nondigit : forall c s i, is_digit c = false -> getint (c :: s) i = Some (i, c :: s).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_some_range : forall s i w s', 0 <= i <= INT_MAX -> getint s i = Some (w, s') -> 0 <= w <= INT_MAX.
Proof.
  induction s as [|c s IH]; intros i w s' Hi H; cbn [getint] in H.
  - inversion H; subst. exact Hi.
  - destruct (is_digit c) eqn:D.
    + destruct (214748364 <? i) eqn:E1; [discriminate|]. destruct (INT_MAX - 10 * i <? c - 48) eqn:E2; [discriminate|]. cbn in H.
      apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. apply digit_range in D. unfold INT_MAX in *. eapply IH; [|exact H]. lia.
    + inversion H; subst. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma lxor_imax : forall x, 0 <= x <= 2147483647 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
  intros x Hx. change 2147483647 with (Z.ones 31).
  assert (E : Z.lxor x (Z.ones 31) = (Z.lnot x) mod 2^31).
  { rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 31).
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; cbn in *; lia|lia]. }
  rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^31)) with (2^31 - 1).
  replace (Z.lnot x) with (-x - 1) by (unfold Z.lnot; lia).
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by (cbn in *; lia). lia.
Qed.

(* [comment removed for export] *)
Definition dir_type (d : dir) (t : Z) (s4 rest : list Z) : Prop :=
  (t <> 122 /\ d_t d = t /\ d_ps d = 0 /\ rest = s4 /\ conv_type t = Some (d_ty d))
  \/ (t = 122 /\ d_ps d = ST_ZTPRE /\ exists t2 s5, s4 = t2 :: s5 /\ d_t d = t2 /\ rest = s5 /\ conv_type_z t2 = Some (d_ty d)).

Lemma dir_type_of : forall fl w p xp t s4 d rest,
  (if t =? 122 then match s4 with [] => None | t2 :: s5 => let? ty := conv_type_z t2 in Some (mkDir fl w p xp t2 ty ST_ZTPRE, s5) end
   else let? ty := conv_type t in Some (mkDir fl w p xp t ty 0, s4)) = Some (d, rest) ->
  d_fl d = fl /\ d_w d = w /\ d_p d = p /\ d_xp d = xp /\ dir_type d t s4 rest.
Proof.
  intros fl w p xp t s4 d rest H. unfold dir_type.
  destruct (Z.eqb_spec t 122) as [E|N].
  - destruct s4 as [|t2 s5]; [discriminate|]. destruct (conv_type_z t2) as [ty|] eqn:CT; [|discriminate].
    injection H as <- <-. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    right. split; [exact E|]. split; [reflexivity|]. exists t2, s5. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. first [exact CT | reflexivity].
  - destruct (conv_type t) as [ty|] eqn:CT; [|discriminate]. injection H as <- <-. cbn.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    left. split; [exact N|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. first [exact CT | reflexivity].
Qed.

Lemma parse_dir_shape : forall s d rest, parse_dir s = Some (d, rest) ->
  match s with c0 :: c0b :: _ => is_digit c0 && (c0b =? 36) = false | [c0] => is_digit c0 = false | [] => True end /\
  let (fl, s1) := parse_flags s 0 in
  d_fl d = fl /\
  exists c1 s1b, s1 = c1 :: s1b /\ c1 <> 42 /\
  exists s2, getint s1 0 = Some (d_w d, s2) /\
  exists c2 s2b, s2 = c2 :: s2b /\
  ( (c2 <> 46 /\ d_p d = -1 /\ d_xp d = false /\ dir_type d c2 s2b rest)
  \/ (c2 = 46 /\ d_xp d = true /\ exists c3 s3b, s2b = c3 :: s3b /\ c3 <> 42 /\
      exists s3, getint s2b 0 = Some (d_p d, s3) /\ exists t s4, s3 = t :: s4 /\ dir_type d t s4 rest) ).
Proof.
  intros s d rest H. unfold parse_dir in H.
  split. { destruct s as [|c0 [|c0b s0]]; try exact I. { destruct (is_digit c0); [discriminate|reflexivity]. } destruct (is_digit c0 && (c0b =? 36)); [discriminate|reflexivity]. }
  match type of H with (if ?pp then None else _) = _ => destruct pp; [discriminate|] end.
  destruct (parse_flags s 0) as [fl s1].
  destruct s1 as [|c1 s1b]; [discriminate|].
  destruct (Z.eqb_spec c1 42) as [E42|N42]; [discriminate|].
  destruct (getint (c1 :: s1b) 0) as [[w s2]|] eqn:G; [|discriminate].
  destruct s2 as [|c2 s2b]; [discriminate|].
  destruct (Z.eqb_spec c2 46) as [E46|N46].
  - destruct s2b as [|c3 s3b]; [discriminate|]. destruct (Z.eqb_spec c3 42) as [E42'|N42']; [discriminate|].
    destruct (getint (c3 :: s3b) 0) as [[p s3]|] eqn:G2; [|discriminate].
    destruct s3 as [|t s4]; [discriminate|].
    destruct (dir_type_of fl w p true t s4 d rest H) as (E1 & E2 & E3 & E4 & DT).
    split; [exact E1|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
    exists (c2 :: c3 :: s3b). split; [rewrite E2; first [reflexivity | exact G]|]. exists c2, (c3 :: s3b). split; [reflexivity|].
    right. split; [exact E46|]. split; [exact E4|]. exists c3, s3b. split; [reflexivity|]. split; [exact N42'|].
    exists (t :: s4). split; [rewrite E3; first [reflexivity | exact G2]|]. exists t, s4. split; [reflexivity| exact DT].
  - destruct (dir_type_of fl w (-1) false c2 s2b d rest H) as (E1 & E2 & E3 & E4 & DT).
    split; [exact E1|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
    exists (c2 :: s2b). split; [rewrite E2; first [reflexivity | exact G]|]. exists c2, s2b. split; [reflexivity|].
    left. split; [exact N46|]. split; [exact E3|]. split; [exact E4| exact DT].
Qed.

(* [comment removed for export] *)
Lemma parse_flags_suffix : forall s acc fl s1, parse_flags s acc = (fl, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
  induction s as [|c s IH]; intros acc fl s1 H; cbn in H.
  - injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
  - destruct (flag_bit c) as [b|].
    + destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
    + injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.
Lemma getint_suffix : forall s acc w s1, getint s acc = Some (w, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
  induction s as [|c s IH]; intros acc w s1 H; cbn [getint] in H.
  - injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
  - destruct (is_digit c).
    + destruct (_ || _); [discriminate|]. destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
    + injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition STATES0 : list Z :=
  [25; 0; 11; 0; 25; 25; 25; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0; 0; 9; 0; 0; 0; 0; 11; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 10; 10; 25; 25; 25; 3; 10; 7; 0; 1; 27; 9; 11; 24; 0; 0; 9; 6; 11; 0; 0; 11; 0; 6].
Lemma conv_type_range : forall t ty, conv_type t = Some ty -> 65 <= t <= 122.
Proof.
  intros t ty H. unfold conv_type in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [try (injection H as <-)|] end; try discriminate;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end; try lia.
Qed.
Lemma states0_conv : forall t ty, conv_type t = Some ty -> znth STATES0 (t - 65) = ty.
Proof.
  intros t ty H. unfold conv_type in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [injection H as <-|] end; try discriminate;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E; subst; reflexivity | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end.
Qed.
(* [comment removed for export] *)
Definition conv_target (t : Z) : Z :=
  if t =? 115 then 0x1c038
  else if (t =? 100) || (t =? 105) then 0x1bff0
  else if t =? 117 then 0x1c128
  else if (t =? 120) || (t =? 88) then 0x1c1a0
  else 0x1bfa0.

Lemma conv_type_ty : forall t ty, conv_type t = Some ty -> ty = 9 \/ ty = 10 \/ ty = 11.
Proof.
  intros t ty H. unfold conv_type, T_PTR, T_INT, T_UINT in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; lia|] end. discriminate.
Qed.
(* [comment removed for export] *)
Definition STATES6 : list Z :=
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 20; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 23; 0; 0; 0; 0; 23; 0; 0; 0; 0; 9; 20; 0; 0; 0; 0; 0; 20; 0; 0; 20; 0; 0].
Lemma conv_type_z_range : forall t ty, conv_type_z t = Some ty -> 65 <= t <= 122.
Proof. intros t ty H. unfold conv_type_z in H. destruct (Z.eqb_spec t 117); [lia| discriminate]. Qed.
Lemma states6_conv : forall t ty, conv_type_z t = Some ty -> znth STATES6 (t - 65) = ty.
Proof. intros t ty H. unfold conv_type_z in H. destruct (Z.eqb_spec t 117); [| discriminate]. injection H as <-. subst t. reflexivity. Qed.
Lemma conv_type_z_ty : forall t ty, conv_type_z t = Some ty -> ty = 20.
Proof. intros t ty H. unfold conv_type_z, T_SIZET in H. destruct (t =? 117); [injection H as <-; lia| discriminate]. Qed.
(* [comment removed for export] *)
Lemma states0_z : znth STATES0 (122 - 65) = ST_ZTPRE.
Proof. reflexivity. Qed.

Lemma land_M64_neg : forall x, - 2^64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2^64.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma nzmask_bits : forall n, 0 <= n < 0 + Z.of_nat 64 -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma nzmask_eq : forall fl, 0 <= fl < 131072 -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof.
  intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases n 64).
  - pose proof (nzmask_bits n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
  - replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
    destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.
Lemma land_bound : forall a m, 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
Proof.
  intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
  pose proof (Z.sub_land_same_l a m) as E.
  assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha).
  lia.
Qed.
End Printf_zfacts.

(* [comment removed for export] *)
Module Printf_fmt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition conv_ok (c : Fmt.conv) (a : farg) : bool :=
  match c, a with
  | Cs, AStr _ => true
  | Cd, AInt _ => true | Cu, AInt _ => true | Czu, AInt _ => true | C08x, AInt _ => true
  | _, _ => false
  end.
Fixpoint items_ok (its : list fitem) (args : list farg) : bool :=
  match its with
  | [] => match args with [] => true | _ => false end
  | FLit l :: its' => forallb (fun c => negb (c =? 0) && negb (c =? 37)) l && items_ok its' args
  | FConv c :: its' => match args with a :: args' => conv_ok c a && items_ok its' args' | [] => false end
  | FBad _ :: _ => false
  end.

(* [comment removed for export] *)
Definition conv_parg (c : Fmt.conv) (a : farg) : parg :=
  match c, a with
  | Cs, AStr s => PA_s s
  | Cd, AInt v => PA_i (s32 v)
  | Cu, AInt v => PA_u (u32 v)
  | C08x, AInt v => PA_u (u32 v)
  | Czu, AInt v => PA_z (u64 v)
  | _, AStr s => PA_s s
  | _, AInt v => PA_i 0
  end.
Fixpoint to_pargs (its : list fitem) (args : list farg) : list parg :=
  match its with
  | [] => []
  | FLit _ :: its' => to_pargs its' args
  | FConv c :: its' => match args with a :: args' => conv_parg c a :: to_pargs its' args' | [] => [] end
  | FBad _ :: _ => []
  end.

(* [comment removed for export] *)
Definition conv_bytes (c : Fmt.conv) : list Z :=
  match c with
  | Cd => [37; 100] | Cu => [37; 117] | Cx => [37; 120] | C08x => [37; 48; 56; 120]
  | Cs => [37; 115] | Czu => [37; 122; 117] | Clu => [37; 108; 117] | Cld => [37; 108; 100]
  end.
Fixpoint render (its : list fitem) : list Z :=
  match its with
  | [] => []
  | FLit l :: its' => l ++ render its'
  | FConv c :: its' => conv_bytes c ++ render its'
  | FBad s :: _ => s
  end.

(* [comment removed for export] *)
Fixpoint wf_items (its : list fitem) : bool :=
  match its with
  | [] => true
  | FLit l :: its' => negb (Nat.eqb (List.length l) 0) && match its' with FLit _ :: _ => false | _ => true end && wf_items its'
  | FConv _ :: its' => wf_items its'
  | FBad _ :: _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma take_lit_spec : forall s l r, take_lit s = (l, r) ->
  s = l ++ r /\ ~ In 37 l /\ (r = [] \/ exists r', r = 37 :: r').
Proof.
  induction s as [|c s IH]; intros l r H; cbn in H.
  - injection H as <- <-. repeat split; [intros []| left; reflexivity].
  - destruct (Z.eqb_spec c 37) as [->|N].
    + injection H as <- <-. split; [reflexivity|]. split; [intros []|]. right. eexists; reflexivity.
    + destruct (take_lit s) as [l0 r0] eqn:E. injection H as <- <-.
      destruct (IH l0 r0 eq_refl) as (E1 & N1 & R1). split; [cbn; congruence|]. split; [| exact R1].
      intros [X|X]; [lia| exact (N1 X)].
Qed.

(* [comment removed for export] *)
Lemma parse_conv_cases : forall r c r', parse_conv r = Some (c, r') ->
  match c with
  | Cd => r = 100 :: r' \/ r = 105 :: r'
  | Cu => r = 117 :: r'
  | Cx => r = 120 :: r'
  | C08x => r = 48 :: 56 :: 120 :: r'
  | Cs => r = 115 :: r'
  | Czu => r = 122 :: 117 :: r'
  | Clu => r = 108 :: 117 :: r'
  | Cld => r = 108 :: 100 :: r'
  end.
Proof.
  intros r c r' H. unfold parse_conv in H.
  repeat match type of H with
  | (match ?x with _ => _ end) = _ => destruct x eqn:?; try discriminate H
  end;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E; subst end;
  injection H as <- <-; auto.
Qed.

(* [comment removed for export] *)
Lemma parse_lit_shape : forall fuel c s0, c <> 37 ->
  parse_fmt_aux (S fuel) (c :: s0) = (let (l, r) := take_lit (c :: s0) in FLit l :: parse_fmt_aux fuel r).
Proof.
  intros fuel c s0 N. cbn [parse_fmt_aux].
  destruct c as [|p|p]; try reflexivity. repeat (destruct p; try reflexivity). exfalso. apply N. reflexivity.
Qed.
Lemma parse_pct_shape : forall fuel s0,
  parse_fmt_aux (S fuel) (37 :: s0) = match parse_conv s0 with Some (c, r') => FConv c :: parse_fmt_aux fuel r' | None => [FBad (37 :: s0)] end.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma digits_aux_more : forall f b d x acc, 1 < b -> 0 <= x < b ^ Z.of_nat f ->
  digits_aux (S f) b d x acc = digits_aux f b d x acc.
Proof.
  induction f as [|f IH]; intros b d x acc Hb Hx.
  - cbn [digits_aux]. replace x with 0 by (cbn in Hx; lia). reflexivity.
  - cbn [digits_aux]. destruct (Z.eqb_spec x 0) as [->|N]; [reflexivity|].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    assert (Hx' : 0 <= x / b < b ^ Z.of_nat f).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
    rewrite <- (IH b d (x / b) (d (x mod b) :: acc) Hb Hx'). reflexivity.
Qed.
Lemma udigits_aux_more : forall f b x acc, 1 < b -> 0 <= x < b ^ Z.of_nat f ->
  udigits_aux (S f) b x acc = udigits_aux f b x acc.
Proof.
  induction f as [|f IH]; intros b x acc Hb Hx.
  - cbn [udigits_aux]. replace x with 0 by (cbn in Hx; lia). reflexivity.
  - cbn [udigits_aux]. destruct (Z.leb_spec x 0) as [L|N]; [reflexivity|].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    assert (Hx' : 0 <= x / b < b ^ Z.of_nat f).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
    rewrite <- (IH b (x / b) _ Hb Hx'). reflexivity.
Qed.
Lemma digits_aux_fuel : forall k f b d x acc, 1 < b -> 0 <= x < b ^ Z.of_nat f ->
  digits_aux (k + f) b d x acc = digits_aux f b d x acc.
Proof.
  induction k as [|k IH]; intros f b d x acc Hb Hx; [reflexivity|].
  cbn [Nat.add]. rewrite digits_aux_more; [apply IH; assumption| exact Hb|].
  split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma udigits_aux_fuel : forall k f b x acc, 1 < b -> 0 <= x < b ^ Z.of_nat f ->
  udigits_aux (k + f) b x acc = udigits_aux f b x acc.
Proof.
  induction k as [|k IH]; intros f b x acc Hb Hx; [reflexivity|].
  cbn [Nat.add]. rewrite udigits_aux_more; [apply IH; assumption| exact Hb|].
  split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.
(* [comment removed for export] *)
Lemma digits_udigits_aux : forall f b d x acc, 1 < b -> 0 <= x ->
  (forall v, 0 <= v < b -> d v = (if v <? 10 then 48 + v else 87 + v)) ->
  digits_aux f b d x acc = udigits_aux f b x acc.
Proof.
  induction f as [|f IH]; intros b d x acc Hb Hx Hd; [reflexivity|].
  cbn [digits_aux udigits_aux].
  destruct (Z.eqb_spec x 0) as [->|N]; [reflexivity|].
  destruct (Z.leb_spec x 0) as [L|G]; [lia|].
  rewrite Hd by (apply Z.mod_pos_bound; lia). apply IH; [exact Hb| apply Z.div_pos; lia| exact Hd].
Qed.

Lemma dec_digits_eq : forall x, 0 <= x < 2^64 -> dec_digits x = dec_udigits x.
Proof.
  intros x Hx. unfold dec_digits, dec_udigits, udigits.
  change 64%nat with (44 + 20)%nat. rewrite (udigits_aux_fuel 44 20 10 x []); [| lia|].
  2:{ split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|]. cbn. lia. }
  apply digits_udigits_aux; [lia| lia|]. intros v Hv. destruct (Z.ltb_spec v 10); lia.
Qed.
Lemma hex_digits_eq : forall x, 0 <= x < 2^64 -> hex_digits 32 x = hex_udigits x.
Proof.
  intros x Hx. unfold hex_digits, hex_udigits, udigits.
  change 64%nat with (48 + 16)%nat. rewrite (udigits_aux_fuel 48 16 16 x []); [| lia|].
  2:{ split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|]. cbn. lia. }
  apply digits_udigits_aux; [lia| lia|]. intros v Hv.
  assert (H : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8 \/ v = 9 \/ v = 10 \/ v = 11 \/ v = 12 \/ v = 13 \/ v = 14 \/ v = 15) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]]]]]]; reflexivity.
Qed.

Lemma digits_aux_len : forall f b d y (acc : list Z), (List.length acc <= List.length (digits_aux f b d y acc))%nat.
Proof.
  induction f as [|f IH]; intros; cbn [digits_aux]; [lia|]. destruct (y =? 0); [lia|].
  eapply Nat.le_trans; [| apply IH]. cbn. lia.
Qed.
Lemma dec_digits_nil : forall x, 0 <= x < 2^64 -> (dec_digits x = [] <-> x = 0).
Proof.
  intros x Hx. unfold dec_digits.
  change (digits_aux 20 10 (fun v : Z => 48 + v) x []) with
    (if x =? 0 then [] else digits_aux 19 10 (fun v : Z => 48 + v) (x / 10) [48 + x mod 10]).
  destruct (Z.eqb_spec x 0) as [->|N]; [tauto|]. split; [| intros; lia].
  intros H. exfalso. pose proof (digits_aux_len 19 10 (fun v => 48 + v) (x / 10) [48 + x mod 10]) as L1. rewrite H in L1. cbn in L1. lia.
Qed.
Lemma hex_digits_nil : forall x, 0 <= x < 2^64 -> (hex_digits 32 x = [] <-> x = 0).
Proof.
  intros x Hx. unfold hex_digits.
  change (digits_aux 16 16 (fun v : Z => Z.lor (znth XDIGITS v) 32) x []) with
    (if x =? 0 then [] else digits_aux 15 16 (fun v : Z => Z.lor (znth XDIGITS v) 32) (x / 16) [Z.lor (znth XDIGITS (x mod 16)) 32]).
  destruct (Z.eqb_spec x 0) as [->|N]; [tauto|]. split; [| intros; lia].
  intros H. exfalso. pose proof (digits_aux_len 15 16 (fun v => Z.lor (znth XDIGITS v) 32) (x / 16) [Z.lor (znth XDIGITS (x mod 16)) 32]) as L1. rewrite H in L1. cbn in L1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_nil_iff : forall {A} (l : list A), zlength l = 0 <-> l = [].
Proof. intros A l. unfold zlength. split; [| intros ->; reflexivity]. destruct l; [reflexivity| cbn; lia]. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma pad_pieces_flag : forall c w l fl, Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) <> 0 -> pad_pieces c w l fl = Some [].
Proof. intros c w l fl H. unfold pad_pieces. destruct (Z.eqb_spec (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD)) 0); [lia|]. reflexivity. Qed.
Lemma pad_pieces_fit : forall c w l fl, w <= l -> pad_pieces c w l fl = Some [].
Proof. intros c w l fl H. unfold pad_pieces. rewrite (proj2 (Z.leb_le w l) H), orb_true_r. reflexivity. Qed.
Lemma pad_pieces_pad : forall c w l, l < w -> w - l < 256 -> pad_pieces c w l 0 = Some [zrepeat c (w - l)].
Proof.
  intros c w l H1 H2. unfold pad_pieces. rewrite Z.land_0_l. cbn [Z.eqb negb orb].
  destruct (Z.leb_spec w l); [lia|]. destruct (Z.leb_spec 256 (w - l)); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tail_pieces_w0 : forall cnt p prefix body,
  0 <= cnt -> zlength body <= p -> p - zlength body < 256 -> cnt + zlength prefix + p <= INT_MAX ->
  tail_pieces cnt 0 0 p prefix body
  = Some (prefix :: (if zlength body <? p then [zrepeat 48 (p - zlength body)] else []) ++ [body], cnt + zlength prefix + p).
Proof.
  intros cnt p prefix body Hc Hn Hp Hb. pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body).
  unfold tail_pieces. cbv zeta.
  rewrite (Z.max_l p (zlength body)) by lia.
  destruct (Z.ltb_spec (INT_MAX - zlength prefix) p); [unfold INT_MAX in *; lia|].
  rewrite (Z.max_r 0 (zlength prefix + p)) by lia.
  destruct (Z.ltb_spec (INT_MAX - cnt) (zlength prefix + p)); [unfold INT_MAX in *; lia|].
  rewrite (pad_pieces_fit 32) by lia.
  rewrite (pad_pieces_flag 48) by (vm_compute; discriminate).
  rewrite (pad_pieces_flag 32 _ _ (Z.lxor 0 LEFT_ADJ)) by (vm_compute; discriminate).
  destruct (Z.ltb_spec (zlength body) p).
  - rewrite pad_pieces_pad by lia. cbn [app]. f_equal. f_equal. lia.
  - rewrite (pad_pieces_fit 48) by lia. cbn [app]. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma tail_pieces_zp8 : forall cnt p body,
  0 <= cnt -> zlength body <= p -> p - zlength body < 256 -> cnt + Z.max 8 p <= INT_MAX ->
  tail_pieces cnt ZERO_PAD 8 p [] body
  = Some ([] :: (if p <? 8 then [zrepeat 48 (8 - p)] else []) ++ (if zlength body <? p then [zrepeat 48 (p - zlength body)] else []) ++ [body],
          cnt + Z.max 8 p).
Proof.
  intros cnt p body Hc Hn Hp Hb. pose proof (zlength_nonneg body).
  unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  rewrite (Z.max_l p (zlength body)) by lia.
  destruct (Z.ltb_spec (INT_MAX - 0) p); [unfold INT_MAX in *; lia|].
  rewrite Z.add_0_l.
  destruct (Z.ltb_spec (INT_MAX - cnt) (Z.max 8 p)); [unfold INT_MAX in *; lia|].
  rewrite (pad_pieces_flag 32 _ _ ZERO_PAD) by (vm_compute; discriminate).
  change (Z.lxor ZERO_PAD ZERO_PAD) with 0.
  rewrite (pad_pieces_flag 32 _ _ (Z.lxor ZERO_PAD LEFT_ADJ)) by (vm_compute; discriminate).
  destruct (Z.ltb_spec p 8).
  - rewrite (Z.max_l 8 p) by lia. rewrite (pad_pieces_pad 48 8 p) by lia.
    destruct (Z.ltb_spec (zlength body) p).
    + rewrite pad_pieces_pad by lia. reflexivity.
    + rewrite (pad_pieces_fit 48 p) by lia. reflexivity.
  - rewrite (Z.max_r 8 p) by lia. rewrite (pad_pieces_fit 48 p p) by lia.
    destruct (Z.ltb_spec (zlength body) p).
    + rewrite pad_pieces_pad by lia. reflexivity.
    + rewrite (pad_pieces_fit 48 p) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma int_pieces_plain : forall cnt x prefix, 0 <= x < 2^64 -> 0 <= cnt ->
  cnt + zlength prefix + Z.max 1 (zlength (dec_digits x)) <= INT_MAX ->
  int_pieces cnt 0 0 (-1) false x prefix (dec_digits x)
  = Some (prefix :: (match dec_digits x with [] => [[48]; []] | dg => [dg] end),
          cnt + zlength prefix + Z.max 1 (zlength (dec_digits x))).
Proof.
  intros cnt x prefix Hx Hc Hb. pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg (dec_digits x)) as LN.
  unfold int_pieces. cbn [andb]. change ((-1) =? 0) with false. rewrite andb_false_r.
  destruct (Z.eqb_spec x 0) as [->|N].
  - rewrite (proj2 (dec_digits_nil 0 ltac:(lia)) eq_refl). change (zlength (@nil Z)) with 0. change (Z.max (-1) (0 + 1)) with 1. change (Z.max 1 0) with 1.
    rewrite tail_pieces_w0; [| lia| cbn; unfold zlength; cbn; lia| unfold zlength at 1; cbn; lia| change (zlength (@nil Z)) with 0 in Hb |- *; lia].
    change (zlength (@nil Z)) with 0. reflexivity.
  - assert (NN : dec_digits x <> []) by (intros E; apply N; apply (proj1 (dec_digits_nil x Hx)); exact E).
    assert (L1 : 1 <= zlength (dec_digits x)) by (destruct (dec_digits x); [exfalso; apply NN; reflexivity| unfold zlength; cbn; lia]).
    rewrite Z.add_0_r. rewrite (Z.max_r (-1)) by lia. rewrite (Z.max_r 1) in Hb |- * by lia.
    rewrite tail_pieces_w0; [| lia| lia| lia| lia].
    rewrite Z.ltb_irrefl. cbn [app]. destruct (dec_digits x) eqn:E; [exfalso; apply NN; reflexivity|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma conv_pieces_s : forall cnt s t rest, 0 <= cnt -> cnt + zlength s < INT_MAX ->
  conv_pieces cnt (mkDir 0 0 (-1) false t T_PTR rest) (PA_s s) = Some ([[]; s], cnt + zlength s).
Proof.
  intros cnt s t rest Hc Hb. pose proof (zlength_nonneg s).
  unfold conv_pieces. cbv beta iota zeta delta [T_PTR T_INT T_UINT T_SIZET LEFT_ADJ ZERO_PAD MARK_POS PAD_POS ALT_FORM d_fl d_w d_p d_xp d_t d_ty d_ps Z.eqb Pos.eqb negb Z.land Z.lnot Z.lxor Z.pred andb N.lxor Z.of_N Pos.lxor N.succ_pos Pos.pred_N Pos.Nsucc_double Pos.Ndouble Pos.land Pos.ldiff Z.ldiff].
  change ((-1) <? 0) with true. cbn [andb].
  destruct (Z.leb_spec INT_MAX (zlength s)); [unfold INT_MAX in *; lia|].
  rewrite firstn_all2 by (unfold zlength; lia).
  rewrite tail_pieces_w0; [| lia| lia| lia| change (zlength (@nil Z)) with 0; lia].
  rewrite Z.ltb_irrefl. change (zlength (@nil Z)) with 0. cbn [app].
  f_equal. f_equal; first [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma conv_pieces_d : forall cnt v t, 0 <= cnt -> (t = 100 \/ t = 105) ->
  cnt + 1 + Z.max 1 (zlength (dec_udigits (Z.abs (s32 v)))) <= INT_MAX ->
  conv_pieces cnt (mkDir 0 0 (-1) false t T_INT 0) (PA_i (s32 v))
  = Some (Fmt.conv_pieces Cd (AInt v), cnt + (if s32 v <? 0 then 1 else 0) + Z.max 1 (zlength (dec_udigits (Z.abs (s32 v))))).
Proof.
  intros cnt v t Hc Ht Hb.
  assert (R : -2^31 <= s32 v < 2^31) by (unfold s32; Z.div_mod_to_equations; lia).
  unfold conv_pieces. cbv beta iota zeta delta [T_PTR T_INT T_UINT T_SIZET LEFT_ADJ ZERO_PAD MARK_POS PAD_POS ALT_FORM d_fl d_w d_p d_xp d_t d_ty d_ps Z.eqb Pos.eqb negb Z.land Z.lnot Z.lxor Z.pred andb N.lxor Z.of_N Pos.lxor N.succ_pos Pos.pred_N Pos.Nsucc_double Pos.Ndouble Pos.land Pos.ldiff Z.ldiff].
  cbn [Fmt.conv_pieces].
  destruct (Z.ltb_spec (s32 v) 0) as [NEG|POS].
  - replace (s32 v mod 2^64) with (2^64 + s32 v) by (Z.div_mod_to_equations; nia).
    destruct (Z.ltb_spec INTMAX_MAX (2^64 + s32 v)); [| unfold INTMAX_MAX in *; lia].
    replace (- (2^64 + s32 v) mod 2^64) with (Z.abs (s32 v)) by (Z.div_mod_to_equations; nia).
    rewrite <- dec_digits_eq in Hb |- * by lia.
    rewrite int_pieces_plain; [| lia| lia| change (zlength [45]) with 1; lia].
    change (zlength [45]) with 1. unfold Fmt.int_pieces. cbv iota. destruct (dec_digits (Z.abs (s32 v))); reflexivity.
  - replace (s32 v mod 2^64) with (s32 v) by (symmetry; apply Z.mod_small; lia).
    destruct (Z.ltb_spec INTMAX_MAX (s32 v)); [unfold INTMAX_MAX in *; lia|].
    replace (Z.abs (s32 v)) with (s32 v) in Hb |- * by lia.
    rewrite <- dec_digits_eq in Hb |- * by lia.
    rewrite int_pieces_plain; [| lia| lia| change (zlength (@nil Z)) with 0; lia].
    change (zlength (@nil Z)) with 0. unfold Fmt.int_pieces. cbv iota. rewrite Z.add_0_r. destruct (dec_digits (s32 v)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma conv_pieces_u : forall cnt u ty ps a (c : Fmt.conv), 0 <= cnt -> 0 <= u < 2^64 ->
  ((ty = T_UINT /\ a = PA_u u) \/ (ty = T_SIZET /\ a = PA_z u)) ->
  cnt + Z.max 1 (zlength (dec_udigits u)) <= INT_MAX ->
  conv_pieces cnt (mkDir 0 0 (-1) false 117 ty ps) a
  = Some (Fmt.int_pieces false (dec_udigits u), cnt + Z.max 1 (zlength (dec_udigits u))).
Proof.
  intros cnt u ty ps a c Hc Hu CASE Hb.
  unfold conv_pieces. destruct CASE as [[-> ->] | [-> ->]]; cbv beta iota zeta delta [T_PTR T_INT T_UINT T_SIZET LEFT_ADJ ZERO_PAD MARK_POS PAD_POS ALT_FORM d_fl d_w d_p d_xp d_t d_ty d_ps Z.eqb Pos.eqb negb Z.land Z.lnot Z.lxor Z.pred andb N.lxor Z.of_N Pos.lxor N.succ_pos Pos.pred_N Pos.Nsucc_double Pos.Ndouble Pos.land Pos.ldiff Z.ldiff];
    rewrite <- dec_digits_eq in Hb |- * by lia;
    (rewrite int_pieces_plain; [| lia| lia| change (zlength (@nil Z)) with 0; lia]);
    change (zlength (@nil Z)) with 0; unfold Fmt.int_pieces; cbv iota; rewrite Z.add_0_r; destruct (dec_digits u); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma conv_pieces_08x : forall cnt u, 0 <= cnt -> 0 <= u < 2^32 ->
  cnt + Z.max 8 (zlength (hex_udigits u) + (if u =? 0 then 1 else 0)) <= INT_MAX ->
  conv_pieces cnt (mkDir ZERO_PAD 8 (-1) false 120 T_UINT 0) (PA_u u)
  = Some (Fmt.conv_pieces C08x (AInt u), cnt + Z.max 8 (zlength (hex_udigits u) + (if u =? 0 then 1 else 0))).
Proof.
  intros cnt u Hc Hu Hb. pose proof (zlength_nonneg (hex_digits 32 u)) as LN.
  unfold conv_pieces. cbn [T_PTR T_INT T_UINT T_SIZET d_fl d_w d_p d_xp d_t d_ty d_ps Z.eqb Pos.eqb negb andb].
  change (Z.land ZERO_PAD LEFT_ADJ =? 0) with true. cbv iota.
  change (Z.land ZERO_PAD ALT_FORM =? 0) with true. cbn [negb andb]. rewrite andb_false_r.
  change (Z.land 120 32) with 32.
  cbn [Fmt.conv_pieces]. replace (u32 u) with u by (unfold u32; symmetry; apply Z.mod_small; lia).
  rewrite <- hex_digits_eq in Hb |- * by lia.
  unfold int_pieces. cbn [andb]. change ((-1) =? 0) with false. rewrite andb_false_r.
  destruct (Z.eqb_spec u 0) as [->|N].
  - rewrite (proj2 (hex_digits_nil 0 ltac:(lia)) eq_refl) in Hb |- *. change (zlength (@nil Z)) with 0 in Hb |- *.
    change (Z.max (-1) (0 + 1)) with 1. change (0 + 1) with 1 in Hb |- *.
    rewrite tail_pieces_zp8; [| lia| cbn; unfold zlength; cbn; lia| unfold zlength; cbn; lia| lia].
    change (zlength (@nil Z)) with 0. change (0 <? 1) with true. change (1 <? 8) with true. cbv iota. cbn [app]. reflexivity.
  - assert (NN : hex_digits 32 u <> []) by (intros E; apply N; apply (proj1 (hex_digits_nil u ltac:(lia))); exact E).
    assert (L1 : 1 <= zlength (hex_digits 32 u)) by (destruct (hex_digits 32 u); [exfalso; apply NN; reflexivity| unfold zlength; cbn; lia]).
    rewrite Z.add_0_r in Hb |- *. rewrite (Z.max_r (-1)) by lia.
    rewrite tail_pieces_zp8; [| lia| lia| lia| lia].
    rewrite Z.ltb_irrefl. cbn [app]. destruct (hex_digits 32 u) eqn:E; [exfalso; apply NN; reflexivity|].
    unfold zeros. destruct (Z.ltb_spec (zlength (z :: l)) 8); reflexivity.
Qed.

(* [comment removed for export] *)
Definition conv_len (c : Fmt.conv) (a : farg) : Z := zlength (List.concat (Fmt.conv_pieces c a)).

Lemma zlength_app : forall {A} (l1 l2 : list A), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_cons : forall {A} (x : A) l, zlength (x :: l) = 1 + zlength l.
Proof. intros. unfold zlength. cbn [Datatypes.length]. lia. Qed.
Lemma zlength_zrepeat : forall c n, 0 <= n -> zlength (zrepeat c n) = n.
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.

Lemma int_pieces_len : forall neg d,
  zlength (List.concat (Fmt.int_pieces neg d)) = (if neg then 1 else 0) + Z.max 1 (zlength d).
Proof.
  intros neg d. unfold Fmt.int_pieces.
  destruct d as [|z l]; destruct neg; cbn [List.concat app]; rewrite ?app_nil_r;
    unfold zlength; cbn [Datatypes.length]; lia.
Qed.

(* [comment removed for export] *)
Definition conv_dir (c : Fmt.conv) (t : Z) : dir :=
  match c with
  | Cd => mkDir 0 0 (-1) false t T_INT 0
  | Cu => mkDir 0 0 (-1) false 117 T_UINT 0
  | Czu => mkDir 0 0 (-1) false 117 T_SIZET ST_ZTPRE
  | C08x => mkDir ZERO_PAD 8 (-1) false 120 T_UINT 0
  | Cs => mkDir 0 0 (-1) false 115 T_PTR 0
  | _ => mkDir 0 0 (-1) false t T_INT 0
  end.

Lemma conv_pieces_ok : forall cnt c a t, 0 <= cnt -> conv_ok c a = true -> (c = Cd -> t = 100 \/ t = 105) ->
  cnt + conv_len c a < INT_MAX ->
  conv_pieces cnt (conv_dir c t) (conv_parg c a) = Some (Fmt.conv_pieces c a, cnt + conv_len c a).
Proof.
  intros cnt c a t Hc OK Ht Hb. unfold conv_len in *.
  destruct c; destruct a as [v|sv]; try discriminate OK; cbn [conv_dir conv_parg].
  - (* [comment removed for export] *) pose proof (int_pieces_len (s32 v <? 0) (dec_udigits (Z.abs (s32 v)))) as L.
    cbn [Fmt.conv_pieces] in Hb |- *. rewrite L in Hb |- *.
    rewrite (conv_pieces_d cnt v t Hc (Ht eq_refl)) by (destruct (s32 v <? 0); lia).
    apply f_equal. apply f_equal2; [reflexivity | destruct (s32 v <? 0); lia].
  - (* [comment removed for export] *) pose proof (int_pieces_len false (dec_udigits (u32 v))) as L.
    cbn [Fmt.conv_pieces] in Hb |- *. rewrite L in Hb |- *.
    assert (R : 0 <= u32 v < 2^64) by (unfold u32; Z.div_mod_to_equations; lia).
    rewrite (conv_pieces_u cnt (u32 v) T_UINT 0 (PA_u (u32 v)) Cu Hc R ltac:(left; split; reflexivity)) by lia.
    apply f_equal. apply f_equal2; [reflexivity | lia].
  - (* [comment removed for export] *) assert (R : 0 <= u32 v < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
    assert (R' : 0 <= u32 v < 2^64) by lia.
    assert (ND : zlength (hex_udigits (u32 v)) + (if u32 v =? 0 then 1 else 0) = Z.max 1 (zlength (hex_udigits (u32 v)))).
    { rewrite <- hex_digits_eq by lia. destruct (Z.eqb_spec (u32 v) 0) as [E|N].
      - rewrite (proj2 (hex_digits_nil _ R') E). change (zlength (@nil Z)) with 0. lia.
      - assert (NN : hex_digits 32 (u32 v) <> []) by (intros X; apply N, (proj1 (hex_digits_nil _ R')), X).
        destruct (hex_digits 32 (u32 v)); [exfalso; apply NN; reflexivity|]. rewrite zlength_cons. pose proof (zlength_nonneg l). lia. }
    assert (L : zlength (List.concat (Fmt.conv_pieces C08x (AInt v))) = Z.max 8 (zlength (hex_udigits (u32 v)) + (if u32 v =? 0 then 1 else 0))).
    { rewrite ND. cbn [Fmt.conv_pieces]. rewrite ND. cbn [List.concat]. rewrite concat_app, !zlength_app. change (zlength (@nil Z)) with 0. rewrite Z.add_0_l.
      pose proof (zlength_nonneg (hex_udigits (u32 v))) as LN.
      replace (zlength (List.concat (if Z.max 1 (zlength (hex_udigits (u32 v))) <? 8 then [zeros (8 - Z.max 1 (zlength (hex_udigits (u32 v))))] else [])))
        with (if Z.max 1 (zlength (hex_udigits (u32 v))) <? 8 then 8 - Z.max 1 (zlength (hex_udigits (u32 v))) else 0).
      2:{ destruct (Z.max 1 (zlength (hex_udigits (u32 v))) <? 8) eqn:E8; cbn [List.concat]; [| reflexivity].
          rewrite app_nil_r. unfold zeros. rewrite zlength_zrepeat; [reflexivity|]. apply Z.ltb_lt in E8. lia. }
      replace (zlength (List.concat match hex_udigits (u32 v) with [] => [[48]; []] | _ :: _ => [hex_udigits (u32 v)] end))
        with (Z.max 1 (zlength (hex_udigits (u32 v)))).
      2:{ destruct (hex_udigits (u32 v)); cbn [List.concat]; rewrite ?app_nil_r; [reflexivity|]. rewrite zlength_cons. pose proof (zlength_nonneg l). lia. }
      destruct (Z.ltb_spec (Z.max 1 (zlength (hex_udigits (u32 v)))) 8); lia. }
    rewrite L in Hb |- *.
    assert (U32U : u32 (u32 v) = u32 v) by (unfold u32; rewrite Z.mod_mod; lia).
    replace (Fmt.conv_pieces C08x (AInt v)) with (Fmt.conv_pieces C08x (AInt (u32 v))) by (cbn [Fmt.conv_pieces]; rewrite U32U; reflexivity).
    exact (conv_pieces_08x cnt (u32 v) Hc R ltac:(lia)).
  - (* [comment removed for export] *) cbn [Fmt.conv_pieces List.concat] in Hb |- *. rewrite app_nil_r in *. rewrite (conv_pieces_s cnt sv 115 0 Hc Hb). reflexivity.
  - (* [comment removed for export] *) pose proof (int_pieces_len false (dec_udigits (u64 v))) as L.
    cbn [Fmt.conv_pieces] in Hb |- *. rewrite L in Hb |- *.
    assert (R : 0 <= u64 v < 2^64) by (unfold u64; Z.div_mod_to_equations; lia).
    rewrite (conv_pieces_u cnt (u64 v) T_SIZET ST_ZTPRE (PA_z (u64 v)) Czu Hc R ltac:(right; split; reflexivity)) by lia.
    apply f_equal. apply f_equal2; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_run_lit : forall l c r, forallb (fun c => negb (c =? 0) && negb (c =? 37)) l = true -> (c = 0 \/ c = 37) ->
  lit_run (l ++ c :: r) = l.
Proof.
  induction l as [|x l IH]; intros c r OK Hc.
  - cbn. destruct Hc as [-> | ->]; reflexivity.
  - cbn in OK. apply andb_prop in OK as [OKx OK]. apply andb_prop in OKx as [N0 N37].
    cbn [lit_run app]. destruct (Z.eqb_spec x 0); [discriminate|]. destruct (Z.eqb_spec x 37); [discriminate|]. cbn [orb].
    f_equal. apply IH; assumption.
Qed.

Lemma ppl_S : forall fuel s args cnt,
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
           else let? (ps, r) := printf_pieces_loop fuel s1 args (cnt + l) in Some (lit :: ps, r))
        else
          match parse_dir s2, args with
          | Some (d, s3), a :: args' =>
              let? (ps1, cnt') := conv_pieces cnt d a in
              let? (ps, r) := printf_pieces_loop fuel s3 args' cnt' in
              Some ([] :: ps1 ++ ps, r)
          | _, _ => None
          end
      end
    end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma parse_pct_next : forall f r args, items_ok (parse_fmt_aux f (37 :: r)) args = true ->
  exists c r2, r = c :: r2 /\ c <> 37 /\ c <> 0.
Proof.
  intros f r args OK. destruct f as [|f]; [cbn in OK; discriminate|].
  rewrite parse_pct_shape in OK. destruct (parse_conv r) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
  pose proof (parse_conv_cases _ _ _ PC) as SH.
  destruct cv; (destruct SH as [-> | ->] || rewrite SH); eexists _, _; (split; [reflexivity| split; lia]).
Qed.

(* [comment removed for export] *)
Lemma parse_dir_1 : forall t ty c2 r2, conv_type t = Some ty -> is_digit t = false -> flag_bit t = None ->
  t <> 42 -> t <> 46 -> t <> 122 ->
  parse_dir (t :: c2 :: r2) = Some (mkDir 0 0 (-1) false t ty 0, c2 :: r2).
Proof.
  intros t ty c2 r2 CT DG FB N42 N46 N122. unfold parse_dir.
  rewrite DG. cbn [andb]. rewrite (parse_flags_cons_none _ _ _ FB).
  destruct (Z.eqb_spec t 42); [lia|]. rewrite (getint_cons_nondigit _ _ _ DG).
  destruct (Z.eqb_spec t 46); [lia|]. destruct (Z.eqb_spec t 122); [lia|]. rewrite CT. reflexivity.
Qed.
Lemma parse_dir_zu : forall rest, parse_dir (122 :: 117 :: rest) = Some (mkDir 0 0 (-1) false 117 T_SIZET ST_ZTPRE, rest).
Proof. intros rest. reflexivity. Qed.
Lemma parse_dir_08x : forall rest, parse_dir (48 :: 56 :: 120 :: rest) = Some (mkDir ZERO_PAD 8 (-1) false 120 T_UINT 0, rest).
Proof. intros rest. vm_compute. reflexivity. Qed.

Lemma zlength_concat_cons : forall (x : list Z) l, zlength (List.concat (x :: l)) = zlength x + zlength (List.concat l).
Proof. intros. cbn [List.concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall (a b : list (list Z)), zlength (List.concat (a ++ b)) = zlength (List.concat a) + zlength (List.concat b).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma fmt_output_nonneg : forall its args, 0 <= zlength (fmt_output its args).
Proof. intros. apply zlength_nonneg. Qed.

Theorem bridge_aux : forall fuel s args cnt pf,
  (Datatypes.length s <= fuel)%nat -> (Datatypes.length s < pf)%nat ->
  items_ok (parse_fmt_aux fuel s) args = true ->
  0 <= cnt -> cnt + zlength (fmt_output (parse_fmt_aux fuel s) args) < INT_MAX ->
  printf_pieces_loop pf (s ++ [0]) (to_pargs (parse_fmt_aux fuel s) args) cnt
  = Some (fmt_pieces (parse_fmt_aux fuel s) args, cnt + zlength (fmt_output (parse_fmt_aux fuel s) args)).
Proof.
  induction fuel as [|f IH]; intros s args cnt pf Hlen Hpf OK Hc Hb.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn in OK. destruct args; [| discriminate].
    destruct pf as [|pf]; [lia|]. cbn. rewrite Z.add_0_r. reflexivity.
  - destruct s as [|c s0].
    { cbn in OK. destruct args; [| discriminate]. destruct pf as [|pf]; [cbn in Hpf; lia|]. cbn. rewrite Z.add_0_r. reflexivity. }
    destruct pf as [|pf]; [cbn in Hpf; lia|]. cbn in Hlen, Hpf.
    destruct (Z.eqb_spec c 37) as [E37|N37].
    + (* [comment removed for export] *)
      subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      unfold fmt_output in Hb |- *. cbn [items_ok to_pargs fmt_pieces hd tl] in *. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      pose proof (parse_conv_cases _ _ _ PC) as SH.
      cbn [hd tl] in Hb |- *.
      rewrite zlength_concat_cons, zlength_concat_app in Hb |- *. change (zlength (@nil Z)) with 0 in Hb |- *.
      fold (fmt_output (parse_fmt_aux f r') args') in Hb |- *. fold (conv_len cv a) in Hb |- *.
      pose proof (fmt_output_nonneg (parse_fmt_aux f r') args') as RN.
      assert (CL : 0 <= conv_len cv a) by (unfold conv_len; apply zlength_nonneg).
      rewrite ppl_S. cbn [app]. change (37 =? 0) with false. cbv iota.
      change (lit_run (37 :: s0 ++ [0])) with (@nil Z). cbv zeta. change (zlength (@nil Z)) with 0. cbn [Datatypes.length skipn].
      change (37 =? 37) with true. change (0 <? 0) with false. cbn [andb].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (STEP : forall tb t, s0 = tb ++ r' -> (1 <= Datatypes.length tb)%nat ->
                (match s0 ++ [0] with [] => true | c2 :: _ => c2 =? 37 end) = false ->
                parse_dir (s0 ++ [0]) = Some (conv_dir cv t, r' ++ [0]) -> (cv = Cd -> t = 100 \/ t = 105) ->
                (if match s0 ++ [0] with [] => true | c2 :: _ => c2 =? 37 end then None
                 else match parse_dir (s0 ++ [0]) with
                      | Some (d, s3) => let? (ps1, cnt') := conv_pieces cnt d (conv_parg cv a) in
                                        let? (ps, r) := printf_pieces_loop pf s3 (to_pargs (parse_fmt_aux f r') args') cnt' in Some ([] :: ps1 ++ ps, r)
                      | None => None end)
                = Some ([] :: Fmt.conv_pieces cv a ++ fmt_pieces (parse_fmt_aux f r') args', cnt + (0 + (conv_len cv a + zlength (fmt_output (parse_fmt_aux f r') args'))))).
      { intros tb t Es0 Ltb NX PD Ht. rewrite NX, PD.
        rewrite (conv_pieces_ok cnt cv a t Hc OKc Ht) by lia.
        subst s0. rewrite length_app in Hlen, Hpf.
        rewrite (IH r' args' (cnt + conv_len cv a) pf) by (first [lia | exact OK]).
        f_equal. f_equal. lia. }
      Local Ltac pd1 SH rq := rewrite SH; cbn [app]; let E := fresh "E" in destruct (rq ++ [0]) as [|c2 r2] eqn:E; [destruct rq; discriminate E|]; apply parse_dir_1; try reflexivity; lia.
      destruct cv; destruct a as [v|sv]; try discriminate OKc.
      * destruct SH as [SH | SH];
          [ eapply (STEP [100] 100 SH); [cbn; lia| rewrite SH; reflexivity| pd1 SH r' | intros _; lia]
          | eapply (STEP [105] 105 SH); [cbn; lia| rewrite SH; reflexivity| pd1 SH r' | intros _; lia] ].
      * eapply (STEP [117] 117 SH); [cbn; lia| rewrite SH; reflexivity| pd1 SH r' | intros X; discriminate X].
      * eapply (STEP [48; 56; 120] 120 SH); [cbn; lia| rewrite SH; reflexivity| rewrite SH; cbn [app]; apply parse_dir_08x | intros X; discriminate X].
      * eapply (STEP [115] 115 SH); [cbn; lia| rewrite SH; reflexivity| pd1 SH r' | intros X; discriminate X].
      * eapply (STEP [122; 117] 117 SH); [cbn; lia| rewrite SH; reflexivity| rewrite SH; cbn [app]; apply parse_dir_zu | intros X; discriminate X].
    + (* [comment removed for export] *)
      rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL.
      destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      unfold fmt_output in Hb |- *. cbn [items_ok to_pargs fmt_pieces] in *. apply andb_prop in OK as [OKl OK].
      assert (Hl : exists l0, l = c :: l0).
      { destruct l as [|c' l0]; [| cbn in E1; injection E1 as <- _; eexists; reflexivity].
        exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      destruct Hl as [l0 El].
      rewrite zlength_concat_cons in Hb |- *.
      fold (fmt_output (parse_fmt_aux f r) args) in Hb |- *.
      pose proof (fmt_output_nonneg (parse_fmt_aux f r) args) as RN.
      assert (Ll : 1 <= zlength l) by (rewrite El, zlength_cons; pose proof (zlength_nonneg l0); lia).
      rewrite ppl_S. cbn [app].
      assert (C0 : (c =? 0) = false).
      { rewrite El in OKl. cbn in OKl. apply andb_prop in OKl as [X _]. apply andb_prop in X as [X _]. destruct (c =? 0); [discriminate| reflexivity]. }
      rewrite C0.
      assert (LR : lit_run (c :: s0 ++ [0]) = l).
      { change (c :: s0 ++ [0]) with ((c :: s0) ++ [0]). rewrite E1, <- app_assoc.
        destruct R1 as [->|[r'' ->]]; cbn [app]; apply lit_run_lit; [exact OKl| left; reflexivity| exact OKl| right; reflexivity]. }
      rewrite LR. cbv zeta.
      replace (skipn (Datatypes.length l) (c :: s0 ++ [0])) with (r ++ [0]).
      2:{ change (c :: s0 ++ [0]) with ((c :: s0) ++ [0]). rewrite E1, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
      pose proof (f_equal (@Datatypes.length Z) E1) as LEN. rewrite El, length_app in LEN. cbn [Datatypes.length] in LEN.
      destruct R1 as [->|[r'' ->]].
      * cbn [app]. change (0 =? 37) with false. cbn [andb].
        destruct (Z.ltb_spec 0 (zlength l)); [| lia].
        destruct (Z.ltb_spec (INT_MAX - cnt) (zlength l)); [lia|].
        pose proof (IH [] args (cnt + zlength l) pf ltac:(cbn; lia) ltac:(cbn; lia) OK ltac:(lia) ltac:(lia)) as IH0. cbn [app] in IH0.
        rewrite IH0. f_equal. f_equal. lia.
      * cbn [app]. change (37 =? 37) with true.
        destruct (parse_pct_next f r'' args OK) as (c2 & r2 & -> & N2 & _).
        cbn [app]. destruct (Z.eqb_spec c2 37); [lia|]. cbn [andb].
        destruct (Z.ltb_spec 0 (zlength l)); [| lia].
        destruct (Z.ltb_spec (INT_MAX - cnt) (zlength l)); [lia|].
        change (37 :: c2 :: r2 ++ [0]) with ((37 :: c2 :: r2) ++ [0]).
        rewrite (IH (37 :: c2 :: r2) args (cnt + zlength l) pf); [| cbn in LEN |- *; lia| cbn in LEN |- *; lia| exact OK| lia| lia].
        f_equal. f_equal. lia.
Qed.

Theorem fmt_bridge : forall fs args,
  items_ok (fmt fs) args = true -> zlength (fmt_output (fmt fs) args) < INT_MAX ->
  printf_pieces (str fs ++ [0]) (to_pargs (fmt fs) args)
  = Some (fmt_pieces (fmt fs) args, zlength (fmt_output (fmt fs) args)).
Proof.
  intros fs args OK Hb. unfold printf_pieces, fmt, parse_fmt in *.
  rewrite (bridge_aux (Datatypes.length (str fs)) (str fs) args 0 (Datatypes.length (str fs ++ [0])));
    [f_equal| lia| rewrite length_app; cbn; lia| exact OK| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma pct_pass1 : forall f r args, items_ok (parse_fmt_aux f (37 :: r)) args = true ->
  match r ++ [0] with
  | [] => false
  | c2 :: _ => negb (c2 =? 37) && match parse_dir (r ++ [0]) with Some _ => true | None => false end
  end = true.
Proof.
  intros f r args OK. destruct f as [|f]; [cbn in OK; discriminate|].
  rewrite parse_pct_shape in OK. destruct (parse_conv r) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
  cbn [items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc _].
  pose proof (parse_conv_cases _ _ _ PC) as SH.
  Local Ltac pdx SH rq t ty := rewrite SH; cbn [app Z.eqb Pos.eqb negb andb]; let E := fresh "E" in
    destruct (rq ++ [0]) as [|c2 r2] eqn:E; [destruct rq; discriminate E|]; rewrite (parse_dir_1 t ty); try reflexivity; lia.
  destruct cv; destruct a as [v|sv]; try discriminate OKc.
  - destruct SH as [SH|SH]; [pdx SH r' 100 T_INT | pdx SH r' 105 T_INT].
  - pdx SH r' 117 T_UINT.
  - rewrite SH. cbn [app Z.eqb Pos.eqb negb andb]. rewrite parse_dir_08x. reflexivity.
  - pdx SH r' 115 T_PTR.
  - rewrite SH. cbn [app Z.eqb Pos.eqb negb andb]. rewrite parse_dir_zu. reflexivity.
Qed.

Theorem fmt_pass1 : forall fs args, items_ok (fmt fs) args = true -> zlength (str fs) <= INT_MAX ->
  pass1_ok (str fs ++ [0]) = true.
Proof.
  intros fs args OK Hl. unfold fmt, parse_fmt in OK. unfold pass1_ok.
  remember (Datatypes.length (str fs)) as fuel eqn:Efuel.
  assert (Hlen : (Datatypes.length (str fs) <= fuel)%nat) by lia. clear Efuel.
  destruct (str fs) as [|c s0] eqn:Es.
  - cbn. reflexivity.
  - destruct fuel as [|f]; [cbn in Hlen; lia|].
    destruct (Z.eqb_spec c 37) as [->|N37].
    + cbn [app]. change (lit_run (37 :: s0 ++ [0])) with (@nil Z). cbv zeta. change (zlength (@nil Z) <=? INT_MAX) with true.
      cbn [andb Datatypes.length skipn]. change (37 =? 0) with false. cbv iota.
      exact (pct_pass1 (S f) s0 args OK).
    + rewrite (parse_lit_shape f c s0 N37) in OK.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL.
      destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [items_ok] in OK. apply andb_prop in OK as [OKl OK].
      change ((c :: s0) ++ [0]) with ((c :: s0) ++ [0]). rewrite E1, <- app_assoc.
      assert (LR : lit_run (l ++ r ++ [0]) = l).
      { destruct R1 as [->|[r'' ->]]; cbn [app]; apply lit_run_lit; [exact OKl| left; reflexivity| exact OKl| right; reflexivity]. }
      rewrite LR. cbv zeta.
      pose proof (f_equal (@Datatypes.length Z) E1) as LEN. rewrite length_app in LEN. cbn [Datatypes.length] in LEN.
      replace (zlength l <=? INT_MAX) with true by (symmetry; apply Z.leb_le; unfold zlength in *; cbn [Datatypes.length] in Hl; lia).
      rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app andb].
      destruct R1 as [->|[r'' ->]]; [reflexivity|].
      cbn [app]. change (37 =? 0) with false. cbv iota.
      destruct l as [|c' l0]; [exfalso; cbn in E1; injection E1 as E _; exact (N37 E)|]. cbn [Datatypes.length] in LEN.
      destruct f as [|f']; [cbn in LEN, Hlen; lia|].
      exact (pct_pass1 (S f') r'' args OK).
Qed.
End Printf_fmt.
