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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From Stdlib Require NArith.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require I_memcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Printf_outsA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
Section OutsA.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Local Notation outsk := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk OUT).

  (* [comment removed for export] *)
  Definition mle {B} (X Y : M St B) : Prop :=
    forall s RNG (Q : B * St -> footprint -> machine_state -> Prop) ms,
      implS asegs RNG (X s) (epostF Q) ms -> implS asegs RNG (Y s) (epostF Q) ms.

  #[using="Type"] Lemma mle_refl : forall {B} (X : M St B), mle X X.
  Proof. intros B X s RNG Q ms H. exact H. Qed.
  #[using="Type"] Lemma mle_trans : forall {B} (X Y Z : M St B), mle X Y -> mle Y Z -> mle X Z.
  Proof. intros B X Y Z H1 H2 s RNG Q ms H. apply H2, H1, H. Qed.
  #[using="Type"] Lemma mle_bind_ext : forall {A B} (a : M St A) (k1 k2 : A -> M St B), (forall x, mle (k1 x) (k2 x)) -> mle (mbind a k1) (mbind a k2).
  Proof.
    intros A B a k1 k2 HK s RNG Q ms H. unfold mbind, ebind in *.
    eapply (implF_bind_ext2 asegs _ _ _ _ _ (fun _ => True)); [apply tforall_true | | exact H].
    cbv beta. intros [|[x s']] RNG' ms' _ H'; cbn [fst snd] in *; [exact H' | apply HK; exact H'].
  Qed.
  #[using="Type"] Lemma mle_ret_l : forall {A B} (v : A) (k : A -> M St B), mle (mbind (mret v) k) (k v).
  Proof. intros A B v k s RNG Q ms H. exact H. Qed.
  #[using="Type"] Lemma mle_assoc_rev : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C),
    mle (mbind (mbind a b) k) (mbind a (fun x => mbind (b x) k)).
  Proof.
    intros A B C a b k s RNG Q ms H. unfold mbind, ebind in *.
    apply (implF_bind_assoc_rev asegs) in H.
    eapply (implF_bind_ext2 asegs _ _ _ _ _ (fun _ => True)); [apply tforall_true | | exact H].
    cbv beta. intros [|[x s']] RNG' ms' _ H'; cbn [ITree.bind fst snd] in *; exact H'.
  Qed.
  #[using="Type"] Lemma outsk_mle : forall {B} ps (k1 k2 : M St B), mle k1 k2 -> mle (outsk ps k1) (outsk ps k2).
  Proof.
    induction ps as [|p ps IH]; intros k1 k2 HK; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]; [exact HK|].
    apply mle_bind_ext. intros x. apply IH. exact HK.
  Qed.

  #[using="Type"] Lemma mpad_outsA : forall {B} c w l fl pp (K : unit -> M St B),
    pad_pieces c w l fl = Some pp -> mle (mbind (mpad OUT c w l fl) K) (outsk pp (K tt)).
  Proof.
    intros B c w l fl pp K P. unfold mpad, pad_pieces in *.
    destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
    - inversion P; subst. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]. apply mle_ret_l.
    - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk].
      apply mle_bind_ext. intros []. apply mle_refl.
  Qed.

  #[using="Type"] Lemma conv_tail_outsA : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B),
    tail_pieces cnt fl w p prefix body = Some (ps, r) -> mle (mbind (conv_tail OUT cnt fl w p prefix body) K) (outsk ps (K r)).
  Proof.
    intros B cnt fl w p prefix body ps r K T. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
    destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
    destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
    destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
    destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
    destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
    destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
    inversion T; subst. clear T.
    match goal with |- mle _ (outsk ?L (K ?rr)) =>
      replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
        by (rewrite ?outsk_app; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]; rewrite ?outsk_app; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]; reflexivity) end.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P1)|]. cbv beta.
    apply outsk_mle.
    eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x2.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P2)|]. cbv beta.
    apply outsk_mle.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P3)|]. cbv beta.
    apply outsk_mle.
    eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x5.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P4)|]. cbv beta.
    apply outsk_mle.
    apply mle_ret_l.
  Qed.

  #[using="Type"] Lemma conv_int_outsA : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B),
    int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> mle (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) (outsk ps (K r)).
  Proof.
    intros B cnt fl w p xp argi prefix body ps r K T. unfold conv_int, int_pieces in *.
    destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
    destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outsA; eassumption.
  Qed.

  #[using="Type"] Lemma conv_outsA : forall {B} cnt d a ps r (K : Z -> M St B),
    conv_pieces cnt d a = Some (ps, r) -> mle (mbind (conv OUT cnt d a) K) (outsk ps (K r)).
  Proof.
    intros B cnt d a ps r K T. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
    destruct a as [str|i|u|zu].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outsA; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outsA; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outsA; eassumption.
    - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
      destruct (d_t d =? 117); [|discriminate]. eapply conv_int_outsA; eassumption.
  Qed.

  #[using="Type"] Lemma printf_loop_outsA : forall {B} fuel s args cnt ps r (k : Z -> M St B),
    printf_pieces_loop fuel s args cnt = Some (ps, r) -> mle (mbind (printf_loop OUT fuel s args cnt) k) (outsk ps (k r)).
  Proof.
    induction fuel as [|fuel IH]; intros s args cnt ps r k P; [discriminate|].
    cbn [printf_pieces_loop] in P. cbn [printf_loop].
    destruct s as [|c s1]; [discriminate|].
    destruct (c =? 0). { inversion P; subst. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]. apply mle_ret_l. }
    cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
    destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
    destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
    destruct (0 <? zlength lit).
    - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
      destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
      inversion P; subst. clear P. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk].
      eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x.
      eapply IH; exact R.
    - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P.
      match goal with |- mle _ (outsk ?L (k ?rr)) =>
        replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk].
      eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x.
      eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (conv_outsA _ _ _ _ _ _ C)|]. cbv beta.
      apply outsk_mle. eapply IH; exact R.
  Qed.

  #[using="Type"] Theorem printf_model_outs_mle : forall {B} fmt args ps r (k : Z -> M St B),
    printf_pieces fmt args = Some (ps, r) -> mle (mbind (printf_model OUT fmt args) k) (outsk ps (k r)).
  Proof. intros B fmt args ps r k P. eapply printf_loop_outsA; exact P. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem printf_model_outsA : forall {B} RNG fmt args ps r (k : Z -> M St B) st Q ms,
    printf_pieces fmt args = Some (ps, r) ->
    implAM RNG (mbind (printf_model OUT fmt args) k) st Q ms -> implAM RNG (outsk ps (k r)) st Q ms.
  Proof. intros B RNG fmt args ps r k st Q ms P H. unfold implAM in *. eapply printf_model_outs_mle; [exact P | exact H]. Qed.
End OutsA.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
Section OutsA.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Local Notation outsk := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk OUT).

  (* [comment removed for export] *)
  Definition mle {B} (X Y : M St B) : Prop :=
    forall s RNG (Q : B * St -> footprint -> machine_state -> Prop) ms,
      implS asegs RNG (X s) (epostF Q) ms -> implS asegs RNG (Y s) (epostF Q) ms.

  #[using="Type"] Lemma mle_refl : forall {B} (X : M St B), mle X X.
  Proof. intros B X s RNG Q ms H. exact H. Qed.
  #[using="Type"] Lemma mle_trans : forall {B} (X Y Z : M St B), mle X Y -> mle Y Z -> mle X Z.
  Proof. intros B X Y Z H1 H2 s RNG Q ms H. apply H2, H1, H. Qed.
  #[using="Type"] Lemma mle_bind_ext : forall {A B} (a : M St A) (k1 k2 : A -> M St B), (forall x, mle (k1 x) (k2 x)) -> mle (mbind a k1) (mbind a k2).
  Proof.
    intros A B a k1 k2 HK s RNG Q ms H. unfold mbind, ebind in *.
    eapply (implF_bind_ext2 asegs _ _ _ _ _ (fun _ => True)); [apply tforall_true | | exact H].
    cbv beta. intros [|[x s']] RNG' ms' _ H'; cbn [fst snd] in *; [exact H' | apply HK; exact H'].
  Qed.
  #[using="Type"] Lemma mle_ret_l : forall {A B} (v : A) (k : A -> M St B), mle (mbind (mret v) k) (k v).
  Proof. intros A B v k s RNG Q ms H. exact H. Qed.
  #[using="Type"] Lemma mle_assoc_rev : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C),
    mle (mbind (mbind a b) k) (mbind a (fun x => mbind (b x) k)).
  Proof.
    intros A B C a b k s RNG Q ms H. unfold mbind, ebind in *.
    apply (implF_bind_assoc_rev asegs) in H.
    eapply (implF_bind_ext2 asegs _ _ _ _ _ (fun _ => True)); [apply tforall_true | | exact H].
    cbv beta. intros [|[x s']] RNG' ms' _ H'; cbn [ITree.bind fst snd] in *; exact H'.
  Qed.
  #[using="Type"] Lemma outsk_mle : forall {B} ps (k1 k2 : M St B), mle k1 k2 -> mle (outsk ps k1) (outsk ps k2).
  Proof.
    induction ps as [|p ps IH]; intros k1 k2 HK; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]; [exact HK|].
    apply mle_bind_ext. intros x. apply IH. exact HK.
  Qed.

  #[using="Type"] Lemma mpad_outsA : forall {B} c w l fl pp (K : unit -> M St B),
    pad_pieces c w l fl = Some pp -> mle (mbind (mpad OUT c w l fl) K) (outsk pp (K tt)).
  Proof.
    intros B c w l fl pp K P. unfold mpad, pad_pieces in *.
    destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
    - inversion P; subst. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]. apply mle_ret_l.
    - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk].
      apply mle_bind_ext. intros []. apply mle_refl.
  Qed.

  #[using="Type"] Lemma conv_tail_outsA : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B),
    tail_pieces cnt fl w p prefix body = Some (ps, r) -> mle (mbind (conv_tail OUT cnt fl w p prefix body) K) (outsk ps (K r)).
  Proof.
    intros B cnt fl w p prefix body ps r K T. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
    destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
    destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
    destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
    destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
    destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
    destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
    inversion T; subst. clear T.
    match goal with |- mle _ (outsk ?L (K ?rr)) =>
      replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
        by (rewrite ?outsk_app; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]; rewrite ?outsk_app; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]; reflexivity) end.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P1)|]. cbv beta.
    apply outsk_mle.
    eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x2.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P2)|]. cbv beta.
    apply outsk_mle.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P3)|]. cbv beta.
    apply outsk_mle.
    eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x5.
    eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (mpad_outsA _ _ _ _ _ _ P4)|]. cbv beta.
    apply outsk_mle.
    apply mle_ret_l.
  Qed.

  #[using="Type"] Lemma conv_int_outsA : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B),
    int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> mle (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) (outsk ps (K r)).
  Proof.
    intros B cnt fl w p xp argi prefix body ps r K T. unfold conv_int, int_pieces in *.
    destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
    destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outsA; eassumption.
  Qed.

  #[using="Type"] Lemma conv_outsA : forall {B} cnt d a ps r (K : Z -> M St B),
    conv_pieces cnt d a = Some (ps, r) -> mle (mbind (conv OUT cnt d a) K) (outsk ps (K r)).
  Proof.
    intros B cnt d a ps r K T. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
    destruct a as [str|i|u|zu].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outsA; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outsA; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outsA; eassumption.
    - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
      destruct (d_t d =? 117); [|discriminate]. eapply conv_int_outsA; eassumption.
  Qed.

  #[using="Type"] Lemma printf_loop_outsA : forall {B} fuel s args cnt ps r (k : Z -> M St B),
    printf_pieces_loop fuel s args cnt = Some (ps, r) -> mle (mbind (printf_loop OUT fuel s args cnt) k) (outsk ps (k r)).
  Proof.
    induction fuel as [|fuel IH]; intros s args cnt ps r k P; [discriminate|].
    cbn [printf_pieces_loop] in P. cbn [printf_loop].
    destruct s as [|c s1]; [discriminate|].
    destruct (c =? 0). { inversion P; subst. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk]. apply mle_ret_l. }
    cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
    destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
    destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
    destruct (0 <? zlength lit).
    - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
      destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
      inversion P; subst. clear P. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk].
      eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x.
      eapply IH; exact R.
    - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P.
      match goal with |- mle _ (outsk ?L (k ?rr)) =>
        replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.outsk].
      eapply mle_trans; [apply mle_assoc_rev|]. apply mle_bind_ext. intros x.
      eapply mle_trans; [apply mle_assoc_rev|]. eapply mle_trans; [apply (conv_outsA _ _ _ _ _ _ C)|]. cbv beta.
      apply outsk_mle. eapply IH; exact R.
  Qed.

  #[using="Type"] Theorem printf_model_outs_mle : forall {B} fmt args ps r (k : Z -> M St B),
    printf_pieces fmt args = Some (ps, r) -> mle (mbind (printf_model OUT fmt args) k) (outsk ps (k r)).
  Proof. intros B fmt args ps r k P. eapply printf_loop_outsA; exact P. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem printf_model_outsA : forall {B} RNG fmt args ps r (k : Z -> M St B) st Q ms,
    printf_pieces fmt args = Some (ps, r) ->
    implAM RNG (mbind (printf_model OUT fmt args) k) st Q ms -> implAM RNG (outsk ps (k r)) st Q ms.
  Proof. intros B RNG fmt args ps r k st Q ms P H. unfold implAM in *. eapply printf_model_outs_mle; [exact P | exact H]. Qed.
End OutsA.
End CANSEC1.
End TwB.
End Printf_outsA.

(* [comment removed for export] *)
Module RtCellsS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation rt_real_strlen m := (rw_cells asegs m 0xa71d8 [C8 (Z_to_bv 64 0x9edb8)]).
Notation rt_real_strchr m := (rw_cells asegs m 0xa71e8 [C8 (Z_to_bv 64 0x9ebcc)]).
Notation rt_real_strrchr m := (rw_cells asegs m 0xa71f0 [C8 (Z_to_bv 64 0x9f038)]).
Notation rt_real_memchr m := (rw_cells asegs m 0xa7200 [C8 (Z_to_bv 64 0x9e5a4)]).
Notation rt_real_fread m := (rw_cells asegs m 0xa7218 [C8 (Z_to_bv 64 0x9a954)]).
Notation rt_real_fwrite m := (rw_cells asegs m 0xa7220 [C8 (Z_to_bv 64 0x9abc8)]).
Notation rt_real_vsnprintf m := (rw_cells asegs m 0xa7248 [C8 (Z_to_bv 64 0x9e00c)]).
Notation rt_real_strerror m := (rw_cells asegs m 0xa7268 [C8 (Z_to_bv 64 0x944c4); C8 (Z_to_bv 64 0x9ed20)]).   (* [comment removed for export] *)
Notation rt_real_fopen m := (rw_cells asegs m 0xa7290 [C8 (Z_to_bv 64 0x9a7c4); C8 (Z_to_bv 64 0x9a324); C8 (Z_to_bv 64 0x9a200)]).   (* [comment removed for export] *)
Notation rt_real_strnlen m := (rw_cells asegs m 0xa7308 [C8 (Z_to_bv 64 0x9eff4)]).
(* [comment removed for export] *)
Notation rt_isl m := (rw_cells asegs m 0x140220 [C8 (Z_to_bv 64 72340172838076673)]).
Notation rt_ssc m := (rw_cells asegs m 0x140218 [C8 (Z_to_bv 64 0x0101000100000000)]).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Record icptenv (m : word -> option byte) : Prop := mkIE {
  ie_got : rt_got m; ie_ric : rt_got_ric m; ie_shb : rt_shbase m; ie_ini : rt_inited m; ie_lay : rt_layout m;
  ie_mem : rt_real_mem m; ie_read : rt_real_read m; ie_printf : rt_real_printf m;
  ie_strlen : rt_real_strlen m; ie_strchr : rt_real_strchr m; ie_strrchr : rt_real_strrchr m; ie_memchr : rt_real_memchr m;
  ie_fread : rt_real_fread m; ie_fwrite : rt_real_fwrite m; ie_vsnprintf : rt_real_vsnprintf m; ie_strerror : rt_real_strerror m;
  ie_fopen : rt_real_fopen m; ie_strnlen : rt_real_strnlen m;
  ie_isl : rt_isl m; ie_ssc : rt_ssc m
}.

(* [comment removed for export] *)
Definition iesafe (W : list (Z * Z)) : Prop :=
  disjoint_from W 0xa54a0 48 /\ disjoint_from W 0xa6018 8 /\ disjoint_from W 0xa71d8 400
  /\ disjoint_from W 0xae5f8 3328 /\ disjoint_from W 0x140218 16.

#[using="Type"] Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof. induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H A B; [exact I|]. destruct H as [H1 H2]. split; [lia| eapply IH; eauto]. Qed.

#[using="Type"] Lemma icptenv_transport : forall W m m', icptenv m -> munch W m m' -> wmono asegs m m' -> iesafe W -> icptenv m'.
Proof.
  intros W m m' [] MU WM (D1 & D2 & D3 & D4 & D5).
  constructor;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM |]; cbn [cells_size csize Nat.add];
     first [ eapply disjoint_from_sub; [exact D1| lia| lia] | eapply disjoint_from_sub; [exact D2| lia| lia]
           | eapply disjoint_from_sub; [exact D3| lia| lia] | eapply disjoint_from_sub; [exact D4| lia| lia]
           | eapply disjoint_from_sub; [exact D5| lia| lia] ]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iesafe_high : forall W, Forall (fun iv => 0x140228 <= fst iv) W -> iesafe W.
Proof.
  intros W H. unfold iesafe. repeat split; (induction H as [|[lo hi] W Hlo HW IH]; cbn [disjoint_from]; [exact I|]; cbn [fst] in Hlo; split; [lia| exact IH]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sobj (RNG : footprint) (m : word -> option byte) (lo hi : Z) : Prop :=
  app_blk lo hi /\ unpoisoned m lo hi /\ hi - lo <= 2^40
  /\ exists RLO RHI, (RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)
                  /\ wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

#[using="Type"] Lemma sobj_sub : forall RNG m lo hi lo' hi', sobj RNG m lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> sobj RNG m lo' hi'.
Proof.
  intros RNG m lo hi lo' hi' (AB & U & SZ & RLO & RHI & H & W & R) A B C.
  split; [eapply app_blk_sub; eauto|]. split; [eapply unpoisoned_sub; [exact U| lia| lia]|]. split; [lia|].
  exists RLO, RHI. split; [lia|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition appW (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= KLOW \/ KHIGH <= fst iv) W.

#[using="Type"] Lemma appW_shadow_disjoint : forall W lo hi, appW W -> app_blk lo hi -> lo < hi ->
  disjoint_from W (shad lo) (shad (hi - 1) + 1 - shad lo).
Proof.
  intros W lo hi HW [LE AB] LT. induction HW as [|[a b] W Hab HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst snd] in Hab. split; [| exact IH].
  rewrite !shad_div. unfold ASHOFF, KLOW, KHIGH, KEND in *. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma sobj_transport : forall RNG W m m' lo hi, sobj RNG m lo hi -> munch W m m' -> wmono asegs m m' -> appW W -> sobj RNG m' lo hi.
Proof.
  intros RNG W m m' lo hi (AB & U & SZ & RLO & RHI & H & WR & R) MU WM HW.
  split; [exact AB|]. split.
  - destruct (Z_lt_le_dec lo hi) as [LT|GE].
    + eapply unpoisoned_munch; [exact U| exact MU|]. apply appW_shadow_disjoint; assumption.
    + destruct U as (U0 & U1 & _). split; [exact U0|]. split; [exact U1|]. intros G HG. lia.
  - split; [exact SZ|]. exists RLO, RHI. split; [exact H|]. split; [eapply wr_at_transport; eauto| exact R].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sobj_appW : forall RNG m lo hi, sobj RNG m lo hi -> appW [(lo, hi)].
Proof.
  intros RNG m lo hi ((LE & AB) & _). constructor; [| constructor]. cbn [fst snd]. unfold KLOW, KHIGH, KEND in *. lia.
Qed.

#[using="Type"] Lemma fp_le_sobj : forall RNG RNG' m lo hi, fp_le RNG RNG' -> sobj RNG m lo hi -> sobj RNG' m lo hi.
Proof.
  intros RNG RNG' m lo hi FP (AB & U & SZ & RLO & RHI & H & WR & R).
  split; [exact AB|]. split; [exact U|]. split; [exact SZ|]. exists RLO, RHI. split; [exact H|]. split; [exact WR|].
  eapply rng_fp_le; eauto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma iesafe_nil : iesafe [].
Proof. repeat split. Qed.
#[using="Type"] Lemma iesafe_cons : forall a b W, iesafe [(a, b)] -> iesafe W -> iesafe ((a, b) :: W).
Proof. intros a b W (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold iesafe in *; cbn [disjoint_from] in *. intuition. Qed.
#[using="Type"] Lemma iesafe_app : forall W1 W2, iesafe W1 -> iesafe W2 -> iesafe (W1 ++ W2).
Proof.
  induction W1 as [|[a b] W1 IH]; intros W2 H1 H2; [exact H2|]. cbn [app].
  destruct H1 as (A1 & A2 & A3 & A4 & A5). cbn [disjoint_from] in *.
  apply iesafe_cons; [unfold iesafe; cbn [disjoint_from]; intuition|]. apply IH; [unfold iesafe; intuition| exact H2].
Qed.
#[using="Type"] Lemma iesafe_one_high : forall a b, 0x140228 <= a -> iesafe [(a, b)].
Proof. intros a b H. apply iesafe_high. constructor; [exact H| constructor]. Qed.
#[using="Type"] Lemma iesafe_one_sub : forall a b a' b', iesafe [(a, b)] -> a <= a' -> b' <= b -> iesafe [(a', b')].
Proof. intros a b a' b' (A1 & A2 & A3 & A4 & A5) Ha Hb. unfold iesafe in *; cbn [disjoint_from] in *. intuition lia. Qed.
#[using="Type"] Lemma iesafe_In : forall W iv, iesafe W -> In iv W -> iesafe [iv].
Proof.
  induction W as [|[a b] W IH]; intros iv H Hin; [destruct Hin|].
  destruct H as (A1 & A2 & A3 & A4 & A5). cbn [disjoint_from] in *. destruct Hin as [<-|Hin].
  - unfold iesafe; cbn [disjoint_from]; intuition.
  - apply IH; [unfold iesafe; intuition| exact Hin].
Qed.
#[using="Type"] Lemma appW_In : forall W iv, appW W -> In iv W -> appW [iv].
Proof. intros W iv H Hin. constructor; [exact (proj1 (Forall_forall _ _) H iv Hin)| constructor]. Qed.
#[using="Type"] Lemma appW_one_sub : forall a b a' b', appW [(a, b)] -> a <= a' -> b' <= b -> appW [(a', b')].
Proof. intros a b a' b' H Ha Hb. inversion H as [|? ? H1 _]; subst. cbn [fst snd] in H1. constructor; [cbn [fst snd]; lia| constructor]. Qed.
#[using="Type"] Lemma appW_cons : forall a b W, appW [(a, b)] -> appW W -> appW ((a, b) :: W).
Proof. intros a b W H HW. inversion H; subst. constructor; assumption. Qed.
#[using="Type"] Lemma appW_one_high : forall a b, KHIGH <= a -> appW [(a, b)].
Proof. intros a b H. constructor; [right; exact H| constructor]. Qed.
End CANSEC1.

(* [comment removed for export] *)
Ltac solve_appW :=
  repeat first [ apply Forall_nil
               | apply appW_cons;
                 [ first [ assumption | apply appW_one_high; unfold KHIGH in *; lia
                         | match goal with H : appW [(_, _)] |- _ => eapply appW_one_sub; [exact H | lia | lia] end
                         | constructor; [unfold KLOW, KHIGH in *; cbn [fst snd]; first [lia | left; lia | right; lia] | constructor] ] |] ].
Ltac solve_iesafe :=
  first [ solve [ apply iesafe_high; repeat first [ apply Forall_nil | apply Forall_cons; [cbn [fst snd]; unfold KHIGH in *; lia|] ] ]
        | repeat first [ apply iesafe_nil
                       | apply iesafe_cons;
                         [ first [ assumption | apply iesafe_one_high; unfold KHIGH in *; lia
                                 | match goal with H : iesafe [(_, _)] |- _ => eapply iesafe_one_sub; [exact H | lia | lia] end
                                 | unfold iesafe; cbn [disjoint_from]; unfold KHIGH in *; repeat split; lia ] |] ] ].

(* [comment removed for export] *)
Tactic Notation "ienv_now" constr(ENV) constr(MU) constr(WM) "as" ident(X) :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (X : icptenv mm) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]) end.
Tactic Notation "sobj_now" constr(SO) constr(MU) constr(WM) "as" ident(X) :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of SO with sobj ?R _ ?lo ?hi =>
      assert (X : sobj R mm lo hi) by (eapply sobj_transport; [exact SO | exact MU | exact WM | solve_appW]) end end.

(* [comment removed for export] *)
Ltac icpt_prem RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- icptenv _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- ~ In _ _ => first [assumption | eassumption]
  | |- sobj _ _ _ _ => first [ assumption | match goal with H : sobj _ _ _ _ |- _ => eapply sobj_sub; [exact H | lia | lia | lia] end ]
  | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia]
                          | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | lia] end ]
  | |- (bv_unsigned (Z_to_bv 64 _) mod 256 <> 0)%Z => let X := fresh in rewrite unsigned_lit by lia; intros X; vm_compute in X; discriminate X
  | |- _ => first [ assumption | lia | rewrite ?length_app; cbn [length]; lia ]
  end.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation rt_real_strlen m := (rw_cells asegs m 0xa75b8 [C8 (Z_to_bv 64 0x9f19c)]).
Notation rt_real_strchr m := (rw_cells asegs m 0xa75c8 [C8 (Z_to_bv 64 0x9efb0)]).
Notation rt_real_strrchr m := (rw_cells asegs m 0xa75d0 [C8 (Z_to_bv 64 0x9f41c)]).
Notation rt_real_memchr m := (rw_cells asegs m 0xa75e0 [C8 (Z_to_bv 64 0x9e988)]).
Notation rt_real_fread m := (rw_cells asegs m 0xa75f8 [C8 (Z_to_bv 64 0x9ad38)]).
Notation rt_real_fwrite m := (rw_cells asegs m 0xa7600 [C8 (Z_to_bv 64 0x9afac)]).
Notation rt_real_vsnprintf m := (rw_cells asegs m 0xa7628 [C8 (Z_to_bv 64 0x9e3f0)]).
Notation rt_real_strerror m := (rw_cells asegs m 0xa7648 [C8 (Z_to_bv 64 0x948a8); C8 (Z_to_bv 64 0x9f104)]).   (* [comment removed for export] *)
Notation rt_real_fopen m := (rw_cells asegs m 0xa7670 [C8 (Z_to_bv 64 0x9aba8); C8 (Z_to_bv 64 0x9a708); C8 (Z_to_bv 64 0x9a5e4)]).   (* [comment removed for export] *)
Notation rt_real_strnlen m := (rw_cells asegs m 0xa76e8 [C8 (Z_to_bv 64 0x9f3d8)]).
(* [comment removed for export] *)
Notation rt_isl m := (rw_cells asegs m 0x140620 [C8 (Z_to_bv 64 72340172838076673)]).
Notation rt_ssc m := (rw_cells asegs m 0x140618 [C8 (Z_to_bv 64 0x0101000100000000)]).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Record icptenv (m : word -> option byte) : Prop := mkIE {
  ie_got : rt_got m; ie_ric : rt_got_ric m; ie_shb : rt_shbase m; ie_ini : rt_inited m; ie_lay : rt_layout m;
  ie_mem : rt_real_mem m; ie_read : rt_real_read m; ie_printf : rt_real_printf m;
  ie_strlen : rt_real_strlen m; ie_strchr : rt_real_strchr m; ie_strrchr : rt_real_strrchr m; ie_memchr : rt_real_memchr m;
  ie_fread : rt_real_fread m; ie_fwrite : rt_real_fwrite m; ie_vsnprintf : rt_real_vsnprintf m; ie_strerror : rt_real_strerror m;
  ie_fopen : rt_real_fopen m; ie_strnlen : rt_real_strnlen m;
  ie_isl : rt_isl m; ie_ssc : rt_ssc m
}.

(* [comment removed for export] *)
Definition iesafe (W : list (Z * Z)) : Prop :=
  disjoint_from W 0xa5880 48 /\ disjoint_from W 0xa63f8 8 /\ disjoint_from W 0xa75b8 400
  /\ disjoint_from W 0xae9f8 3328 /\ disjoint_from W 0x140618 16.

#[using="Type"] Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof. induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H A B; [exact I|]. destruct H as [H1 H2]. split; [lia| eapply IH; eauto]. Qed.

#[using="Type"] Lemma icptenv_transport : forall W m m', icptenv m -> munch W m m' -> wmono asegs m m' -> iesafe W -> icptenv m'.
Proof.
  intros W m m' [] MU WM (D1 & D2 & D3 & D4 & D5).
  constructor;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM |]; cbn [cells_size csize Nat.add];
     first [ eapply disjoint_from_sub; [exact D1| lia| lia] | eapply disjoint_from_sub; [exact D2| lia| lia]
           | eapply disjoint_from_sub; [exact D3| lia| lia] | eapply disjoint_from_sub; [exact D4| lia| lia]
           | eapply disjoint_from_sub; [exact D5| lia| lia] ]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iesafe_high : forall W, Forall (fun iv => 0x140628 <= fst iv) W -> iesafe W.
Proof.
  intros W H. unfold iesafe. repeat split; (induction H as [|[lo hi] W Hlo HW IH]; cbn [disjoint_from]; [exact I|]; cbn [fst] in Hlo; split; [lia| exact IH]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sobj (RNG : footprint) (m : word -> option byte) (lo hi : Z) : Prop :=
  app_blk lo hi /\ unpoisoned m lo hi /\ hi - lo <= 2^40
  /\ exists RLO RHI, (RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)
                  /\ wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

#[using="Type"] Lemma sobj_sub : forall RNG m lo hi lo' hi', sobj RNG m lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> sobj RNG m lo' hi'.
Proof.
  intros RNG m lo hi lo' hi' (AB & U & SZ & RLO & RHI & H & W & R) A B C.
  split; [eapply app_blk_sub; eauto|]. split; [eapply unpoisoned_sub; [exact U| lia| lia]|]. split; [lia|].
  exists RLO, RHI. split; [lia|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition appW (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= KLOW \/ KHIGH <= fst iv) W.

#[using="Type"] Lemma appW_shadow_disjoint : forall W lo hi, appW W -> app_blk lo hi -> lo < hi ->
  disjoint_from W (shad lo) (shad (hi - 1) + 1 - shad lo).
Proof.
  intros W lo hi HW [LE AB] LT. induction HW as [|[a b] W Hab HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst snd] in Hab. split; [| exact IH].
  rewrite !shad_div. unfold ASHOFF, KLOW, KHIGH, KEND in *. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma sobj_transport : forall RNG W m m' lo hi, sobj RNG m lo hi -> munch W m m' -> wmono asegs m m' -> appW W -> sobj RNG m' lo hi.
Proof.
  intros RNG W m m' lo hi (AB & U & SZ & RLO & RHI & H & WR & R) MU WM HW.
  split; [exact AB|]. split.
  - destruct (Z_lt_le_dec lo hi) as [LT|GE].
    + eapply unpoisoned_munch; [exact U| exact MU|]. apply appW_shadow_disjoint; assumption.
    + destruct U as (U0 & U1 & _). split; [exact U0|]. split; [exact U1|]. intros G HG. lia.
  - split; [exact SZ|]. exists RLO, RHI. split; [exact H|]. split; [eapply wr_at_transport; eauto| exact R].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sobj_appW : forall RNG m lo hi, sobj RNG m lo hi -> appW [(lo, hi)].
Proof.
  intros RNG m lo hi ((LE & AB) & _). constructor; [| constructor]. cbn [fst snd]. unfold KLOW, KHIGH, KEND in *. lia.
Qed.

#[using="Type"] Lemma fp_le_sobj : forall RNG RNG' m lo hi, fp_le RNG RNG' -> sobj RNG m lo hi -> sobj RNG' m lo hi.
Proof.
  intros RNG RNG' m lo hi FP (AB & U & SZ & RLO & RHI & H & WR & R).
  split; [exact AB|]. split; [exact U|]. split; [exact SZ|]. exists RLO, RHI. split; [exact H|]. split; [exact WR|].
  eapply rng_fp_le; eauto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma iesafe_nil : iesafe [].
Proof. repeat split. Qed.
#[using="Type"] Lemma iesafe_cons : forall a b W, iesafe [(a, b)] -> iesafe W -> iesafe ((a, b) :: W).
Proof. intros a b W (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold iesafe in *; cbn [disjoint_from] in *. intuition. Qed.
#[using="Type"] Lemma iesafe_app : forall W1 W2, iesafe W1 -> iesafe W2 -> iesafe (W1 ++ W2).
Proof.
  induction W1 as [|[a b] W1 IH]; intros W2 H1 H2; [exact H2|]. cbn [app].
  destruct H1 as (A1 & A2 & A3 & A4 & A5). cbn [disjoint_from] in *.
  apply iesafe_cons; [unfold iesafe; cbn [disjoint_from]; intuition|]. apply IH; [unfold iesafe; intuition| exact H2].
Qed.
#[using="Type"] Lemma iesafe_one_high : forall a b, 0x140628 <= a -> iesafe [(a, b)].
Proof. intros a b H. apply iesafe_high. constructor; [exact H| constructor]. Qed.
#[using="Type"] Lemma iesafe_one_sub : forall a b a' b', iesafe [(a, b)] -> a <= a' -> b' <= b -> iesafe [(a', b')].
Proof. intros a b a' b' (A1 & A2 & A3 & A4 & A5) Ha Hb. unfold iesafe in *; cbn [disjoint_from] in *. intuition lia. Qed.
#[using="Type"] Lemma iesafe_In : forall W iv, iesafe W -> In iv W -> iesafe [iv].
Proof.
  induction W as [|[a b] W IH]; intros iv H Hin; [destruct Hin|].
  destruct H as (A1 & A2 & A3 & A4 & A5). cbn [disjoint_from] in *. destruct Hin as [<-|Hin].
  - unfold iesafe; cbn [disjoint_from]; intuition.
  - apply IH; [unfold iesafe; intuition| exact Hin].
Qed.
#[using="Type"] Lemma appW_In : forall W iv, appW W -> In iv W -> appW [iv].
Proof. intros W iv H Hin. constructor; [exact (proj1 (Forall_forall _ _) H iv Hin)| constructor]. Qed.
#[using="Type"] Lemma appW_one_sub : forall a b a' b', appW [(a, b)] -> a <= a' -> b' <= b -> appW [(a', b')].
Proof. intros a b a' b' H Ha Hb. inversion H as [|? ? H1 _]; subst. cbn [fst snd] in H1. constructor; [cbn [fst snd]; lia| constructor]. Qed.
#[using="Type"] Lemma appW_cons : forall a b W, appW [(a, b)] -> appW W -> appW ((a, b) :: W).
Proof. intros a b W H HW. inversion H; subst. constructor; assumption. Qed.
#[using="Type"] Lemma appW_one_high : forall a b, KHIGH <= a -> appW [(a, b)].
Proof. intros a b H. constructor; [right; exact H| constructor]. Qed.
End CANSEC1.

(* [comment removed for export] *)
Ltac solve_appW :=
  repeat first [ apply Forall_nil
               | apply appW_cons;
                 [ first [ assumption | apply appW_one_high; unfold KHIGH in *; lia
                         | match goal with H : appW [(_, _)] |- _ => eapply appW_one_sub; [exact H | lia | lia] end
                         | constructor; [unfold KLOW, KHIGH in *; cbn [fst snd]; first [lia | left; lia | right; lia] | constructor] ] |] ].
Ltac solve_iesafe :=
  first [ solve [ apply iesafe_high; repeat first [ apply Forall_nil | apply Forall_cons; [cbn [fst snd]; unfold KHIGH in *; lia|] ] ]
        | repeat first [ apply iesafe_nil
                       | apply iesafe_cons;
                         [ first [ assumption | apply iesafe_one_high; unfold KHIGH in *; lia
                                 | match goal with H : iesafe [(_, _)] |- _ => eapply iesafe_one_sub; [exact H | lia | lia] end
                                 | unfold iesafe; cbn [disjoint_from]; unfold KHIGH in *; repeat split; lia ] |] ] ].

(* [comment removed for export] *)
Tactic Notation "ienv_now" constr(ENV) constr(MU) constr(WM) "as" ident(X) :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (X : icptenv mm) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]) end.
Tactic Notation "sobj_now" constr(SO) constr(MU) constr(WM) "as" ident(X) :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of SO with sobj ?R _ ?lo ?hi =>
      assert (X : sobj R mm lo hi) by (eapply sobj_transport; [exact SO | exact MU | exact WM | solve_appW]) end end.

(* [comment removed for export] *)
Ltac icpt_prem RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- icptenv _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- ~ In _ _ => first [assumption | eassumption]
  | |- sobj _ _ _ _ => first [ assumption | match goal with H : sobj _ _ _ _ |- _ => eapply sobj_sub; [exact H | lia | lia | lia] end ]
  | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia]
                          | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | lia] end ]
  | |- (bv_unsigned (Z_to_bv 64 _) mod 256 <> 0)%Z => let X := fresh in rewrite unsigned_lit by lia; intros X; vm_compute in X; discriminate X
  | |- _ => first [ assumption | lia | rewrite ?length_app; cbn [length]; lia ]
  end.
End TwB.
End RtCellsS.

(* [comment removed for export] *)
Module I_memwb.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require I_memcpy. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.I_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition ICPT_DEPTH : Z := 2240.

Definition memset_postw (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q); (D, D + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].

#[using="Type"] Lemma memset_wb_spec : forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte) (lo : Z),
  rw_cells asegs m D [CB (Z.to_nat N) junk] ->
  mem_inv asegs m ->
  (0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
  stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> sobj RNG m D (D + N) ->
  (D + N <= lo \/ q <= D)%Z ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG D N ->
  evtF asegs RNG (memset_postw ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54958) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros DST MI Hq HD HC HN ST LO KH ENV (AB & U & N40 & RLO & RHI & HU & WR & RSH) SEP RIMG RSTK RD.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(q - 2240, q); (D, D + N)]%Z m) as MU.
  pose proof (ie_got _ ENV) as E1. pose proof (ie_ric _ ENV) as E2. pose proof (ie_shb _ ENV) as E3.
  pose proof (ie_ini _ ENV) as E4. pose proof (ie_lay _ ENV) as E5. pose proof (ie_mem _ ENV) as E6.
  step.
  eapply evtF_mono.
  { eapply (memset_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N)) with (RLO2 := RLO) (RHI2 := RHI);
      rewrite ?Eq, ?Ed, ?En; try eassumption; try lia. }
  intros ms' P. unfold memset_i_post in P. rewrite !Eq, !Ed, !Ec, !En in P. unfold memset_postw.
  destruct_exs P. destruct P as (E & MU' & REST). repeat (lazymatch goal with |- ex _ => eexists end).
  split; [exact E|]. split; [| exact REST].
  (* [comment removed for export] *)
  eapply munch_weaken; [| exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
Qed.

Definition memcpy_postw (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q); (Dst, Dst + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at asegs m' Src src.

#[using="Type"] Lemma memcpy_wb_spec : forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Dst Src N : Z) (src junk : list byte) (lo : Z),
  bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv asegs m ->
  (0 <= q < 2^64)%Z ->
  stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> sobj RNG m Src (Src + N) -> sobj RNG m Dst (Dst + N) ->
  (Src + N <= q - 2240 \/ q <= Src)%Z ->
  (Dst + N <= lo \/ q <= Dst)%Z ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG Src N -> rng RNG Dst N ->
  evtF asegs RNG (memcpy_postw ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54960) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros BA LEN DC SEP HN HS HD MI Hq ST LO KH ENV (AB1 & U1 & N41 & RLO1 & RHI1 & HU1 & WR1 & RSH1)
         (AB2 & U2 & N42 & RLO2 & RHI2 & HU2 & WR2 & RSH2) SEPS SEPD RIMG RSTK RS RD.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(q - 2240, q); (Dst, Dst + N)]%Z m) as MU.
  pose proof (ie_got _ ENV) as E1. pose proof (ie_ric _ ENV) as E2. pose proof (ie_shb _ ENV) as E3.
  pose proof (ie_ini _ ENV) as E4. pose proof (ie_lay _ ENV) as E5. pose proof (ie_mem _ ENV) as E6.
  step.
  eapply evtF_mono.
  { eapply (memcpy_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N)) with (src := src) (junk := junk)
      (RLO1 := RLO1) (RHI1 := RHI1) (RLO2 := RLO2) (RHI2 := RHI2);
      rewrite ?ED, ?ES, ?EN, ?Eq; try eassumption; try lia. }
  intros ms' P. unfold memcpy_i_post in P. rewrite !ED, !ES, !EN, !Eq in P. unfold memcpy_postw. exact P.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.I_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition ICPT_DEPTH : Z := 2240.

Definition memset_postw (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q); (D, D + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].

#[using="Type"] Lemma memset_wb_spec : forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte) (lo : Z),
  rw_cells asegs m D [CB (Z.to_nat N) junk] ->
  mem_inv asegs m ->
  (0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
  stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> sobj RNG m D (D + N) ->
  (D + N <= lo \/ q <= D)%Z ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG D N ->
  evtF asegs RNG (memset_postw ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x549c0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros DST MI Hq HD HC HN ST LO KH ENV (AB & U & N40 & RLO & RHI & HU & WR & RSH) SEP RIMG RSTK RD.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(q - 2240, q); (D, D + N)]%Z m) as MU.
  pose proof (ie_got _ ENV) as E1. pose proof (ie_ric _ ENV) as E2. pose proof (ie_shb _ ENV) as E3.
  pose proof (ie_ini _ ENV) as E4. pose proof (ie_lay _ ENV) as E5. pose proof (ie_mem _ ENV) as E6.
  step.
  eapply evtF_mono.
  { eapply (memset_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N)) with (RLO2 := RLO) (RHI2 := RHI);
      rewrite ?Eq, ?Ed, ?En; try eassumption; try lia. }
  intros ms' P. unfold memset_i_post in P. rewrite !Eq, !Ed, !Ec, !En in P. unfold memset_postw.
  destruct_exs P. destruct P as (E & MU' & REST). repeat (lazymatch goal with |- ex _ => eexists end).
  split; [exact E|]. split; [| exact REST].
  (* [comment removed for export] *)
  eapply munch_weaken; [| exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
Qed.

Definition memcpy_postw (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q); (Dst, Dst + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at asegs m' Src src.

#[using="Type"] Lemma memcpy_wb_spec : forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Dst Src N : Z) (src junk : list byte) (lo : Z),
  bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv asegs m ->
  (0 <= q < 2^64)%Z ->
  stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> sobj RNG m Src (Src + N) -> sobj RNG m Dst (Dst + N) ->
  (Src + N <= q - 2240 \/ q <= Src)%Z ->
  (Dst + N <= lo \/ q <= Dst)%Z ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG Src N -> rng RNG Dst N ->
  evtF asegs RNG (memcpy_postw ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x549c8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros BA LEN DC SEP HN HS HD MI Hq ST LO KH ENV (AB1 & U1 & N41 & RLO1 & RHI1 & HU1 & WR1 & RSH1)
         (AB2 & U2 & N42 & RLO2 & RHI2 & HU2 & WR2 & RSH2) SEPS SEPD RIMG RSTK RS RD.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(q - 2240, q); (Dst, Dst + N)]%Z m) as MU.
  pose proof (ie_got _ ENV) as E1. pose proof (ie_ric _ ENV) as E2. pose proof (ie_shb _ ENV) as E3.
  pose proof (ie_ini _ ENV) as E4. pose proof (ie_lay _ ENV) as E5. pose proof (ie_mem _ ENV) as E6.
  step.
  eapply evtF_mono.
  { eapply (memcpy_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N)) with (src := src) (junk := junk)
      (RLO1 := RLO1) (RHI1 := RHI1) (RLO2 := RLO2) (RHI2 := RHI2);
      rewrite ?ED, ?ES, ?EN, ?Eq; try eassumption; try lia. }
  intros ms' P. unfold memcpy_i_post in P. rewrite !ED, !ES, !EN, !Eq in P. unfold memcpy_postw. exact P.
Qed.
End CANSEC1.
End TwB.
End I_memwb.
