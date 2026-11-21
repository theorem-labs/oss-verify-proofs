(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (13 recorded proofs replaced by written proofs (mteq_bind_l, outsk_cong, mteq_seq_unit and 10 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib Printf_fmts Printf_pieces.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto MonadF MonadF2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Printf_outsA () := "C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF2:teq_bind_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF24mteqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF5postFC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI59OSSVerify5KrLib6Common;Printf_mlib3teq00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces5outskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4mpadC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsA;mteq_bind_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF29mteq_congC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4unit00c59OSSVerify5KrLib5BothW<Printf_outsA:outsk_congC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF29mteq_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib5BothW<Printf_outsA=mteq_seq_unitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF2:mteq_ret_lC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib6Common<Printf_model:pad_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3orbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Prelim7zrepeatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib6Common5FmtFp8LEFT_ADJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ZERO_PADC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW<Printf_outsA=mpad_outs_teqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsA<out_outs_teqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF2:mteq_assocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF2:mteq_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsA<mteq_assoc_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsA<mteq_ret_l_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces9outsk_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;tail_piecesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3ltbK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes3appC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib6Common<Printf_model9conv_tailC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsABconv_tail_outs_teqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:int_piecesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z4lnotC59OSSVerify5KrLib6Common<Printf_model8conv_intC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsAAconv_int_outs_teqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;conv_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_tyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_flC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib6Common<Printf_model4d_xpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:dec_digitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat9f128_of_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4convC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib6Common<Printf_model:hex_digitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8MARK_POSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7PAD_POSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ALT_FORMC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model3dir00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_PTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_INTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp:INTMAX_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6T_UINTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_DBLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;printf_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsA=conv_outs_teqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_modelBprintf_pieces_loopC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common<Printf_model7lit_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model9parse_dirC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef5skipnI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5BothW<Printf_outsADprintf_loop_outs_teqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model=printf_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7MonadF2:implAM_teqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF6implAMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model<printf_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<Printf_outsAEprintf_model_outs_teqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
Section OutsTeq.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
  Local Notation outsk := (outsk OUT).

  Lemma mteq_bind_l : forall {A B} (a a' : M St A) (f : A -> M St B), mteq a a' -> mteq (mbind a f) (mbind a' f).
  Proof. intros A B a a' f H s. unfold mbind, ebind. apply teq_bind_l. apply H. Qed.

  Lemma outsk_cong : forall {B} ps (k1 k2 : M St B), mteq k1 k2 -> mteq (outsk ps k1) (outsk ps k2).
  Proof.
    induction ps as [|p ps IH]; intros k1 k2 H; cbn [Printf_pieces.outsk]; [exact H|].
    apply mteq_cong. intros _. apply IH. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma mteq_seq_unit : forall {B} (a : M St unit) (k : unit -> M St B), mteq (mbind a k) (a ;;; k tt).
  Proof. intros B a k. apply mteq_cong. intros []. apply mteq_refl. Qed.

  Lemma mpad_outs_teq : forall {B} c w l fl pp (K : unit -> M St B),
    pad_pieces c w l fl = Some pp -> mteq (mbind (mpad OUT c w l fl) K) (outsk pp (K tt)).
  Proof.
    intros B c w l fl pp K P. unfold mpad, pad_pieces in *.
    destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
    - inversion P; subst. cbn [Printf_pieces.outsk]. apply mteq_ret_l.
    - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [Printf_pieces.outsk]. apply mteq_seq_unit.
  Qed.

  Lemma out_outs_teq : forall {B} p (K : unit -> M St B), mteq (mbind (OUT p) K) (outsk [p] (K tt)).
  Proof. intros B p K. cbn [Printf_pieces.outsk]. apply mteq_seq_unit. Qed.

  (* [comment removed for export] *)
  Lemma mteq_assoc_l : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) (t : M St C),
    mteq (mbind a (fun x => mbind (b x) k)) t -> mteq (mbind (mbind a b) k) t.
  Proof. intros A B C a b k t H. eapply mteq_trans; [apply mteq_assoc | exact H]. Qed.
  Lemma mteq_ret_l_l : forall {A B} (v : A) (k : A -> M St B) (t : M St B), mteq (k v) t -> mteq (mbind (mret v) k) t.
  Proof. intros A B v k t H. eapply mteq_trans; [apply mteq_ret_l | exact H]. Qed.

  Lemma conv_tail_outs_teq : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B),
    tail_pieces cnt fl w p prefix body = Some (ps, r) ->
    mteq (mbind (conv_tail OUT cnt fl w p prefix body) K) (outsk ps (K r)).
  Proof.
    intros B cnt fl w p prefix body ps r K T. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
    destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
    destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
    destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
    destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
    destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
    destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
    inversion T; subst. clear T.
    match goal with |- mteq _ (outsk ?L (K ?rr)) =>
      replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
        by (rewrite ?outsk_app; cbn [Printf_pieces.outsk]; rewrite ?outsk_app; cbn [Printf_pieces.outsk]; reflexivity) end.
    apply mteq_assoc_l. eapply mteq_trans; [apply (mpad_outs_teq _ _ _ _ _ _ P1)|]. apply outsk_cong.
    apply mteq_assoc_l. apply mteq_cong. intros _.
    apply mteq_assoc_l. eapply mteq_trans; [apply (mpad_outs_teq _ _ _ _ _ _ P2)|]. apply outsk_cong.
    apply mteq_assoc_l. eapply mteq_trans; [apply (mpad_outs_teq _ _ _ _ _ _ P3)|]. apply outsk_cong.
    apply mteq_assoc_l. apply mteq_cong. intros _.
    apply mteq_assoc_l. eapply mteq_trans; [apply (mpad_outs_teq _ _ _ _ _ _ P4)|]. apply outsk_cong.
    apply mteq_ret_l.
  Qed.

  Lemma conv_int_outs_teq : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B),
    int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
    mteq (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) (outsk ps (K r)).
  Proof.
    intros B cnt fl w p xp argi prefix body ps r K T. unfold conv_int, int_pieces in *.
    destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
    destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs_teq; eassumption.
  Qed.

  Lemma conv_outs_teq : forall {B} cnt d a ps r (K : Z -> M St B),
    conv_pieces cnt d a = Some (ps, r) ->
    mteq (mbind (conv OUT OUTFP cnt d a) K) (outsk ps (K r)).
  Proof.
    intros B cnt d a ps r K T. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
    destruct a as [str|i|u|dd].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outs_teq; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outs_teq; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outs_teq; eassumption.
    - discriminate.
  Qed.

  Lemma printf_loop_outs_teq : forall {B} fuel s args cnt ps r (k : Z -> M St B),
    printf_pieces_loop fuel s args cnt = Some (ps, r) ->
    mteq (mbind (printf_loop OUT OUTFP fuel s args cnt) k) (outsk ps (k r)).
  Proof.
    induction fuel as [|fuel IH]; intros s args cnt ps r k P; [discriminate|].
    cbn [printf_pieces_loop] in P. cbn [printf_loop].
    destruct s as [|c s1]; [discriminate|].
    destruct (c =? 0). { inversion P; subst. cbn [Printf_pieces.outsk]. apply mteq_ret_l. }
    cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
    destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
    destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
    destruct (0 <? zlength lit).
    - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
      destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
      inversion P; subst. clear P. cbn [Printf_pieces.outsk].
      apply mteq_assoc_l. apply mteq_cong. intros _. eapply IH. exact R.
    - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P.
      match goal with |- mteq _ (outsk ?L (k ?rr)) =>
        replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
      cbn [Printf_pieces.outsk].
      apply mteq_assoc_l. apply mteq_cong. intros _.
      apply mteq_assoc_l. eapply mteq_trans; [apply (conv_outs_teq _ _ _ _ _ _ C)|]. apply outsk_cong.
      eapply IH. exact R.
  Qed.

  Theorem printf_model_outs_teq : forall {B} fmt args ps r (k : Z -> M St B),
    printf_pieces fmt args = Some (ps, r) -> mteq (mbind (printf_model OUT OUTFP fmt args) k) (outsk ps (k r)).
  Proof. intros B fmt args ps r k P. eapply printf_loop_outs_teq. exact P. Qed.

  (* [comment removed for export] *)
  Theorem printf_model_outsA : forall {B} RNG fmt args ps r (k : Z -> M St B) st Q ms,
    printf_pieces fmt args = Some (ps, r) ->
    implAM RNG (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implAM RNG (outsk ps (k r)) st Q ms.
  Proof. intros B RNG fmt args ps r k st Q ms P H. eapply implAM_teq; [apply (printf_model_outs_teq _ _ _ _ _ P) | exact H]. Qed.
End OutsTeq.
End CANSEC1.
