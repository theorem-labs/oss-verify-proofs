(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX PrintfFormats Stdio.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Printf_mlib.
From OSSVerify.Proofs.openssl.ct.lib.P Require Export Printf_pieces.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section OutsX.
  Variable segs : list Segment.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
  Local Notation implM := (Monad.implM segs).
  Local Notation outsk := (outsk OUT).

  Lemma convx_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
    conv_piecesx cnt d a = Some (ps, r) ->
    implM (mbind (convx OUT OUTFP cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt d a ps r K s Q ms T H. unfold convx, conv_piecesx in *. cbv zeta in T. cbv zeta in H.
    destruct a as [str| |i|u|u|dd].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outs; eassumption.
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
      eapply conv_tail_outs; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (d_t d =? 99). { eapply conv_tail_outs; eassumption. }
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outs; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
    - destruct ((d_ty d =? T_SIZET) || (d_ty d =? T_ULONG))%bool.
      + destruct (d_t d =? 117); [eapply conv_int_outs; eassumption|].
        destruct ((d_t d =? 120) || (d_t d =? 88))%bool; [|discriminate]. eapply conv_int_outs; eassumption.
      + destruct (d_ty d =? T_LONG); [|discriminate].
        destruct (INTMAX_MAX <? u);
          [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
          eapply conv_int_outs; eassumption.
    - discriminate.
  Qed.

  Lemma printf_loopx_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
    printf_piecesx_loop fuel s args cnt = Some (ps, r) ->
    implM (mbind (printf_loopx OUT OUTFP fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
  Proof.
    induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms P H; [discriminate|].
    cbn [printf_piecesx_loop] in P. cbn [printf_loopx] in H.
    destruct s as [|c s1]; [discriminate|].
    destruct (c =? 0). { inversion P; subst. cbn [Printf_pieces.outsk]. apply implM_ret_l_rev in H. exact H. }
    cbv zeta in P. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
    destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
    destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
    destruct (0 <? zlength lit).
    - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
      destruct (printf_piecesx_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
      inversion P; subst. clear P. cbn [Printf_pieces.outsk].
      apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      eapply IH; [exact R | exact H'].
    - destruct (parse_dirx s2) as [[[d0 ws] s3]|]; [|discriminate].
      destruct (dir_eff d0 ws args) as [[d [|a args']]|]; [discriminate| |discriminate].
      destruct (conv_piecesx cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_piecesx_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P.
      match goal with |- implM (outsk ?L (k ?rr)) _ _ _ =>
        replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
      cbn [Printf_pieces.outsk].
      apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      apply implM_assoc_rev in H'. apply (convx_outs _ _ _ _ _ _ _ _ _ C) in H'.
      eapply outsk_mono; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
  Qed.

  Theorem printf_modelx_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
    printf_piecesx fmt args = Some (ps, r) ->
    implM (mbind (printf_modelx OUT OUTFP fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
  Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loopx_outs; [exact P | exact H]. Qed.
End OutsX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma printf_piecesx_emit0 : printf_piecesx FMT_emit [PA_i 0] = Some (pieces_emit_0, 2).
Proof. apply printf_pieces_x. exact printf_pieces_emit0. Qed.
Lemma printf_piecesx_usage : forall s, zlength s < INT_MAX - 256 ->
  printf_piecesx FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof. intros s H. apply printf_pieces_x. exact (printf_pieces_usage s H). Qed.
Lemma printf_piecesx_cannot_open : forall s, zlength s < INT_MAX - 256 ->
  printf_piecesx FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof. intros s H. apply printf_pieces_x. exact (printf_pieces_cannot_open s H). Qed.
Lemma printf_piecesx_read_error : forall s, zlength s < INT_MAX - 256 ->
  printf_piecesx FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof. intros s H. apply printf_pieces_x. exact (printf_pieces_read_error s H). Qed.
Lemma printf_piecesx_too_big : printf_piecesx FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. apply printf_pieces_x. exact printf_pieces_too_big. Qed.
Lemma printf_piecesx_unreached : forall s, zlength s < INT_MAX - 256 ->
  printf_piecesx FMT_unreached [PA_s s] = Some (pieces_precond_reached s, 34 + zlength s).
Proof. intros s H. apply printf_pieces_x. exact (printf_pieces_unreached s H). Qed.
Lemma printf_piecesx_precond : forall x fn, zlength x < 2^20 -> zlength fn < 2^20 ->
  printf_piecesx FMT_precond [PA_s x; PA_s fn] = Some (pieces_precond_fail x fn, 25 + zlength x + zlength fn).
Proof. intros x fn Hx Hf. apply printf_pieces_x. exact (printf_pieces_precond x fn Hx Hf). Qed.
Lemma printf_piecesx_msg_gen : forall (a1 : parg) (f : list Z) n msg,
  (a1 = PA_s f \/ (a1 = PA_sn /\ f = NULLSTR)) ->
  zlength f < 2^20 -> 0 <= n < 2^64 -> zlength msg < 2^20 ->
  printf_piecesx FMT_msg [a1; PA_z n; PA_s msg]
  = Some (pieces_msg f n msg, zlength f + 1 + (if n =? 0 then 1 else zlength (dec_digits n)) + 2 + zlength msg).
Proof. intros a1 f n msg H1 H2 H3 H4. apply printf_pieces_x. exact (printf_pieces_msg_gen a1 f n msg H1 H2 H3 H4). Qed.

Lemma pass1x_ok_emit : pass1x_ok FMT_emit = true. Proof. exact (pass1_ok_x _ pass1_ok_emit). Qed.
Lemma pass1x_ok_usage : pass1x_ok FMT_usage = true. Proof. exact (pass1_ok_x _ pass1_ok_usage). Qed.
Lemma pass1x_ok_cannot_open : pass1x_ok FMT_cannot_open = true. Proof. exact (pass1_ok_x _ pass1_ok_cannot_open). Qed.
Lemma pass1x_ok_read_error : pass1x_ok FMT_read_error = true. Proof. exact (pass1_ok_x _ pass1_ok_read_error). Qed.
Lemma pass1x_ok_too_big : pass1x_ok FMT_too_big = true. Proof. exact (pass1_ok_x _ pass1_ok_too_big). Qed.
Lemma pass1x_ok_precond : pass1x_ok FMT_precond = true. Proof. exact (pass1_ok_x _ pass1_ok_precond). Qed.
Lemma pass1x_ok_unreached : pass1x_ok FMT_unreached = true. Proof. exact (pass1_ok_x _ pass1_ok_unreached). Qed.
Lemma pass1x_ok_msg : pass1x_ok FMT_msg = true. Proof. exact (pass1_ok_x _ pass1_ok_msg). Qed.

(* [comment removed for export] *)
Lemma fp_callsx_s : forall fmt s n, fp_callsx n fmt [PA_s s] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_emit : forall fmt i n, fp_callsx n fmt [PA_i i] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_too_big : forall fmt u n, fp_callsx n fmt [PA_u u] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_precond : forall fmt x fn n, fp_callsx n fmt [PA_s x; PA_s fn] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_msg : forall fmt f z msg n, fp_callsx n fmt [PA_s f; PA_z z; PA_s msg] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_msg_null : forall fmt z msg n, fp_callsx n fmt [PA_sn; PA_z z; PA_s msg] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
