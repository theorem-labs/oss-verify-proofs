(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Monad Stdio Canon ProgDetIface ProgDetLogic ProgDetNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma concat_iov_start : forall buf s, concat (iov_start buf s) = buf ++ s.
Proof. intros [|b buf] s; cbn; [rewrite app_nil_r; reflexivity| rewrite app_nil_r; reflexivity]. Qed.

Lemma length_iov_start : forall buf s, (length (iov_start buf s) <= 2)%nat.
Proof. intros [|b buf] s; cbn; lia. Qed.

Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma zlen_app : forall {A} (l1 l2 : list A), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

Lemma iov_advance_concat : forall iovs k, (length iovs <= 2)%nat -> 0 < k < zlength (concat iovs) ->
  concat (iov_advance iovs k) = skipn (Z.to_nat k) (concat iovs) /\ (length (iov_advance iovs k) <= 2)%nat.
Proof.
  intros [|a [|b [|c rest]]] k Hn Hk; cbn [length] in Hn; try lia.
  - cbn in Hk. unfold zlength in Hk. cbn in Hk. lia.
  - cbn [concat] in *. rewrite app_nil_r in *. unfold iov_advance.
    destruct (Z.ltb_spec (zlength a) k); [lia|]. cbn [concat length]. rewrite app_nil_r. split; [reflexivity| lia].
  - cbn [concat] in *. rewrite app_nil_r in *. unfold iov_advance.
    destruct (Z.ltb_spec (zlength a) k).
    + cbn [concat length]. rewrite app_nil_r. unfold zdrop. split; [|lia].
      unfold zlength in *. rewrite skipn_app. rewrite (skipn_all2 (n := Z.to_nat k) a) by lia. cbn [app].
      f_equal. lia.
    + cbn [concat length]. unfold zdrop. rewrite app_nil_r. split; [|lia].
      unfold zlength in *. rewrite skipn_app. replace (Z.to_nat k - length a)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma evw_firstn_skipn : forall fd n l, evw fd (firstn n l) ++ evw fd (skipn n l) = evw fd l.
Proof. intros. rewrite <- evw_app, firstn_skipn. reflexivity. Qed.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma wv_body_E : forall fd iovs T (Kt : St -> Model -> Prop),
  (length iovs <= 2)%nat -> zlength (concat iovs) < 2^62 ->
  mspecE sel X (fun s mo tr => Kt s mo /\ tr ++ evw fd (concat iovs) = T) (wv_body fd iovs)
    (fun r s mo tr => Kt s mo /\ match r with
       | inr _ => tr = T
       | inl iovs' => tr ++ evw fd (concat iovs') = T /\ (length iovs' <= 2)%nat /\ zlength (concat iovs') < 2^62
       end).
Proof.
  intros fd iovs T Kt Hn Hl. unfold wv_body.
  eapply mspecE_bind with (Q1 := fun k s mo tr => Kt s mo /\ ((iov_total iovs = 0 /\ k = 0) \/ 1 <= k <= iov_total iovs)
                                   /\ tr ++ evw fd (skipn (Z.to_nat k) (concat iovs)) = T).
  { apply msysE_node; [exact I| intros; apply nprog_writev|].
    intros s mo tr rsp mo' evs k [HK HT] Hst Hd.
    destruct (stepR_writev sel fd iovs mo rsp mo' evs k ltac:(lia) Hst Hd) as (-> & Hk & ->).
    split; [exact HK|]. split; [exact Hk|]. rewrite <- app_assoc, evw_firstn_skipn. exact HT. }
  intros k. apply mspecE_if; intros Hc.
  - apply mspecE_ret. intros s mo tr (HK & _ & HT). split; [exact HK|]. apply Z.eqb_eq in Hc.
    rewrite Hc in HT. unfold iov_total, zlength in HT. rewrite Nat2Z.id, skipn_all, app_nil_r in HT. exact HT.
  - apply mspecE_ret. intros s mo tr (HK & Hk & HT). split; [exact HK|]. apply Z.eqb_neq in Hc.
    assert (Hk' : 0 < k < zlength (concat iovs)) by (unfold iov_total in *; lia).
    destruct (iov_advance_concat iovs k Hn Hk') as [Hc' Hn']. rewrite Hc'. split; [exact HT|]. split; [exact Hn'|].
    unfold zlength in *. rewrite length_skipn. lia.
Qed.

Lemma stdio_writev_E : forall fd buf bs tr0 (Kt : St -> Model -> Prop),
  zlength (buf ++ bs) < 2^62 ->
  mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (stdio_writev fd buf bs)
               (fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw fd (buf ++ bs)).
Proof.
  intros fd buf bs tr0 Kt Hl. unfold stdio_writev.
  eapply mspecE_pre.
  - apply (mspecE_loop sel X (wv_body fd)
             (fun iovs s mo tr => Kt s mo /\ tr ++ evw fd (concat iovs) = tr0 ++ evw fd (buf ++ bs)
                                  /\ (length iovs <= 2)%nat /\ zlength (concat iovs) < 2^62)
             (fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw fd (buf ++ bs))).
    intros iovs. apply mspecE_pointwise. intros s mo tr (HK & HT & Hn & Hz).
    eapply mspecE_conseq; [apply (wv_body_E fd iovs (tr0 ++ evw fd (buf ++ bs)) Kt Hn Hz)| |].
    + intros s' mo' tr' (-> & -> & ->). split; assumption.
    + intros [iovs'|[]] s' mo' tr' (HK' & H'); [destruct H' as (H1 & H2 & H3); auto| auto].
  - intros s mo tr [HK ->]. rewrite concat_iov_start. split; [exact HK|]. split; [reflexivity|].
    split; [apply length_iov_start| exact Hl].
Qed.

Lemma stderr_pieces_E : forall ps buf T (Kt : St -> Model -> Prop),
  zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p < 2^61) ps ->
  mspecE sel X (fun s mo tr => Kt s mo /\ tr ++ evw 2 (buf ++ concat ps) = T) (@stderr_pieces St buf ps)
               (fun buf' s mo tr => Kt s mo /\ tr ++ evw 2 buf' = T /\ zlength buf' <= INTERNAL_BUFSIZ).
Proof.
  induction ps as [|p ps IH]; intros buf T Kt Hb Hps; cbn [stderr_pieces].
  - apply mspecE_ret. intros s mo tr [HK HT]. rewrite app_nil_r in HT. auto.
  - inversion Hps as [|p' ps' Hp Hps' E1]; subst p' ps'. unfold INTERNAL_BUFSIZ in *. apply mspecE_if; intros C.
    + apply Z.ltb_lt in C. apply mspecE_pointwise. intros s0 mo0 tr0 [HK HT].
      eapply mspecE_seq.
      { eapply mspecE_pre; [apply (stdio_writev_E 2 buf p tr0 (fun s mo => Kt s mo /\ s = s0))|].
        - rewrite zlen_app. lia.
        - intros s mo tr (-> & -> & ->). auto. }
      intros _. eapply mspecE_pre; [apply IH; [unfold zlength; cbn; lia| exact Hps']|].
      intros s mo tr ((HK' & _) & ->). split; [exact HK'|]. cbn [app]. rewrite <- app_assoc, <- evw_app. cbn [concat] in HT.
      rewrite <- app_assoc. exact HT.
    + apply Z.ltb_ge in C. eapply mspecE_pre; [apply IH; [rewrite zlen_app; lia| exact Hps']|].
      intros s mo tr [HK HT]. split; [exact HK|]. rewrite <- app_assoc. cbn [concat] in HT. exact HT.
Qed.

Lemma stderr_fprintf_E : forall ps tr0 (Kt : St -> Model -> Prop),
  Forall (fun p => zlength p < 2^61) ps ->
  mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (@stderr_fprintf St ps)
               (fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw 2 (concat ps)).
Proof.
  intros ps tr0 Kt Hps. unfold stderr_fprintf.
  eapply mspecE_bind; [eapply mspecE_pre; [apply (stderr_pieces_E ps [] (tr0 ++ evw 2 (concat ps)) Kt); [unfold zlength, INTERNAL_BUFSIZ; cbn; lia| exact Hps]|]|].
  { intros s mo tr [HK ->]. split; [exact HK| reflexivity]. }
  intros buf. apply mspecE_pointwise. intros s0 mo0 tr1 (HK & HT & Hb).
  eapply mspecE_conseq; [apply (stdio_writev_E 2 buf [] tr1 (fun s mo => Kt s mo /\ s = s0 /\ mo = mo0))| |].
  - rewrite app_nil_r. unfold INTERNAL_BUFSIZ in Hb. lia.
  - intros s mo tr (-> & -> & ->). auto.
  - intros _ s mo tr ((HK' & _ & _) & ->). split; [exact HK'|]. rewrite app_nil_r. exact HT.
Qed.

Lemma stderr_fwrite_E : forall bs tr0 (Kt : St -> Model -> Prop),
  zlength bs < 2^61 ->
  mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (@stderr_fwrite St bs)
               (fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw 2 bs).
Proof.
  intros bs tr0 Kt Hbs. unfold stderr_fwrite. apply mspecE_if; intros C.
  - eapply mspecE_post; [apply (stdio_writev_E 2 [] bs tr0 Kt); cbn [app]; lia|]. intros _ s mo tr [HK ->]. auto.
  - apply mspecE_ret. intros s mo tr [HK ->]. split; [exact HK|]. apply Z.ltb_ge in C.
    destruct bs; [rewrite app_nil_r; reflexivity| unfold zlength in C; cbn in C; lia].
Qed.

Hypothesis get_set : forall v s, get_so (set_so v s) = v.

Lemma upd_so_E : forall f (P : assnE St) (Q : unit -> assnE St),
  (forall s mo tr, P s mo tr -> Q tt (set_so (f (get_so s)) s) mo tr) -> mspecE sel X P (upd_so get_so set_so f) Q.
Proof. intros f P Q H s mo tr HP. exact (H s mo tr HP). Qed.

Definition SoA (Km : Model -> Prop) (so : stdout_st) (tr0 : list event) : assnE St :=
  fun s mo tr => Km mo /\ get_so s = so /\ tr = tr0.

Lemma rd_so_SoA : forall {B} Km so tr0 (f : stdout_st -> Monad.M St B) (Q : B -> assnE St),
  mspecE sel X (SoA Km so tr0) (f so) Q -> mspecE sel X (SoA Km so tr0) (mbind (rd_so get_so) f) Q.
Proof.
  intros B Km so tr0 f Q H s mo tr HP. pose proof HP as (_ & Hso & _).
  change (twfE sel X (f (get_so s) s) mo tr (fun p mo' tr' => Q (fst p) (snd p) mo' tr')). rewrite Hso. exact (H s mo tr HP).
Qed.

Lemma upd_so_SoA : forall {B} h Km so tr0 (f : unit -> Monad.M St B) (Q : B -> assnE St),
  mspecE sel X (SoA Km (h so) tr0) (f tt) Q -> mspecE sel X (SoA Km so tr0) (mbind (upd_so get_so set_so h) f) Q.
Proof.
  intros B h Km so tr0 f Q H s mo tr (HK & Hso & ->). apply H. split; [exact HK|]. split; [|reflexivity].
  rewrite get_set, Hso. reflexivity.
Qed.

Lemma upd_so_SoA_last : forall h Km so tr0,
  mspecE sel X (SoA Km so tr0) (upd_so get_so set_so h) (fun _ => SoA Km (h so) tr0).
Proof.
  intros h Km so tr0 s mo tr (HK & Hso & ->). split; [exact HK|]. split; [|reflexivity]. cbn. rewrite get_set, Hso. reflexivity.
Qed.

Lemma ioctl_SoA : forall {B} Km so tr0 (f : sret -> Monad.M St B) (Q : B -> assnE St),
  mspecE sel X (SoA Km so tr0) (f (SErr ENOTTY)) Q ->
  mspecE sel X (SoA Km so tr0) (mbind (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) f) Q.
Proof.
  intros B Km so tr0 f Q H.
  eapply mspecE_bind with (Q1 := fun a s mo tr => SoA Km so tr0 s mo tr /\ a = SErr ENOTTY).
  - apply msysE_node; [exact I| intros; apply nprog_ioctl|].
    intros s mo tr rsp mo' evs a HP Hst Hd. destruct (stepR_ioctl sel 1 TIOCGWINSZ mo rsp mo' evs a Hst Hd) as (-> & -> & ->).
    rewrite app_nil_r. auto.
  - intros a. apply mspecE_pointwise. intros s mo tr [HP ->]. eapply mspecE_pre; [exact H|]. intros s' mo' tr' (-> & -> & ->). exact HP.
Qed.

Lemma stdout_stdio_write_E : forall Km so bs tr0,
  zlength (so_buf so ++ bs) < 2^62 ->
  mspecE sel X (SoA Km so tr0) (stdout_stdio_write get_so set_so bs)
               (fun _ => SoA Km (mkStdout true [] (so_lbf_nl so) (so_first so)) (tr0 ++ evw 1 (so_buf so ++ bs))).
Proof.
  intros Km so bs tr0 Hl. unfold stdout_stdio_write. apply rd_so_SoA.
  eapply mspecE_seq.
  { eapply mspecE_pre; [apply (stdio_writev_E 1 (so_buf so) bs tr0 (fun s mo => Km mo /\ get_so s = so)); exact Hl|].
    intros s mo tr (HK & Hso & ->). auto. }
  intros _. apply upd_so_E. intros s mo tr ((HK & Hso) & ->). split; [exact HK|].
  split; [rewrite get_set, Hso; reflexivity| reflexivity].
Qed.

Lemma stdout_writefn_E : forall Km so bs tr0,
  zlength (so_buf so ++ bs) < 2^62 ->
  mspecE sel X (SoA Km so tr0) (stdout_writefn get_so set_so bs)
               (fun _ => SoA Km (mkStdout true [] (if so_first so then false else so_lbf_nl so) false) (tr0 ++ evw 1 (so_buf so ++ bs))).
Proof.
  intros Km so bs tr0 Hl. unfold stdout_writefn. apply rd_so_SoA.
  destruct (so_first so) eqn:Ef.
  - eapply mspecE_seq with (R := SoA Km (mkStdout (so_active so) (so_buf so) false false) tr0).
    + apply upd_so_SoA. apply ioctl_SoA. apply upd_so_SoA_last.
    + intros _. eapply mspecE_post; [apply stdout_stdio_write_E; cbn [so_buf]; exact Hl|]. cbn [so_lbf_nl so_first so_buf]. auto.
  - eapply mspecE_seq with (R := SoA Km so tr0); [apply mspecE_ret; auto|].
    intros _. eapply mspecE_post; [apply stdout_stdio_write_E; exact Hl|]. rewrite Ef. auto.
Qed.

Lemma fwritex_lbf_nonl : forall Km buf fst p tr0,
  zlength buf + zlength p <= STDOUT_BUFSIZ -> after_last_nl p = 0 ->
  mspecE sel X (SoA Km (mkStdout true buf true fst) tr0) (stdout_fwritex get_so set_so p)
               (fun _ => SoA Km (mkStdout true (buf ++ p) true fst) tr0).
Proof.
  intros Km buf fst p tr0 Hl Hnl. unfold stdout_fwritex, stdout_towrite. apply upd_so_SoA. cbn [so_active]. apply rd_so_SoA.
  cbn [so_buf so_lbf_nl]. destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength p)); [lia|].
  rewrite Hnl. cbn [Z.ltb Z.compare]. eapply mspecE_seq with (R := SoA Km (mkStdout true buf true fst) tr0); [apply mspecE_ret; auto|].
  intros _. apply upd_so_SoA_last.
Qed.

Lemma fwritex_buffered : forall Km buf fst p tr0,
  zlength buf + zlength p <= STDOUT_BUFSIZ ->
  mspecE sel X (SoA Km (mkStdout true buf false fst) tr0) (stdout_fwritex get_so set_so p)
               (fun _ => SoA Km (mkStdout true (buf ++ p) false fst) tr0).
Proof.
  intros Km buf fst p tr0 Hl. unfold stdout_fwritex, stdout_towrite. apply upd_so_SoA. cbn [so_active]. apply rd_so_SoA.
  cbn [so_buf so_lbf_nl]. destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength p)); [lia|].
  apply upd_so_SoA_last.
Qed.

Lemma stdout_emit_first : forall Km tr0,
  mspecE sel X (SoA Km stdout_init tr0) (stdout_vprintf get_so set_so pieces_emit_0)
               (fun _ => SoA Km (mkStdout true [] false false) (tr0 ++ evw 1 [48; 10])).
Proof.
  intros Km tr0. unfold stdout_vprintf, pieces_emit_0, stdout_init. cbn [out_pieces].
  unfold stdout_towrite at 1. apply upd_so_SoA. cbn [so_active so_lbf_nl so_first].
  eapply mspecE_seq; [apply fwritex_lbf_nonl; [unfold zlength, STDOUT_BUFSIZ; cbn; lia| reflexivity]|]. intros _.
  eapply mspecE_seq; [apply fwritex_lbf_nonl; [unfold zlength, STDOUT_BUFSIZ; cbn; lia| reflexivity]|]. intros _.
  eapply mspecE_seq; [apply fwritex_lbf_nonl; [unfold zlength, STDOUT_BUFSIZ; cbn; lia| reflexivity]|]. intros _.
  eapply mspecE_seq; [apply fwritex_lbf_nonl; [unfold zlength, STDOUT_BUFSIZ; cbn; lia| reflexivity]|]. intros _.
  cbn [app].
  eapply mspecE_seq.
  { unfold stdout_fwritex, stdout_towrite. apply upd_so_SoA. cbn [so_active]. apply rd_so_SoA.
    cbn [so_buf so_lbf_nl]. change (STDOUT_BUFSIZ - zlength [48] <? zlength [10]) with false. cbv iota.
    change (after_last_nl [10]) with 1. change (0 <? 1) with true. cbv iota. change (firstn (Z.to_nat 1) [10]) with [10].
    eapply mspecE_seq; [apply stdout_writefn_E; unfold zlength; cbn; lia|]. intros _.
    apply upd_so_SoA_last. }
  intros _. apply mspecE_ret. intros s mo tr H. exact H.
Qed.

Lemma stdout_emit_next : forall Km buf tr0,
  zlength buf + 2 <= STDOUT_BUFSIZ ->
  mspecE sel X (SoA Km (mkStdout true buf false false) tr0) (stdout_vprintf get_so set_so pieces_emit_0)
               (fun _ => SoA Km (mkStdout true (buf ++ [48; 10]) false false) tr0).
Proof.
  intros Km buf tr0 Hl. unfold stdout_vprintf, pieces_emit_0. cbn [out_pieces].
  unfold stdout_towrite at 1. apply upd_so_SoA. cbn [so_active].
  eapply mspecE_seq; [apply fwritex_buffered; unfold zlength in *; cbn [length]; lia|]. intros _.
  eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
  eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
  eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
  eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
  apply mspecE_ret. intros s mo tr H. rewrite !app_nil_r, <- !app_assoc in H. exact H.
Qed.

Lemma stdout_exit_flush_E : forall Km so tr0,
  zlength (so_buf so) < 2^62 ->
  mspecE sel X (SoA Km so tr0) (stdout_exit_flush get_so set_so)
               (fun _ s mo tr => Km mo /\ tr = tr0 ++ evw 1 (so_buf so)).
Proof.
  intros Km so tr0 Hl. unfold stdout_exit_flush. apply rd_so_SoA. apply mspecE_if; intros C.
  - eapply mspecE_post; [apply stdout_writefn_E; rewrite app_nil_r; exact Hl|]. intros _ s mo tr (HK & _ & ->).
    rewrite app_nil_r. auto.
  - apply mspecE_ret. intros s mo tr (HK & _ & ->). split; [exact HK|]. apply Z.ltb_ge in C.
    destruct (so_buf so); [rewrite app_nil_r; reflexivity| unfold zlength in C; cbn in C; lia].
Qed.

End Stdio.
