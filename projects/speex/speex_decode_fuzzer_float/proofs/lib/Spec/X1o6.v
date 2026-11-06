(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ri X1r8 X1nu X1o3 X1o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma zlen_app : forall {A} (l1 l2 : list A), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

Lemma evw_firstn_skipn : forall fd n l, evw fd (firstn n l) ++ evw fd (skipn n l) = evw fd l.
Proof. intros. rewrite <- evw_app, firstn_skipn. reflexivity. Qed.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma stdio_wloop_E : forall fuel fd iovs T (Kt : St -> Model -> Prop),
(length iovs <= 2)%nat -> wv_total iovs < 2^64 ->
mspecE sel X (fun s mo tr => Kt s mo /\ tr ++ evw fd (concat iovs) = T) (stdio_wloop fuel fd iovs)
(fun _ s mo tr => Kt s mo /\ tr = T).
Proof.
induction fuel as [|fuel IH]; intros fd iovs T Kt Hn Hl; cbn [stdio_wloop]; [apply mspecE_munr|].
eapply mspecE_bind with (Q1 := fun k s mo tr => Kt s mo /\ ((wv_total iovs = 0 /\ k = 0) \/ 1 <= k <= wv_total iovs)
/\ tr ++ evw fd (skipn (Z.to_nat k) (concat iovs)) = T).
{ apply msysE_node; [exact I| intros; apply nprog_writev|].
intros s mo tr rsp mo' evs k [HK HT] Hst Hd.
destruct (stepR_writev sel fd iovs mo rsp mo' evs k Hl Hst Hd) as (-> & Hk & ->).
split; [exact HK|]. split; [exact Hk|]. rewrite <- app_assoc, evw_firstn_skipn. exact HT. }
intros k. apply mspecE_if; intros Hc.
- apply mspecE_ret. intros s mo tr (HK & _ & HT). split; [exact HK|]. apply Z.eqb_eq in Hc.
rewrite Hc in HT. unfold wv_total, zlength in HT. rewrite Nat2Z.id, skipn_all, app_nil_r in HT. exact HT.
- apply Z.eqb_neq in Hc. apply mspecE_pointwise. intros s0 mo0 tr1 (HK & Hk & HT).
assert (Hk' : 0 <= k < wv_total iovs) by (pose proof (wv_total_nonneg iovs); lia).
eapply mspecE_pre; [apply (IH fd (wv_advance k iovs) T Kt)|].
+ pose proof (wv_advance_length k iovs). lia.
+ rewrite (wv_advance_total k iovs Hn Hk'). lia.
+ intros s mo tr (-> & -> & ->). split; [exact HK|]. rewrite (wv_advance_concat k iovs Hn Hk'). exact HT.
Qed.

Lemma stdio_writev_E : forall fd buf bs tr0 (Kt : St -> Model -> Prop),
mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (stdio_writev fd buf bs)
(fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw fd (buf ++ bs)).
Proof.
intros fd buf bs tr0 Kt. unfold stdio_writev.
destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength bs)) as [LT|GE]; [apply mspecE_munr|].
eapply mspecE_pre; [apply (stdio_wloop_E _ fd (wv_iovs buf bs) (tr0 ++ evw fd (buf ++ bs)) Kt)|].
- apply wv_iovs_length.
- rewrite wv_iovs_total. unfold WRITEV_MAX in GE. lia.
- intros s mo tr [HK ->]. split; [exact HK|]. rewrite wv_iovs_concat. reflexivity.
Qed.

Lemma stderr_pieces_E : forall ps buf T (Kt : St -> Model -> Prop),
mspecE sel X (fun s mo tr => Kt s mo /\ tr ++ evw 2 (buf ++ concat ps) = T) (@stderr_pieces St buf ps)
(fun buf' s mo tr => Kt s mo /\ tr ++ evw 2 buf' = T).
Proof.
induction ps as [|p ps IH]; intros buf T Kt; cbn [stderr_pieces].
- apply mspecE_ret. intros s mo tr [HK HT]. rewrite app_nil_r in HT. auto.
- apply mspecE_if; intros C.
+ apply mspecE_pointwise. intros s0 mo0 tr0 [HK HT].
eapply mspecE_seq.
{ eapply mspecE_pre; [apply (stdio_writev_E 2 buf p tr0 (fun s mo => Kt s mo /\ s = s0))|].
intros s mo tr (-> & -> & ->). auto. }
intros _. eapply mspecE_pre; [apply IH|].
intros s mo tr ((HK' & _) & ->). split; [exact HK'|]. cbn [app]. rewrite <- app_assoc, <- evw_app. cbn [concat] in HT.
rewrite <- app_assoc. exact HT.
+ eapply mspecE_pre; [apply IH|].
intros s mo tr [HK HT]. split; [exact HK|]. rewrite <- app_assoc. cbn [concat] in HT. exact HT.
Qed.

Lemma stderr_fprintf_E : forall ps tr0 (Kt : St -> Model -> Prop),
mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (@stderr_fprintf St ps)
(fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw 2 (concat ps)).
Proof.
intros ps tr0 Kt. unfold stderr_fprintf.
eapply mspecE_bind; [eapply mspecE_pre; [apply (stderr_pieces_E ps [] (tr0 ++ evw 2 (concat ps)) Kt)|]|].
{ intros s mo tr [HK ->]. split; [exact HK| reflexivity]. }
intros buf. apply mspecE_pointwise. intros s0 mo0 tr1 (HK & HT).
eapply mspecE_conseq; [apply (stdio_writev_E 2 buf [] tr1 (fun s mo => Kt s mo /\ s = s0 /\ mo = mo0))| |].
- intros s mo tr (-> & -> & ->). auto.
- intros _ s mo tr ((HK' & _ & _) & ->). split; [exact HK'|]. rewrite app_nil_r. exact HT.
Qed.

Lemma stderr_fwrite_E : forall bs tr0 (Kt : St -> Model -> Prop),
mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (@stderr_fwrite St bs)
(fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw 2 bs).
Proof.
intros bs tr0 Kt. unfold stderr_fwrite. apply mspecE_if; intros C.
- eapply mspecE_post; [apply (stdio_writev_E 2 [] bs tr0 Kt)|]. intros _ s mo tr [HK ->]. auto.
- apply mspecE_ret. intros s mo tr [HK ->]. split; [exact HK|]. apply Z.ltb_ge in C.
destruct bs; [rewrite app_nil_r; reflexivity| unfold zlength in C; cbn in C; lia].
Qed.

Lemma s_notify_E : forall msg tr0 (Kt : St -> Model -> Prop),
mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (@s_notify St msg)
(fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw 2 (notify_bytes msg)).
Proof. intros. apply stderr_fprintf_E. Qed.

Lemma s_warning_E : forall msg tr0 (Kt : St -> Model -> Prop),
mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (@s_warning St msg)
(fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw 2 (warning_bytes msg)).
Proof. intros. apply stderr_fprintf_E. Qed.

Lemma REL_s_notify : forall (K : St -> Model -> Prop) msg,
REL sel X K (fun u : unit => u) (@s_notify St msg) (p_notify msg).
Proof.
intros K msg. constructor. intros tr0 q. eapply mspecE_conseq; [apply (s_notify_E msg (tr0 ++ evw 2 (p_err q)) K)| |].
- intros s mo tr H. exact H.
- intros [] s mo tr [HK ->]. exists (p_app (notify_bytes msg) q). split; [reflexivity|]. split; [exact HK|].
cbn [p_app p_err]. rewrite evw_app, app_assoc. reflexivity.
Qed.

Lemma REL_s_warning : forall (K : St -> Model -> Prop) msg,
REL sel X K (fun u : unit => u) (@s_warning St msg) (p_warning msg).
Proof.
intros K msg. constructor. intros tr0 q. eapply mspecE_conseq; [apply (s_warning_E msg (tr0 ++ evw 2 (p_err q)) K)| |].
- intros s mo tr H. exact H.
- intros [] s mo tr [HK ->]. exists (p_app (warning_bytes msg) q). split; [reflexivity|]. split; [exact HK|].
cbn [p_app p_err]. rewrite evw_app, app_assoc. reflexivity.
Qed.

Hypothesis get_set : forall v s, get_so (set_so v s) = v.

Lemma upd_so_E : forall f (P : assnE St) (Q : unit -> assnE St),
(forall s mo tr, P s mo tr -> Q tt (set_so (f (get_so s)) s) mo tr) -> mspecE sel X P (upd_so get_so set_so f) Q.
Proof. intros f P Q H s mo tr HP. exact (H s mo tr HP). Qed.

Definition SoA (Km : Model -> Prop) (so : stdout_st) (tr0 : list event) : assnE St :=
fun s mo tr => Km mo /\ get_so s = so /\ tr = tr0.

Lemma rd_so_SoA : forall {B} Km so tr0 (f : stdout_st -> X1qx.M St B) (Q : B -> assnE St),
mspecE sel X (SoA Km so tr0) (f so) Q -> mspecE sel X (SoA Km so tr0) (mbind (rd_so get_so) f) Q.
Proof.
intros B Km so tr0 f Q H s mo tr HP. pose proof HP as (_ & Hso & _).
change (twfE sel X (f (get_so s) s) mo tr (fun p mo' tr' => Q (fst p) (snd p) mo' tr')). rewrite Hso. exact (H s mo tr HP).
Qed.

Lemma upd_so_SoA : forall {B} h Km so tr0 (f : unit -> X1qx.M St B) (Q : B -> assnE St),
mspecE sel X (SoA Km (h so) tr0) (f tt) Q -> mspecE sel X (SoA Km so tr0) (mbind (upd_so get_so set_so h) f) Q.
Proof.
intros B h Km so tr0 f Q H s mo tr (HK & Hso & ->). apply H. split; [exact HK|]. split; [|reflexivity].
cbn [snd]. rewrite get_set, Hso. reflexivity.
Qed.

Lemma upd_so_SoA_last : forall h Km so tr0,
mspecE sel X (SoA Km so tr0) (upd_so get_so set_so h) (fun _ => SoA Km (h so) tr0).
Proof.
intros h Km so tr0 s mo tr (HK & Hso & ->). split; [exact HK|]. split; [|reflexivity]. cbn. rewrite get_set, Hso. reflexivity.
Qed.

Lemma ioctl_SoA : forall {B} Km so tr0 (f : sret -> X1qx.M St B) (Q : B -> assnE St),
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
mspecE sel X (SoA Km so tr0) (stdout_stdio_write get_so set_so bs)
(fun _ => SoA Km (mkStdout true [] (so_lbf_nl so) (so_first so)) (tr0 ++ evw 1 (so_buf so ++ bs))).
Proof.
intros Km so bs tr0. unfold stdout_stdio_write. apply rd_so_SoA.
eapply mspecE_seq.
{ eapply mspecE_pre; [apply (stdio_writev_E 1 (so_buf so) bs tr0 (fun s mo => Km mo /\ get_so s = so))|].
intros s mo tr (HK & Hso & ->). auto. }
intros _. apply upd_so_E. intros s mo tr ((HK & Hso) & ->). split; [exact HK|].
split; [rewrite get_set, Hso; reflexivity| reflexivity].
Qed.

Lemma stdout_writefn_E : forall Km so bs tr0,
mspecE sel X (SoA Km so tr0) (stdout_writefn get_so set_so bs)
(fun _ => SoA Km (mkStdout true [] (if so_first so then false else so_lbf_nl so) false) (tr0 ++ evw 1 (so_buf so ++ bs))).
Proof.
intros Km so bs tr0. unfold stdout_writefn. apply rd_so_SoA.
destruct (so_first so) eqn:Ef.
- eapply mspecE_seq with (R := SoA Km (mkStdout (so_active so) (so_buf so) false false) tr0).
+ apply upd_so_SoA. apply ioctl_SoA. apply upd_so_SoA_last.
+ intros _. eapply mspecE_post; [apply stdout_stdio_write_E|]. cbn [so_lbf_nl so_first so_buf]. auto.
- eapply mspecE_seq with (R := SoA Km so tr0); [apply mspecE_ret; auto|].
intros _. eapply mspecE_post; [apply stdout_stdio_write_E|]. rewrite Ef. auto.
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
mspecE sel X (SoA Km stdout_init tr0) (stdout_vprintf get_so set_so (pieces_emit 0))
(fun _ => SoA Km (mkStdout true [] false false) (tr0 ++ evw 1 [48; 10])).
Proof.
intros Km tr0. unfold stdout_vprintf, stdout_init. change (pieces_emit 0) with [ []; []; [48]; []; [10] ]. cbn [out_pieces].
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
eapply mspecE_seq; [apply stdout_writefn_E|]. intros _.
apply upd_so_SoA_last. }
intros _. apply mspecE_ret. intros s mo tr H. exact H.
Qed.

Lemma stdout_emit_next : forall Km buf tr0,
zlength buf + 2 <= STDOUT_BUFSIZ ->
mspecE sel X (SoA Km (mkStdout true buf false false) tr0) (stdout_vprintf get_so set_so (pieces_emit 0))
(fun _ => SoA Km (mkStdout true (buf ++ [48; 10]) false false) tr0).
Proof.
intros Km buf tr0 Hl. unfold stdout_vprintf. change (pieces_emit 0) with [ []; []; [48]; []; [10] ]. cbn [out_pieces].
unfold stdout_towrite at 1. apply upd_so_SoA. cbn [so_active].
eapply mspecE_seq; [apply fwritex_buffered; unfold zlength in *; cbn [length]; lia|]. intros _.
eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
eapply mspecE_seq; [apply fwritex_buffered; rewrite !zlen_app; unfold zlength in *; cbn [length]; lia|]. intros _.
apply mspecE_ret. intros s mo tr H. rewrite !app_nil_r, <- !app_assoc in H. exact H.
Qed.

Lemma stdout_exit_flush_E : forall Km so tr0,
mspecE sel X (SoA Km so tr0) (stdout_exit_flush get_so set_so)
(fun _ s mo tr => Km mo /\ tr = tr0 ++ evw 1 (so_buf so)).
Proof.
intros Km so tr0. unfold stdout_exit_flush. apply rd_so_SoA. apply mspecE_if; intros C.
- eapply mspecE_post; [apply stdout_writefn_E|]. intros _ s mo tr (HK & _ & ->).
rewrite app_nil_r. auto.
- apply mspecE_ret. intros s mo tr (HK & _ & ->). split; [exact HK|]. apply Z.ltb_ge in C.
destruct (so_buf so); [rewrite app_nil_r; reflexivity| unfold zlength in C; cbn in C; lia].
Qed.

End Stdio.
