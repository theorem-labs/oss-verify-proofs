(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim Canon.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import RzCPS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ct_shape (fs : Fs) (ct : ctrace) : TSet :=
  t_emit (evw (ct_fd ct) (ct_bytes ct)) (t_exit (Z_to_bv 64 (ct_code ct)) fs).

Lemma is_prefix_app_single : forall {X} (l : list X) (x : X) tr,
  is_prefix tr (l ++ [x]) <-> is_prefix tr l \/ tr = l ++ [x].
Proof.
  intros X l x tr. split.
  - intros H. apply is_prefix_app_split in H as [H|(b' & -> & Hb)]; [left; exact H|].
    destruct b' as [|y b']; [left; rewrite app_nil_r; apply is_prefix_refl|].
    right. cbn in Hb. destruct Hb as [-> Hb]. apply is_prefix_nil_r in Hb. subst. reflexivity.
  - intros [H| ->]; [apply is_prefix_app_r; exact H| apply is_prefix_refl].
Qed.

Lemma ct_shape_iff : forall fs ct tr, ct_shape fs ct tr <-> is_prefix tr (ct_events fs ct).
Proof.
  intros fs ct tr. unfold ct_shape, ct_events. rewrite is_prefix_app_single.
  set (e := evw (ct_fd ct) (ct_bytes ct)). set (x := ExitEv (Z_to_bv 64 (ct_code ct)) fs).
  change (t_emit e (t_emit [x] t_nil) tr <-> is_prefix tr e \/ tr = e ++ [x]).
  split.
  - intros [H|(tr' & E & H2)]; [left; exact H|]. subst tr.
    destruct H2 as [H3|(tr'' & E2 & H4)].
    + destruct tr' as [|y tr']; [left; rewrite app_nil_r; apply is_prefix_refl|].
      cbn in H3. destruct H3 as [-> H3]. apply is_prefix_nil_r in H3. subst. right. reflexivity.
    + unfold t_nil in H4. subst. right. rewrite app_nil_r. reflexivity.
  - intros [H| ->].
    + left. exact H.
    + right. exists [x]. split; [reflexivity|]. right. exists []. split; reflexivity.
Qed.

Lemma canonT_shape : forall argv fs, t_eq (canonT argv fs) (t_alt2 (ct_shape fs (ctrace_of argv fs false)) (ct_shape fs (ctrace_of argv fs true))).
Proof.
  intros argv fs tr. unfold canonT, t_alt2. rewrite !ct_shape_iff. split.
  - intros (ct & Hin & Hp). cbn in Hin. destruct Hin as [<-|[<-|[]]]; [left| right]; exact Hp.
  - intros [Hp|Hp]; eexists; split; [| exact Hp| | exact Hp]; cbn; auto.
Qed.

Lemma t_alt2_same : forall T, t_eq (t_alt2 T T) T.
Proof. intros T tr. unfold t_alt2. tauto. Qed.

Lemma file_trace_code : forall d, ct_code (file_trace d) = 0 \/ ct_code (file_trace d) = 2.
Proof. intros d. unfold file_trace. repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; auto. Qed.

Lemma ctrace_of_2' : forall argv fs ok, Z.of_nat (length argv) = 2 ->
  ctrace_of argv fs ok = match (if ok then open_class (nth 1 argv []) fs else OCFail) with
                         | OCFail => mkCT 2 (msg_cannot_open (nth 1 argv [])) 2
                         | OCDir => mkCT 2 (msg_read_error (nth 1 argv [])) 2
                         | OCFile data => file_trace (map bv_unsigned data)
                         end.
Proof. intros argv fs ok H. unfold ctrace_of. rewrite H. reflexivity. Qed.

Lemma ctrace_of_usage' : forall argv fs ok, Z.of_nat (length argv) <> 2 ->
  ctrace_of argv fs ok = mkCT 2 (msg_usage (nth 0 argv [])) 2.
Proof. intros argv fs ok H. unfold ctrace_of. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

Section Skel.
Variable segs : list Segment.
Variable argv : list (list Z).
Variable fs : Fs.
Variables START OPEN FAILED OPENED : config -> Prop.
Variable EXIT : Z -> config -> Prop.

Hypothesis H_exit : forall code c, EXIT code c -> realizes segs c (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) fs).
Hypothesis H_usage : Z.of_nat (length argv) <> 2 -> cpsE segs START (evw 2 (msg_usage (nth 0 argv []))) (EXIT 2).
Hypothesis H_to_open : Z.of_nat (length argv) = 2 -> cps segs START OPEN.
Hypothesis H_open_fail : Z.of_nat (length argv) = 2 -> open_class (nth 1 argv []) fs = OCFail -> cps segs OPEN FAILED.
Hypothesis H_open : Z.of_nat (length argv) = 2 -> open_class (nth 1 argv []) fs <> OCFail -> cps2 segs OPEN FAILED OPENED.
Hypothesis H_failed : Z.of_nat (length argv) = 2 -> cpsE segs FAILED (evw 2 (msg_cannot_open (nth 1 argv []))) (EXIT 2).
Hypothesis H_dir : Z.of_nat (length argv) = 2 -> open_class (nth 1 argv []) fs = OCDir -> cpsE segs OPENED (evw 2 (msg_read_error (nth 1 argv []))) (EXIT 2).
Hypothesis H_file : Z.of_nat (length argv) = 2 -> forall data, open_class (nth 1 argv []) fs = OCFile data ->
  cpsE segs OPENED (evw (ct_fd (file_trace (map bv_unsigned data))) (ct_bytes (file_trace (map bv_unsigned data))))
                   (EXIT (ct_code (file_trace (map bv_unsigned data)))).

Lemma cpsE_exit_shape : forall P ct c, ct_code ct = 0 \/ ct_code ct = 2 ->
  cpsE segs P (evw (ct_fd ct) (ct_bytes ct)) (EXIT (ct_code ct)) -> P c -> realizes segs c (ct_shape fs ct).
Proof.
  intros P ct c Hcode H HP. apply (H _ c HP). intros c' HE.
  replace (Z_to_bv 64 (ct_code ct)) with (bv_and (Z_to_bv 64 (ct_code ct)) (Z_to_bv 64 255)); [apply H_exit; exact HE|].
  destruct Hcode as [-> | ->]; apply bv_eq; vm_compute; reflexivity.
Qed.

Theorem main_realizes : forall c, START c -> realizes segs c (canonT argv fs).
Proof.
  intros c Hc. eapply rz_conseq; [| apply t_eq_sym, canonT_shape].
  destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
  - rewrite (ctrace_of_2' argv fs false E2), (ctrace_of_2' argv fs true E2).
    apply (H_to_open E2 _ c Hc). intros c1 Hopen.
    destruct (open_class (nth 1 argv []) fs) as [| |data] eqn:Hcl.
    +
      eapply rz_conseq; [| apply t_eq_sym, t_alt2_same].
      apply (H_open_fail E2 eq_refl _ c1 Hopen). intros c2 Hf.
      exact (cpsE_exit_shape FAILED (mkCT 2 (msg_cannot_open (nth 1 argv [])) 2) c2 (or_intror eq_refl) (H_failed E2) Hf).
    + apply (H_open E2 ltac:(discriminate) _ _ c1 Hopen).
      * intros c2 Hf. exact (cpsE_exit_shape FAILED (mkCT 2 (msg_cannot_open (nth 1 argv [])) 2) c2 (or_intror eq_refl) (H_failed E2) Hf).
      * intros c2 Ho. exact (cpsE_exit_shape OPENED (mkCT 2 (msg_read_error (nth 1 argv [])) 2) c2 (or_intror eq_refl) (H_dir E2 eq_refl) Ho).
    + apply (H_open E2 ltac:(discriminate) _ _ c1 Hopen).
      * intros c2 Hf. exact (cpsE_exit_shape FAILED (mkCT 2 (msg_cannot_open (nth 1 argv [])) 2) c2 (or_intror eq_refl) (H_failed E2) Hf).
      * intros c2 Ho. exact (cpsE_exit_shape OPENED (file_trace (map bv_unsigned data)) c2 (file_trace_code _) (H_file E2 data eq_refl) Ho).
  - rewrite !(ctrace_of_usage' argv fs _ NE2). eapply rz_conseq; [| apply t_eq_sym, t_alt2_same].
    exact (cpsE_exit_shape START (mkCT 2 (msg_usage (nth 0 argv [])) 2) c (or_intror eq_refl) (H_usage NE2) Hc).
Qed.

End Skel.
