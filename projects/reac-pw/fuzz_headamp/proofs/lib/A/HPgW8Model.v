(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Model.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp (the Pod model is the same file in both units). *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

Lemma wm_L0 : forall sh ps es,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es ->
  (length ps <= 2)%nat -> (length es < 32)%nat ->
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) <= 5384 /\
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) mod 8 = 0.
Proof.
  intros sh ps es Hv He Hes Hp Hq. destruct (pc_buf_len_open sh ps es Hv He Hes) as [H1 H2].
  split; [lia|]. apply Z.mod_divide; [lia | exact H2].
Qed.

Lemma wm_ents_first : forall sh ps es,
  pc_first (PbCut sh ps (Some es)) = true -> pc_ents (PbCut sh ps (Some es)) = es.
Proof.
  intros sh ps es H. unfold pc_first in H. cbn [pc_props] in H. unfold pc_ents, first_params. cbn [pc_props pc_open].
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:E.
  - apply find_some in E as [Hin Hk]. exfalso. apply negb_true_iff in H.
    assert (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps = true) by (apply existsb_exists; eauto).
    congruence.
  - reflexivity.
Qed.

(** |pc_buf| + |enc_pod ed| fits in buf, and the new len in the statement's form. *)
Lemma wm_put_bound : forall sh ps es ed,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es -> ent_wf ed ->
  (length ps <= 2)%nat -> (length es < 32)%nat ->
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es))) + length (enc_pod ed)) <= POD_BUF_MAX /\
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es))) + length (enc_pod ed))
  = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) + 8 + e_size ed + pad8 (e_size ed).
Proof.
  intros sh ps es ed Hv He Hes Hed Hp Hq. destruct (wm_L0 sh ps es Hv He Hes Hp Hq) as [H1 _].
  rewrite Nat2Z.inj_add, (zlen_enc_pod ed Hed). pose proof (pad8_bound (e_size ed)).
  destruct Hed as (_ & _ & Hs). unfold POD_BUF_MAX. split; lia.
Qed.

Lemma wm_body_bound : forall e, ent_wf e -> (length (e_body e) <= 96)%nat.
Proof. intros e (_ & Hb & Hs). rewrite Hb. lia. Qed.

Lemma wm_img_other : forall sh ps es ed,
  pc_first (PbCut sh ps (Some es)) = false ->
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es -> ent_wf ed ->
  (length ps <= 2)%nat -> (length es < 32)%nat ->
  pc_image (PbCut sh ps (Some (es ++ [ed]))) =
  overwrite (overwrite (pc_image (PbCut sh ps (Some es))) (length (pc_buf (PbCut sh ps (Some es)))) (enc_pod ed))
    (Z.to_nat OFF_LEN)
    (le64 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) + 8 + e_size ed + pad8 (e_size ed))).
Proof.
  intros sh ps es ed H Hv He Hes Hed Hp Hq.
  destruct (wm_put_bound sh ps es ed Hv He Hes Hed Hp Hq) as [B E].
  unfold pc_image. cbn [pc_shape pc_props]. rewrite <- pc_buf_pod. rewrite (pc_ents_pod_other sh ps es ed H).
  rewrite pp_image_put by exact B. rewrite E. reflexivity.
Qed.

Lemma wm_img_first : forall sh ps es ed,
  pc_first (PbCut sh ps (Some es)) = true ->
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es -> ent_wf ed ->
  (length ps <= 2)%nat -> (length es < 32)%nat ->
  pc_image (PbCut sh ps (Some (es ++ [ed]))) =
  overwrite (overwrite (overwrite (overwrite (pc_image (PbCut sh ps (Some es)))
      (length (pc_buf (PbCut sh ps (Some es)))) (enc_pod ed))
      (Z.to_nat OFF_LEN)
      (le64 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) + 8 + e_size ed + pad8 (e_size ed))))
      (Z.to_nat (OFF_ENT + ENT_SIZE * Z.of_nat (length es))) (ent_mem ed))
    (Z.to_nat OFF_N_ENT) (le32 (Z.of_nat (length es) + 1)).
Proof.
  intros sh ps es ed H Hv He Hes Hed Hp Hq.
  destruct (wm_put_bound sh ps es ed Hv He Hes Hed Hp Hq) as [B E].
  assert (Bs : Forall (fun e => (length (e_body e) <= 96)%nat) (es ++ [ed])).
  { apply Forall_app. split; [eapply Forall_impl; [exact wm_body_bound | exact Hes] | constructor; [apply wm_body_bound; exact Hed | constructor]]. }
  assert (Bb : Z.of_nat (length (pc_buf (PbCut sh ps (Some es)) ++ enc_pod ed)) <= POD_BUF_MAX)
    by (rewrite length_app; exact B).
  unfold pc_image. cbn [pc_shape pc_props]. rewrite <- pc_buf_pod. rewrite (pc_ents_pod sh ps es ed H).
  rewrite (wm_ents_first sh ps es H).
  rewrite (pp_image_ent _ _ _ _ es ed false Bb Hq Bs).
  rewrite pp_image_put by exact B. rewrite E. reflexivity.
Qed.

