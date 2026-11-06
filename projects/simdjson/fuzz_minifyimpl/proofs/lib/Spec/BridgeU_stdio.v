(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver BridgeU_base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition Wz (fd : Z) (l : list Z) : list event := map (WriteEv (Z_to_bv 64 fd)) (to_bytes l).

Lemma Wz_app : forall fd a b, Wz fd (a ++ b) = Wz fd a ++ Wz fd b.
Proof. intros. unfold Wz, to_bytes. rewrite !map_app. reflexivity. Qed.
Lemma Wz_nil : forall fd, Wz fd [] = []. Proof. reflexivity. Qed.

Lemma concat_to_bytes : forall iov, concat (map to_bytes iov) = to_bytes (concat iov).
Proof. intros. unfold to_bytes. symmetry. apply concat_map. Qed.

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nonneg : forall {A} (a : list A), 0 <= zlength a.
Proof. intros. unfold zlength. lia. Qed.

Lemma concat_iov_advance : forall iov cnt, (length iov <= 2)%nat -> 0 <= cnt ->
  concat (iov_advance iov cnt) = skipn (Z.to_nat cnt) (concat iov).
Proof.
  intros iov cnt Hl Hc. destruct iov as [|a [|b [|c r]]]; cbn [length] in Hl; try lia.
  - cbn. rewrite skipn_nil. reflexivity.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn [iov_advance]. unfold zlength. destruct (Z.ltb_spec (Z.of_nat (length a)) cnt) as [H|H]; cbn [concat]; rewrite !app_nil_r.
    + rewrite skipn_app. rewrite (skipn_all2 a) by lia. cbn [app]. f_equal. lia.
    + rewrite skipn_app. replace (Z.to_nat cnt - length a)%nat with O by lia. reflexivity.
Qed.

Lemma length_iov_advance : forall iov cnt, (length iov <= 2)%nat -> (length (iov_advance iov cnt) <= 2)%nat.
Proof.
  intros iov cnt Hl. destruct iov as [|a [|b r]]; cbn [iov_advance length]; try lia.
  destruct (zlength a <? cnt); cbn; lia.
Qed.

Lemma dec_writev_full : forall k, 0 <= k < 2^64 -> dec_writev k (eff0 (Z_to_bv 64 k)) = Some k.
Proof.
  intros k Hk. unfold dec_writev, dec_count0, dec_count, eff0. rewrite unsigned_lit by lia.
  destruct (Z.eqb_spec k 0) as [->|E]; [reflexivity|].
  replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.leb_refl. reflexivity.
Qed.

Section StdioWrite.
Context {St : Type}.

Lemma write_loop_det : forall fuel fd iov (s : St) mo,
  (length iov <= 2)%nat -> iov_total iov < Z.of_nat fuel -> iov_total iov < 2^64 ->
  det (stdio_write_loop fuel fd iov s) mo (Wz fd (concat iov)) (tt, s) (eq mo).
Proof.
  induction fuel as [|f IH]; intros fd iov s mo Hl Hf H64.
  - pose proof (zlength_nonneg (concat iov)). unfold iov_total in Hf. lia.
  - cbn [stdio_write_loop]. unfold mbind, msys.
    eapply sound_ebind.
    + apply (sound_enode _ _ mo (fun tr x mo1 => mo1 = mo /\ exists k, x = (k, s) /\
               ((iov_total iov = 0 /\ k = 0) \/ 1 <= k <= iov_total iov) /\ tr = Wz fd (firstn (Z.to_nat k) (concat iov)))).
      * intros rsp mo1 evs Hst. apply nstep_dec_writev in Hst.
        2:{ rewrite concat_to_bytes. unfold to_bytes. rewrite length_map. exact H64. }
        destruct Hst as (k & Hd & Hk & -> & ->). rewrite concat_to_bytes in Hd, Hk |- *.
        unfold to_bytes in Hd, Hk. rewrite length_map in Hd, Hk. fold (zlength (concat iov)) in Hd, Hk. fold (iov_total iov) in Hd, Hk.
        rewrite Hd. exists (k, s). split; [reflexivity|]. split; [reflexivity|]. exists k. split; [reflexivity|]. split.
        -- destruct Hk as [[Hz ->]|Hk]; [left|right; exact Hk]. unfold iov_total, zlength. split; [lia|reflexivity].
        -- unfold Wz, to_bytes. rewrite firstn_map. reflexivity.
      * intros code mo' H. exact H.
    + intros tr x mo1 (-> & k & -> & Hk & ->). cbn [fst snd].
      destruct (Z.eqb_spec k (iov_total iov)) as [E|E].
      * apply sound_ret. split; [|split; reflexivity]. rewrite app_nil_r. subst k.
        unfold iov_total, zlength. rewrite Nat2Z.id. rewrite firstn_all. reflexivity.
      * assert (Hk' : 1 <= k < iov_total iov) by lia.
        eapply sound_conseq.
        -- apply (IH fd (iov_advance iov k) s mo).
           ++ apply length_iov_advance. exact Hl.
           ++ unfold iov_total in *. rewrite concat_iov_advance by (auto; lia). unfold zlength in *. rewrite length_skipn. lia.
           ++ unfold iov_total in *. rewrite concat_iov_advance by (auto; lia). unfold zlength in *. rewrite length_skipn. lia.
        -- intros tr2 y mo2 (-> & -> & <-). split; [|split; reflexivity].
           rewrite concat_iov_advance by (auto; lia). rewrite <- Wz_app. rewrite firstn_skipn. reflexivity.
Qed.

Lemma write_loop_ex : forall fuel fd iov (s : St) mo,
  iov_total iov < 2^64 ->
  ex (stdio_write_loop (S fuel) fd iov s) mo (Wz fd (concat iov)) (tt, s) (eq mo).
Proof.
  intros fuel fd iov s mo H64. cbn [stdio_write_loop]. unfold mbind, msys.
  rewrite <- (app_nil_r (Wz fd (concat iov))).
  set (k := iov_total iov).
  assert (Hst : nstep (NWritev fd (map to_bytes iov)) mo (eff0 (Z_to_bv 64 k)) mo (Wz fd (concat iov))).
  { cbn [nstep]. split; [reflexivity|]. cbv zeta. rewrite concat_to_bytes. unfold to_bytes at 1 2. rewrite !length_map.
    fold (zlength (concat iov)). fold (iov_total iov). fold k.
    destruct (Z.eqb_spec k 0) as [E|E].
    - split; [rewrite E; reflexivity|]. unfold k, iov_total, zlength in E. destruct (concat iov); [reflexivity|cbn in E; lia].
    - exists k. pose proof (zlength_nonneg (concat iov)). unfold k, iov_total in *. split; [lia|]. split; [reflexivity|].
      unfold Wz. unfold zlength. rewrite Nat2Z.id. unfold to_bytes. rewrite <- (length_map (Z_to_bv 8) (concat iov)). rewrite firstn_all. reflexivity. }
  eapply ex_ebind.
  - eapply (ex_enode _ _ mo _ mo _ (k, s) (eq mo) Hst); [|reflexivity].
    pose proof (zlength_nonneg (concat iov)) as Hnn. fold (iov_total iov) in Hnn. fold k in Hnn.
    rewrite (dec_writev_full k) by (unfold k; lia). reflexivity.
  - intros mo1 <-. cbn [fst snd]. unfold k. rewrite Z.eqb_refl. apply ex_ret. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stdio_write_det : forall fd buf sbytes (s : St) mo,
  zlength buf + zlength sbytes <= WRITE_MAX ->
  det (stdio_write fd buf sbytes s) mo (Wz fd (buf ++ sbytes)) (tt, s) (eq mo).
Proof.
  intros fd buf sb s mo Hm. unfold stdio_write.
  destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength sb)) as [H|H]; [lia|].
  assert (E : concat (match buf with [] => [sb] | _ => [buf; sb] end) = buf ++ sb).
  { destruct buf; cbn; rewrite app_nil_r; reflexivity. }
  rewrite <- E. apply write_loop_det.
  - destruct buf; cbn; lia.
  - unfold iov_total. rewrite E, zlength_app. pose proof (zlength_nonneg buf). pose proof (zlength_nonneg sb). lia.
  - unfold iov_total. rewrite E, zlength_app. unfold WRITE_MAX in Hm. lia.
Qed.

Lemma stdio_write_ex : forall fd buf sbytes (s : St) mo,
  zlength buf + zlength sbytes <= WRITE_MAX ->
  ex (stdio_write fd buf sbytes s) mo (Wz fd (buf ++ sbytes)) (tt, s) (eq mo).
Proof.
  intros fd buf sb s mo Hm. unfold stdio_write.
  destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength sb)) as [H|H]; [lia|].
  assert (E : concat (match buf with [] => [sb] | _ => [buf; sb] end) = buf ++ sb).
  { destruct buf; cbn; rewrite app_nil_r; reflexivity. }
  rewrite <- E. apply write_loop_ex.
  unfold iov_total. rewrite E, zlength_app. unfold WRITE_MAX in Hm. lia.
Qed.

End StdioWrite.

(* [comment removed for export] *)
Section Stderr.
Context {St : Type}.

Lemma stdio_write_run1 : forall fd buf sbytes (s : St) mo,
  zlength buf + zlength sbytes <= WRITE_MAX ->
  run1 (stdio_write fd buf sbytes s) mo (Wz fd (buf ++ sbytes)) (tt, s) (eq mo).
Proof. intros. split; [apply stdio_write_det|apply stdio_write_ex]; assumption. Qed.

(* [comment removed for export] *)
Fixpoint sp_run (buf : list Z) (ps : list (list Z)) : list Z * list Z :=
  match ps with
  | [] => ([], buf)
  | p :: ps' => if INTERNAL_BUFSIZ - zlength buf <? zlength p
                then (buf ++ p ++ fst (sp_run [] ps'), snd (sp_run [] ps'))
                else sp_run (buf ++ p) ps'
  end.

Lemma sp_run_concat : forall ps buf, fst (sp_run buf ps) ++ snd (sp_run buf ps) = buf ++ concat ps.
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [sp_run concat].
  - cbn. rewrite app_nil_r. reflexivity.
  - destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); cbn [fst snd].
    + rewrite <- !app_assoc. rewrite (IH []). reflexivity.
    + rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

Lemma sp_run_small : forall ps buf, zlength buf <= INTERNAL_BUFSIZ -> zlength (snd (sp_run buf ps)) <= INTERNAL_BUFSIZ.
Proof.
  induction ps as [|p ps IH]; intros buf Hb; cbn [sp_run]; [exact Hb|].
  destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)); cbn [snd].
  - apply IH. unfold INTERNAL_BUFSIZ, zlength. cbn. lia.
  - apply IH. rewrite zlength_app. lia.
Qed.

Definition PIECE_OK (p : list Z) : Prop := zlength p <= WRITE_MAX - INTERNAL_BUFSIZ.

Lemma stderr_pieces_run1 : forall ps buf (s : St) mo,
  zlength buf <= INTERNAL_BUFSIZ -> Forall PIECE_OK ps ->
  run1 (stderr_pieces buf ps s) mo (Wz 2 (fst (sp_run buf ps))) (snd (sp_run buf ps), s) (eq mo).
Proof.
  induction ps as [|p ps IH]; intros buf s mo Hb HF; cbn [stderr_pieces sp_run].
  - apply run1_ret. reflexivity.
  - inversion HF as [|p' ps' Hp HF']; subst.
    destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)) as [H|H]; cbn [fst snd].
    + unfold mbind.
      replace (Wz 2 (buf ++ p ++ fst (sp_run [] ps))) with (Wz 2 (buf ++ p) ++ Wz 2 (fst (sp_run [] ps)))
        by (rewrite <- Wz_app, app_assoc; reflexivity).
      eapply run1_ebind.
      * apply stdio_write_run1. unfold PIECE_OK in Hp. lia.
      * intros mo1 <-. cbn [fst snd]. apply IH; [|exact HF']. unfold INTERNAL_BUFSIZ, zlength. cbn. lia.
    + apply IH; [|exact HF']. rewrite zlength_app. lia.
Qed.

Lemma stderr_fprintf_run1 : forall ps (s : St) mo, Forall PIECE_OK ps ->
  run1 (stderr_fprintf ps s) mo (Wz 2 (concat ps)) (tt, s) (eq mo).
Proof.
  intros ps s mo HF. unfold stderr_fprintf, mbind.
  replace (Wz 2 (concat ps)) with (Wz 2 (fst (sp_run [] ps)) ++ Wz 2 (snd (sp_run [] ps) ++ [])).
  2:{ rewrite app_nil_r, <- Wz_app, sp_run_concat. reflexivity. }
  eapply run1_ebind.
  - apply stderr_pieces_run1; [|exact HF]. unfold INTERNAL_BUFSIZ, zlength. cbn. lia.
  - intros mo1 <-. cbn [fst snd]. apply stdio_write_run1.
    pose proof (sp_run_small ps [] ltac:(unfold INTERNAL_BUFSIZ, zlength; cbn; lia)) as Hs.
    unfold INTERNAL_BUFSIZ, WRITE_MAX in *. unfold zlength at 2. cbn. lia.
Qed.

Lemma stderr_fwrite_run1 : forall sb (s : St) mo, zlength sb <= WRITE_MAX ->
  run1 (stderr_fwrite sb s) mo (Wz 2 sb) (tt, s) (eq mo).
Proof.
  intros sb s mo Hl. unfold stderr_fwrite. destruct (Z.ltb_spec 0 (zlength sb)) as [H|H].
  - apply (stdio_write_run1 2 [] sb s mo). unfold zlength at 1. cbn. lia.
  - assert (sb = []) as -> by (destruct sb; [reflexivity|unfold zlength in H; cbn in H; lia]).
    apply run1_ret. reflexivity.
Qed.

(* [comment removed for export] *)
Definition diag_bytes (d : diag_msg) : list Z :=
  match d with
  | DUsage argv0 => concat (pieces_usage argv0)
  | DCannotOpen p => concat (pieces_cannot_open p)
  | DReadError p => concat (pieces_read_error p)
  | DOom => concat pieces_oom
  | DTooBig => concat pieces_too_big
  | DShortHdr => concat pieces_short_hdr
  | DCfgOverrun => concat pieces_cfg_overrun
  end.
Definition diag_ok (d : diag_msg) : Prop :=
  match d with
  | DUsage a | DCannotOpen a | DReadError a => PIECE_OK a
  | _ => True
  end.

Ltac lit_ok := unfold PIECE_OK, WRITE_MAX, INTERNAL_BUFSIZ; vm_compute; discriminate.

Lemma s_diag_run1 : forall d (s : St) mo, diag_ok d ->
  run1 (s_diag d s) mo (Wz 2 (diag_bytes d)) (tt, s) (eq mo).
Proof.
  intros d s mo Hd. destruct d as [a|a|a| | | |]; cbn [s_diag diag_bytes diag_ok] in *.
  - apply stderr_fprintf_run1. unfold pieces_usage. repeat constructor; try exact Hd; lit_ok.
  - apply stderr_fprintf_run1. unfold pieces_cannot_open. repeat constructor; try exact Hd; lit_ok.
  - apply stderr_fprintf_run1. unfold pieces_read_error. repeat constructor; try exact Hd; lit_ok.
  - apply stderr_fwrite_run1. unfold WRITE_MAX. vm_compute. discriminate.
  - apply stderr_fprintf_run1. unfold pieces_too_big. repeat constructor; lit_ok.
  - apply stderr_fwrite_run1. unfold WRITE_MAX. vm_compute. discriminate.
  - apply stderr_fwrite_run1. unfold WRITE_MAX. vm_compute. discriminate.
Qed.

End Stderr.
