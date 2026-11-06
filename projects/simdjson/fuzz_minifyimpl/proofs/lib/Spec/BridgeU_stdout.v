(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver HarnessM ProgA ProgZ BridgeU_base BridgeU_stdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma mbind_pure : forall {St A B} (m : Monad.M St A) (f : A -> Monad.M St B) s a s1,
  m s = Ret (Ok (a, s1)) -> mbind m f s = f a s1.
Proof. intros St A B m f s a s1 H. unfold mbind. rewrite H. reflexivity. Qed.

Lemma run1_pure : forall {X} (t : itree node (exc X)) mo x, t = Ret (Ok x) -> run1 t mo [] x (eq mo).
Proof. intros X t mo x ->. apply run1_ret. reflexivity. Qed.

Lemma run1_mbind : forall {St A B} (m : Monad.M St A) (f : A -> Monad.M St B) s mo E1 a s1 R1 E2 b s2 (R2 : Model -> Prop),
  run1 (m s) mo E1 (a, s1) R1 -> (forall mo1, R1 mo1 -> run1 (f a s1) mo1 E2 (b, s2) R2) ->
  run1 (mbind m f s) mo (E1 ++ E2) (b, s2) R2.
Proof. intros. unfold mbind. eapply run1_ebind; [eassumption|]. intros mo1 H1. cbn [fst snd]. auto. Qed.

Notation zfwritex := (stdout_fwritex z_so z_set_so).
Notation zwritefn := (stdout_writefn z_so z_set_so).

(* [comment removed for export] *)
Lemma fwritex_append_full : forall buf first p cl, zlength buf + zlength p <= STDOUT_BUFSIZ ->
  zfwritex p (mkZ (mkStdout true buf false first) cl) = Ret (Ok (tt, mkZ (mkStdout true (buf ++ p) false first) cl)).
Proof.
  intros buf first p cl H. unfold stdout_fwritex, stdout_towrite, upd_so, rd_so, mbind, mupd, mget, mret. cbn.
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength p)) as [H1|H1]; [lia|]. reflexivity.
Qed.

Lemma fwritex_append_lbf : forall buf first p cl, zlength buf + zlength p <= STDOUT_BUFSIZ -> after_last_nl p = 0 ->
  zfwritex p (mkZ (mkStdout true buf true first) cl) = Ret (Ok (tt, mkZ (mkStdout true (buf ++ p) true first) cl)).
Proof.
  intros buf first p cl H Hnl. unfold stdout_fwritex, stdout_towrite, upd_so, rd_so, mbind, mupd, mget, mret. cbn.
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength p)) as [H1|H1]; [lia|]. rewrite Hnl. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ioctl_run1 : forall (s : ZSt) mo,
  run1 (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl s) mo [] (SErr ENOTTY, s) (eq mo).
Proof.
  intros s mo. unfold msys. apply run1_enode.
  - intros rsp mo1 evs H. apply nstep_dec_ioctl in H as (Hd & -> & ->). rewrite Hd. auto.
  - exists (efferr ENOTTY). cbn. auto.
  - intros code mo' H. exact H.
Qed.

(* [comment removed for export] *)
Ltac pure_step :=
  lazymatch goal with
  | |- run1 (mbind _ _ _) _ ?E _ _ =>
      change E with (@nil event ++ E); eapply run1_mbind; [apply run1_pure; cbn; reflexivity | intros ? <-];
      cbn [fst snd z_so z_cl z_set_so z_set_cl so_first so_active so_buf so_lbf_nl]
  end.

(* [comment removed for export] *)
Lemma writefn_first : forall a buf lbf sb cl mo, zlength buf + zlength sb <= WRITE_MAX ->
  run1 (zwritefn sb (mkZ (mkStdout a buf lbf true) cl)) mo (Wz 1 (buf ++ sb)) (tt, mkZ (mkStdout true [] false false) cl) (eq mo).
Proof.
  intros a buf lbf sb cl mo H. unfold stdout_writefn.
  pure_step. cbn [so_first z_so].
  change (Wz 1 (buf ++ sb)) with ([] ++ Wz 1 (buf ++ sb)).
  eapply run1_mbind.
  - (* [comment removed for export] *)
    pure_step. change (@nil event) with (@nil event ++ []).
    eapply run1_mbind; [apply ioctl_run1|]. intros mo1 <-.
    apply run1_pure. reflexivity.
  - intros mo1 <-. unfold stdout_stdio_write.
    pure_step. rewrite <- (app_nil_r (Wz 1 (buf ++ sb))).
    eapply run1_mbind; [apply stdio_write_run1; exact H|]. intros mo1 <-.
    apply run1_pure. reflexivity.
Qed.

Lemma writefn_later : forall a buf lbf sb cl mo, zlength buf + zlength sb <= WRITE_MAX ->
  run1 (zwritefn sb (mkZ (mkStdout a buf lbf false) cl)) mo (Wz 1 (buf ++ sb)) (tt, mkZ (mkStdout true [] lbf false) cl) (eq mo).
Proof.
  intros a buf lbf sb cl mo H. unfold stdout_writefn.
  pure_step. cbn [so_first z_so].
  pure_step. unfold stdout_stdio_write.
  pure_step. rewrite <- (app_nil_r (Wz 1 (buf ++ sb))).
  eapply run1_mbind; [apply stdio_write_run1; exact H|]. intros mo1 <-.
  apply run1_pure. reflexivity.
Qed.

(* [comment removed for export] *)
Arguments stdout_writefn : simpl never.
Arguments stdio_write : simpl never.
Arguments stdout_fwritex : simpl never.
Arguments out_pieces : simpl never.
Arguments Wz : simpl never.
Arguments mbind : simpl never.
#[local] Hint Unfold stdout_fwritex stdout_towrite upd_so rd_so mbind mupd mget mret : zpure.
Lemma z_set_so_eq : forall v s, z_set_so v s = mkZ v (z_cl s). Proof. reflexivity. Qed.
Lemma z_set_cl_eq : forall v s, z_set_cl v s = mkZ (z_so s) v. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac pstep :=
  lazymatch goal with
  | |- run1 (mbind _ _ _) _ ?E _ _ =>
      change E with (@nil event ++ E); eapply run1_mbind;
      [apply run1_pure; autounfold with zpure; cbn; reflexivity
      | intros ? <-; rewrite ?z_set_so_eq, ?z_set_cl_eq; cbn; repeat change (Z.to_nat 0) with O; cbn [skipn firstn app]]
  end.

Lemma fwritex_nl_first : forall buf cl mo, zlength buf + 1 <= STDOUT_BUFSIZ ->
  run1 (zfwritex [10] (mkZ (mkStdout true buf true true) cl)) mo (Wz 1 (buf ++ [10])) (tt, mkZ (mkStdout true [] false false) cl) (eq mo).
Proof.
  intros buf cl mo H. unfold stdout_fwritex. pstep. pstep.
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength [10])) as [H1|H1]; [unfold zlength in H1 at 2; cbn in H1; lia|].
  change (after_last_nl [10]) with 1. cbv zeta. change (0 <? 1) with true. cbv iota.
  change (firstn (Z.to_nat 1) [10]) with [10]. change (skipn (Z.to_nat 1) [10]) with (@nil Z).
  rewrite <- (app_nil_r (Wz 1 (buf ++ [10]))).
  eapply run1_mbind.
  - apply writefn_first. unfold STDOUT_BUFSIZ, WRITE_MAX in *. unfold zlength at 2. cbn. lia.
  - intros mo1 <-. apply run1_pure. reflexivity.
Qed.

Lemma emit0_first : forall cl mo,
  run1 (s_emit z_so z_set_so 0 (mkZ stdout_init cl)) mo (Wz 1 [48;10]) (tt, mkZ (mkStdout true [] false false) cl) (eq mo).
Proof.
  intros cl mo. unfold s_emit, stdout_vprintf. change (pieces_pct_d 0) with [ @nil Z; []; [48]; []; [10] ].
  unfold stdout_init. pstep. unfold out_pieces; fold (@out_pieces ZSt z_so z_set_so).
  pstep. pstep. pstep. pstep.
  rewrite <- (app_nil_r (Wz 1 [48;10])).
  eapply run1_mbind.
  - apply (fwritex_nl_first [48] cl mo). unfold STDOUT_BUFSIZ, zlength. cbn. lia.
  - intros mo1 <-. apply run1_pure. reflexivity.
Qed.

Ltac zl := rewrite ?zlength_app; unfold zlength, STDOUT_BUFSIZ, WRITE_MAX in *; cbn [length] in *; lia.

(* [comment removed for export] *)
Ltac pstep_by L :=
  lazymatch goal with
  | |- run1 (mbind _ _ _) _ ?E _ _ =>
      change E with (@nil event ++ E); eapply run1_mbind; [apply run1_pure; apply L | intros ? <-]
  end.

Lemma emit0_later : forall buf cl mo, zlength buf + 2 <= STDOUT_BUFSIZ ->
  run1 (s_emit z_so z_set_so 0 (mkZ (mkStdout true buf false false) cl)) mo [] (tt, mkZ (mkStdout true (buf ++ [48;10]) false false) cl) (eq mo).
Proof.
  intros buf cl mo H. unfold s_emit, stdout_vprintf. change (pieces_pct_d 0) with [ @nil Z; []; [48]; []; [10] ].
  pstep. unfold out_pieces; fold (@out_pieces ZSt z_so z_set_so).
  pstep_by (fwritex_append_full buf false [] cl); [zl|].
  pstep_by (fwritex_append_full (buf ++ []) false [] cl); [zl|].
  pstep_by (fwritex_append_full ((buf ++ []) ++ []) false [48] cl); [zl|].
  pstep_by (fwritex_append_full (((buf ++ []) ++ []) ++ [48]) false [] cl); [zl|].
  pstep_by (fwritex_append_full ((((buf ++ []) ++ []) ++ [48]) ++ []) false [10] cl); [zl|].
  apply run1_pure. rewrite !app_nil_r, <- app_assoc. reflexivity.
Qed.

Notation zflush := (stdout_exit_flush z_so z_set_so).

Lemma flush_init : forall cl mo, run1 (zflush (mkZ stdout_init cl)) mo [] (tt, mkZ stdout_init cl) (eq mo).
Proof. intros. apply run1_pure. reflexivity. Qed.

Lemma flush_buf : forall buf cl mo, zlength buf <= STDOUT_BUFSIZ ->
  run1 (zflush (mkZ (mkStdout true buf false false) cl)) mo (Wz 1 buf) (tt, mkZ (mkStdout true [] false false) cl) (eq mo).
Proof.
  intros buf cl mo H. unfold stdout_exit_flush. pstep.
  destruct (Z.ltb_spec 0 (zlength buf)) as [H1|H1].
  - rewrite <- (app_nil_r buf) at 2. apply writefn_later. zl.
  - assert (buf = []) as -> by (destruct buf; [reflexivity|unfold zlength in H1; cbn in H1; lia]).
    apply run1_pure. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fuzz_oneZ_pure : forall payload so cl,
  fuzz_oneA AAllocZ payload (mkZ so cl) = Ret (Ok (0, mkZ so (Some tt))).
Proof.
  intros payload so cl. unfold fuzz_oneA, HarnessM.fuzz_one, HarnessM.minify_call, HarnessM.ERRMSG_LEN.
  destruct (Z.of_nat (length payload) =? 0); destruct (unclosed payload); destruct (54 <=? Z.of_nat (length payload)); destruct cl as [[]|]; reflexivity.
Qed.

Lemma client_exitZ_pure : forall so cl, exists cl', client_exitA AAllocZ (mkZ so cl) = Ret (Ok (tt, mkZ so cl')).
Proof. intros so [[]|]; eexists; reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint zlines (k : nat) : list Z := match k with O => [] | S k' => 48 :: 10 :: zlines k' end.
Lemma zlength_zlines : forall k, zlength (zlines k) = 2 * Z.of_nat k.
Proof. induction k as [|k IH]; [reflexivity|]. unfold zlength in *. cbn [zlines length]. lia. Qed.
Lemma zlines_snoc : forall k, zlines k ++ [48; 10] = zlines (S k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn [zlines app]. rewrite IH. reflexivity. Qed.

Notation zrun_calls := (Adapter.run_calls (fuzz_oneA AAllocZ) (io_emit (ioA AAllocZ))).

Lemma run_calls_later : forall k j payload mo, 2 * Z.of_nat (j + k) <= STDOUT_BUFSIZ ->
  run1 (zrun_calls k payload 0 (mkZ (mkStdout true (zlines j) false false) (Some tt))) mo []
       (0, mkZ (mkStdout true (zlines (j + k)) false false) (Some tt)) (eq mo).
Proof.
  induction k as [|k IH]; intros j payload mo H.
  - cbn [Adapter.run_calls]. rewrite Nat.add_0_r. apply run1_pure. reflexivity.
  - cbn [Adapter.run_calls].
    pstep_by (fuzz_oneZ_pure payload (mkStdout true (zlines j) false false) (Some tt)).
    change (@nil event) with (@nil event ++ []).
    eapply run1_mbind.
    + apply (emit0_later (zlines j) (Some tt) mo). rewrite zlength_zlines. lia.
    + intros mo1 <-. rewrite zlines_snoc. replace (j + S k)%nat with (S j + k)%nat by lia. apply IH. lia.
Qed.

Lemma run_calls_first : forall k payload cl mo, 2 * Z.of_nat k <= STDOUT_BUFSIZ ->
  run1 (zrun_calls (S k) payload 0 (mkZ stdout_init cl)) mo (Wz 1 [48;10])
       (0, mkZ (mkStdout true (zlines k) false false) (Some tt)) (eq mo).
Proof.
  intros k payload cl mo H. cbn [Adapter.run_calls].
  pstep_by (fuzz_oneZ_pure payload stdout_init cl).
  rewrite <- (app_nil_r (Wz 1 [48;10])).
  eapply run1_mbind.
  - apply emit0_first.
  - intros mo1 <-. apply (run_calls_later k 0 payload mo). cbn [Nat.add]. exact H.
Qed.
