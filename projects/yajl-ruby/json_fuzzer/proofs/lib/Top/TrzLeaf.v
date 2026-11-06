(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz TrzNodes TrzStdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Leaf.
Context {St : Type}.

(* [comment removed for export] *)
Lemma leaf_mbind_inv : forall {A B} (m : @M St A) (g : A -> @M St B) (s : St) mo r mo'',
  leaf (mbind m g s) mo r mo'' ->
  exists a mo', leaf (m s) mo a mo' /\
    match a with
    | Unr => r = Unr /\ mo'' = mo'
    | Ok p => leaf (g (fst p) (snd p)) mo' r mo''
    end.
Proof.
  intros A B m g s mo r mo'' H. unfold mbind, ebind in H. apply leaf_bind in H as (a & mo' & L1 & L2).
  exists a, mo'. split; [exact L1|]. destruct a as [|p]; [| exact L2].
  apply leaf_ret_inv in L2 as [-> ->]. auto.
Qed.

Lemma leaf_mret_inv : forall {A} (a : A) (s : St) mo r mo', leaf (mret a s) mo r mo' -> r = Ok (a, s) /\ mo' = mo.
Proof. intros A a s mo r mo' H. unfold mret in H. apply leaf_ret_inv in H. exact H. Qed.
Lemma leaf_munr_inv : forall {A} (s : St) mo (r : exc (A * St)) mo', leaf (munr s) mo r mo' -> r = Unr /\ mo' = mo.
Proof. intros A s mo r mo' H. unfold munr in H. apply leaf_ret_inv in H. exact H. Qed.
Lemma leaf_upd_inv : forall (f : St -> St) (s : St) mo r mo', leaf (mupd f s) mo r mo' -> r = Ok (tt, f s) /\ mo' = mo.
Proof. intros f s mo r mo' H. unfold mupd in H. apply leaf_ret_inv in H. exact H. Qed.
Lemma leaf_get_inv : forall (s : St) mo r mo', leaf (mget s) mo r mo' -> r = Ok (s, s) /\ mo' = mo.
Proof. intros s mo r mo' H. unfold mget in H. apply leaf_ret_inv in H. exact H. Qed.

Ltac leaf_bind H a mo1 L1 :=
  apply leaf_mbind_inv in H; destruct H as (a & mo1 & L1 & H).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma leaf_writev_loop_ok : forall fuel fd iovs (st : St) mo r mo',
  (fd = 1 \/ fd = 2) -> (length iovs <= 2)%nat ->
  (length (zconcat iovs) <= fuel)%nat -> zlength (zconcat iovs) < 2^64 ->
  leaf (writev_loop fuel fd iovs st) mo r mo' -> r = Ok (tt, st) /\ mo' = mo.
Proof.
  induction fuel as [|fuel IH]; intros fd iovs st mo r mo' Hfd Hlen Hfuel H64 L.
  - assert (E : zconcat iovs = []) by (destruct (zconcat iovs); [reflexivity | cbn in Hfuel; lia]).
    cbn [writev_loop] in L. leaf_bind L a mo1 L1.
    apply leaf_msys in L1 as (rsp & evs & Hst & ->).
    cbn [nstep] in Hst. rewrite zconcat_concat_to_bytes, E in Hst.
    destruct Hst as [-> [(_ & -> & ->) | (k & Hk & _)]]; [| cbn in Hk; lia].
    unfold dec_writev in L. rewrite E in L. change (zlength (@nil Z)) with 0 in L.
    rewrite dec_count_full in L by lia. cbn [fst snd Z.eqb] in L. apply leaf_mret_inv in L. exact L.
  - change (writev_loop (S fuel) fd iovs st) with
      ((k <- msys (NWritev fd (map to_bytes iovs)) (dec_writev (zlength (zconcat iovs))) ;;
        if k =? zlength (zconcat iovs) then mret tt else writev_loop fuel fd (advance_iovs iovs k)) st) in L.
    leaf_bind L a mo1 L1.
    apply leaf_msys in L1 as (rsp & evs & Hst & ->).
    cbn [nstep] in Hst. rewrite zconcat_concat_to_bytes in Hst.
    destruct (zconcat iovs) as [|b0 bs'] eqn:EZ.
    + destruct Hst as [-> [(_ & -> & ->) | (k & Hk & _)]]; [| cbn in Hk; lia].
      unfold dec_writev in L. change (zlength (@nil Z)) with 0 in L.
      rewrite dec_count_full in L by lia. cbn [fst snd Z.eqb] in L. apply leaf_mret_inv in L. exact L.
    + destruct Hst as [-> [(Hb & _ & _) | (k & Hk & -> & ->)]]; [discriminate|].
      unfold to_bytes in Hk. rewrite length_map in Hk.
      assert (DC : dec_writev (zlength (b0 :: bs')) (eff0 (Z_to_bv 64 k)) = Some k).
      { unfold dec_writev, dec_count, eff0. unfold zlength in *. cbn [length] in *. rewrite unsigned_lit by lia.
        replace ((1 <=? k) && (k <=? Z.of_nat (S (length bs')))) with true
          by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
        rewrite orb_true_r. reflexivity. }
      rewrite DC in L. cbn [fst snd] in L.
      destruct (Z.eqb_spec k (zlength (b0 :: bs'))) as [-> | NE].
      * apply leaf_mret_inv in L. exact L.
      * assert (HkR : 0 <= k <= zlength (zconcat iovs)) by (rewrite EZ; unfold zlength; cbn [length] in *; lia).
        pose proof (zlength_zconcat_advance iovs k HkR Hlen) as EA.
        apply (f_equal (@length byte)) in EA. rewrite length_skipn in EA. unfold to_bytes in EA. rewrite !length_map in EA.
        rewrite EZ in EA. cbn [length] in EA.
        apply (IH fd (advance_iovs iovs k) st mo r mo' Hfd).
        -- pose proof (length_advance_iovs iovs k). lia.
        -- cbn [length] in Hfuel. unfold zlength in NE. cbn [length] in *. lia.
        -- unfold zlength. unfold zlength in H64. cbn [length] in H64. lia.
        -- exact L.
Qed.

Lemma leaf_stdio_writev_ok : forall fd buf s (st : St) mo r mo',
  (fd = 1 \/ fd = 2) -> zlength buf + zlength s <= WRITEV_MAX ->
  leaf (stdio_writev fd buf s st) mo r mo' -> r = Ok (tt, st) /\ mo' = mo.
Proof.
  intros fd buf s st mo r mo' Hfd Hlen L. unfold stdio_writev in L.
  destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength s)); [lia|].
  assert (EI : zconcat (iovs_init buf s) = buf ++ s) by (unfold iovs_init; destruct buf; cbn; rewrite ?app_nil_r; reflexivity).
  eapply (leaf_writev_loop_ok _ fd (iovs_init buf s) st); [exact Hfd | unfold iovs_init; destruct buf; cbn; lia | | | exact L].
  - rewrite EI, length_app. lia.
  - rewrite EI. unfold WRITEV_MAX, zlength in *. rewrite length_app. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma leaf_stderr_fwrite_ok : forall s (st : St) mo r mo',
  zlength s <= WRITEV_MAX ->
  leaf (stderr_fwrite s st) mo r mo' -> r = Ok (tt, st) /\ mo' = mo.
Proof.
  intros s st mo r mo' Hlen L. unfold stderr_fwrite in L.
  destruct (Z.ltb_spec 0 (zlength s)).
  - eapply (leaf_stdio_writev_ok 2 [] s st); [right; reflexivity | change (zlength (@nil Z)) with 0; lia | exact L].
  - apply leaf_mret_inv in L. exact L.
Qed.

Lemma leaf_stderr_pieces_ok : forall ps buf (st : St) mo r mo',
  zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  leaf (stderr_pieces buf ps st) mo r mo' -> r = Ok (sp_final buf ps, st) /\ mo' = mo.
Proof.
  induction ps as [|p ps IH]; intros buf st mo r mo' Hb Hps L; cbn [stderr_pieces sp_final] in L |- *.
  - apply leaf_mret_inv in L. exact L.
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)).
    + leaf_bind L a mo1 L1.
      apply leaf_stdio_writev_ok in L1 as [-> ->]; [| right; reflexivity | lia].
      cbn [fst snd] in L. apply (IH [] st mo r mo'); [change (zlength (@nil Z)) with 0; unfold INTERNAL_BUFSIZ; lia | exact Hps | exact L].
    + apply (IH (buf ++ p) st mo r mo'); [unfold zlength in *; rewrite length_app; lia | exact Hps | exact L].
Qed.

Lemma leaf_stderr_fprintf_ok : forall ps (st : St) mo r mo',
  Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  leaf (stderr_fprintf ps st) mo r mo' -> r = Ok (tt, st) /\ mo' = mo.
Proof.
  intros ps st mo r mo' Hps L. unfold stderr_fprintf in L. leaf_bind L a mo1 L1.
  apply leaf_stderr_pieces_ok in L1 as [-> ->]; [| change (zlength (@nil Z)) with 0; unfold INTERNAL_BUFSIZ; lia | exact Hps].
  cbn [fst snd] in L.
  eapply (leaf_stdio_writev_ok 2 (sp_final [] ps) [] st); [right; reflexivity | | exact L].
  pose proof (sp_final_bound ps [] ltac:(change (zlength (@nil Z)) with 0; unfold INTERNAL_BUFSIZ; lia)).
  change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ, WRITEV_MAX in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis GS : forall so x, get_so (set_so so x) = so.
Hypothesis SS : forall so so' x, set_so so' (set_so so x) = set_so so' x.

Lemma leaf_rdso_bind : forall {B} (f : stdout_st -> @M St B) (s : St) mo r mo',
  leaf (mbind (rd_so get_so) f s) mo r mo' -> leaf (f (get_so s) s) mo r mo'.
Proof.
  intros B f s mo r mo' L. unfold rd_so in L. leaf_bind L a mo1 L1.
  leaf_bind L1 b mo2 L2. apply leaf_get_inv in L2 as [-> ->]. cbn [fst snd] in L1. apply leaf_mret_inv in L1 as [-> ->]. exact L.
Qed.

Lemma leaf_stdout_stdio_write_ok : forall s (st : St) mo r mo',
  zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX ->
  leaf (stdout_stdio_write get_so set_so s st) mo r mo' ->
  r = Ok (tt, set_so (mkStdout true [] (so_lbf_nl (get_so st)) (so_first (get_so st))) st) /\ mo' = mo.
Proof.
  intros s st mo r mo' Hlen L. unfold stdout_stdio_write in L. apply leaf_rdso_bind in L.
  leaf_bind L a mo1 L1. apply leaf_stdio_writev_ok in L1 as [-> ->]; [| left; reflexivity | exact Hlen].
  cbn [fst snd] in L. unfold upd_so in L. apply leaf_upd_inv in L. exact L.
Qed.

Lemma leaf_stdout_writefn_ok : forall s (st : St) mo r mo',
  zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX ->
  leaf (stdout_writefn get_so set_so s st) mo r mo' ->
  r = Ok (tt, set_so (snd (writefn_pure (get_so st) s)) st) /\ mo' = mo.
Proof.
  intros s st mo r mo' Hlen L. unfold stdout_writefn, writefn_pure in L |- *. apply leaf_rdso_bind in L.
  leaf_bind L a mo1 L1.
  destruct (so_first (get_so st)) eqn:EF.
  - leaf_bind L1 b mo2 L2. unfold upd_so in L2. apply leaf_upd_inv in L2 as [-> ->]. cbn [fst snd] in L1.
    leaf_bind L1 c mo3 L3. apply leaf_msys in L3 as (rsp & evs & Hst & ->).
    destruct (nstep_dec_ioctl _ _ _ _ _ _ Hst) as (D & -> & _). rewrite D in L1. cbn [fst snd] in L1.
    unfold upd_so in L1. apply leaf_upd_inv in L1 as [-> ->]. cbn [fst snd] in L.
    apply leaf_stdout_stdio_write_ok in L as [-> ->]; [| rewrite !GS; cbn; exact Hlen].
    rewrite !GS, !SS. cbn. unfold ioctl_pure. rewrite EF. cbn. auto.
  - apply leaf_mret_inv in L1 as [-> ->]. cbn [fst snd] in L.
    apply leaf_stdout_stdio_write_ok in L as [-> ->]; [| exact Hlen]. unfold ioctl_pure. rewrite EF. cbn. rewrite EF. auto.
Qed.

Lemma leaf_stdout_fwritex_ok : forall s (st : St) mo r mo',
  zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> zlength s + STDOUT_BUFSIZ <= WRITEV_MAX ->
  leaf (stdout_fwritex get_so set_so s st) mo r mo' ->
  r = Ok (tt, set_so (snd (fwritex_pure (get_so st) s)) st) /\ mo' = mo.
Proof.
  intros s st mo r mo' Hb Hs L. unfold stdout_fwritex, fwritex_pure in L |- *.
  leaf_bind L a mo1 L1. unfold stdout_towrite, upd_so in L1. apply leaf_upd_inv in L1 as [-> ->]. cbn [fst snd] in L.
  apply leaf_rdso_bind in L. rewrite !GS in L.
  assert (Hb' : zlength (so_buf (towrite_pure (get_so st))) <= STDOUT_BUFSIZ).
  { unfold towrite_pure. destruct (so_active (get_so st)); [exact Hb | unfold zlength, STDOUT_BUFSIZ; cbn; lia]. }
  change (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |})
    with (towrite_pure (get_so st)) in L.
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength (so_buf (towrite_pure (get_so st)))) (zlength s)).
  - apply leaf_stdout_writefn_ok in L as [-> ->]; [| rewrite GS; lia]. rewrite GS, SS. auto.
  - destruct (so_lbf_nl (towrite_pure (get_so st))) eqn:EL.
    + leaf_bind L b mo2 L2.
      pose proof (after_last_nl_range s) as HR.
      destruct (Z.ltb_spec 0 (after_last_nl s)).
      * apply leaf_stdout_writefn_ok in L2 as [-> ->].
        2:{ rewrite GS. unfold zlength in *. rewrite length_firstn. lia. }
        cbn [fst snd] in L. unfold upd_so in L. apply leaf_upd_inv in L as [-> ->]. rewrite !GS, !SS.
        cbn [fst snd writefn_pure]. rewrite ?EL. auto.
      * apply leaf_mret_inv in L2 as [-> ->]. cbn [fst snd] in L. unfold upd_so in L. apply leaf_upd_inv in L as [-> ->].
        rewrite !GS, !SS. cbn [fst snd]. rewrite ?EL. auto.
    + unfold upd_so in L. apply leaf_upd_inv in L as [-> ->]. rewrite !GS, !SS. cbn [fst snd]. rewrite ?EL. auto.
Qed.

Lemma leaf_out_pieces_ok : forall ps (st : St) mo r mo',
  zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  (forall x, set_so (get_so x) x = x) ->
  leaf (out_pieces get_so set_so ps st) mo r mo' ->
  r = Ok (tt, set_so (snd (pieces_pure (get_so st) ps)) st) /\ mo' = mo.
Proof.
  induction ps as [|p ps IH]; intros st mo r mo' Hb Hps SG L; cbn [out_pieces pieces_pure] in L |- *.
  - apply leaf_mret_inv in L as [-> ->]. cbn. rewrite SG. auto.
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    leaf_bind L a mo1 L1. apply leaf_stdout_fwritex_ok in L1 as [-> ->]; [| exact Hb | exact Hp]. cbn [fst snd] in L.
    apply IH in L as [-> ->]; [| rewrite GS; apply fwritex_pure_buf_bound; exact Hb | exact Hps | exact SG].
    rewrite GS, SS. auto.
Qed.

Lemma leaf_stdout_vprintf_ok : forall ps (st : St) mo r mo',
  zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  (forall x, set_so (get_so x) x = x) ->
  leaf (stdout_vprintf get_so set_so ps st) mo r mo' ->
  r = Ok (tt, set_so (snd (vprintf_pure (get_so st) ps)) st) /\ mo' = mo.
Proof.
  intros ps st mo r mo' Hb Hps SG L. unfold stdout_vprintf, vprintf_pure in L |- *.
  leaf_bind L a mo1 L1. unfold stdout_towrite, upd_so in L1. apply leaf_upd_inv in L1 as [-> ->]. cbn [fst snd] in L.
  change (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |})
    with (towrite_pure (get_so st)) in L.
  apply leaf_out_pieces_ok in L as [-> ->]; [| rewrite GS | exact Hps | exact SG].
  - rewrite GS, SS. auto.
  - unfold towrite_pure. destruct (so_active (get_so st)); [exact Hb | unfold zlength, STDOUT_BUFSIZ; cbn; lia].
Qed.

Lemma leaf_stdout_exit_flush_ok : forall (st : St) mo r mo',
  zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ ->
  (forall x, set_so (get_so x) x = x) ->
  leaf (stdout_exit_flush get_so set_so st) mo r mo' ->
  r = Ok (tt, set_so (snd (exit_flush_pure (get_so st))) st) /\ mo' = mo.
Proof.
  intros st mo r mo' Hb SG L. unfold stdout_exit_flush, exit_flush_pure in L |- *. apply leaf_rdso_bind in L.
  destruct (Z.ltb_spec 0 (zlength (so_buf (get_so st)))).
  - apply leaf_stdout_writefn_ok in L as [-> ->]; [| change (zlength (@nil Z)) with 0; unfold STDOUT_BUFSIZ, WRITEV_MAX in *; lia]. auto.
  - apply leaf_mret_inv in L as [-> ->]. cbn. rewrite SG. auto.
Qed.
End Leaf.
End RC__1.
