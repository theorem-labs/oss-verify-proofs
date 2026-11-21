(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad MSafe Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL ZApiC ZHarnessC ZInstC ZTargetC Target.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section Leak.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.

Definition lown (X : list ptr) : assn St := fun s mo => exists Y, own (Y ++ X) s mo.

Lemma lown_of_own : forall X s mo, own X s mo -> lown X s mo.
Proof. intros X s mo H. exists []. exact H. Qed.

Lemma lown_perm : forall X Y s mo, Permutation X Y -> lown X s mo -> lown Y s mo.
Proof. intros X Y s mo HP [L H]. exists L. eapply Hperm; [|exact H]. apply Permutation_app_head. exact HP. Qed.

Lemma lown_leak : forall L X s mo, lown (L ++ X) s mo -> lown X s mo.
Proof. intros L X s mo [Y H]. exists (Y ++ L). rewrite <- app_assoc. exact H. Qed.
Lemma lown_leak1 : forall p X s mo, lown (p :: X) s mo -> lown X s mo.
Proof. intros p X. apply (lown_leak [p]). Qed.

Lemma lown_frame {A} (m : Monad.M St A) :
  (forall X, mspec (own X) m (fun _ => own X)) -> forall X, mspec (lown X) m (fun _ => lown X).
Proof.
  intros H X. unfold lown. apply mspec_exI. intros Y. eapply mspec_post; [apply H|].
  intros a s mo Ho. exists Y. exact Ho.
Qed.

Lemma lown_malloc (raw_malloc : Z -> Monad.M St (option ptr)) :
  (forall X n, 0 <= n -> mspec (own X) (raw_malloc n)
     (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end)) ->
  forall X n, 0 <= n -> mspec (lown X) (raw_malloc n)
     (fun r s mo => match r with Some p => lown (p :: X) s mo /\ n < 2^63 | None => lown X s mo end).
Proof.
  intros H X n Hn. unfold lown. apply mspec_exI. intros Y. eapply mspec_post; [apply (H (Y ++ X) n Hn)|].
  intros [p|] s mo Ho.
  - destruct Ho as [Ho Hlt]. split; [|exact Hlt]. exists Y. eapply Hperm; [|exact Ho]. apply Permutation_middle.
  - exists Y. exact Ho.
Qed.

Lemma lown_free (raw_free : ptr -> Monad.M St unit) :
  (forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X)) ->
  forall X p, mspec (lown (p :: X)) (raw_free p) (fun _ => lown X).
Proof.
  intros H X p. unfold lown. apply mspec_exI. intros Y.
  eapply mspec_conseq; [apply (H (Y ++ X) p)| |].
  - intros s mo Ho. eapply Hperm; [|exact Ho]. apply Permutation_sym, Permutation_middle.
  - intros a s mo Ho. exists Y. exact Ho.
Qed.
End Leak.

Section TargetSafe.
Context {St ptr : Type}.
Variable za : zapiC.
Hypothesis ZOK : zapiC_ok za.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.

Variable own : list ptr -> assn St.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n)
        (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hleak : forall p X s mo, own (p :: X) s mo -> own X s mo.
Hypothesis Herr : forall X bs, zlength bs <= INTERNAL_BUFSIZ ->
  mspec (own X) (stderr_fprintf (St:=St) [bs]) (fun _ => own X).
Hypothesis Hfw : forall X bs, zlength bs <= INTERNAL_BUFSIZ ->
  mspec (own X) (stderr_fwrite (St:=St) bs) (fun _ => own X).
Hypothesis Hout : forall X, mspec (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X).

Hypothesis Herrp : forall X ps, Forall (fun p => zlength p < 2^62) ps ->
  mspec (own X) (stderr_fprintf (St:=St) ps) (fun _ => own X).
Hypothesis Hflush : forall X, mspec (own X) (stdout_exit_flush get_so set_so) (fun _ => own X).

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Let errp : list (list Z) -> Monad.M St unit := Target.err_pieces.
Let cbx : forall A : Type, Monad.M St A := Target.cb_exit get_so set_so.

Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store out_stderr_fw ops Target.ops lib_free_opt].

Definition optl (p : option ptr) : list ptr := match p with Some q => [q] | None => [] end.

Lemma mspec_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (ret ops a) Q.
Proof. intros H. red_ops. apply mspec_ret. exact H. Qed.

Lemma mspec_bind_ops {A B} (m : Monad.M St A) (f : A -> Monad.M St B) P Q1 Q :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (bind ops m f) Q.
Proof. intros H1 H2. red_ops. eapply mspec_bind; eauto. Qed.

Lemma malloc_ops : forall X n, 0 <= n ->
  mspec (own X) (lib_malloc ops n) (fun r => own (optl r ++ X)).
Proof.
  intros X n Hn. red_ops. eapply mspec_post; [apply (Hdm X n Hn)|].
  intros [p|] s mo H; cbn [optl app]; [exact (proj1 H)| exact H].
Qed.

Lemma free_ops : forall X p, mspec (own (optl p ++ X)) (lib_free ops p) (fun _ => own X).
Proof. intros X [p|]; red_ops; cbn [optl app]; [apply Hdf| apply mspec_ret; auto]. Qed.

Lemma zsizes : 0 <= zc_dstate za /\ 0 <= zc_dwin za /\ 0 <= zc_dprev za /\ 0 <= zc_dhead za /\ 0 <= zc_dpend za
               /\ 0 <= zc_isize za /\ 0 <= zc_wsize za.
Proof.
  pose proof (zo_sizesC za ZOK) as H.
  repeat (match type of H with Forall _ (_ :: _) => let a := fresh "Ha" in let b := fresh "Hb" in inversion H as [|? ? a b]; subst; clear H; rename b into H end).
  lia.
Qed.

Lemma cb_exit_mspec {A} : forall X (Q : A -> assn St), mspec (own X) (cbx A) Q.
Proof.
  intros X Q. unfold cbx, Target.cb_exit, Target.cb_exit_prog.
  eapply mspec_bind with (Q1 := fun (e : Empty_set) _ _ => False); [| intros e; destruct e].
  eapply mspec_seq; [apply Hflush|]. intros _.
  apply mspec_sys. intros s mo _. split; [exact I|]. intros rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.

Lemma ck_pieces_short : forall k, Forall (fun p => zlength p < 2^62) (ck_pieces k).
Proof. intros [|]; unfold ck_pieces, pieces_check; repeat constructor; vm_compute; reflexivity. Qed.

Definition blk5 (b : ptr * ptr * ptr * ptr * ptr) : list ptr :=
  let '(sp, wp, pp, hp, bp) := b in [bp; hp; pp; wp; sp].

Lemma deflate_init_mspec : forall X,
  mspec (own X) (deflate_initC ops za)
        (fun r => match r with Some b => own (blk5 b ++ X) | None => own X end).
Proof.
  intros X. destruct zsizes as (H1 & H2 & H3 & H4 & H5 & _). unfold deflate_initC.
  eapply mspec_bind_ops; [apply malloc_ops; exact H1|]. intros [sp|]; cbn [optl app]; [|apply mspec_ret_ops; auto].
  eapply mspec_bind_ops; [apply malloc_ops; exact H2|]. intros w.
  eapply mspec_bind_ops; [apply malloc_ops; exact H3|]. intros p.
  eapply mspec_bind_ops; [apply malloc_ops; exact H4|]. intros h.
  eapply mspec_bind_ops; [apply malloc_ops; exact H5|]. intros b.
  assert (FAIL : mspec (own (optl b ++ optl h ++ optl p ++ optl w ++ sp :: X))
                       (bind ops (lib_free ops b) (fun _ => bind ops (lib_free ops h) (fun _ => bind ops (lib_free ops p) (fun _ =>
                        bind ops (lib_free ops w) (fun _ => bind ops (lib_free ops (Some sp)) (fun _ => ret ops None))))))
                       (fun r => match r with Some b0 => own (blk5 b0 ++ X) | None => own X end)).
  { eapply mspec_bind_ops; [apply free_ops|]. intro.
    eapply mspec_bind_ops; [apply free_ops|]. intro.
    eapply mspec_bind_ops; [apply free_ops|]. intro.
    eapply mspec_bind_ops; [apply free_ops|]. intro.
    eapply mspec_bind_ops; [apply (free_ops X (Some sp))|]. intro. apply mspec_ret_ops. auto. }
  destruct w as [wp|]; [|exact FAIL]. destruct p as [pp|]; [|exact FAIL]. destruct h as [hp|]; [|exact FAIL].
  destruct b as [bp|]; [|exact FAIL].
  apply mspec_ret_ops. intros s mo H. exact H.
Qed.

Lemma deflate_end_mspec : forall X b, mspec (own (blk5 b ++ X)) (deflate_endC ops b) (fun _ => own X).
Proof.
  intros X [[[[sp wp] pp] hp] bp]. unfold deflate_endC, blk5.
  eapply mspec_bind_ops; [apply (free_ops _ (Some bp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some hp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some pp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some wp))|]. intro.
  apply (free_ops X (Some sp)).
Qed.

Lemma compress2_mspec : forall X N src level, 0 <= N <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src -> 0 <= level <= 9 ->
  mspec (own X) (compress2M ops za N src level) (fun r s mo => own X s mo /\ zlength (fst (fst r)) = snd (fst r) /\ snd (fst r) <= N).
Proof.
  intros X N src level HN Hs Hb Hl. unfold compress2M.
  eapply mspec_bind_ops; [apply deflate_init_mspec|]. intros [b|].
  - pose proof (zo_c2C za ZOK N src level HN Hs Hb Hl) as NS.
    destruct (c2_pure za N src level) as [[[out tout] rc]|] eqn:EC; [| exfalso; exact (NS eq_refl)].
    destruct (c2_pure_post za N src level out tout rc EC) as [E1 E2].
    eapply mspec_bind_ops; [apply deflate_end_mspec|]. intro. apply mspec_ret_ops. intros s mo H. cbn [fst snd]. split; [exact H| split; [symmetry; exact E1| exact E2]].
  - apply mspec_ret_ops. intros s mo H. cbn [fst snd]. split; [exact H|]. split; [reflexivity| lia].
Qed.

Lemma u2_loop_mspec : forall dlen src n x w X,
  0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
  u2_reach za dlen src x -> u2_after za n x <> None ->
  mspec (own (optl w ++ X)) (u2_loopM ops za n x w) (fun r => own (optl (snd r) ++ X)).
Proof.
  intros dlen src n. destruct zsizes as (_ & _ & _ & _ & _ & _ & HW).
  induction n as [|f IH]; intros x w X Hd Hs Hb HR NS; [exfalso; apply NS; reflexivity|].
  rewrite u2_after_S in NS. cbn [u2_loopM].
  set (wants := u2_wants za x && match w with Some _ => false | None => true end).
  assert (GRANTED : forall w0, mspec (own (optl w0 ++ X))
             match u2_stepP za true x with
             | inl x' => u2_loopM ops za f x' w0
             | inr (Some (x', err)) => ret ops (x', err, w0)
             | inr None => unreachable ops
             end (fun r => own (optl (snd r) ++ X))).
  { intros w0. destruct (u2_stepP za true x) as [x'|[[x' err]|]] eqn:ES.
    - apply IH; [exact Hd | exact Hs | exact Hb | exact (u2_reach_step za dlen src x x' HR ES) | exact NS].
    - apply mspec_ret_ops. intros s mo H. exact H.
    - exfalso. exact (NS eq_refl). }
  destruct wants eqn:EW.
  - subst wants. apply andb_true_iff in EW. destruct EW as [EW Ew]. destruct w as [q|]; [discriminate Ew|]. cbn [optl app].
    eapply mspec_bind_ops; [apply malloc_ops; exact HW|].
    intros [p|]; cbn [optl app].
    + exact (GRANTED (Some p)).
    +
      destruct (zo_nomemC za ZOK dlen src x Hd Hs Hb HR EW) as [x' EX]. rewrite EX.
      apply mspec_ret_ops. intros s mo H. exact H.
  - apply (mspec_bind_ops _ _ _ (fun _ => own (optl w ++ X))); [apply mspec_ret_ops; intros s mo H; exact H|]. intros r. exact (GRANTED w).
Qed.

Lemma uncompress2_mspec : forall X dlen src, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
  mspec (own X) (uncompress2M ops za dlen src) (fun _ => own X).
Proof.
  intros X dlen src Hd Hs Hb. destruct zsizes as (_ & _ & _ & _ & _ & HI & _). unfold uncompress2M.
  eapply mspec_bind_ops; [apply malloc_ops; exact HI|]. intros [sp|]; cbn [optl app]; [| apply mspec_ret_ops; auto].
  pose proof (zo_u2C za ZOK dlen src Hd Hs Hb) as NS. unfold u2_pure in NS. rewrite u2_loop_after in NS.
  eapply mspec_bind_ops.
  { apply (u2_loop_mspec dlen src _ _ None (sp :: X) Hd Hs Hb (u2_reach_x0 za dlen src)).
    intros E. rewrite E in NS. exact (NS eq_refl). }
  intros [[x err] w]. cbn [snd]. destruct (u2_result za dlen x err) as [[out tout] rc].
  eapply mspec_bind_ops; [apply free_ops|]. intro.
  eapply mspec_bind_ops; [apply (free_ops X (Some sp))|]. intro. apply mspec_ret_ops. intros s mo H. exact H.
Qed.

Lemma check_decompress_mspec : forall X data n cl cm flags, 0 < cl <= ZBC_MAX -> 0 <= n -> n + 2 <= ZBC_MAX -> zlength data = n ->
  Forall (fun b => 0 <= b < 256) data ->
  mspec (own X) (check_decompressM ops za data n cl cm flags) (fun _ => own X).
Proof.
  intros X data n cl cm flags Hcl Hn Hn2 Hlen Hb. unfold check_decompressM.
  eapply mspec_bind_ops; [apply malloc_ops; lia|]. intros [kp|]; cbn [optl app]; [| apply mspec_ret_ops; auto].
  destruct (zhdr_bytes_ok cm flags) as [HB2 HL2].
  eapply mspec_bind_ops.
  { apply (uncompress2_mspec (kp :: X) cl _ Hcl); [| apply Forall_app; split; [exact HB2| exact Hb]].
    unfold zlength in *. rewrite length_app. unfold zlength in HL2. lia. }
  intro. apply (free_ops X (Some kp)).
Qed.

Lemma Forall_skipn_Z : forall (P : Z -> Prop) n (l : list Z), Forall P l -> Forall P (skipn n l).
Proof. intros P n l H. revert n. induction H as [|a l Ha Hl IH]; intros [|n]; cbn; [constructor|constructor|constructor; assumption|apply IH]. Qed.

End TargetSafe.
