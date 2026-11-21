(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad MSafe Stdio ZApi ZHarness ZInst ZTarget Target.
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
Variable za : zapi.
Hypothesis ZOK : zapi_ok za.
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

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

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

Lemma own_leak_list : forall L X s mo, own (L ++ X) s mo -> own X s mo.
Proof. induction L as [|p L IH]; intros X s mo H; [exact H|]. apply IH. eapply Hleak. exact H. Qed.


Lemma zsizes : 0 <= z_dstate za /\ 0 <= z_dwin za /\ 0 <= z_dprev za /\ 0 <= z_dhead za /\ 0 <= z_dpend za
               /\ 0 <= z_isize za /\ 0 <= z_wsize za.
Proof.
  pose proof (zo_sizes za ZOK) as H.
  repeat (match type of H with Forall _ (_ :: _) => let a := fresh "Ha" in let b := fresh "Hb" in inversion H as [|? ? a b]; subst; clear H; rename b into H end).
  lia.
Qed.

Lemma zlength_app' {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.

Lemma dec_digits_n_len : forall fuel n acc, 0 <= n < 10 ^ Z.of_nat fuel -> (0 < fuel)%nat ->
  zlength (dec_digits_n fuel n acc) <= Z.of_nat fuel + zlength acc.
Proof.
  induction fuel as [|f IH]; intros n acc Hn Hf; [lia|].
  cbn [dec_digits_n]. destruct (Z.ltb_spec n 10).
  - unfold zlength. cbn [length]. lia.
  - destruct f as [|f']; [cbn in Hn; lia|].
    etransitivity; [apply IH; [|lia]|].
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
    + unfold zlength. cbn [length]. lia.
Qed.

Lemma Zsdecimal_len : forall rc, - 2^31 <= rc < 2^31 -> zlength (Zsdecimal rc) <= 11.
Proof.
  intros rc Hrc. unfold Zsdecimal, Zdecimal.
  assert (H10 : forall n, 0 <= n <= 2^31 -> zlength (dec_digits_n 64 n []) <= 10).
  { intros n Hn.
    assert (E : dec_digits_n 64 n [] = dec_digits_n 10 n []).
    { clear - Hn. assert (G : forall f1 f2 m acc, 0 <= m < 10 ^ Z.of_nat f1 -> (f1 <= f2)%nat -> (0 < f1)%nat -> dec_digits_n f2 m acc = dec_digits_n f1 m acc).
      { induction f1 as [|f1 IH]; intros f2 m acc Hm Hle Hpos; [lia|]. destruct f2 as [|f2]; [lia|]. cbn [dec_digits_n].
        destruct (Z.ltb_spec m 10); [reflexivity|]. destruct f1 as [|f1']; [cbn in Hm; lia|].
        apply IH; [|lia|lia]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hm by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
      apply G; [|lia|lia]. change (10 ^ Z.of_nat 10) with 10000000000. lia. }
    rewrite E. pose proof (dec_digits_n_len 10 n [] ltac:(change (10 ^ Z.of_nat 10) with 10000000000; lia) ltac:(lia)) as L.
    unfold zlength in *. cbn [length] in L. lia. }
  destruct (Z.ltb_spec rc 0).
  - pose proof (H10 (- rc) ltac:(lia)) as L. unfold zlength in *. cbn [length]. lia.
  - pose proof (H10 rc ltac:(lia)). lia.
Qed.

Lemma msg_err_len : forall what rc, zlength what <= 15 -> - 2^31 <= rc < 2^31 -> zlength (msg_err what rc) <= INTERNAL_BUFSIZ.
Proof.
  intros what rc Hw Hrc. unfold msg_err. rewrite !zlength_app'. pose proof (Zsdecimal_len rc Hrc).
  change (zlength (str " error: "%string)) with 8. change (zlength [10]) with 1. unfold INTERNAL_BUFSIZ. lia.
Qed.

Lemma err_ops : forall X what rc, zlength what <= 15 -> - 2^31 <= rc < 2^31 ->
  mspec (own X) (out_stderr ops (msg_err what rc)) (fun _ => own X).
Proof. intros X what rc Hw Hrc. red_ops. apply Herr. apply msg_err_len; assumption. Qed.


Definition blk5 (b : ptr * ptr * ptr * ptr * ptr) : list ptr :=
  let '(sp, wp, pp, hp, bp) := b in [bp; hp; pp; wp; sp].

Lemma deflate_init_mspec : forall X,
  mspec (own X) (deflate_init ops za)
        (fun r => match r with Some b => own (blk5 b ++ X) | None => own X end).
Proof.
  intros X. destruct zsizes as (H1 & H2 & H3 & H4 & H5 & _). unfold deflate_init.
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

Lemma deflate_end_mspec : forall X b, mspec (own (blk5 b ++ X)) (deflate_end ops b) (fun _ => own X).
Proof.
  intros X [[[[sp wp] pp] hp] bp]. unfold deflate_end, blk5.
  eapply mspec_bind_ops; [apply (free_ops _ (Some bp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some hp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some pp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some wp))|]. intro.
  apply (free_ops X (Some sp)).
Qed.

Definition d8_ok (d8 : list Z) (cl : Z) : Prop :=
  1 <= zlength d8 <= ZH_MAX /\ Forall (fun b => 0 <= b < 256) d8 /\ cl = z_bound za (zlength d8).

Lemma test_deflate_mspec : forall X d8 cl, d8_ok d8 cl ->
  mspec (own X) (test_deflate ops za d8 cl)
        (fun comprc s mo => own X s mo /\ zlength comprc = cl).
Proof.
  intros X d8 cl (Hlen & Hb & ->). pose proof (zo_bound za ZOK _ Hlen) as Hcl. unfold test_deflate.
  eapply mspec_bind_ops; [apply deflate_init_mspec|]. intros [b|].
  - destruct (test_deflate_pure za d8 (z_bound za (zlength d8))) as [comprc|] eqn:E.
    + eapply mspec_bind_ops; [apply deflate_end_mspec|]. intro. apply mspec_ret_ops. intros s mo H. split; [exact H|].
      clear - E Hcl. unfold test_deflate_pure in E.
      assert (L1 : forall fuel d c ds out r, dloop1 za fuel d c ds out = Some r -> zlength (snd r) = zlength out).
      { induction fuel as [|f IH]; intros d c ds out r H; [discriminate|]. cbn [dloop1] in H.
        destruct (negb (d_total_in za (fst ds) =? zlength d) && (d_total_out za (fst ds) <? c)).
        - destruct (d_call za d ds Z_NO_FLUSH) as [[ds' bs] rc]. destruct (d_step_ok za d c (fst ds) ds' bs); [|discriminate].
          destruct (rc =? Z_OK); [|discriminate].
          rewrite (IH _ _ _ _ _ H). apply zstore_length.
        - inversion H; subst. reflexivity. }
      assert (L2 : forall fuel d c ds out r, dloop2 za fuel d c ds out = Some r -> zlength (snd r) = zlength out).
      { induction fuel as [|f IH]; intros d c ds out r H; [discriminate|]. cbn [dloop2] in H.
        destruct (d_call za d ds Z_FINISH) as [[ds' bs] rc].
        destruct (d_step_ok za d c (fst ds) ds' bs); [|discriminate]. destruct (rc =? Z_STREAM_END).
        - inversion H; subst. cbn [snd]. apply zstore_length.
        - destruct (rc =? Z_OK); [|discriminate]. rewrite (IH _ _ _ _ _ H). apply zstore_length. }
      destruct (dloop1 za _ d8 _ (d_init za, 0) _) as [[ds1 out1]|] eqn:E1; [|discriminate].
      destruct (dloop2 za _ d8 _ ds1 out1) as [[ds2 out2]|] eqn:E2; [|discriminate].
      destruct (d_end za (fst ds2) =? Z_OK); [|discriminate]. inversion E; subst.
      apply L1 in E1. apply L2 in E2. cbn [snd] in *. rewrite E2, E1. apply zlength_zrepeat. lia.
    + exfalso. exact (zo_deflate za ZOK d8 Hlen Hb E).
  - eapply mspec_bind_ops; [apply err_ops; [vm_compute; discriminate| unfold Z_MEM_ERROR; lia]|].
    intro. apply mspec_ret_ops. intros s mo H. split; [exact H| apply zlength_zrepeat; lia].
Qed.


Lemma iloop_mspec : forall fuel comprc size cl is uc w X,
  iloop_pure za fuel comprc size cl is uc <> IRstuck ->
  mspec (own (optl w ++ X)) (iloop ops za fuel comprc size cl is uc w)
        (fun r s mo => match r with
                       | ILdone is' uc' w' => own (optl w' ++ X) s mo /\ iloop_pure za fuel comprc size cl is uc = IRdone is' uc'
                       | ILerr rc w' => own X s mo /\ - 2^31 <= rc < 2^31
                       end).
Proof.
  destruct zsizes as (_ & _ & _ & _ & _ & _ & HW).
  induction fuel as [|f IH]; intros comprc size cl is uc w X NS; [exfalso; apply NS; reflexivity|].
  cbn [iloop iloop_pure] in *.
  destruct ((i_total_out za is <? size) && (i_total_in za is <? cl)).
  2:{ apply mspec_ret_ops. intros s mo H. split; [exact H| reflexivity]. }
  destruct (i_wants_window za comprc is && match w with None => true | Some _ => false end) eqn:EW.
  - apply andb_true_iff in EW. destruct EW as [EW Ew]. destruct w as [q|]; [discriminate|]. cbn [optl app].
    eapply mspec_bind_ops; [apply malloc_ops; exact HW|].
    intros [p|]; cbn [optl app].
    +
      destruct (i_call za comprc is true) as [[is' bs] rc] eqn:EC.
      destruct (i_out_ok za size is bs); [| exfalso; apply NS; reflexivity].
      destruct (rc =? Z_STREAM_END).
      * apply mspec_ret_ops. intros s mo H. split; [exact H| reflexivity].
      * destruct (rc =? Z_OK).
        -- destruct (i_next_ok za size cl is'); [| exfalso; apply NS; reflexivity].
           apply (IH comprc size cl is' _ (Some p) X NS).
        -- apply mspec_ret_ops. intros s mo H. split; [eapply Hleak; exact H|].
           pose proof (zo_irc za ZOK comprc is true) as R. rewrite EC in R. exact R.
    +
      pose proof (zo_nomem za ZOK comprc is EW) as NM. pose proof (zo_irc za ZOK comprc is false) as R.
      pose proof (zo_nomem_bs za ZOK comprc is EW) as NB.
      destruct (i_call za comprc is true) as [[is1 bs1] rc1].
      destruct (i_call za comprc is false) as [[is' bs] rc]. cbn [fst snd] in NM, R, NB. subst rc bs.
      destruct (i_out_ok za size is bs1); [| exfalso; apply NS; reflexivity].
      change (Z_MEM_ERROR =? Z_STREAM_END) with false. change (Z_MEM_ERROR =? Z_OK) with false. cbv iota.
      apply mspec_ret_ops. intros s mo H. split; [exact H| exact R].
  - apply (mspec_bind_ops _ _ _ (fun _ => own (optl w ++ X))); [apply mspec_ret_ops; intros s mo H; exact H|]. intros r. cbv beta.
    destruct (i_call za comprc is true) as [[is' bs] rc] eqn:EC.
    destruct (i_out_ok za size is bs); [| exfalso; apply NS; reflexivity].
    destruct (rc =? Z_STREAM_END).
    + apply mspec_ret_ops. intros s mo H. split; [exact H| reflexivity].
    + destruct (rc =? Z_OK).
      * destruct (i_next_ok za size cl is'); [| exfalso; apply NS; reflexivity].
        apply (IH comprc size cl is' _ w X NS).
      * apply mspec_ret_ops. intros s mo H. split; [apply (own_leak_list (optl w)); exact H|].
        pose proof (zo_irc za ZOK comprc is true) as R. rewrite EC in R. exact R.
Qed.

Lemma test_inflate_mspec : forall X d8 comprc cl, d8_ok d8 cl -> zlength comprc = cl ->
  mspec (own X) (test_inflate ops za d8 comprc (zlength d8) cl) (fun _ => own X).
Proof.
  intros X d8 comprc cl (Hlen & Hb & ->) Hc. destruct zsizes as (_ & _ & _ & _ & _ & HI & _). unfold test_inflate.
  eapply mspec_bind_ops; [apply malloc_ops; exact HI|]. intros [sp|]; cbn [optl app].
  2:{ apply err_ops; [vm_compute; discriminate| unfold Z_MEM_ERROR; lia]. }
  pose proof (zo_inflate za ZOK (zlength d8) (norm8 comprc) Hlen ltac:(rewrite norm8_length; exact Hc) (norm8_bytes comprc)) as ZI.
  eapply mspec_bind_ops.
  { apply (iloop_mspec _ _ _ _ _ _ None (sp :: X)). intros E. rewrite E in ZI. exact ZI. }
  intros [is' uc' w'|rc w'].
  - apply mspec_pure. intros E. rewrite E in ZI. rewrite ZI. change (Z_OK =? Z_OK) with true. cbv iota.
    eapply mspec_bind_ops; [apply free_ops|]. intro.
    eapply mspec_bind_ops; [apply (free_ops X (Some sp))|]. intro.
    destruct (zlist_eqb (norm8 uc') d8); [apply mspec_ret_ops; auto|].
    red_ops. apply Hfw. vm_compute. discriminate.
  - apply mspec_pure. intros Hrc. eapply mspec_pre; [apply err_ops; [vm_compute; discriminate| exact Hrc]|].
    intros s mo H. eapply Hleak. exact H.
Qed.


Lemma fuzz_one_mspec : forall d X,
  mspec (own X) (fuzz_one ops za d) (fun rc s mo => own X s mo /\ rc = 0).
Proof.
  intros d X. unfold fuzz_one.
  destruct ((zlength d <? 1) || (ZH_MAX <? zlength d)) eqn:ER; [apply mspec_ret_ops; auto|].
  apply orb_false_iff in ER. destruct ER as [E1 E2]. apply Z.ltb_ge in E1, E2.
  assert (DOK : d8_ok (norm8 d) (z_bound za (zlength d))).
  { unfold d8_ok. rewrite norm8_length. split; [lia|]. split; [apply norm8_bytes| reflexivity]. }
  pose proof (zo_bound za ZOK (zlength d) ltac:(lia)) as Hcl.
  eapply mspec_bind_ops; [apply malloc_ops; lia|]. intros c.
  eapply mspec_bind_ops; [apply malloc_ops; lia|]. intros u.
  destruct c as [cp|]; destruct u as [up|]; cbn [optl app].
  2:{ eapply mspec_bind_ops; [apply (free_ops X (Some cp))|]. intro.
      eapply mspec_bind_ops; [apply (free_ops X None)|]. intro. apply mspec_ret_ops. auto. }
  2:{ eapply mspec_bind_ops; [apply (free_ops (up :: X) None)|]. intro.
      eapply mspec_bind_ops; [apply (free_ops X (Some up))|]. intro. apply mspec_ret_ops. auto. }
  2:{ eapply mspec_bind_ops; [apply (free_ops X None)|]. intro.
      eapply mspec_bind_ops; [apply (free_ops X None)|]. intro. apply mspec_ret_ops. auto. }
  eapply mspec_bind_ops; [apply (test_deflate_mspec _ _ _ DOK)|]. intros comprc. apply mspec_pure. intros Hc.
  eapply mspec_bind_ops.
  { pose proof (test_inflate_mspec (up :: cp :: X) _ comprc _ DOK Hc) as TI. rewrite norm8_length in TI. exact TI. }
  intro.
  eapply mspec_bind_ops; [eapply mspec_pre; [apply (free_ops (up :: X) (Some cp))|]|].
  { intros s mo H. cbn [optl app]. eapply Hperm; [apply perm_swap| exact H]. }
  intro. eapply mspec_bind_ops; [apply (free_ops X (Some up))|]. intro.
  apply mspec_ret_ops. auto.
Qed.

Lemma run_calls_mspec : forall d X n rc, rc = 0 ->
  mspec (own X) (run_calls ops za d n rc) (fun rc' s mo => own X s mo /\ rc' = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc Hrc; cbn [run_calls].
  - apply mspec_ret_ops. intros s mo H. auto.
  - apply (mspec_bind_ops _ _ _ (fun rc' s mo => own X s mo /\ rc' = 0)); [apply fuzz_one_mspec|].
    intros rc'. apply mspec_pure. intros ->.
    apply (mspec_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0. apply Hout.
    + intro. apply IH. reflexivity.
Qed.

End TargetSafe.

Theorem target_run_mspec {St ptr : Type}
  (raw_malloc : Z -> Monad.M St (option ptr)) (raw_free : ptr -> Monad.M St unit)
  (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) (own : list ptr -> assn St) :
  (forall X n, 0 <= n -> mspec (own X) (raw_malloc n)
     (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end)) ->
  (forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X)) ->
  (forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo) ->
  (forall p X s mo, own (p :: X) s mo -> own X s mo) ->
  (forall X bs, zlength bs <= INTERNAL_BUFSIZ -> mspec (own X) (stderr_fprintf (St:=St) [bs]) (fun _ => own X)) ->
  (forall X bs, zlength bs <= INTERNAL_BUFSIZ -> mspec (own X) (stderr_fwrite (St:=St) bs) (fun _ => own X)) ->
  (forall X, mspec (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X)) ->
  forall X cfg payload,
  mspec (own X) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X).
Proof.
  intros Hdm Hdf Hperm Hleak Herr Hfw Hout X cfg payload. unfold Target.target_run, ZTarget.target_run.
  set (ops := Target.ops raw_malloc raw_free get_so set_so).
  pose proof (@run_calls_mspec St ptr the_zapi the_zapi_ok raw_malloc raw_free get_so set_so own Hdm Hdf Hperm Hleak Herr Hfw Hout) as RC.
  assert (zlen0 : 0 <= zlength payload) by (unfold zlength; lia).
  eapply mspec_bind with (Q1 := fun a s mo => match a with
                                               | None => own X s mo
                                               | Some None => own X s mo
                                               | Some (Some p) => own (p :: X) s mo
                                               end).
  - destruct (zlength payload =? 0).
    + cbn. apply mspec_ret. auto.
    + cbn. eapply mspec_bind; [apply (Hdm X _ zlen0)|].
      intros [p|]; apply mspec_ret; intros s mo H; [exact (proj1 H)| exact H].
  - intros [[p|]|]; [| |cbn; apply mspec_ret; auto].
    + cbn -[run_calls]. eapply mspec_bind; [apply (RC payload (p :: X)); reflexivity|].
      intros rc. apply (mspec_bind _ _ _ (fun _ => own X)); [eapply mspec_pre; [apply Hdf|]; intros s mo H; exact (proj1 H)|].
      intros u. apply mspec_ret. auto.
    + cbn -[run_calls]. eapply mspec_bind; [apply (RC payload X); reflexivity|].
      intros rc. apply (mspec_bind _ _ _ (fun _ => own X)); [apply mspec_ret; intros s mo H; exact (proj1 H)|].
      intros u. apply mspec_ret. auto.
Qed.
