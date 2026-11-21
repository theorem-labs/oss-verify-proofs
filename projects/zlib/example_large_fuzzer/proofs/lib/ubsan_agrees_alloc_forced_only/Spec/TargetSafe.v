(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad MSafe Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL ZInstL ZTargetL Target.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Leak.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.

Definition lown (X : list ptr) : assn St := fun s mo => exists Y, own (Y ++ X) s mo.

Lemma lown_of_own : forall X s mo, own X s mo -> lown X s mo.
Proof. intros X s mo H. exists []. exact H. Qed.

Lemma lown_perm : forall X Y s mo, Permutation X Y -> lown X s mo -> lown Y s mo.
Proof. intros X Y s mo HP [L H]. exists L. eapply Hperm; [|exact H]. apply Permutation_app_head. exact HP. Qed.

(* [comment removed for export] *)
Lemma lown_leak : forall L X s mo, lown (L ++ X) s mo -> lown X s mo.
Proof. intros L X s mo [Y H]. exists (Y ++ L). rewrite <- app_assoc. exact H. Qed.
Lemma lown_leak1 : forall p X s mo, lown (p :: X) s mo -> lown X s mo.
Proof. intros p X. apply (lown_leak [p]). Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TargetSafe.
Context {St ptr : Type}.
Variable za : zapiL.
Hypothesis ZOK : zapiL_ok za.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store out_stderr_fw ops Target.ops lib_free_opt].

Definition optl (p : option ptr) : list ptr := match p with Some q => [q] | None => [] end.

Lemma mspec_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (ret ops a) Q.
Proof. intros H. red_ops. apply mspec_ret. exact H. Qed.

Lemma mspec_bind_ops {A B} (m : Monad.M St A) (f : A -> Monad.M St B) P Q1 Q :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (bind ops m f) Q.
Proof. intros H1 H2. red_ops. eapply mspec_bind; eauto. Qed.

(* [comment removed for export] *)
Lemma malloc_ops : forall X n, 0 <= n ->
  mspec (own X) (lib_malloc ops n) (fun r => own (optl r ++ X)).
Proof.
  intros X n Hn. red_ops. eapply mspec_post; [apply (Hdm X n Hn)|].
  intros [p|] s mo H; cbn [optl app]; [exact (proj1 H)| exact H].
Qed.

(* [comment removed for export] *)
Lemma free_ops : forall X p, mspec (own (optl p ++ X)) (lib_free ops p) (fun _ => own X).
Proof. intros X [p|]; red_ops; cbn [optl app]; [apply Hdf| apply mspec_ret; auto]. Qed.

Lemma own_leak_list : forall L X s mo, own (L ++ X) s mo -> own X s mo.
Proof. induction L as [|p L IH]; intros X s mo H; [exact H|]. apply IH. eapply Hleak. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsizes : 0 <= zl_dstate za /\ 0 <= zl_dwin za /\ 0 <= zl_dprev za /\ 0 <= zl_dhead za /\ 0 <= zl_dpend za
               /\ 0 <= zl_isize za /\ 0 <= zl_wsize za.
Proof.
  pose proof (zo_sizesL za ZOK) as H.
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

Lemma dec_digits_fuel : forall f1 f2 m acc, 0 <= m < 10 ^ Z.of_nat f1 -> (f1 <= f2)%nat -> (0 < f1)%nat ->
  dec_digits_n f2 m acc = dec_digits_n f1 m acc.
Proof.
  induction f1 as [|f1 IH]; intros f2 m acc Hm Hle Hpos; [lia|]. destruct f2 as [|f2]; [lia|]. cbn [dec_digits_n].
  destruct (Z.ltb_spec m 10); [reflexivity|]. destruct f1 as [|f1']; [cbn in Hm; lia|].
  apply IH; [|lia|lia]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hm by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

(* [comment removed for export] *)
Lemma Zdecimal_len : forall k n, 0 <= n < 10 ^ Z.of_nat k -> (0 < k <= 64)%nat -> zlength (Zdecimal n) <= Z.of_nat k.
Proof.
  intros k n Hn Hk. unfold Zdecimal. rewrite (dec_digits_fuel k 64 n [] Hn ltac:(lia) ltac:(lia)).
  pose proof (dec_digits_n_len k n [] Hn ltac:(lia)) as L. unfold zlength in *. cbn [length] in L. lia.
Qed.

(* [comment removed for export] *)
Lemma Zsdecimal_len : forall rc, cint rc -> zlength (Zsdecimal rc) <= 11.
Proof.
  intros rc Hrc. unfold cint in Hrc. unfold Zsdecimal.
  assert (H10 : forall n, 0 <= n <= 2^31 -> zlength (Zdecimal n) <= 10).
  { intros n Hn. apply (Zdecimal_len 10 n); [change (10 ^ Z.of_nat 10) with 10000000000; lia | lia]. }
  destruct (Z.ltb_spec rc 0).
  - pose proof (H10 (- rc) ltac:(lia)) as L. unfold zlength in *. cbn [length]. lia.
  - pose proof (H10 rc ltac:(lia)). lia.
Qed.

Lemma msg_err_len : forall what rc, zlength what <= 15 -> cint rc -> zlength (msg_err what rc) <= INTERNAL_BUFSIZ.
Proof.
  intros what rc Hw Hrc. unfold msg_err. rewrite !zlength_app'. pose proof (Zsdecimal_len rc Hrc).
  change (zlength (str " error: "%string)) with 8. change (zlength [10]) with 1. unfold INTERNAL_BUFSIZ. lia.
Qed.

Lemma err_ops : forall X what rc, zlength what <= 15 -> cint rc ->
  mspec (own X) (out_stderr ops (msg_err what rc)) (fun _ => own X).
Proof. intros X what rc Hw Hrc. red_ops. apply Herr. apply msg_err_len; assumption. Qed.

(* [comment removed for export] *)
Lemma msgl_bad_len : forall t, 0 <= t < 2^64 -> zlength (msgl_bad t) <= INTERNAL_BUFSIZ.
Proof.
  intros t Ht. unfold msgl_bad. rewrite !zlength_app'.
  pose proof (Zdecimal_len 20 t ltac:(change (10 ^ Z.of_nat 20) with 100000000000000000000; lia) ltac:(lia)).
  change (zlength (str "bad large inflate: "%string)) with 19. change (zlength [10]) with 1. unfold INTERNAL_BUFSIZ. lia.
Qed.

Lemma bad_ops : forall X t, 0 <= t < 2^64 -> mspec (own X) (out_stderr ops (msgl_bad t)) (fun _ => own X).
Proof. intros X t Ht. red_ops. apply Herr. apply msgl_bad_len. exact Ht. Qed.

(* [comment removed for export] *)
Definition dexit_ok (e : dexitL) : Prop :=
  match e with DXL_err w rc => zlength w <= 15 /\ cint rc | _ => True end.

Lemma emit_dexit_ops : forall X e, dexit_ok e -> mspec (own X) (emit_dexit ops e) (fun _ => own X).
Proof.
  intros X [|w rc| |] He; cbn [emit_dexit].
  - apply mspec_ret_ops. auto.
  - destruct He as [Hw Hrc]. apply err_ops; assumption.
  - red_ops. apply Hfw. vm_compute. discriminate.
  - red_ops. apply Hfw. vm_compute. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition blk5 (b : ptr * ptr * ptr * ptr * ptr) : list ptr :=
  let '(sp, wp, pp, hp, bp) := b in [bp; hp; pp; wp; sp].

Lemma deflate_init_mspec : forall X,
  mspec (own X) (deflate_initL ops za)
        (fun r => match r with Some b => own (blk5 b ++ X) | None => own X end).
Proof.
  intros X. destruct zsizes as (H1 & H2 & H3 & H4 & H5 & _). unfold deflate_initL.
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

Lemma deflate_end_mspec : forall X b, mspec (own (blk5 b ++ X)) (deflate_endL ops b) (fun _ => own X).
Proof.
  intros X [[[[sp wp] pp] hp] bp]. unfold deflate_endL, blk5.
  eapply mspec_bind_ops; [apply (free_ops _ (Some bp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some hp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some pp))|]. intro.
  eapply mspec_bind_ops; [apply (free_ops _ (Some wp))|]. intro.
  apply (free_ops X (Some sp)).
Qed.

(* [comment removed for export] *)
Lemma d_callL_rc : forall N flush inp x, cint (snd (d_callL za N flush inp x)).
Proof.
  intros N flush inp x. unfold d_callL.
  pose proof (zo_drcL za ZOK inp (dp_ds za x) (N - dp_n za x) flush) as H.
  destruct (dl_deflate za inp (dp_ds za x) (N - dp_n za x) flush) as [[[ds' c] bs] rc]. cbn [snd] in *. exact H.
Qed.

(* [comment removed for export] *)
Lemma tdeflL_exit_ok : forall N, dexit_ok (snd (fst (fst (tdeflL za N)))).
Proof.
  intros N. unfold tdeflL.
  pose proof (d_callL_rc N Z_NO_FLUSH (zrepeat 0 N) (mkDPL za (dl_init9 za) [] 0 [])) as R1.
  destruct (d_callL za N Z_NO_FLUSH (zrepeat 0 N) _) as [x1 rc1]. cbn [snd] in R1.
  destruct (negb (rc1 =? Z_OK)); [cbn; split; [vm_compute; discriminate | exact R1]|].
  destruct (negb (zlength (dp_in za x1) =? 0)); [exact I|].
  destruct (p_callL za N Z_NO_COMPRESSION Z_DEFAULT_STRATEGY x1) as [x2 rc2].
  pose proof (d_callL_rc N Z_NO_FLUSH (rev_append (dp_orev za x2) []) x2) as R3.
  destruct (d_callL za N Z_NO_FLUSH (rev_append (dp_orev za x2) []) x2) as [x3 rc3]. cbn [snd] in R3.
  destruct (negb (rc3 =? Z_OK)); [cbn; split; [vm_compute; discriminate | exact R3]|].
  destruct (p_callL za N Z_BEST_COMPRESSION Z_FILTERED x3) as [x4 rc4].
  pose proof (d_callL_rc N Z_NO_FLUSH (zrepeat 0 N) x4) as R5.
  destruct (d_callL za N Z_NO_FLUSH (zrepeat 0 N) x4) as [x5 rc5]. cbn [snd] in R5.
  destruct (negb (rc5 =? Z_OK)); [cbn; split; [vm_compute; discriminate | exact R5]|].
  pose proof (d_callL_rc N Z_FINISH (dp_in za x5) x5) as R6.
  destruct (d_callL za N Z_FINISH (dp_in za x5) x5) as [x6 rc6]. cbn [snd] in R6.
  destruct (negb (rc6 =? Z_STREAM_END)); [exact I|].
  pose proof (zo_dendL za ZOK (dp_ds za x6)) as RE.
  destruct (dl_end za (dp_ds za x6) =? Z_OK); cbn; [exact I|]. split; [vm_compute; discriminate | exact RE].
Qed.

Lemma test_deflate_mspec : forall X N diff, 0 <= N ->
  mspec (own X) (test_large_deflateM ops za N diff)
        (fun r s mo => own X s mo /\ zlength (fst r) = N).
Proof.
  intros X N diff HN. unfold test_large_deflateM.
  eapply mspec_bind_ops; [apply deflate_init_mspec|]. intros [b|].
  - pose proof (tdeflL_exit_ok N) as EOK. unfold test_large_deflate_pure.
    destruct (tdeflL za N) as [[[x e] od] ended]. cbn [fst snd] in EOK.
    eapply mspec_bind_ops with (Q1 := fun _ => own X).
    { destruct ended; [apply deflate_end_mspec|]. apply mspec_ret_ops. intros s mo H. exact (own_leak_list _ _ _ _ H). }
    intros u1. eapply mspec_bind_ops; [apply emit_dexit_ops; exact EOK|]. intros u2.
    apply mspec_ret_ops. intros s mo H. split; [exact H|]. cbn [fst]. apply comprL_length. exact HN.
  - eapply mspec_bind_ops; [apply err_ops; [vm_compute; discriminate| unfold cint, Z_MEM_ERROR; lia]|].
    intro. apply mspec_ret_ops. intros s mo H. split; [exact H| cbn [fst]; apply zlength_zrepeat; exact HN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ipure (n : nat) (N : Z) (comprc : list Z) (is : ISL za) : iresL za :=
  match iterNL n (il_stepP za N comprc) is with inl _ => IRLstuck | inr r => r end.

Lemma i_callL_rc : forall N comprc is ok, cint (snd (i_callL za N comprc is ok)).
Proof.
  intros N comprc is ok. unfold i_callL.
  pose proof (zo_ircL za ZOK (zdrop (il_total_in za is) comprc) is N ok) as H.
  destruct (il_inflate za _ is N ok) as [[[is' c] bs] rc]. cbn [snd] in *. exact H.
Qed.

Lemma i_callL_refused : forall N comprc is, i_wantsL za N comprc is = true ->
  snd (i_callL za N comprc is false) = Z_MEM_ERROR.
Proof.
  intros N comprc is Hw. unfold i_callL, i_wantsL in *.
  pose proof (zo_nomemL za ZOK (zdrop (il_total_in za is) comprc) is N Hw) as [H _].
  destruct (il_inflate za _ is N false) as [[[is' c] bs] rc]. cbn [snd] in *. exact H.
Qed.

Lemma iloop_mspec : forall n N comprc is w X,
  ipure n N comprc is <> IRLstuck ->
  mspec (own (optl w ++ X)) (iloopL ops za n N comprc is w)
        (fun r s mo => match r with
                       | ILLdone is' w' => own (optl w' ++ X) s mo /\ ipure n N comprc is = IRLdone is'
                       | ILLerr rc w' => own X s mo /\ cint rc
                       end).
Proof.
  destruct zsizes as (_ & _ & _ & _ & _ & _ & HW).
  induction n as [|f IH]; intros N comprc is w X NS; [exfalso; apply NS; reflexivity|].
  unfold ipure in *. cbn [iloopL iterNL] in *.
  assert (PURE : forall w0, mspec (own (optl w0 ++ X))
            (let '(is', bs, rc) := i_callL za N comprc is true in
             if rc =? Z_STREAM_END then ret ops (ILLdone is' w0)
             else if rc =? Z_OK then iloopL ops za f N comprc is' w0 else ret ops (ILLerr rc w0))
            (fun r s mo => match r with
                           | ILLdone is' w' => own (optl w' ++ X) s mo
                               /\ match match il_stepP za N comprc is with inl a' => iterNL f (il_stepP za N comprc) a' | inr b => inr b end
                                  with inl _ => IRLstuck | inr r0 => r0 end = IRLdone is'
                           | ILLerr rc w' => own X s mo /\ cint rc
                           end)).
  { intros w0. revert NS. unfold il_stepP. pose proof (i_callL_rc N comprc is true) as R.
    destruct (i_callL za N comprc is true) as [[is' bs] rc]. cbn [snd] in R.
    destruct (rc =? Z_STREAM_END); [intros _; apply mspec_ret_ops; intros s mo H; split; [exact H | reflexivity]|].
    destruct (rc =? Z_OK); [intros NS; apply IH; exact NS|].
    intros _. apply mspec_ret_ops. intros s mo H. split; [exact (own_leak_list (optl w0) _ _ _ H) | exact R]. }
  destruct (i_wantsL za N comprc is && match w with None => true | Some _ => false end) eqn:EW.
  - apply andb_true_iff in EW. destruct EW as [EW Ew]. destruct w as [q|]; [discriminate|]. cbn [optl app].
    eapply mspec_bind_ops; [apply malloc_ops; exact HW|].
    intros [p|]; cbn [optl app].
    + (* [comment removed for export] *) exact (PURE (Some p)).
    + (* [comment removed for export] *)
      pose proof (i_callL_refused N comprc is EW) as NM.
      destruct (i_callL za N comprc is false) as [[is' bs] rc]. cbn [snd] in NM. subst rc.
      change (Z_MEM_ERROR =? Z_STREAM_END) with false. change (Z_MEM_ERROR =? Z_OK) with false. cbv iota.
      apply mspec_ret_ops. intros s mo H. split; [exact H| unfold cint, Z_MEM_ERROR; lia].
  - apply (mspec_bind_ops _ _ _ (fun _ => own (optl w ++ X))); [apply mspec_ret_ops; intros s mo H; exact H|]. intros r. cbv beta.
    exact (PURE w).
Qed.

(* [comment removed for export] *)
Definition N_ok (N : Z) : Prop := exists size, 1 <= size <= ZL_MAX /\ N = NofL size.

Lemma test_inflate_mspec : forall X N comprc diff, N_ok N -> zlength comprc = N ->
  mspec (own X) (test_large_inflateM ops za N comprc diff) (fun _ => own X).
Proof.
  intros X N comprc diff (size & Hsz & ->) Hc. destruct zsizes as (_ & _ & _ & _ & _ & HI & _). unfold test_large_inflateM.
  eapply mspec_bind_ops; [apply malloc_ops; exact HI|]. intros [sp|]; cbn [optl app].
  2:{ apply err_ops; [vm_compute; discriminate| unfold cint, Z_MEM_ERROR; lia]. }
  pose proof (zo_inflateL za ZOK size (norm8 comprc) Hsz ltac:(rewrite norm8_length; exact Hc) (norm8_bytes comprc)) as ZI.
  unfold iloopL_pure in ZI. rewrite iterZL_nat in ZI. fold (ipure (Z.to_nat (ZIL_FUEL (NofL size))) (NofL size) (norm8 comprc) (il_init za)) in ZI.
  eapply mspec_bind_ops.
  { apply (iloop_mspec _ _ _ _ None (sp :: X)). intros E. rewrite E in ZI. exact ZI. }
  intros [is' w'|rc w'].
  - apply mspec_pure. intros E. rewrite E in ZI.
    eapply mspec_bind_ops; [apply free_ops|]. intro.
    eapply mspec_bind_ops; [apply (free_ops X (Some sp))|]. intro.
    destruct (il_end za is' =? Z_OK) eqn:EE.
    + destruct (il_total_out za is' =? 2 * NofL size + diff); [apply mspec_ret_ops; auto|].
      apply bad_ops. exact ZI.
    + apply err_ops; [vm_compute; discriminate | exact (zo_iendL za ZOK is')].
  - apply mspec_pure. intros Hrc. eapply mspec_pre; [apply err_ops; [vm_compute; discriminate| exact Hrc]|].
    intros s mo H. eapply Hleak. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fuzz_one_mspec : forall d diff X,
  mspec (own X) (fuzz_oneL ops za d diff) (fun r s mo => own X s mo /\ fst r = 0).
Proof.
  intros d diff X. unfold fuzz_oneL.
  destruct ((zlength d <? 1) || (ZL_MAX <? zlength d)) eqn:ER; [apply mspec_ret_ops; auto|].
  apply orb_false_iff in ER. destruct ER as [E1 E2]. apply Z.ltb_ge in E1, E2.
  assert (HN : N_ok (NofL (zlength d))) by (exists (zlength d); split; [lia | reflexivity]).
  assert (HN0 : 0 <= NofL (zlength d)) by (unfold NofL; lia).
  eapply mspec_bind_ops; [apply malloc_ops; exact HN0|]. intros c. cbv beta.
  eapply mspec_bind_ops; [apply malloc_ops; exact HN0|]. intros u. cbv beta.
  destruct c as [cp|], u as [up|]; cbn [optl app].
  2:{ eapply mspec_bind_ops; [apply (free_ops X (Some cp))|]. intro.
      eapply mspec_bind_ops; [apply (free_ops X None)|]. intro.
      apply mspec_ret_ops. auto. }
  2:{ eapply mspec_bind_ops; [apply (free_ops (up :: X) None)|]. intro.
      eapply mspec_bind_ops; [apply (free_ops X (Some up))|]. intro.
      apply mspec_ret_ops. auto. }
  2:{ eapply mspec_bind_ops; [apply (free_ops X None)|]. intro.
      eapply mspec_bind_ops; [apply (free_ops X None)|]. intro.
      apply mspec_ret_ops. auto. }
  eapply mspec_bind_ops; [apply (test_deflate_mspec _ _ diff HN0)|]. intros [comprc diff']. apply mspec_pure. cbn [fst]. intros Hc.
  eapply mspec_bind_ops; [apply (test_inflate_mspec (up :: cp :: X) _ comprc diff' HN Hc)|]. intro.
  eapply mspec_bind_ops; [eapply mspec_pre; [apply (free_ops (up :: X) (Some cp))|]|].
  { intros s mo H. cbn [optl app]. eapply Hperm; [apply perm_swap| exact H]. }
  intro. eapply mspec_bind_ops; [apply (free_ops X (Some up))|]. intro.
  apply mspec_ret_ops. auto.
Qed.

Lemma run_calls_mspec : forall d X n rc diff, rc = 0 ->
  mspec (own X) (run_callsL ops za d n rc diff) (fun rc' s mo => own X s mo /\ rc' = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc diff Hrc; cbn [run_callsL].
  - apply mspec_ret_ops. intros s mo H. auto.
  - apply (mspec_bind_ops _ _ _ (fun r s mo => own X s mo /\ fst r = 0)); [apply fuzz_one_mspec|].
    intros [rc' diff']. apply mspec_pure. cbn [fst]. intros ->.
    apply (mspec_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0. apply Hout.
    + intro. apply IH. reflexivity.
Qed.

End TargetSafe.

(* [comment removed for export] *)
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
  intros Hdm Hdf Hperm Hleak Herr Hfw Hout X cfg payload. unfold Target.target_run, ZTargetL.target_runL.
  set (ops := Target.ops raw_malloc raw_free get_so set_so).
  pose proof (@run_calls_mspec St ptr the_zapiL the_zapiL_ok raw_malloc raw_free get_so set_so own Hdm Hdf Hperm Hleak Herr Hfw Hout) as RC.
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
    + cbn -[run_callsL]. eapply mspec_bind; [apply (RC payload (p :: X)); reflexivity|].
      intros rc. apply (mspec_bind _ _ _ (fun _ => own X)); [eapply mspec_pre; [apply Hdf|]; intros s mo H; exact (proj1 H)|].
      intros u. apply mspec_ret. auto.
    + cbn -[run_callsL]. eapply mspec_bind; [apply (RC payload X); reflexivity|].
      intros rc. apply (mspec_bind _ _ _ (fun _ => own X)); [apply mspec_ret; intros s mo H; exact (proj1 H)|].
      intros u. apply mspec_ret. auto.
Qed.
