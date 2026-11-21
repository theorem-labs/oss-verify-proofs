(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad Stdio. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog Canon.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZApi ZHarness ZTarget ZApiL ZHarnessL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTargetL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target TargetSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc ProgDetStdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store out_stderr_fw Target.ops lib_free_opt].

Section TargetE.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable za : zapiL.
Hypothesis ZOK : zapiL_ok za.

Let ops : target_ops (Monad.M PState) bptr := Target.ops raw_malloc raw_free ps_so set_so_ps.

Lemma mspecE_ret_ops {A} (a : A) (P : assnE PState) (Q : A -> assnE PState) :
  (forall s mo tr, P s mo tr -> Q a s mo tr) -> mspecE sel X P (ret ops a) Q.
Proof. intros H. cbn. apply mspecE_ret. exact H. Qed.

Lemma mspecE_bind_ops {A B} (m : Monad.M PState A) (f : A -> Monad.M PState B) P Q1 Q :
  mspecE sel X P m Q1 -> (forall a, mspecE sel X (Q1 a) (f a) Q) -> mspecE sel X P (bind ops m f) Q.
Proof. intros. cbn. eapply mspecE_bind; eauto. Qed.

Lemma size_ok : forall n, n < 2^62 -> Malloc.size_overflows n = false.
Proof. intros n H. unfold Malloc.size_overflows. apply Z.leb_gt. lia. Qed.

Definition Km_ok (Km : Model -> Prop) : Prop := forall mo mo', Km mo -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> Km mo'.

Lemma SoA_fstable : forall Km so tr0, Km_ok Km -> fstable (SoA ps_so Km so tr0).
Proof.
  intros Km so tr0 HKm s mo tr s' mo' (H1 & H2 & H3) Hso Hfd Hfs. split; [eapply HKm; eauto|]. split; [congruence| exact H3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stable.
Variable K : assnE PState.
Hypothesis HK : fstable K.

Lemma malloc_ops_E : forall n, n < 2^62 ->
  mspecE sel X K (lib_malloc ops n) (fun r s mo tr => K s mo tr /\ r <> None).
Proof. intros n Hn. red_ops. apply raw_malloc_E; [exact HK| apply size_ok; exact Hn]. Qed.

Lemma free_ops_E : forall p, mspecE sel X K (lib_free ops p) (fun _ => K).
Proof. intros [p|]; red_ops; [apply raw_free_E; exact HK| apply mspecE_ret; auto]. Qed.

Lemma zsizesE : zl_dstate za < 2^62 /\ zl_dwin za < 2^62 /\ zl_dprev za < 2^62 /\ zl_dhead za < 2^62 /\ zl_dpend za < 2^62
                /\ zl_isize za < 2^62 /\ zl_wsize za < 2^62.
Proof.
  pose proof (zo_sizesL za ZOK) as H.
  repeat (match type of H with Forall _ (_ :: _) => let a := fresh "Ha" in let b := fresh "Hb" in inversion H as [|? ? a b]; subst; clear H; rename b into H end).
  repeat split; lia.
Qed.

Lemma deflate_init_E : mspecE sel X K (deflate_initL ops za) (fun r s mo tr => K s mo tr /\ r <> None).
Proof.
  destruct zsizesE as (H1 & H2 & H3 & H4 & H5 & _). unfold deflate_initL.
  eapply mspecE_bind_ops; [apply malloc_ops_E; exact H1|]. intros s0. apply mspecE_pure. intros N0. destruct s0 as [sp|]; [|contradiction].
  eapply mspecE_bind_ops; [apply malloc_ops_E; exact H2|]. intros w0. apply mspecE_pure. intros Nw. destruct w0 as [wp|]; [|contradiction].
  eapply mspecE_bind_ops; [apply malloc_ops_E; exact H3|]. intros p0. apply mspecE_pure. intros Np. destruct p0 as [pp|]; [|contradiction].
  eapply mspecE_bind_ops; [apply malloc_ops_E; exact H4|]. intros h0. apply mspecE_pure. intros Nh. destruct h0 as [hp|]; [|contradiction].
  eapply mspecE_bind_ops; [apply malloc_ops_E; exact H5|]. intros b0. apply mspecE_pure. intros Nb. destruct b0 as [bp|]; [|contradiction].
  apply mspecE_ret_ops. intros s mo tr H. split; [exact H| discriminate].
Qed.

Lemma deflate_end_E : forall b, mspecE sel X K (deflate_endL ops b) (fun _ => K).
Proof.
  intros [[[[sp wp] pp] hp] bp]. unfold deflate_endL.
  eapply mspecE_bind_ops; [apply free_ops_E|]. intro. eapply mspecE_bind_ops; [apply free_ops_E|]. intro.
  eapply mspecE_bind_ops; [apply free_ops_E|]. intro. eapply mspecE_bind_ops; [apply free_ops_E|]. intro. apply free_ops_E.
Qed.

(* [comment removed for export] *)
Definition ipure (n : nat) (N : Z) (comprc : list Z) (is : ISL za) : iresL za :=
  match iterNL n (il_stepP za N comprc) is with inl _ => IRLstuck | inr r => r end.

Definition iloop_rel (r : @iloopL_res bptr za) (p : iresL za) : Prop :=
  match r, p with
  | ILLdone is _, IRLdone is' => is = is'
  | ILLerr rc _, IRLerr rc' => rc = rc'
  | _, _ => False
  end.

Lemma iloop_E : forall n N comprc is w,
  mspecE sel X K (iloopL ops za n N comprc is w) (fun r s mo tr => K s mo tr /\ iloop_rel r (ipure n N comprc is)).
Proof.
  destruct zsizesE as (_ & _ & _ & _ & _ & _ & HW).
  induction n as [|f IH]; intros N comprc is w; unfold ipure; cbn [iloopL iterNL]; [red_ops; apply mspecE_munr|].
  assert (PURE : forall w0, mspecE sel X K
            (let '(is', bs, rc) := i_callL za N comprc is true in
             if rc =? Z_STREAM_END then ret ops (ILLdone is' w0)
             else if rc =? Z_OK then iloopL ops za f N comprc is' w0 else ret ops (ILLerr rc w0))
            (fun r s mo tr => K s mo tr /\ iloop_rel r
               match match il_stepP za N comprc is with inl a' => iterNL f (il_stepP za N comprc) a' | inr b => inr b end
               with inl _ => IRLstuck | inr r0 => r0 end)).
  { intros w0. unfold il_stepP. destruct (i_callL za N comprc is true) as [[is' bs] rc].
    destruct (rc =? Z_STREAM_END); [apply mspecE_ret_ops; intros s mo tr H; split; [exact H| cbn; auto]|].
    destruct (rc =? Z_OK); [apply IH|]. apply mspecE_ret_ops. intros s mo tr H. split; [exact H| cbn; auto]. }
  destruct (i_wantsL za N comprc is && match w with None => true | Some _ => false end).
  - eapply mspecE_bind_ops; [apply malloc_ops_E; exact HW|]. intros r. apply mspecE_pure. intros Nr. destruct r as [p|]; [|contradiction].
    exact (PURE (Some p)).
  - apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply mspecE_ret_ops; auto|]. intros r. cbv beta. exact (PURE w).
Qed.
End Stable.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_digits_n_len' : forall fuel n acc, zlength (dec_digits_n fuel n acc) <= Z.of_nat fuel + zlength acc.
Proof.
  induction fuel as [|f IH]; intros n acc; cbn [dec_digits_n]; [lia|].
  destruct (n <? 10); [unfold zlength; cbn [length]; lia|].
  etransitivity; [apply IH|]. unfold zlength. cbn [length]. lia.
Qed.

Lemma Zdecimal_short : forall n, zlength (Zdecimal n) <= 64.
Proof. intros n. unfold Zdecimal. pose proof (dec_digits_n_len' 64 n []) as L. unfold zlength in *. cbn [length] in *. lia. Qed.

Lemma msg_err_short : forall what rc, zlength what < 2^32 -> zlength (msg_err what rc) < 2^61.
Proof.
  intros what rc Hw. unfold msg_err. rewrite !zlen_app. unfold Zsdecimal.
  assert (zlength (if rc <? 0 then 45 :: Zdecimal (- rc) else Zdecimal rc) <= 65).
  { destruct (rc <? 0); [pose proof (Zdecimal_short (- rc)); unfold zlength in *; cbn [length]; lia| pose proof (Zdecimal_short rc); lia]. }
  change (zlength (str " error: "%string)) with 8. change (zlength [10]) with 1. lia.
Qed.

Lemma msgl_bad_short : forall t, zlength (msgl_bad t) < 2^61.
Proof.
  intros t. unfold msgl_bad. rewrite !zlen_app. pose proof (Zdecimal_short t).
  change (zlength (str "bad large inflate: "%string)) with 19. change (zlength [10]) with 1. lia.
Qed.

Section Out.
Variable Km : Model -> Prop.
Hypothesis HKm : Km_ok Km.

Lemma err_E : forall so tr0 bs, zlength bs < 2^61 ->
  mspecE sel X (SoA ps_so Km so tr0) (out_stderr ops bs) (fun _ => SoA ps_so Km so (tr0 ++ evw 2 bs)).
Proof.
  intros so tr0 bs Hb. red_ops.
  eapply mspecE_conseq; [apply (stderr_fprintf_E sel X [bs] tr0 (fun s mo => Km mo /\ ps_so s = so)); constructor; [exact Hb| constructor]| |].
  - intros s mo tr (H1 & H2 & H3). auto.
  - intros a s mo tr ((H1 & H2) & H3). cbn [concat] in H3. rewrite app_nil_r in H3. split; [exact H1|]. split; [exact H2| exact H3].
Qed.

Lemma fw_E : forall so tr0 bs, zlength bs < 2^61 ->
  mspecE sel X (SoA ps_so Km so tr0) (out_stderr_fw ops bs) (fun _ => SoA ps_so Km so (tr0 ++ evw 2 bs)).
Proof.
  intros so tr0 bs Hb. red_ops.
  eapply mspecE_conseq; [apply (stderr_fwrite_E sel X bs tr0 (fun s mo => Km mo /\ ps_so s = so)); exact Hb| |].
  - intros s mo tr (H1 & H2 & H3). auto.
  - intros a s mo tr ((H1 & H2) & H3). split; [exact H1|]. split; [exact H2| exact H3].
Qed.

(* [comment removed for export] *)
Lemma emit_dexit_E : forall so tr0 e, (match e with DXL_err w _ => zlength w < 2^32 | _ => True end) ->
  mspecE sel X (SoA ps_so Km so tr0) (emit_dexit ops e) (fun _ => SoA ps_so Km so (tr0 ++ evw 2 (dexitL_msg e))).
Proof.
  intros so tr0 [|w rc| |] He; cbn [emit_dexit dexitL_msg].
  - apply mspecE_ret_ops. intros s mo tr H. cbn [evw map]. rewrite app_nil_r. exact H.
  - apply err_E. apply msg_err_short. exact He.
  - apply fw_E. vm_compute. reflexivity.
  - apply fw_E. vm_compute. reflexivity.
Qed.

Lemma tdeflL_tags : forall N, match snd (fst (fst (tdeflL za N))) with DXL_err w _ => zlength w < 2^32 | _ => True end.
Proof.
  intros N. unfold tdeflL.
  destruct (d_callL za N Z_NO_FLUSH (zrepeat 0 N) _) as [x1 rc1].
  destruct (negb (rc1 =? Z_OK)); [cbn; vm_compute; reflexivity|].
  destruct (negb (zlength (dp_in za x1) =? 0)); [exact I|].
  destruct (p_callL za N Z_NO_COMPRESSION Z_DEFAULT_STRATEGY x1) as [x2 rc2].
  destruct (d_callL za N Z_NO_FLUSH (rev_append (dp_orev za x2) []) x2) as [x3 rc3].
  destruct (negb (rc3 =? Z_OK)); [cbn; vm_compute; reflexivity|].
  destruct (p_callL za N Z_BEST_COMPRESSION Z_FILTERED x3) as [x4 rc4].
  destruct (d_callL za N Z_NO_FLUSH (zrepeat 0 N) x4) as [x5 rc5].
  destruct (negb (rc5 =? Z_OK)); [cbn; vm_compute; reflexivity|].
  destruct (d_callL za N Z_FINISH (dp_in za x5) x5) as [x6 rc6].
  destruct (negb (rc6 =? Z_STREAM_END)); [exact I|].
  destruct (dl_end za (dp_ds za x6) =? Z_OK); cbn; [exact I|]. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tldp_tags : forall N, match snd (fst (fst (test_large_deflate_pure za N))) with DXL_err w _ => zlength w < 2^32 | _ => True end.
Proof.
  intros N. pose proof (tdeflL_tags N) as TG. unfold test_large_deflate_pure.
  destruct (tdeflL za N) as [[[x e] od] ended]. cbn [fst snd] in *. exact TG.
Qed.

(* [comment removed for export] *)
Lemma test_deflate_E : forall so tr0 N diff,
  mspecE sel X (SoA ps_so Km so tr0) (test_large_deflateM ops za N diff)
         (fun rd s mo tr =>
            let '(r, _) := test_large_deflate_pure za N in let '(r2, od) := r in let '(comprc, e) := r2 in
            SoA ps_so Km so (tr0 ++ evw 2 (dexitL_msg e)) s mo tr /\ rd = (comprc, match od with Some d => d | None => diff end)).
Proof.
  intros so tr0 N diff. pose proof (SoA_fstable Km so tr0 HKm) as HK. pose proof (tldp_tags N) as TG.
  unfold test_large_deflateM.
  destruct (test_large_deflate_pure za N) as [[[comprc e] od] ended]. cbn [fst snd] in TG.
  eapply mspecE_bind_ops; [apply (deflate_init_E _ HK)|]. intros r. apply mspecE_pure. intros Nr. destruct r as [b|]; [|contradiction].
  eapply mspecE_bind_ops with (Q1 := fun _ => SoA ps_so Km so tr0).
  { destruct ended; [apply (deflate_end_E _ HK)| apply mspecE_ret_ops; auto]. }
  intro. eapply mspecE_bind_ops; [apply emit_dexit_E; exact TG|]. intro.
  apply mspecE_ret_ops. intros s mo tr H. split; [exact H| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma test_inflate_E : forall so tr0 N comprc diff,
  mspecE sel X (SoA ps_so Km so tr0) (test_large_inflateM ops za N comprc diff)
         (fun _ => SoA ps_so Km so (tr0 ++ evw 2 (test_large_inflate_msg za N comprc diff))).
Proof.
  intros so tr0 N comprc diff. destruct (zsizesE) as (_ & _ & _ & _ & _ & HI & _).
  pose proof (SoA_fstable Km so tr0 HKm) as HK. unfold test_large_inflateM, test_large_inflate_msg.
  eapply mspecE_bind_ops; [apply (malloc_ops_E _ HK); exact HI|]. intros s0. apply mspecE_pure. intros N0. destruct s0 as [sp|]; [|contradiction].
  eapply mspecE_bind_ops; [apply (iloop_E _ HK)|]. intros r. apply mspecE_pure. intros REL.
  unfold iloopL_pure. rewrite iterZL_nat. fold (ipure (Z.to_nat (ZIL_FUEL N)) N (norm8 comprc) (il_init za)).
  destruct (ipure (Z.to_nat (ZIL_FUEL N)) N (norm8 comprc) (il_init za)) as [is'|rc'|];
    destruct r as [is w|rc w]; cbn [iloop_rel] in REL; try contradiction.
  - subst is'.
    eapply mspecE_bind_ops; [apply (free_ops_E _ HK)|]. intro. eapply mspecE_bind_ops; [apply (free_ops_E _ HK)|]. intro.
    destruct (il_end za is =? Z_OK).
    + destruct (il_total_out za is =? 2 * N + diff).
      * apply mspecE_ret_ops. intros s mo tr H. cbn [evw map]. rewrite app_nil_r. exact H.
      * apply err_E. apply msgl_bad_short.
    + apply err_E. apply msg_err_short. vm_compute. reflexivity.
  - subst rc'. apply err_E. apply msg_err_short. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fuzz_one_E : forall so tr0 d diff, zlength d < 2^61 ->
  mspecE sel X (SoA ps_so Km so tr0) (fuzz_oneL ops za d diff)
         (fun r s mo tr => SoA ps_so Km so (tr0 ++ evw 2 (fst (harness_callL za (zlength d) diff))) s mo tr
                           /\ r = (0, snd (harness_callL za (zlength d) diff))).
Proof.
  intros so tr0 d diff Hd. pose proof (SoA_fstable Km so tr0 HKm) as HK. unfold fuzz_oneL, harness_callL.
  destruct ((zlength d <? 1) || (ZL_MAX <? zlength d)) eqn:ER.
  { apply mspecE_ret_ops. intros s mo tr H. cbn [fst snd evw map]. rewrite app_nil_r. auto. }
  apply orb_false_iff in ER. destruct ER as [E1 E2]. apply Z.ltb_ge in E1, E2. unfold ZL_MAX in *.
  assert (HN : NofL (zlength d) < 2^62) by (unfold NofL; lia).
  eapply mspecE_bind_ops; [apply (malloc_ops_E _ HK); exact HN|]. intros c0. apply mspecE_pure. intros Nc.
  eapply mspecE_bind_ops; [apply (malloc_ops_E _ HK); exact HN|]. intros u0. apply mspecE_pure. intros Nu.
  destruct c0 as [cp|]; [|contradiction]. destruct u0 as [up|]; [|contradiction].
  pose proof (test_deflate_E so tr0 (NofL (zlength d)) diff) as TD.
  destruct (test_large_deflate_pure za (NofL (zlength d))) as [[[comprc e] od] ended].
  eapply mspecE_bind_ops; [exact TD|]. intros [comprc' diff']. apply mspecE_pure. intros Erd. injection Erd. intros -> ->.
  eapply mspecE_bind_ops; [apply test_inflate_E|]. intro.
  set (tr1 := tr0 ++ evw 2 (dexitL_msg e) ++ evw 2 (test_large_inflate_msg za (NofL (zlength d)) comprc (match od with Some d0 => d0 | None => diff end))).
  pose proof (SoA_fstable Km so tr1 HKm) as HK'.
  rewrite <- app_assoc. fold tr1.
  eapply mspecE_bind_ops; [apply (free_ops_E _ HK')|]. intro. eapply mspecE_bind_ops; [apply (free_ops_E _ HK')|]. intro.
  apply mspecE_ret_ops. intros s mo tr H. cbn [fst snd]. subst tr1. rewrite evw_app. auto.
Qed.

End Out.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition so_after (j : nat) : stdout_st :=
  match j with O => stdout_init | S j' => mkStdout true (zeros_out j') false false end.
(* [comment removed for export] *)
Definition ev_after (Ms : list (list Z)) : list event :=
  match Ms with [] => [] | M1 :: Ms' => evw 2 M1 ++ evw 1 [48; 10] ++ concat (map (evw 2) Ms') end.

Lemma zlength_zeros_out : forall j, zlength (zeros_out j) = 2 * Z.of_nat j.
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S, zlen_app, IH. unfold zlength. cbn [length]. lia.
Qed.

Lemma zeros_out_app : forall j, zeros_out j ++ [48; 10] = zeros_out (S j).
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S. rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma Zdecimal_0 : Zdecimal 0 ++ [10] = [48; 10].
Proof. reflexivity. Qed.

Lemma ev_after_snoc : forall M1 Ms' M, ev_after ((M1 :: Ms') ++ [M]) = ev_after (M1 :: Ms') ++ evw 2 M.
Proof.
  intros M1 Ms' M. cbn [ev_after app]. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evws_call_chunks_cons : forall M1 Ms', evws (call_chunks (M1 :: Ms')) = ev_after (M1 :: Ms') ++ evw 1 (zeros_out (length Ms')).
Proof.
  intros M1 Ms'. cbn [call_chunks ev_after]. rewrite !evws_app, evws_map2. cbn [evws fst snd app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma harness_msgsL_from_length : forall size k d, length (harness_msgsL_from za size k d) = k.
Proof. intros size k. induction k as [|k IH]; intros d; cbn; [reflexivity|]. destruct (harness_callL za size d). cbn. f_equal. apply IH. Qed.

Lemma run_calls_E : forall Km d n Ms tr0 diff, Km_ok Km -> zlength d < 2^61 -> (length Ms + n <= 500)%nat ->
  mspecE sel X (SoA ps_so Km (so_after (length Ms)) (tr0 ++ ev_after Ms)) (run_callsL ops za d n 0 diff)
    (fun rc => fun s mo tr => SoA ps_so Km (so_after (length Ms + n)) (tr0 ++ ev_after (Ms ++ harness_msgsL_from za (zlength d) n diff)) s mo tr /\ rc = 0).
Proof.
  intros Km d n. induction n as [|n IH]; intros Ms tr0 diff HKm Hd Hj; cbn [run_callsL harness_msgsL_from].
  - apply mspecE_ret_ops. intros s mo tr H. rewrite Nat.add_0_r, app_nil_r. auto.
  - eapply mspecE_bind_ops; [apply (fuzz_one_E Km HKm); exact Hd|].
    destruct (harness_callL za (zlength d) diff) as [M diff'] eqn:EC. cbn [fst snd].
    intros [rc' d1]. apply mspecE_pure. intros E. injection E. intros -> ->. red_ops. rewrite Zdecimal_0. cbn [pieces_emit_of].
    eapply mspecE_seq with (R := SoA ps_so Km (so_after (S (length Ms))) (tr0 ++ ev_after (Ms ++ [M]))).
    + destruct Ms as [|M1 Ms'].
      * eapply mspecE_conseq; [apply (stdout_emit_first ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (tr0 ++ evw 2 M))| |].
        { intros s mo tr H. cbn [length so_after ev_after] in H. rewrite app_nil_r in H. exact H. }
        intros a s mo tr H. cbn [length so_after ev_after app map concat zeros_out]. rewrite app_nil_r. rewrite <- app_assoc in H. exact H.
      * eapply mspecE_conseq; [apply (stdout_emit_next ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (zeros_out (length Ms')) (tr0 ++ ev_after ((M1 :: Ms') ++ [M])))| |].
        { rewrite zlength_zeros_out. unfold STDOUT_BUFSIZ. cbn [length] in Hj. lia. }
        { intros s mo tr H. rewrite ev_after_snoc, app_assoc. exact H. }
        intros a s mo tr H. cbv beta in H. rewrite zeros_out_app in H. exact H.
    + intros _. eapply mspecE_conseq; [apply (IH (Ms ++ [M]) tr0 diff' HKm Hd); rewrite length_app; cbn [length]; lia| |].
      * intros s mo tr H. rewrite length_app. cbn [length]. rewrite Nat.add_1_r. exact H.
      * intros rc s mo tr [H ->]. split; [|reflexivity]. rewrite length_app in H. cbn [length] in H. rewrite <- app_assoc in H. cbn [app] in H.
        replace (length Ms + S n)%nat with (length Ms + 1 + n)%nat by lia. exact H.
Qed.

End TargetE.

Section PhaseE.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma calls_pos : forall cfg, (1 <= Z.to_nat (Z.land cfg 3 + 1) <= 4)%nat.
Proof.
  intros cfg. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound cfg (2^2) ltac:(lia)) as H. change (2^2) with 4 in *. lia.
Qed.

(* [comment removed for export] *)
Theorem target_run_E : forall Km cfg payload tr0, Km_ok Km -> zlength payload < 2^61 ->
  mspecE sel X (SoA ps_so Km stdout_init tr0) (Prog.run cfg payload)
    (fun rc s mo tr => SoA ps_so Km (so_after (Z.to_nat (Z.land cfg 3 + 1)))
                           (tr0 ++ ev_after (harness_msgs payload (Z.to_nat (Z.land cfg 3 + 1)))) s mo tr /\ rc = 0).
Proof.
  intros Km cfg payload tr0 HKm Hd. unfold Prog.run, Target.target_run, ZTargetL.target_runL, harness_msgs, harness_msgsL.
  pose proof (SoA_fstable Km stdout_init tr0 HKm) as HK0.
  set (ops := Target.ops raw_malloc raw_free ps_so set_so_ps).
  eapply mspecE_bind with (Q1 := fun a s mo tr => SoA ps_so Km stdout_init tr0 s mo tr /\ a <> None).
  - destruct (zlength payload =? 0).
    + cbn. apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
    + cbn. eapply mspecE_bind; [apply (malloc_ops_E sel X _ HK0); lia|].
      intros r. apply mspecE_pure. intros Hr. destruct r as [p|]; [|contradiction Hr; reflexivity].
      apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
  - intros [owned|]; [|apply mspecE_pure; intros []; reflexivity].
    apply mspecE_pure. intros _.
    destruct (calls_pos cfg) as [Hc1 Hc2]. destruct (Z.to_nat (Z.land cfg 3 + 1)) as [|n] eqn:En; [lia|].
    cbn -[run_callsL ev_after so_after harness_msgsL_from].
    eapply mspecE_bind.
    + eapply mspecE_conseq; [apply (run_calls_E sel X the_zapiL the_zapiL_ok Km payload (S n) [] tr0 0 HKm Hd); cbn [length]; lia| |].
      * intros s mo tr H. cbn [length so_after ev_after]. rewrite app_nil_r. exact H.
      * intros rc s mo tr H. exact H.
    + intros rc. apply mspecE_pure. intros ->. cbn [length Nat.add app].
      eapply mspecE_bind with (Q1 := fun _ => SoA ps_so Km (so_after (S n)) (tr0 ++ ev_after (harness_msgsL_from the_zapiL (zlength payload) (S n) 0))).
      * apply (free_ops_E sel X). apply SoA_fstable. exact HKm.
      * intros u. apply mspecE_ret. intros s mo tr H. auto.
Qed.

(* [comment removed for export] *)
Lemma evws_call_chunks_S : forall payload j,
  evws (call_chunks (harness_msgs payload (S j))) = ev_after (harness_msgs payload (S j)) ++ evw 1 (zeros_out j).
Proof.
  intros payload j. unfold harness_msgs, harness_msgsL. cbn [harness_msgsL_from].
  destruct (harness_callL the_zapiL (zlength payload) 0) as [M1 d1].
  rewrite evws_call_chunks_cons, (harness_msgsL_from_length the_zapiL). reflexivity.
Qed.

End PhaseE.
