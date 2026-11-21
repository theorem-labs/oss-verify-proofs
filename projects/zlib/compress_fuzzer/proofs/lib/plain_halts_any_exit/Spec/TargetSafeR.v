(** * TargetSafeR — compress_fuzzer's target model never reaches a leaf on a run where no allocation fails

    The issued binary is built without harness patch 02, so a failed check of [fuzz_oneC] is an [unreachable]
    leaf of the model ([ZTargetC.check_failM]) rather than a print and an exit.  The target is then no longer
    safe on EVERY run ([TargetSafe]'s logic): a refused allocation inside compress2 or uncompress2 breaks the
    round trip and the check fires.  It is safe on the runs [MSafeR] admits, where no [mmap] or [mprotect]
    answers -ENOMEM and so every allocation the model makes succeeds ([HdmR]), under the one hypothesis [NoCk]:
    the harness's checks never fail on the pure model ([ZHarnessC.harness_outC], the shape part C's
    [harness_no_ckfail_all] delivers).  On those runs the model's compress2 and uncompress2 compute exactly
    [c2_pure] and [u2_pure], the values [harness_outC] inspects, so a fired check would make
    [harness_outC d = HC_exit k].

    The shape follows [TargetSafe] (submission 5) for the ownership bookkeeping, submission 15's [TargetSafe]
    for the [mspecR] form, and [ProgDetTarget] for tracking the computed values. *)

From Stdlib Require Import ZArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad MSafe MSafeR Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL ZApiC ZHarnessC ZInstC ZTargetC Target TargetSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** The one hypothesis: the pure harness never exits through a failed check. *)
Definition NoCkFail : Prop := forall d k, harness_outC ZApiInstC.zinstC d <> HC_exit k.

(** Allocations below this size cannot overflow the allocator's size arithmetic. *)
Definition NMAX : Z := 2 ^ 62.

Section LeakR.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.

Lemma lown_frameR {A} (m : Monad.M St A) :
  (forall X, mspecR (own X) m (fun _ => own X)) -> forall X, mspecR (lown own X) m (fun _ => lown own X).
Proof.
  intros H X. unfold lown. apply mspecR_exI. intros Y. eapply mspecR_post; [apply H|].
  intros a s mo Ho. exists Y. exact Ho.
Qed.

Lemma lown_mallocR (raw_malloc : Z -> Monad.M St (option ptr)) :
  (forall X n, 0 <= n -> mspecR (own X) (raw_malloc n)
     (fun r s mo => match r with Some p => own (p :: X) s mo | None => NMAX <= n /\ own X s mo end)) ->
  forall X n, 0 <= n -> mspecR (lown own X) (raw_malloc n)
     (fun r s mo => match r with Some p => lown own (p :: X) s mo | None => NMAX <= n /\ lown own X s mo end).
Proof.
  intros H X n Hn. unfold lown. apply mspecR_exI. intros Y. eapply mspecR_post; [apply (H (Y ++ X) n Hn)|].
  intros [p|] s mo Ho.
  - exists Y. eapply Hperm; [|exact Ho]. apply Permutation_middle.
  - destruct Ho as [Hge Ho]. split; [exact Hge|]. exists Y. exact Ho.
Qed.

Lemma lown_freeR (raw_free : ptr -> Monad.M St unit) :
  (forall X p, mspecR (own (p :: X)) (raw_free p) (fun _ => own X)) ->
  forall X p, mspecR (lown own (p :: X)) (raw_free p) (fun _ => lown own X).
Proof.
  intros H X p. unfold lown. apply mspecR_exI. intros Y.
  eapply mspecR_conseq; [apply (H (Y ++ X) p)| |].
  - intros s mo Ho. eapply Hperm; [|exact Ho]. apply Permutation_sym, Permutation_middle.
  - intros a s mo Ho. exists Y. exact Ho.
Qed.
End LeakR.

Section TargetSafeR.
Context {St ptr : Type}.
Variable za : zapiC.
Hypothesis ZOK : zapiC_ok za.
Hypothesis NoCk : forall d k, harness_outC za d <> HC_exit k.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.

Variable own : list ptr -> assn St.

Hypothesis HdmR : forall X n, 0 <= n ->
  mspecR (own X) (raw_malloc n)
         (fun r s mo => match r with Some p => own (p :: X) s mo | None => NMAX <= n /\ own X s mo end).
Hypothesis Hdf : forall X p, mspecR (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hout : forall X, mspecR (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X).

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Let errp : list (list Z) -> Monad.M St unit := Target.err_pieces.
Let cbx : forall A : Type, Monad.M St A := Target.cb_exit get_so set_so.

Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store out_stderr_fw ops Target.ops lib_free_opt].

Lemma mspecR_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecR P (ret ops a) Q.
Proof. intros H. red_ops. apply mspecR_ret. exact H. Qed.

Lemma mspecR_bind_ops {A B} (m : Monad.M St A) (f : A -> Monad.M St B) P Q1 Q :
  mspecR P m Q1 -> (forall a, mspecR (Q1 a) (f a) Q) -> mspecR P (bind ops m f) Q.
Proof. intros H1 H2. red_ops. eapply mspecR_bind; eauto. Qed.

(** On these runs an allocation below [NMAX] always succeeds. *)
Lemma malloc_opsR : forall X n, 0 <= n < NMAX ->
  mspecR (own X) (lib_malloc ops n) (fun r s mo => match r with Some _ => own (optl r ++ X) s mo | None => False end).
Proof.
  intros X n Hn. red_ops. eapply mspecR_post; [apply (HdmR X n (proj1 Hn))|].
  intros [p|] s mo H; cbn [optl app]; [exact H | destruct H as [H _]; lia].
Qed.

Lemma free_opsR : forall X p, mspecR (own (optl p ++ X)) (lib_free ops p) (fun _ => own X).
Proof. intros X [p|]; red_ops; cbn [optl app]; [apply Hdf| apply mspecR_ret; auto]. Qed.

Lemma zsizesR : 0 <= zc_dstate za < NMAX /\ 0 <= zc_dwin za < NMAX /\ 0 <= zc_dprev za < NMAX
                /\ 0 <= zc_dhead za < NMAX /\ 0 <= zc_dpend za < NMAX /\ 0 <= zc_isize za < NMAX
                /\ 0 <= zc_wsize za < NMAX.
Proof.
  pose proof (zo_sizesC za ZOK) as H. unfold NMAX.
  repeat (match type of H with Forall _ (_ :: _) => let a := fresh "Ha" in let b := fresh "Hb" in inversion H as [|? ? a b]; subst; clear H; rename b into H end).
  repeat split; lia.
Qed.

Lemma deflate_init_R : forall X,
  mspecR (own X) (deflate_initC ops za)
         (fun r => match r with Some b => own (blk5 b ++ X) | None => fun _ _ => False end).
Proof.
  intros X. destruct zsizesR as (H1 & H2 & H3 & H4 & H5 & _). unfold deflate_initC.
  eapply mspecR_bind_ops; [apply malloc_opsR; exact H1|]. intros [sp|]; cbn [optl app];
    [| intros s mo []].
  eapply mspecR_bind_ops; [apply malloc_opsR; exact H2|]. intros [wp|];
    [| intros s mo []].
  eapply mspecR_bind_ops; [apply malloc_opsR; exact H3|]. intros [pp|];
    [| intros s mo []].
  eapply mspecR_bind_ops; [apply malloc_opsR; exact H4|]. intros [hp|];
    [| intros s mo []].
  eapply mspecR_bind_ops; [apply malloc_opsR; exact H5|]. intros [bp|];
    [| intros s mo []].
  apply mspecR_ret_ops. intros s mo H. exact H.
Qed.

Lemma deflate_end_R : forall X b, mspecR (own (blk5 b ++ X)) (deflate_endC ops b) (fun _ => own X).
Proof.
  intros X [[[[sp wp] pp] hp] bp]. unfold deflate_endC, blk5.
  eapply mspecR_bind_ops; [apply (free_opsR _ (Some bp))|]. intro.
  eapply mspecR_bind_ops; [apply (free_opsR _ (Some hp))|]. intro.
  eapply mspecR_bind_ops; [apply (free_opsR _ (Some pp))|]. intro.
  eapply mspecR_bind_ops; [apply (free_opsR _ (Some wp))|]. intro.
  apply (free_opsR X (Some sp)).
Qed.

(** compress2 computes [c2_pure]. *)
Lemma compress2_R : forall X N src level, 0 <= N <= ZBC_MAX -> zlength src <= ZBC_MAX ->
  Forall (fun b => 0 <= b < 256) src -> 0 <= level <= 9 ->
  mspecR (own X) (compress2M ops za N src level)
         (fun r s mo => own X s mo /\ c2_pure za N src level = Some r).
Proof.
  intros X N src level HN Hs Hb Hl. unfold compress2M.
  eapply mspecR_bind_ops; [apply deflate_init_R|]. intros [b|]; [| intros s mo []].
  pose proof (zo_c2C za ZOK N src level HN Hs Hb Hl) as NS.
  destruct (c2_pure za N src level) as [[[out tout] rc]|] eqn:EC; [| exfalso; exact (NS eq_refl)].
  eapply mspecR_bind_ops; [apply deflate_end_R|]. intro.
  apply mspecR_ret_ops. intros s mo H. split; [exact H| reflexivity].
Qed.

(** The inflate loop runs [u2_stepP true] (the window allocation never fails) until [u2_after] answers. *)
Lemma u2_loop_R : forall n x w X, u2_after za n x <> None ->
  mspecR (own (optl w ++ X)) (u2_loopM ops za n x w)
         (fun r s mo => own (optl (snd r) ++ X) s mo /\ u2_after za n x = Some (fst r)).
Proof.
  destruct zsizesR as (_ & _ & _ & _ & _ & _ & HW).
  induction n as [|f IH]; intros x w X NS; [exfalso; apply NS; reflexivity|].
  rewrite u2_after_S in NS. cbn [u2_loopM].
  assert (GRANTED : forall w0, mspecR (own (optl w0 ++ X))
             match u2_stepP za true x with
             | inl x' => u2_loopM ops za f x' w0
             | inr (Some (x', err)) => ret ops (x', err, w0)
             | inr None => unreachable ops
             end
             (fun r s mo => own (optl (snd r) ++ X) s mo
                            /\ match u2_stepP za true x with inl x' => u2_after za f x' | inr r => r end = Some (fst r))).
  { intros w0. destruct (u2_stepP za true x) as [x'|[[x' err]|]].
    - apply IH. exact NS.
    - apply mspecR_ret_ops. intros s mo H. split; [exact H| reflexivity].
    - exfalso. exact (NS eq_refl). }
  rewrite u2_after_S.
  destruct (u2_wants za x && match w with Some _ => false | None => true end) eqn:EW.
  - apply andb_true_iff in EW. destruct EW as [_ Ew]. destruct w as [q|]; [discriminate Ew|]. cbn [optl app].
    eapply mspecR_bind_ops; [apply malloc_opsR; exact HW|].
    intros [p|]; [| intros s mo []].
    exact (GRANTED (Some p)).
  - apply (mspecR_bind_ops _ _ _ (fun _ => own (optl w ++ X))); [apply mspecR_ret_ops; intros s mo H; exact H|].
    intros r. exact (GRANTED w).
Qed.

(** uncompress2 computes [u2_pure]. *)
Lemma uncompress2_R : forall X dlen src, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX ->
  Forall (fun b => 0 <= b < 256) src ->
  mspecR (own X) (uncompress2M ops za dlen src)
         (fun r s mo => own X s mo /\ u2_pure za dlen src = Some r).
Proof.
  intros X dlen src Hd Hs Hb. destruct zsizesR as (_ & _ & _ & _ & _ & HI & _). unfold uncompress2M.
  eapply mspecR_bind_ops; [apply malloc_opsR; exact HI|].
  intros [sp|]; [| intros s mo []]. cbn [optl app].
  pose proof (zo_u2C za ZOK dlen src Hd Hs Hb) as NS. unfold u2_pure in NS |- *. rewrite u2_loop_after in NS |- *.
  eapply mspecR_bind_ops.
  { apply (u2_loop_R _ _ None (sp :: X)). intros E. rewrite E in NS. exact (NS eq_refl). }
  intros [[x err] w]. apply mspecR_pure. cbn [fst snd]. intros EA. rewrite EA.
  destruct (u2_result za dlen x err) as [[out tout] rc] eqn:ER.
  eapply mspecR_bind_ops; [apply free_opsR|]. intro.
  eapply mspecR_bind_ops; [apply (free_opsR X (Some sp))|]. intro.
  apply mspecR_ret_ops. intros s mo H. split; [exact H| reflexivity].
Qed.

Lemma check_decompress_R : forall X data n cl cm flags, 0 < cl <= ZBC_MAX -> 0 <= n -> n + 2 <= ZBC_MAX ->
  zlength data = n -> Forall (fun b => 0 <= b < 256) data ->
  mspecR (own X) (check_decompressM ops za data n cl cm flags) (fun _ => own X).
Proof.
  intros X data n cl cm flags Hcl Hn Hn2 Hlen Hb. unfold check_decompressM.
  eapply mspecR_bind_ops; [apply malloc_opsR; unfold ZBC_MAX, ZC_MAX, NMAX in *; lia|].
  intros [kp|]; [| intros s mo []]. cbn [optl app].
  destruct (zhdr_bytes_ok cm flags) as [HB2 HL2].
  eapply mspecR_bind_ops.
  { eapply mspecR_post; [apply (uncompress2_R (kp :: X) cl _ Hcl)|].
    - unfold zlength in *. rewrite length_app. unfold zlength in HL2. lia.
    - apply Forall_app. split; [exact HB2| exact Hb].
    - intros r s mo [H _]. exact H. }
  intro. apply (free_opsR X (Some kp)).
Qed.

(** The two failed checks are exactly the inputs on which the pure harness exits. *)
Lemma harness_outC_ck1 : forall d cout clen rc1 uout ulen rc2,
  (zlength d <? ZC_MIN) || (ZC_MAX <? zlength d) = false ->
  c2_pure za (zc_bound za (zlength d - 3)) (zdrop 3 (norm8 d)) (sel_level (norm8 d)) = Some (cout, clen, rc1) ->
  u2_pure za (zlength d - 3) (norm8 cout) = Some (uout, ulen, rc2) ->
  negb (zlength d - 3 =? ulen) = true ->
  harness_outC za d = HC_exit CK1.
Proof.
  intros d cout clen rc1 uout ulen rc2 ER EC EU B1.
  unfold harness_outC, check_level_pure. cbv beta zeta. rewrite ER, EC. cbv beta iota. rewrite EU. cbv beta iota.
  rewrite B1. reflexivity.
Qed.

Lemma harness_outC_ck2 : forall d cout clen rc1 uout ulen rc2,
  (zlength d <? ZC_MIN) || (ZC_MAX <? zlength d) = false ->
  c2_pure za (zc_bound za (zlength d - 3)) (zdrop 3 (norm8 d)) (sel_level (norm8 d)) = Some (cout, clen, rc1) ->
  u2_pure za (zlength d - 3) (norm8 cout) = Some (uout, ulen, rc2) ->
  negb (zlength d - 3 =? ulen) = false ->
  negb (zlist_eqb (zdrop 3 (norm8 d)) (norm8 (bufC uout (zlength d - 3)))) = true ->
  harness_outC za d = HC_exit CK2.
Proof.
  intros d cout clen rc1 uout ulen rc2 ER EC EU B1 B2.
  unfold harness_outC, check_level_pure. cbv beta zeta. rewrite ER, EC. cbv beta iota. rewrite EU. cbv beta iota.
  rewrite B1, B2. reflexivity.
Qed.

(** One harness call: the two checks never fire, because the values they test are [harness_outC]'s. *)
Lemma fuzz_one_R : forall d X,
  mspecR (own X) (fuzz_oneC ops errp cbx za d) (fun r s mo => own X s mo /\ r = 0).
Proof.
  intros d X. unfold fuzz_oneC.
  destruct ((zlength d <? ZC_MIN) || (ZC_MAX <? zlength d)) eqn:ER; [apply mspecR_ret_ops; auto|].
  pose proof ER as ER0.
  apply orb_false_iff in ER. destruct ER as [E1 E2]. apply Z.ltb_ge in E1, E2. unfold ZC_MIN, ZC_MAX in E1, E2.
  set (d8 := norm8 d). set (data := zdrop 3 d8). set (n := zlength d - 3). set (cl := zc_bound za n).
  assert (Hn : 1 <= n <= ZC_MAX) by (unfold ZC_MAX; lia).
  pose proof (zo_boundC za ZOK n Hn) as HB. fold cl in HB.
  assert (Hdata : zlength data = n) by (subst data d8 n; rewrite zlength_zdrop; [rewrite norm8_length; reflexivity | rewrite norm8_length; lia]).
  assert (Hbytes : Forall (fun b => 0 <= b < 256) data) by (subst data; unfold zdrop; apply Forall_skipn_Z; apply norm8_bytes).
  unfold ZBC_MAX in *. unfold ZC_MAX in *.
  eapply mspecR_bind_ops; [apply malloc_opsR; unfold NMAX; lia|].
  intros [cp|]; [| intros s mo []]. cbn [optl app].
  eapply mspecR_bind_ops; [apply malloc_opsR; unfold NMAX; lia|].
  intros [up|]; [| intros s mo []]. cbn [optl app].
  eapply mspecR_bind_ops; [apply (compress2_R _ cl data (sel_level d8)); [unfold ZBC_MAX, ZC_MAX; lia | unfold ZBC_MAX, ZC_MAX; lia | exact Hbytes | apply sel_level_range]|].
  intros [[cout clen] crc]. apply mspecR_pure. cbn [fst snd]. intros EC.
  destruct (c2_pure_post za cl data (sel_level d8) cout clen crc EC) as [Hcl1 Hcl2].
  (* oss-fuzz #16582: on Z_MEM_ERROR from compress2 or uncompress the harness goes straight to check_decompress; the
     same tail ends the path where both checks pass. *)
  lazymatch goal with |- mspecR ?P (if _ then ?TL else _) ?Q => assert (TAIL : mspecR P TL Q) end.
  { eapply mspecR_bind_ops; [apply (check_decompress_R _ data n cl); [unfold ZBC_MAX, ZC_MAX; lia | lia | unfold ZBC_MAX, ZC_MAX; lia | exact Hdata | exact Hbytes]|]. intro.
    eapply mspecR_bind_ops; [eapply mspecR_pre; [apply (free_opsR (up :: X) (Some cp))|]|].
    { intros s mo H. cbn [optl app]. eapply Hperm; [apply perm_swap| exact H]. }
    intro. eapply mspecR_bind_ops; [apply (free_opsR X (Some up))|]. intro.
    apply mspecR_ret_ops. auto. }
  destruct (crc =? Z_MEM_ERROR); [exact TAIL|].
  eapply mspecR_bind_ops; [apply (uncompress2_R _ n (norm8 cout)); [unfold ZBC_MAX, ZC_MAX; lia | rewrite norm8_length; unfold ZBC_MAX, ZC_MAX; lia | apply norm8_bytes]|].
  intros [[uout ulen] urc]. apply mspecR_pure. cbn [fst snd]. intros EU.
  destruct (urc =? Z_MEM_ERROR); [exact TAIL|].
  destruct (negb (n =? ulen)) eqn:B1.
  { exfalso. exact (NoCk d CK1 (harness_outC_ck1 d cout clen crc uout ulen urc ER0 EC EU B1)). }
  destruct (negb (zlist_eqb data (norm8 (bufC uout n)))) eqn:B2.
  { exfalso. exact (NoCk d CK2 (harness_outC_ck2 d cout clen crc uout ulen urc ER0 EC EU B1 B2)). }
  exact TAIL.
Qed.

Lemma run_calls_R : forall d X n rc, rc = 0 ->
  mspecR (own X) (run_callsC ops errp cbx za d n rc) (fun rc' s mo => own X s mo /\ rc' = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc Hrc; cbn [run_callsC].
  - apply mspecR_ret_ops. intros s mo H. auto.
  - apply (mspecR_bind_ops _ _ _ (fun r s mo => own X s mo /\ r = 0)); [apply fuzz_one_R|].
    intros rc'. apply mspecR_pure. intros ->.
    apply (mspecR_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0. apply Hout.
    + intro. apply IH. reflexivity.
Qed.

End TargetSafeR.

Theorem target_run_mspecR {St ptr : Type}
  (raw_malloc : Z -> Monad.M St (option ptr)) (raw_free : ptr -> Monad.M St unit)
  (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) (own : list ptr -> assn St) :
  NoCkFail ->
  (forall X n, 0 <= n -> mspecR (own X) (raw_malloc n)
     (fun r s mo => match r with Some p => own (p :: X) s mo | None => NMAX <= n /\ own X s mo end)) ->
  (forall X p, mspecR (own (p :: X)) (raw_free p) (fun _ => own X)) ->
  (forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo) ->
  (forall X, mspecR (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X)) ->
  forall X cfg payload,
  mspecR (own X) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X).
Proof.
  intros NoCk Hdm Hdf Hperm Hout X cfg payload. unfold Target.target_run, ZTargetC.target_runC.
  set (ops := Target.ops raw_malloc raw_free get_so set_so).
  assert (NoCk' : forall d k, harness_outC the_zapiC d <> HC_exit k) by exact NoCk.
  pose proof (@run_calls_R St ptr the_zapiC the_zapiC_ok NoCk' raw_malloc raw_free get_so set_so own Hdm Hdf Hperm Hout) as RC.
  assert (zlen0 : 0 <= zlength payload) by (unfold zlength; lia).
  eapply mspecR_bind with (Q1 := fun a s mo => match a with
                                                | None => own X s mo
                                                | Some None => own X s mo
                                                | Some (Some p) => own (p :: X) s mo
                                                end).
  - destruct (zlength payload =? 0).
    + cbn. apply mspecR_ret. auto.
    + cbn. eapply mspecR_bind; [apply (Hdm X _ zlen0)|].
      intros [p|]; apply mspecR_ret; intros s mo H; [exact H| exact (proj2 H)].
  - intros [[p|]|]; [| |cbn; apply mspecR_ret; auto].
    + cbn -[run_callsC]. eapply mspecR_bind; [apply (RC payload (p :: X)); reflexivity|].
      intros rc. apply (mspecR_bind _ _ _ (fun _ => own X)); [eapply mspecR_pre; [apply Hdf|]; intros s mo H; exact (proj1 H)|].
      intros u. apply mspecR_ret. auto.
    + cbn -[run_callsC]. eapply mspecR_bind; [apply (RC payload X); reflexivity|].
      intros rc. apply (mspecR_bind _ _ _ (fun _ => own X)); [apply mspecR_ret; intros s mo H; exact (proj1 H)|].
      intros u. apply mspecR_ret. auto.
Qed.
