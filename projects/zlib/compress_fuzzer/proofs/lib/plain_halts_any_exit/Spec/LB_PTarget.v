(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad MSafe Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL ZApiC ZHarnessC ZInstC ZTargetC Target Driver LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition szsum {ptr : Type} (X : list (ptr * Z)) : Z := fold_right (fun xb a => snd xb + a) 0 X.
Definition nonnegX {ptr : Type} (X : list (ptr * Z)) : Prop := Forall (fun xb => 0 <= snd xb) X.

Lemma szsum_app {ptr : Type} (X Y : list (ptr * Z)) : szsum (X ++ Y) = szsum X + szsum Y.
Proof. unfold szsum. induction X as [|x X IH]; cbn [fold_right app]; [reflexivity|]. rewrite IH. ring. Qed.
Lemma nonnegX_app {ptr : Type} (X Y : list (ptr * Z)) : nonnegX X -> nonnegX Y -> nonnegX (X ++ Y).
Proof. intros; unfold nonnegX in *; apply Forall_app; auto. Qed.

Definition SUMMAX : Z := 2 * (MAX_INPUT + 1) + 14 * (2 * ZH_MAX).

Section TargetL.
Context {St ptr : Type}.
Variable B : Z.
Variable za : zapiC.
Hypothesis ZOK : zapiC_ok za.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list (ptr * Z) -> assn St.
Variable mal_ok : list (ptr * Z) -> Z -> Prop.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Herr : forall X ps, mspecL B (own X) (stderr_fprintf (St:=St) ps) (fun _ => own X).
Hypothesis Hfw : forall X bs, mspecL B (own X) (stderr_fwrite (St:=St) bs) (fun _ => own X).
Hypothesis Hout : forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X).

Hypothesis Hflush : forall X, mspecL B (own X) (stdout_exit_flush get_so set_so) (fun _ => own X).

Hypothesis OK_tgt : forall X n, (length X <= 15)%nat -> nonnegX X -> szsum X <= SUMMAX -> 0 <= n <= MAX_INPUT + 1 -> mal_ok X n.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Let errp : list (list Z) -> Monad.M St unit := Target.err_pieces.
Let cbx : forall A : Type, Monad.M St A := Target.cb_exit get_so set_so.
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store out_stderr_fw ops Target.ops lib_free_opt].

Definition lownL (c : nat) (w : Z) (X : list (ptr * Z)) : assn St :=
  fun s mo => exists Y, own (Y ++ X) s mo /\ (length Y <= c)%nat /\ szsum Y <= w /\ nonnegX Y.

Definition fits (c : nat) (w : Z) (X : list (ptr * Z)) : Prop :=
  (length X + c <= 15)%nat /\ nonnegX X /\ szsum X + w <= SUMMAX.

Definition optz (r : option ptr) (n : Z) : list (ptr * Z) := match r with Some p => [(p, n)] | None => [] end.

Lemma lownL_perm : forall c w X X' s mo, Permutation X X' -> lownL c w X s mo -> lownL c w X' s mo.
Proof. intros c w X X' s mo HP (Y & H & R). exists Y. split; [|exact R]. eapply Hperm; [|exact H]. apply Permutation_app_head. exact HP. Qed.

Lemma lownL_frame {A} (m : Monad.M St A) : (forall X, mspecL B (own X) m (fun _ => own X)) ->
  forall c w X, mspecL B (lownL c w X) m (fun _ => lownL c w X).
Proof.
  intros H c w X. unfold lownL. apply mspecL_exI. intros Y. apply mspecL_pure. intros R.
  eapply mspecL_post; [apply H|]. intros a s mo Ho. exists Y. split; [exact Ho| exact R].
Qed.

Lemma malloc_L : forall c w X n, fits c w X -> 0 <= n <= MAX_INPUT + 1 ->
  mspecL B (lownL c w X) (lib_malloc ops n) (fun r => lownL c w (optz r n ++ X)).
Proof.
  intros c w X n (F1 & F2 & F3) Hn. red_ops. unfold lownL. apply mspecL_exI. intros Y. apply mspecL_pure. intros (R1 & R2 & R3).
  eapply mspecL_conseq; [apply (Hdm (Y ++ X) n); lia| |].
  - intros s mo H. split; [exact H|]. apply OK_tgt; [rewrite length_app; lia| apply nonnegX_app; assumption| rewrite szsum_app; lia| exact Hn].
  - intros [p|] s mo H; cbn [optz app].
    + exists Y. split; [|auto]. eapply Hperm; [|exact (proj1 H)]. apply Permutation_middle.
    + exists Y. auto.
Qed.

Lemma free_L : forall c w X p n, mspecL B (lownL c w ((p, n) :: X)) (lib_free ops (Some p)) (fun _ => lownL c w X).
Proof.
  intros c w X p n. red_ops. unfold lownL. apply mspecL_exI. intros Y. apply mspecL_pure. intros R.
  eapply mspecL_conseq; [apply (Hdf (Y ++ X) p n)| |].
  - intros s mo H. eapply Hperm; [|exact H]. apply Permutation_sym, Permutation_middle.
  - intros a s mo H. exists Y. auto.
Qed.

Lemma free_opt_L : forall c w X r n, mspecL B (lownL c w (optz r n ++ X)) (lib_free ops r) (fun _ => lownL c w X).
Proof. intros c w X [p|] n; cbn [optz app]; [apply free_L|]. red_ops. apply mspecL_ret. auto. Qed.

Lemma mspecL_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL B P (ret ops a) Q.
Proof. intros H. red_ops. apply mspecL_ret. exact H. Qed.
Lemma mspecL_bind_ops {A C} (m : Monad.M St A) (f : A -> Monad.M St C) P Q1 Q :
  mspecL B P m Q1 -> (forall a, mspecL B (Q1 a) (f a) Q) -> mspecL B P (bind ops m f) Q.
Proof. intros H1 H2. red_ops. eapply mspecL_bind; eauto. Qed.

Lemma check_fail_L {A} : forall c w X k (Q : A -> assn St), mspecL B (lownL c w X) (check_failM ops errp cbx k) Q.
Proof using Herr Hflush.
  (* a failed check is an unreachable leaf of the issued build's model ([ZTargetC.check_failM]); [Herr] and
     [Hflush], which the print-and-exit of the patched build needed, stay among the section variables so the
     lemmas above it keep their arguments *)
  intros c w X k Q. unfold check_failM. cbv zeta. red_ops. apply mspecL_munr.
Qed.

Lemma zsizesL : 0 < zc_dstate za <= ZH_MAX /\ 0 < zc_dwin za <= ZH_MAX /\ 0 < zc_dprev za <= ZH_MAX /\ 0 < zc_dhead za <= ZH_MAX
                /\ 0 < zc_dpend za <= ZH_MAX /\ 0 < zc_isize za <= ZH_MAX /\ 0 < zc_wsize za <= ZH_MAX.
Proof.
  pose proof (zo_sizesC za ZOK) as H.
  repeat (match type of H with Forall _ (_ :: _) => let a := fresh "Ha" in let b := fresh "Hb" in inversion H as [|? ? a b]; subst; clear H; rename b into H end).
  unfold ZH_MAX. repeat split; lia.
Qed.

Section Call.
Variable X : list (ptr * Z).
Variables (c : nat) (w : Z).

Hypothesis FX : (length X + c <= 8)%nat /\ nonnegX X /\ szsum X + w + 5 * (2 * ZH_MAX) <= SUMMAX.

Lemma fitsX : forall L, (length L <= 7)%nat -> nonnegX L -> szsum L <= 5 * (2 * ZH_MAX) -> fits c w (L ++ X).
Proof.
  intros L H1 H2 H3. destruct FX as (F1 & F2 & F3). unfold fits. rewrite length_app, szsum_app.
  split; [lia|]. split; [apply nonnegX_app; assumption| lia].
Qed.

Definition blk5z (b : ptr * ptr * ptr * ptr * ptr) : list (ptr * Z) :=
  let '(sp, wp, pp, hp, bp) := b in
  [(bp, zc_dpend za); (hp, zc_dhead za); (pp, zc_dprev za); (wp, zc_dwin za); (sp, zc_dstate za)].

Lemma step_E : forall (r : option ptr) n (E : list (ptr * Z)) (k : nat) W, 0 <= n -> (length E <= k)%nat -> nonnegX E -> szsum E <= W ->
  (length (optz r n ++ E) <= S k)%nat /\ nonnegX (optz r n ++ E) /\ szsum (optz r n ++ E) <= W + n.
Proof.
  intros r n E k W Hn H1 H2 H3. rewrite length_app, szsum_app. destruct r; cbn [optz length szsum fold_right snd].
  - split; [lia|]. split; [apply nonnegX_app; [repeat constructor; cbn; lia| exact H2]| lia].
  - split; [lia|]. split; [exact H2| lia].
Qed.

Lemma deflate_init_L : forall L, (length L <= 2)%nat -> nonnegX L -> szsum L <= 3 * ZH_MAX ->
  mspecL B (lownL c w (L ++ X)) (deflate_initC ops za)
         (fun r => match r with Some b => lownL c w (blk5z b ++ L ++ X) | None => lownL c w (L ++ X) end).
Proof.
  intros L HL1 HL2 HL3. destruct zsizesL as (H1 & H2 & H3 & H4 & H5 & _). unfold deflate_initC.
  assert (MX : ZH_MAX <= MAX_INPUT + 1) by (unfold ZH_MAX, MAX_INPUT; lia).
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact HL2| unfold ZH_MAX in *; lia]| lia]|].
  intros [sp|]; [|cbn [optz app]; apply mspecL_ret_ops; auto].
  destruct (step_E (Some sp) (zc_dstate za) L 2 _ ltac:(lia) HL1 HL2 HL3) as (A1 & A2 & A3).
  rewrite app_assoc. set (E1 := optz (Some sp) (zc_dstate za) ++ L) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact A2| unfold ZH_MAX in *; lia]| lia]|]. intros wr.
  destruct (step_E wr (zc_dwin za) E1 3 _ ltac:(lia) A1 A2 A3) as (B1 & B2 & B3).
  rewrite app_assoc. set (E2 := optz wr (zc_dwin za) ++ E1) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact B2| unfold ZH_MAX in *; lia]| lia]|]. intros pr.
  destruct (step_E pr (zc_dprev za) E2 4 _ ltac:(lia) B1 B2 B3) as (C1 & C2 & C3).
  rewrite app_assoc. set (E3 := optz pr (zc_dprev za) ++ E2) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact C2| unfold ZH_MAX in *; lia]| lia]|]. intros hr.
  destruct (step_E hr (zc_dhead za) E3 5 _ ltac:(lia) C1 C2 C3) as (D1 & D2 & D3).
  rewrite app_assoc. set (E4 := optz hr (zc_dhead za) ++ E3) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact D2| unfold ZH_MAX in *; lia]| lia]|]. intros br.
  subst E4 E3 E2 E1. rewrite <- !app_assoc.
  assert (FAIL : mspecL B (lownL c w (optz br (zc_dpend za) ++ optz hr (zc_dhead za) ++ optz pr (zc_dprev za) ++ optz wr (zc_dwin za) ++ optz (Some sp) (zc_dstate za) ++ L ++ X))
                        (bind ops (lib_free ops br) (fun _ => bind ops (lib_free ops hr) (fun _ => bind ops (lib_free ops pr) (fun _ =>
                         bind ops (lib_free ops wr) (fun _ => bind ops (lib_free ops (Some sp)) (fun _ => ret ops None))))))
                        (fun r => match r with Some b => lownL c w (blk5z b ++ L ++ X) | None => lownL c w (L ++ X) end)).
  { eapply mspecL_bind_ops; [apply free_opt_L|]. intro.
    eapply mspecL_bind_ops; [apply free_opt_L|]. intro.
    eapply mspecL_bind_ops; [apply free_opt_L|]. intro.
    eapply mspecL_bind_ops; [apply free_opt_L|]. intro.
    eapply mspecL_bind_ops; [apply free_opt_L|]. intro. apply mspecL_ret_ops. auto. }
  destruct wr as [wp|]; [|exact FAIL]. destruct pr as [pp|]; [|exact FAIL]. destruct hr as [hp|]; [|exact FAIL].
  destruct br as [bp|]; [|exact FAIL].
  apply mspecL_ret_ops. intros s mo H. exact H.
Qed.

Lemma deflate_end_L : forall L b, mspecL B (lownL c w (blk5z b ++ L)) (deflate_endC ops b) (fun _ => lownL c w L).
Proof.
  intros L [[[[sp wp] pp] hp] bp]. unfold deflate_endC, blk5z. cbn [app].
  eapply mspecL_bind_ops; [apply free_L|]. intro. eapply mspecL_bind_ops; [apply free_L|]. intro.
  eapply mspecL_bind_ops; [apply free_L|]. intro. eapply mspecL_bind_ops; [apply free_L|]. intro. apply free_L.
Qed.

Lemma compress2_L : forall L N src level, (length L <= 2)%nat -> nonnegX L -> szsum L <= 3 * ZH_MAX ->
  mspecL B (lownL c w (L ++ X)) (compress2M ops za N src level) (fun _ => lownL c w (L ++ X)).
Proof.
  intros L N src level HL1 HL2 HL3. unfold compress2M.
  eapply mspecL_bind_ops; [apply deflate_init_L; assumption|]. intros [b|].
  - destruct (c2_pure za N src level) as [[[out tout] rc]|]; [|red_ops; apply mspecL_munr].
    eapply mspecL_bind_ops; [apply deflate_end_L|]. intro. apply mspecL_ret_ops. auto.
  - apply mspecL_ret_ops. auto.
Qed.

Lemma u2_loop_L : forall n x wr L, (length L <= 4)%nat -> nonnegX L -> szsum L <= 7 * ZH_MAX ->
  mspecL B (lownL c w (optz wr (zc_wsize za) ++ L ++ X)) (u2_loopM ops za n x wr)
         (fun r => lownL c w (optz (snd r) (zc_wsize za) ++ L ++ X)).
Proof.
  destruct zsizesL as (_ & _ & _ & _ & _ & _ & HW).
  assert (MX : ZH_MAX <= MAX_INPUT + 1) by (unfold ZH_MAX, MAX_INPUT; lia).
  induction n as [|f IH]; intros x wr L HL1 HL2 HL3; cbn [u2_loopM]; [red_ops; apply mspecL_munr|].
  assert (STEP : forall w0 ok, mspecL B (lownL c w (optz w0 (zc_wsize za) ++ L ++ X))
            match u2_stepP za ok x with
            | inl x' => u2_loopM ops za f x' w0
            | inr (Some (x', err)) => ret ops (x', err, w0)
            | inr None => unreachable ops
            end (fun r => lownL c w (optz (snd r) (zc_wsize za) ++ L ++ X))).
  { intros w0 ok. destruct (u2_stepP za ok x) as [x'|[[x' err]|]]; [apply IH; assumption | apply mspecL_ret_ops; intros s mo H; exact H | red_ops; apply mspecL_munr]. }
  destruct (u2_wants za x && match wr with Some _ => false | None => true end) eqn:EW.
  - apply andb_true_iff in EW. destruct EW as [_ Ew]. destruct wr as [q|]; [discriminate Ew|]. cbn [optz app].
    eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact HL2| unfold ZH_MAX in *; lia]| lia]|].
    intros r. exact (STEP r _).
  - apply (mspecL_bind_ops _ _ _ (fun _ => lownL c w (optz wr (zc_wsize za) ++ L ++ X))); [apply mspecL_ret_ops; intros s mo H; exact H|]. intros r. exact (STEP wr true).
Qed.

Lemma uncompress2_L : forall L dlen src, (length L <= 3)%nat -> nonnegX L -> szsum L <= 6 * ZH_MAX ->
  mspecL B (lownL c w (L ++ X)) (uncompress2M ops za dlen src) (fun _ => lownL c w (L ++ X)).
Proof.
  intros L dlen src HL1 HL2 HL3. destruct zsizesL as (_ & _ & _ & _ & _ & HI & _). unfold uncompress2M.
  assert (MX : ZH_MAX <= MAX_INPUT + 1) by (unfold ZH_MAX, MAX_INPUT; lia).
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact HL2| unfold ZH_MAX in *; lia]| lia]|].
  intros [sp|]; cbn [optz app]; [| apply mspecL_ret_ops; auto].
  eapply mspecL_bind_ops.
  { rewrite app_comm_cons. apply (u2_loop_L _ _ None ((sp, zc_isize za) :: L)); [cbn; lia | constructor; [cbn; lia| exact HL2] | cbn [szsum fold_right snd]; fold (@szsum ptr L); lia]. }
  intros [[x err] w']. cbn [snd]. destruct (u2_result za dlen x err) as [[out tout] rc].
  eapply mspecL_bind_ops; [apply free_opt_L|]. intro. cbn [app].
  eapply mspecL_bind_ops; [apply free_L|]. intro. apply mspecL_ret_ops. auto.
Qed.

Lemma fuzz_one_L : forall d,
  mspecL B (lownL c w X) (fuzz_oneC ops errp cbx za d) (fun rc s mo => lownL c w X s mo /\ rc = 0).
Proof.
  intros d. unfold fuzz_oneC.
  destruct ((zlength d <? ZC_MIN) || (ZC_MAX <? zlength d)) eqn:ER.
  { apply mspecL_ret_ops. intros s mo H. auto. }
  apply orb_false_iff in ER. destruct ER as [E1 E2]. apply Z.ltb_ge in E1, E2. unfold ZC_MIN, ZC_MAX in E1, E2.
  set (d8 := norm8 d). set (data := zdrop 3 d8). set (n := zlength d - 3). set (cl := zc_bound za n).
  pose proof (zo_boundC za ZOK n ltac:(unfold ZC_MAX; lia)) as Hcl. fold cl in Hcl. unfold ZBC_MAX, ZC_MAX in Hcl.
  assert (MX : 2 * ZH_MAX <= MAX_INPUT + 1) by (unfold ZH_MAX, MAX_INPUT; lia).
  eapply mspecL_bind_ops; [apply (malloc_L c w X cl); [apply (fitsX []); [cbn; lia| constructor| cbn; unfold ZH_MAX; lia]| unfold ZH_MAX in *; lia]|].
  intros [cp|]; cbn [optz app]; [| apply mspecL_ret_ops; intros s mo H; auto].
  eapply mspecL_bind_ops.
  { apply (malloc_L c w ((cp, cl) :: X) n); [| unfold ZH_MAX in *; lia].
    apply (fitsX [(cp, cl)]); [cbn; lia| repeat constructor; cbn; unfold ZH_MAX in *; lia| cbn [szsum fold_right snd]; unfold ZH_MAX in *; lia]. }
  intros [up|]; cbn [optz app].
  2:{ eapply mspecL_bind_ops; [apply free_L|]. intro. apply mspecL_ret_ops. intros s mo H. auto. }
  assert (L1 : (length [(up, n); (cp, cl)] <= 2)%nat) by (cbn; lia).
  assert (L2 : nonnegX [(up, n); (cp, cl)]) by (repeat constructor; cbn; unfold ZH_MAX in *; lia).
  assert (L3 : szsum [(up, n); (cp, cl)] <= 3 * ZH_MAX) by (cbn [szsum fold_right snd]; unfold ZH_MAX in *; lia).
  eapply mspecL_bind_ops; [apply (compress2_L [(up, n); (cp, cl)] _ _ _ L1 L2 L3)|]. intros [[cout clen] crc].
  (* oss-fuzz #16582: the check_decompress tail ends three paths (Z_MEM_ERROR from compress2, from uncompress, and
     both checks passed). *)
  lazymatch goal with |- mspecL ?B' ?P (if _ then ?TL else _) ?Q => assert (TAIL : mspecL B' P TL Q) end.
  { unfold check_decompressM.
    eapply mspecL_bind_ops with (Q1 := fun _ => lownL c w ([(up, n); (cp, cl)] ++ X)).
    { eapply mspecL_bind_ops.
      { apply (malloc_L c w ([(up, n); (cp, cl)] ++ X) (n + 2)); [| unfold ZH_MAX in *; lia]. apply fitsX; [cbn; lia | exact L2 | unfold ZH_MAX in *; lia]. }
      intros [kp|]; cbn [optz app]; [| apply mspecL_ret_ops; intros s mo H; exact H].
      eapply mspecL_bind_ops.
      { apply (uncompress2_L [(kp, n + 2); (up, n); (cp, cl)]); [cbn; lia | constructor; [cbn; unfold ZH_MAX in *; lia| exact L2] | cbn [szsum fold_right snd] in *; unfold ZH_MAX in *; lia]. }
      intros u1. cbn [app]. apply free_L. }
    intros u2. cbn [app].
    eapply mspecL_bind_ops; [eapply mspecL_pre; [apply (free_L c w ((up, n) :: X) cp cl)|]|].
    { intros s mo H. eapply lownL_perm; [apply perm_swap| exact H]. }
    intro. eapply mspecL_bind_ops; [apply free_L|]. intro.
    apply mspecL_ret_ops. auto. }
  destruct (crc =? Z_MEM_ERROR); [exact TAIL|].
  eapply mspecL_bind_ops; [apply (uncompress2_L [(up, n); (cp, cl)] _ _ ltac:(cbn; lia) L2 ltac:(unfold ZH_MAX in *; lia))|]. intros [[uout ulen] urc].
  destruct (urc =? Z_MEM_ERROR); [exact TAIL|].
  destruct (negb (n =? ulen)); [apply check_fail_L|].
  destruct (negb (zlist_eqb data (norm8 (bufC uout n)))); [apply check_fail_L|].
  exact TAIL.
Qed.
End Call.

Lemma run_calls_L : forall X d n rc, (length X <= 2)%nat -> nonnegX X -> szsum X <= 2 * (MAX_INPUT + 1) -> rc = 0 ->
  mspecL B (lownL 0 0 X) (run_callsC ops errp cbx za d n rc) (fun rc' s mo => lownL 0 0 X s mo /\ rc' = 0).
Proof.
  intros X d n. induction n as [|n IH]; intros rc HX1 HX2 HX3 Hrc; cbn [run_callsC].
  - apply mspecL_ret_ops. intros s mo H. auto.
  - eapply mspecL_bind_ops.
    { apply (fuzz_one_L X 0%nat 0). split; [lia|]. split; [exact HX2|]. unfold SUMMAX, ZH_MAX, MAX_INPUT in *. lia. }
    intros rc'. apply mspecL_pure. intros ->.
    eapply mspecL_bind_ops; [red_ops; apply (lownL_frame _ (fun X' => Hout X' _))|]. intro.
    apply IH; [exact HX1 | exact HX2 | exact HX3 | reflexivity].
Qed.
End TargetL.

Theorem target_run_L {St ptr : Type} (B : Z)
  (raw_malloc : Z -> Monad.M St (option ptr)) (raw_free : ptr -> Monad.M St unit)
  (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St)
  (own : list (ptr * Z) -> assn St) (mal_ok : list (ptr * Z) -> Z -> Prop) :
  (forall X n, 0 <= n ->
     mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
            (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end)) ->
  (forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X)) ->
  (forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo) ->
  (forall X ps, mspecL B (own X) (stderr_fprintf (St:=St) ps) (fun _ => own X)) ->
  (forall X bs, mspecL B (own X) (stderr_fwrite (St:=St) bs) (fun _ => own X)) ->
  (forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X)) ->
  (forall X, mspecL B (own X) (stdout_exit_flush get_so set_so) (fun _ => own X)) ->
  (forall X n, (length X <= 15)%nat -> nonnegX X -> szsum X <= SUMMAX -> 0 <= n <= MAX_INPUT + 1 -> mal_ok X n) ->
  forall X0 cfg payload, (length X0 <= 1)%nat -> nonnegX X0 -> szsum X0 <= MAX_INPUT + 1 -> zlength payload <= MAX_INPUT ->
  mspecL B (own X0) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ s mo => exists Y, own (Y ++ X0) s mo).
Proof.
  intros Hdm Hdf Hperm Herr Hfw Hout Hflush OK X0 cfg payload HX1 HX2 HX3 Hpl.
  unfold Target.target_run, ZTargetC.target_runC.
  pose proof (@run_calls_L St ptr B the_zapiC the_zapiC_ok raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm Herr Hout Hflush OK) as RC.
  assert (Hpl0 : 0 <= zlength payload) by (unfold zlength; lia).
  set (lo := @lownL St ptr own).
  assert (IN : forall X s mo, own X s mo -> lo 0%nat 0 X s mo) by (intros X s mo H; exists []; repeat split; [exact H| cbn; lia| cbn; lia| constructor]).
  assert (OUT : forall c w X s mo, lo c w X s mo -> exists Y, own (Y ++ X) s mo) by (intros c w X s mo (Y & H & _); exists Y; exact H).
  eapply mspecL_bind with (Q1 := fun a s mo => match a with
                                                | None => own X0 s mo
                                                | Some None => own X0 s mo
                                                | Some (Some p) => own ((p, zlength payload) :: X0) s mo
                                                end).
  - destruct (zlength payload =? 0).
    + cbn. apply mspecL_ret. auto.
    + cbn. eapply mspecL_bind.
      * eapply mspecL_conseq; [apply (Hdm X0 (zlength payload) Hpl0)| |intros r s mo H; exact H].
        intros s mo H. split; [exact H|]. apply OK; [lia| exact HX2| unfold SUMMAX, MAX_INPUT, ZH_MAX in *; lia| unfold MAX_INPUT in *; lia].
      * intros [p|]; apply mspecL_ret; intros s mo H; [exact (proj1 H)| exact H].
  - intros [[p|]|]; [| |cbn; apply mspecL_ret; intros s mo H; exists []; exact H].
    + cbn -[run_callsC MAX_INPUT].
      eapply mspecL_bind.
      { eapply mspecL_conseq; [apply (RC ((p, zlength payload) :: X0) payload (Z.to_nat (Z.land cfg 3 + 1)) 0)| |intros r s mo H; exact H].
        - cbn [length]; lia. - constructor; [cbn; lia| exact HX2]. - cbn [szsum fold_right snd]. fold (@szsum ptr X0). lia. - reflexivity.
        - intros s mo H. apply IN. exact H. }
      intros rc. apply mspecL_pure. intros _.
      eapply mspecL_bind; [eapply (free_L B raw_malloc raw_free get_so set_so own Hdf Hperm)|].
      intros u. apply mspecL_ret. intros s mo H. eapply OUT. exact H.
    + cbn -[run_callsC MAX_INPUT].
      eapply mspecL_bind.
      { eapply mspecL_conseq; [apply (RC X0 payload (Z.to_nat (Z.land cfg 3 + 1)) 0)| |intros r s mo H; exact H].
        - lia. - exact HX2. - lia. - reflexivity.
        - intros s mo H. apply IN. exact H. }
      intros rc. apply mspecL_pure. intros _.
      eapply (mspecL_bind B _ _ _ (fun _ => @lownL St ptr own _ _ X0)); [apply mspecL_ret; intros s mo H; exact H|].
      intros u. apply mspecL_ret. intros s mo H. eapply OUT. exact H.
Qed.
