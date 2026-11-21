(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad MSafe Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTargetL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Driver. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition szsum {ptr : Type} (X : list (ptr * Z)) : Z := fold_right (fun xb a => snd xb + a) 0 X.
Definition nonnegX {ptr : Type} (X : list (ptr * Z)) : Prop := Forall (fun xb => 0 <= snd xb) X.

Lemma szsum_app {ptr : Type} (X Y : list (ptr * Z)) : szsum (X ++ Y) = szsum X + szsum Y.
Proof. unfold szsum. induction X as [|x X IH]; cbn [fold_right app]; [reflexivity|]. rewrite IH. ring. Qed.
Lemma nonnegX_app {ptr : Type} (X Y : list (ptr * Z)) : nonnegX X -> nonnegX Y -> nonnegX (X ++ Y).
Proof. intros; unfold nonnegX in *; apply Forall_app; auto. Qed.

(* [comment removed for export] *)
Definition U : Z := 2 * ZH_MAX.
(* [comment removed for export] *)
Definition SUMMAX : Z := 2 * (MAX_INPUT + 1) + 7 * (2 * ZH_MAX).

Section TargetL.
Context {St ptr : Type}.
Variable B : Z.
Variable za : zapiL.
Hypothesis ZOK : zapiL_ok za.
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
(* [comment removed for export] *)
Hypothesis OK_tgt : forall X n, (length X <= 31)%nat -> nonnegX X -> szsum X <= SUMMAX -> 0 <= n <= MAX_INPUT + 1 -> mal_ok X n.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store out_stderr_fw ops Target.ops lib_free_opt].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lownL (c : nat) (w : Z) (X : list (ptr * Z)) : assn St :=
  fun s mo => exists Y, own (Y ++ X) s mo /\ (length Y <= c)%nat /\ szsum Y <= w /\ nonnegX Y.

(* [comment removed for export] *)
Definition fits (c : nat) (w : Z) (X : list (ptr * Z)) : Prop :=
  (length X + c <= 31)%nat /\ nonnegX X /\ szsum X + w <= SUMMAX.

Definition optz (r : option ptr) (n : Z) : list (ptr * Z) := match r with Some p => [(p, n)] | None => [] end.

Lemma lownL_weaken : forall c w c' w' X s mo, (c <= c')%nat -> w <= w' -> lownL c w X s mo -> lownL c' w' X s mo.
Proof. intros c w c' w' X s mo Hc Hw (Y & H & H1 & H2 & H3). exists Y. repeat split; [exact H| lia| lia| exact H3]. Qed.

Lemma lownL_perm : forall c w X X' s mo, Permutation X X' -> lownL c w X s mo -> lownL c w X' s mo.
Proof. intros c w X X' s mo HP (Y & H & R). exists Y. split; [|exact R]. eapply Hperm; [|exact H]. apply Permutation_app_head. exact HP. Qed.

(* [comment removed for export] *)
Lemma lownL_leak : forall c w p n X s mo, 0 <= n -> lownL c w ((p, n) :: X) s mo -> lownL (S c) (w + n) X s mo.
Proof.
  intros c w p n X s mo Hn (Y & H & H1 & H2 & H3). exists (Y ++ [(p, n)]). rewrite <- app_assoc. cbn [app].
  split; [exact H|]. split; [rewrite length_app; cbn [length]; lia|]. split; [rewrite szsum_app; cbn [szsum fold_right snd]; lia|].
  apply nonnegX_app; [exact H3| constructor; [exact Hn| constructor]].
Qed.

(* [comment removed for export] *)
Lemma lownL_leak_list : forall L c w X s mo, nonnegX L -> lownL c w (L ++ X) s mo -> lownL (c + length L) (w + szsum L) X s mo.
Proof.
  induction L as [|[p n] L IH]; intros c w X s mo HL H.
  - cbn [length szsum fold_right app] in *. eapply lownL_weaken; [| |exact H]; lia.
  - inversion HL as [|x l Hn HL']; subst. cbn [app] in H. apply lownL_leak in H; [|exact Hn].
    pose proof (IH (S c) (w + n) X s mo HL' H) as H'. cbn [length]. unfold szsum. cbn [fold_right snd]. fold (@szsum ptr L).
    eapply lownL_weaken; [| |exact H']; [lia|]. unfold szsum. lia.
Qed.

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

(* [comment removed for export] *)
Lemma free_opt_L : forall c w X r n, mspecL B (lownL c w (optz r n ++ X)) (lib_free ops r) (fun _ => lownL c w X).
Proof. intros c w X [p|] n; cbn [optz app]; [apply free_L|]. red_ops. apply mspecL_ret. auto. Qed.

Lemma mspecL_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL B P (ret ops a) Q.
Proof. intros H. red_ops. apply mspecL_ret. exact H. Qed.
Lemma mspecL_bind_ops {A C} (m : Monad.M St A) (f : A -> Monad.M St C) P Q1 Q :
  mspecL B P m Q1 -> (forall a, mspecL B (Q1 a) (f a) Q) -> mspecL B P (bind ops m f) Q.
Proof. intros H1 H2. red_ops. eapply mspecL_bind; eauto. Qed.

Lemma err_L : forall c w X bs, mspecL B (lownL c w X) (out_stderr ops bs) (fun _ => lownL c w X).
Proof. intros. red_ops. apply (lownL_frame _ (fun X' => Herr X' [bs])). Qed.
Lemma fw_L : forall c w X bs, mspecL B (lownL c w X) (out_stderr_fw ops bs) (fun _ => lownL c w X).
Proof. intros. red_ops. apply (lownL_frame _ (fun X' => Hfw X' bs)). Qed.
Lemma emit_dexit_L : forall c w X e, mspecL B (lownL c w X) (emit_dexit ops e) (fun _ => lownL c w X).
Proof. intros c w X [| | |]; cbn [emit_dexit]; [apply mspecL_ret_ops; auto | apply err_L | apply fw_L | apply fw_L]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsizesL : 0 < zl_dstate za <= 65536 /\ 0 < zl_dwin za <= 65536 /\ 0 < zl_dprev za <= 65536 /\ 0 < zl_dhead za <= 65536
                /\ 0 < zl_dpend za <= 65536 /\ 0 < zl_isize za <= 65536 /\ 0 < zl_wsize za <= 65536.
Proof.
  pose proof (zo_sizesL za ZOK) as H.
  repeat (match type of H with Forall _ (_ :: _) => let a := fresh "Ha" in let b := fresh "Hb" in inversion H as [|? ? a b]; subst; clear H; rename b into H end).
  repeat split; lia.
Qed.

Lemma U_facts : 65536 <= U /\ 7 * 65536 <= U /\ U <= MAX_INPUT + 1 /\ NofL ZL_MAX <= U.
Proof. unfold U, ZH_MAX, MAX_INPUT, NofL, ZL_MAX. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variable X : list (ptr * Z).
Hypothesis HX : nonnegX X.

Definition blk5z (b : ptr * ptr * ptr * ptr * ptr) : list (ptr * Z) :=
  let '(sp, wp, pp, hp, bp) := b in
  [(bp, zl_dpend za); (hp, zl_dhead za); (pp, zl_dprev za); (wp, zl_dwin za); (sp, zl_dstate za)].

Lemma blk5z_facts : forall b, length (blk5z b) = 5%nat /\ nonnegX (blk5z b) /\ szsum (blk5z b) <= 5 * 65536.
Proof.
  intros [[[[sp wp] pp] hp] bp]. destruct zsizesL as (H1 & H2 & H3 & H4 & H5 & _). unfold blk5z.
  split; [reflexivity|]. split; [repeat constructor; cbn [snd]; lia|]. cbn [szsum fold_right snd]. lia.
Qed.

Lemma step_E : forall (r : option ptr) n (E : list (ptr * Z)) (k : nat) W, 0 <= n -> (length E <= k)%nat -> nonnegX E -> szsum E <= W ->
  (length (optz r n ++ E) <= S k)%nat /\ nonnegX (optz r n ++ E) /\ szsum (optz r n ++ E) <= W + n.
Proof.
  intros r n E k W Hn H1 H2 H3. rewrite length_app, szsum_app. destruct r; cbn [optz length szsum fold_right snd].
  - split; [lia|]. split; [apply nonnegX_app; [repeat constructor; cbn; lia| exact H2]| lia].
  - split; [lia|]. split; [exact H2| lia].
Qed.

(* [comment removed for export] *)
Lemma fitsX : forall c w L, (length L + length X + c <= 31)%nat -> nonnegX L -> szsum L + szsum X + w <= SUMMAX -> fits c w (L ++ X).
Proof.
  intros c w L H1 H2 H3. unfold fits. rewrite length_app, szsum_app.
  split; [lia|]. split; [apply nonnegX_app; assumption| lia].
Qed.

(* [comment removed for export] *)
Lemma deflate_init_L : forall c w L, (length L + length X + c + 5 <= 31)%nat -> nonnegX L -> szsum L + szsum X + w + 5 * 65536 <= SUMMAX ->
  mspecL B (lownL c w (L ++ X)) (deflate_initL ops za)
         (fun r => match r with Some b => lownL c w (blk5z b ++ L ++ X) | None => lownL c w (L ++ X) end).
Proof.
  intros c w L HL1 HL2 HL3. destruct zsizesL as (H1 & H2 & H3 & H4 & H5 & _). pose proof U_facts as (U1 & U5 & UM & UN). unfold deflate_initL.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact HL2| lia]| lia]|].
  intros [sp|]; [|cbn [optz app]; apply mspecL_ret_ops; auto].
  destruct (step_E (Some sp) (zl_dstate za) L (length L) _ ltac:(lia) ltac:(lia) HL2 (Z.le_refl _)) as (A1 & A2 & A3).
  rewrite app_assoc. set (E1 := optz (Some sp) (zl_dstate za) ++ L) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact A2| lia]| lia]|]. intros wr.
  destruct (step_E wr (zl_dwin za) E1 _ _ ltac:(lia) A1 A2 A3) as (B1 & B2 & B3).
  rewrite app_assoc. set (E2 := optz wr (zl_dwin za) ++ E1) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact B2| lia]| lia]|]. intros pr.
  destruct (step_E pr (zl_dprev za) E2 _ _ ltac:(lia) B1 B2 B3) as (C1 & C2 & C3).
  rewrite app_assoc. set (E3 := optz pr (zl_dprev za) ++ E2) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact C2| lia]| lia]|]. intros hr.
  destruct (step_E hr (zl_dhead za) E3 _ _ ltac:(lia) C1 C2 C3) as (D1 & D2 & D3).
  rewrite app_assoc. set (E4 := optz hr (zl_dhead za) ++ E3) in *.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact D2| lia]| lia]|]. intros br.
  subst E4 E3 E2 E1. rewrite <- !app_assoc.
  assert (FAIL : mspecL B (lownL c w (optz br (zl_dpend za) ++ optz hr (zl_dhead za) ++ optz pr (zl_dprev za) ++ optz wr (zl_dwin za) ++ optz (Some sp) (zl_dstate za) ++ L ++ X))
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

Lemma deflate_end_L : forall c w L b, mspecL B (lownL c w (blk5z b ++ L)) (deflate_endL ops b) (fun _ => lownL c w L).
Proof.
  intros c w L [[[[sp wp] pp] hp] bp]. unfold deflate_endL, blk5z. cbn [app].
  eapply mspecL_bind_ops; [apply free_L|]. intro. eapply mspecL_bind_ops; [apply free_L|]. intro.
  eapply mspecL_bind_ops; [apply free_L|]. intro. eapply mspecL_bind_ops; [apply free_L|]. intro. apply free_L.
Qed.

(* [comment removed for export] *)
Lemma test_deflate_L : forall c w L N diff, (length L + length X + c + 5 <= 31)%nat -> nonnegX L -> szsum L + szsum X + w + 5 * 65536 <= SUMMAX ->
  mspecL B (lownL c w (L ++ X)) (test_large_deflateM ops za N diff) (fun _ => lownL (c + 5) (w + 5 * 65536) (L ++ X)).
Proof.
  intros c w L N diff HL1 HL2 HL3. unfold test_large_deflateM.
  eapply mspecL_bind_ops; [apply deflate_init_L; assumption|]. intros [b|].
  - destruct (test_large_deflate_pure za N) as [[[comprc e] od] ended].
    eapply mspecL_bind_ops with (Q1 := fun _ => lownL (c + 5) (w + 5 * 65536) (L ++ X)).
    { destruct ended.
      - eapply mspecL_post; [apply deflate_end_L|]. intros a s mo H. eapply lownL_weaken; [| |exact H]; lia.
      - apply mspecL_ret_ops. intros s mo H. destruct (blk5z_facts b) as (F1 & F2 & F3).
        pose proof (lownL_leak_list (blk5z b) c w (L ++ X) s mo F2 H) as H'. rewrite F1 in H'. eapply lownL_weaken; [| |exact H']; lia. }
    intro. eapply mspecL_bind_ops; [apply emit_dexit_L|]. intro. apply mspecL_ret_ops. auto.
  - eapply mspecL_bind_ops; [apply err_L|]. intro. apply mspecL_ret_ops. intros s mo H. eapply lownL_weaken; [| |exact H]; lia.
Qed.

(* [comment removed for export] *)
Lemma iloop_L : forall c w fuel N comprc is wr L, (length L + length X + c <= 31)%nat -> nonnegX L -> szsum L + szsum X + w <= SUMMAX ->
  mspecL B (lownL c w (optz wr (zl_wsize za) ++ L ++ X)) (iloopL ops za fuel N comprc is wr)
         (fun r => match r with
                   | ILLdone _ w' => lownL c w (optz w' (zl_wsize za) ++ L ++ X)
                   | ILLerr _ w' => lownL c w (optz w' (zl_wsize za) ++ L ++ X)
                   end).
Proof.
  intros c w fuel. destruct zsizesL as (_ & _ & _ & _ & _ & _ & HW). pose proof U_facts as (U1 & _ & UM & _).
  induction fuel as [|f IH]; intros N comprc is wr L HL1 HL2 HL3; cbn [iloopL]; [red_ops; apply mspecL_munr|].
  destruct (i_wantsL za N comprc is && match wr with None => true | Some _ => false end) eqn:EW.
  - apply andb_true_iff in EW. destruct EW as [_ Ew]. destruct wr as [q|]; [discriminate|]. cbn [optz app].
    eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact HL2| lia]| lia]|].
    intros r. destruct (i_callL za N comprc is (match r with Some _ => true | None => false end)) as [[is' bs] rc].
    destruct (rc =? Z_STREAM_END); [apply mspecL_ret_ops; auto|]. destruct (rc =? Z_OK); [|apply mspecL_ret_ops; auto].
    apply IH; assumption.
  - apply (mspecL_bind_ops _ _ _ (fun _ => lownL c w (optz wr (zl_wsize za) ++ L ++ X))); [apply mspecL_ret_ops; auto|]. intros r. cbv beta.
    destruct (i_callL za N comprc is true) as [[is' bs] rc].
    destruct (rc =? Z_STREAM_END); [apply mspecL_ret_ops; auto|]. destruct (rc =? Z_OK); [|apply mspecL_ret_ops; auto].
    apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma test_inflate_L : forall c w L N comprc diff, (length L + length X + c + 1 <= 31)%nat -> nonnegX L -> szsum L + szsum X + w + 2 * 65536 <= SUMMAX ->
  mspecL B (lownL c w (L ++ X)) (test_large_inflateM ops za N comprc diff) (fun _ => lownL (c + 2) (w + 2 * 65536) (L ++ X)).
Proof.
  intros c w L N comprc diff HL1 HL2 HL3. destruct zsizesL as (_ & _ & _ & _ & _ & HI & HW). pose proof U_facts as (U1 & _ & UM & _).
  unfold test_large_inflateM.
  eapply mspecL_bind_ops; [apply malloc_L; [apply fitsX; [lia| exact HL2| lia]| lia]|].
  intros [sp|]; cbn [optz app].
  2:{ eapply mspecL_post; [apply err_L|]. intros a s mo H. eapply lownL_weaken; [| |exact H]; lia. }
  eapply mspecL_bind_ops.
  { apply (iloop_L c w _ _ _ _ None ((sp, zl_isize za) :: L)); [cbn [length]; lia| constructor; [cbn; lia| exact HL2]|].
    cbn [szsum fold_right snd]. fold (@szsum ptr L). lia. }
  intros [is' w'|rc w'].
  - eapply mspecL_bind_ops; [apply free_opt_L|]. intro. cbn [app].
    eapply mspecL_bind_ops; [apply free_L|]. intro.
    eapply (mspecL_post B _ _ (fun _ => lownL c w (L ++ X))).
    + destruct (il_end za is' =? Z_OK); [destruct (il_total_out za is' =? 2 * N + diff); [apply mspecL_ret_ops; intros s mo H; exact H | apply err_L]| apply err_L].
    + intros a1 s mo H. eapply lownL_weaken; [| |exact H]; lia.
  - (* [comment removed for export] *)
    eapply mspecL_conseq; [apply (err_L (c + 2) (w + 2 * 65536) (L ++ X))| |auto].
    intros s mo H. destruct w' as [wp|]; cbn [optz app] in H.
    + apply lownL_leak in H; [|lia]. apply lownL_leak in H; [|lia]. eapply lownL_weaken; [| |exact H]; lia.
    + apply lownL_leak in H; [|lia]. eapply lownL_weaken; [| |exact H]; lia.
Qed.

(* [comment removed for export] *)
Lemma fuzz_one_L : forall c w d diff, (length X + c + 9 <= 32)%nat -> szsum X + w + 4 * U <= SUMMAX ->
  mspecL B (lownL c w X) (fuzz_oneL ops za d diff) (fun r s mo => lownL (c + 7) (w + U) X s mo /\ fst r = 0).
Proof.
  intros c w d diff HC HS. pose proof U_facts as (U1 & U5 & UM & UN). unfold fuzz_oneL.
  destruct ((zlength d <? 1) || (ZL_MAX <? zlength d)) eqn:ER.
  { apply mspecL_ret_ops. intros s mo H. split; [eapply lownL_weaken; [| |exact H]; unfold U, ZH_MAX; lia| reflexivity]. }
  apply orb_false_iff in ER. destruct ER as [E1 E2]. apply Z.ltb_ge in E1, E2.
  set (N := NofL (zlength d)).
  assert (HN : 0 <= N <= U) by (subst N; unfold NofL, ZL_MAX in *; unfold NofL, ZL_MAX in UN; lia).
  eapply mspecL_bind_ops; [apply (malloc_L c w X N); [apply (fitsX c w []); [cbn; lia| constructor| cbn; lia]| lia]|].
  intros [cp|]; cbn [optz app].
  2:{ (* S3b (#16543): the first calloc failed; the second still runs; then both are freed *)
      eapply mspecL_bind_ops; [apply (malloc_L c w X N); [apply (fitsX c w []); [cbn; lia| constructor| cbn; lia]| lia]|].
      intros [up|]; cbn [optz app].
      - eapply mspecL_bind_ops; [apply (free_opt_L c w ((up, N) :: X) None N)|]. intro.
        eapply mspecL_bind_ops; [apply free_L|]. intro.
        apply mspecL_ret_ops. intros s mo H. split; [eapply lownL_weaken; [| |exact H]; unfold U, ZH_MAX; lia| reflexivity].
      - eapply mspecL_bind_ops; [apply (free_opt_L c w X None N)|]. intro.
        eapply mspecL_bind_ops; [apply (free_opt_L c w X None N)|]. intro.
        apply mspecL_ret_ops. intros s mo H. split; [eapply lownL_weaken; [| |exact H]; unfold U, ZH_MAX; lia| reflexivity]. }
  eapply mspecL_bind_ops.
  { apply (malloc_L c w ((cp, N) :: X) N); [|lia].
    apply (fitsX c w [(cp, N)]); [cbn; lia| repeat constructor; cbn; lia| cbn [szsum fold_right snd]; lia]. }
  intros [up|]; cbn [optz app].
  2:{ (* S3b (#16543): the second calloc failed: free(cp), then free(NULL); nothing leaks now *)
      eapply mspecL_bind_ops; [apply free_L|]. intro.
      eapply mspecL_bind_ops; [apply (free_opt_L c w X None N)|]. intro.
      apply mspecL_ret_ops. intros s mo H. split; [eapply lownL_weaken; [| |exact H]; unfold U, ZH_MAX; lia| reflexivity]. }
  assert (L1 : (length [(up, N); (cp, N)] = 2)%nat) by reflexivity.
  assert (L2 : nonnegX [(up, N); (cp, N)]) by (repeat constructor; cbn; lia).
  assert (L3 : szsum [(up, N); (cp, N)] <= 2 * U) by (cbn [szsum fold_right snd]; lia).
  eapply mspecL_bind_ops; [apply (test_deflate_L c w [(up, N); (cp, N)] N diff); [rewrite L1; lia | exact L2 | lia]|]. intros [comprc diff'].
  eapply mspecL_bind_ops; [apply (test_inflate_L (c + 5) (w + 5 * 65536) [(up, N); (cp, N)] N comprc diff'); [rewrite L1; lia | exact L2 | lia]|]. intro. cbn [app].
  eapply mspecL_bind_ops; [eapply mspecL_pre; [apply (free_L (c + 5 + 2) (w + 5 * 65536 + 2 * 65536) ((up, N) :: X) cp N)|]|].
  { intros s mo H. eapply lownL_perm; [apply perm_swap| exact H]. }
  intro. eapply mspecL_bind_ops; [apply free_L|]. intro.
  apply mspecL_ret_ops. intros s mo H. split; [|reflexivity]. eapply lownL_weaken; [| |exact H]; lia.
Qed.
End Call.

(* [comment removed for export] *)
Lemma run_calls_L : forall X d n j rc diff, (length X <= 2)%nat -> nonnegX X -> szsum X <= 2 * (MAX_INPUT + 1) -> (j + n <= 4)%nat -> rc = 0 ->
  mspecL B (lownL (7 * j) (Z.of_nat j * U) X) (run_callsL ops za d n rc diff)
         (fun rc' s mo => lownL (7 * (j + n)) (Z.of_nat (j + n) * U) X s mo /\ rc' = 0).
Proof.
  intros X d n. induction n as [|n IH]; intros j rc diff HX1 HX2 HX3 Hj Hrc; cbn [run_callsL].
  - apply mspecL_ret_ops. intros s mo H. rewrite Nat.add_0_r. auto.
  - eapply mspecL_bind_ops.
    { apply (fuzz_one_L X HX2 (7 * j) (Z.of_nat j * U)). lia. unfold SUMMAX. fold U. unfold U, ZH_MAX, MAX_INPUT in *. lia. }
    intros [rc' diff']. apply mspecL_pure. cbn [fst]. intros ->.
    eapply mspecL_bind_ops; [red_ops; apply (lownL_frame _ (fun X' => Hout X' _))|]. intro.
    eapply mspecL_conseq; [apply (IH (S j) 0 diff' HX1 HX2 HX3); [lia| reflexivity]| |].
    + intros s mo H. eapply lownL_weaken; [| |exact H]; lia.
    + intros a1 s mo [H ->]. split; [|reflexivity]. replace (j + S n)%nat with (S j + n)%nat by lia. exact H.
Qed.
End TargetL.

(* [comment removed for export] *)
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
  (forall X n, (length X <= 31)%nat -> nonnegX X -> szsum X <= SUMMAX -> 0 <= n <= MAX_INPUT + 1 -> mal_ok X n) ->
  forall X0 cfg payload, (length X0 <= 1)%nat -> nonnegX X0 -> szsum X0 <= MAX_INPUT + 1 -> zlength payload <= MAX_INPUT ->
  mspecL B (own X0) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ s mo => exists Y, own (Y ++ X0) s mo).
Proof.
  intros Hdm Hdf Hperm Herr Hfw Hout OK X0 cfg payload HX1 HX2 HX3 Hpl.
  unfold Target.target_run, ZTargetL.target_runL.
  pose proof (@run_calls_L St ptr B the_zapiL the_zapiL_ok raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm Herr Hfw Hout OK) as RC.
  assert (Hpl0 : 0 <= zlength payload) by (unfold zlength; lia).
  assert (Hc : (Z.to_nat (Z.land cfg 3 + 1) <= 4)%nat).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound cfg (2^2) ltac:(lia)). change (2^2) with 4 in *. lia. }
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
    + cbn -[run_callsL MAX_INPUT].
      eapply mspecL_bind.
      { eapply mspecL_conseq; [apply (RC ((p, zlength payload) :: X0) payload (Z.to_nat (Z.land cfg 3 + 1)) 0%nat 0 0)| |intros r s mo H; exact H].
        - cbn [length]; lia. - constructor; [cbn; lia| exact HX2]. - cbn [szsum fold_right snd]. fold (@szsum ptr X0). lia. - lia. - reflexivity.
        - intros s mo H. apply IN. exact H. }
      intros rc. apply mspecL_pure. intros _.
      eapply mspecL_bind; [eapply (free_L B raw_malloc raw_free get_so set_so own Hdf Hperm)|].
      intros u. apply mspecL_ret. intros s mo H. eapply OUT. exact H.
    + cbn -[run_callsL MAX_INPUT].
      eapply mspecL_bind.
      { eapply mspecL_conseq; [apply (RC X0 payload (Z.to_nat (Z.land cfg 3 + 1)) 0%nat 0 0)| |intros r s mo H; exact H].
        - lia. - exact HX2. - lia. - lia. - reflexivity.
        - intros s mo H. apply IN. exact H. }
      intros rc. apply mspecL_pure. intros _.
      eapply (mspecL_bind B _ _ _ (fun _ => @lownL St ptr own _ _ X0)); [apply mspecL_ret; intros s mo H; exact H|].
      intros u. apply mspecL_ret. intros s mo H. eapply OUT. exact H.
Qed.
