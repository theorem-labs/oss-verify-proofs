(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim Monad MSafe Malloc KStep MI_Inv MI_Cnt Stdio Adapter Driver PState Prog StepB
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc LB_PCaps LB_Hist LB_Proph LB_PStdio.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import CMonad CLogic HarnessC ProgC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require AdapterC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import Keeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section TARGETP.
Variable FM : flush_model.
Variable P : Z -> Z.
Hypothesis HPc : forall c, P c <= Penv c.
Hypothesis HP8 : forall c, validc c = true -> AMBC <= P c.

Definition malok (X : list (bptr * Z)) (n : Z) : Prop := ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET /\ n <= NREQ.

Definition RHOLD : Z := 2 * (2^26 + 8192) + 2 * W.

Lemma bigb_le n b : 0 <= n <= b -> bigb n <= b + 4115.
Proof.
  intros Hn. unfold bigb. destruct (Z.leb_spec MMAP_THRESHOLD n); [| lia]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
  pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia.
Qed.

Lemma malok_of : forall X n, 0 <= n <= 2^26 + 64 ->
  (n < MMAP_THRESHOLD -> LRX X (size_to_class n) <= 7) -> n63X X <= 7 -> R63X X <= RHOLD -> malok X n.
Proof.
  intros X n Hn HS HB HR. pose proof PHI_Penv as HPh. pose proof (PHI_mono P Penv HPc) as PM.
  pose proof (bigb_le n (2^26 + 64) Hn) as Hbb. unfold RHOLD, RBIG, W in *.
  split; [| split; [lia| unfold NREQ; lia]].
  split.
  - intros Hsmall. pose proof (validc_cls n ltac:(lia)) as Vc. specialize (HP8 _ Vc). specialize (HS Hsmall). unfold AMBC in *. lia.
  - intros Hbig. specialize (HP8 63 validc_63). unfold AMBC in *. lia.
Qed.

Definition Q (X : list (bptr * Z)) : assn PState := QI X P.
Local Notation mspecL := (mspecL LBUDGET).
Local Notation cspecL := (cspecL LBUDGET).

Lemma Q_live X s mo : Q X s mo -> live mo <= LBUDGET. Proof. apply QI_live. Qed.
Lemma Q_so X s mo v : Q X s mo -> Q X (set_so_ps v s) mo. Proof. apply QI_set_so. Qed.
Lemma Q_perm X Y s mo : Permutation X Y -> Q X s mo -> Q Y s mo. Proof. apply QI_perm. Qed.

Lemma malloc_Q : forall X n, 0 <= n ->
  mspecL (fun s mo => Q X s mo /\ malok X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Q ((p, n) :: X) s mo /\ n < 2^63 | None => Q X s mo end).
Proof. intros X n Hn. unfold Q, malok. eapply mspecL_pre; [apply raw_malloc_LQ; exact Hn|]. intros s mo [H1 (H2 & H3 & H4)]. auto. Qed.
Lemma free_Q : forall X p n, mspecL (Q ((p, n) :: X)) (raw_free p) (fun _ => Q X).
Proof. intros X p n. unfold Q. apply raw_free_LQ. Qed.
Lemma emit_Q : forall X v, mspecL (Q X) (io_emit io v) (fun _ => Q X).
Proof. intros X v. cbn [io io_emit io_S]. apply (s_emit_L LBUDGET (Q X) (Q_live X) (Q_so X)). Qed.
Lemma fprintf_Q : forall X ps, mspecL (Q X) (stderr_fprintf ps) (fun _ => Q X).
Proof. intros X ps. apply (stderr_fprintf_L LBUDGET (Q X) (Q_live X)). Qed.
Lemma fwrite_Q : forall X bs, mspecL (Q X) (stderr_fwrite bs) (fun _ => Q X).
Proof. intros X bs. apply (stderr_fwrite_L LBUDGET (Q X) (Q_live X)). Qed.

Local Ltac ret_Q := apply mspecL_ret; intros ? ? HH; exact HH.


Definition HOLD (X : list (bptr * Z)) (lc l44 nb : Z) (rb : Z) : Prop :=
  (forall c, LRX X c <= lc) /\ LRX X 44 <= l44 /\ n63X X <= nb /\ R63X X <= rb /\ Forall (fun b => 0 <= snd b <= 2^26 + 64) X.

Lemma HOLD_cons : forall X lc l44 nb rb p n, HOLD X lc l44 nb rb -> 0 <= n <= 2^26 + 64 ->
  HOLD ((p, n) :: X) (lc + 1) (l44 + (if negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? 44) then 1 else 0)) (nb + 1) (rb + bigb n).
Proof.
  intros X lc l44 nb rb p n (A & B & C & D & E) Hn. unfold HOLD. rewrite !LRX_cons, n63X_cons, R63X_cons.
  splits; [intros c; specialize (A c); rewrite LRX_cons; destruct (negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c)); lia| destruct (negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? 44)); lia| destruct (MMAP_THRESHOLD <=? n); lia| lia| constructor; [cbn; lia| exact E]].
Qed.
Lemma HOLD_weak : forall X lc l44 nb rb lc' l44' nb' rb', HOLD X lc l44 nb rb -> lc <= lc' -> l44 <= l44' -> nb <= nb' -> rb <= rb' -> HOLD X lc' l44' nb' rb'.
Proof. intros X lc l44 nb rb lc' l44' nb' rb' (A & B & C & D & E) ? ? ? ?. unfold HOLD. splits; [intros c; specialize (A c); lia| lia| lia| lia| exact E]. Qed.

Lemma malok_HOLD : forall X lc l44 nb rb n, HOLD X lc l44 nb rb -> 0 <= n <= 2^26 + 64 ->
  (n < MMAP_THRESHOLD -> size_to_class n <> 44 -> lc <= 7) -> (n < MMAP_THRESHOLD -> size_to_class n = 44 -> l44 <= 7) -> nb <= 7 -> rb <= RHOLD -> malok X n.
Proof.
  intros X lc l44 nb rb n (A & B & C & D & E) Hn Hc H44 Hb Hr. apply malok_of; [exact Hn| | lia| lia].
  intros Hs. destruct (Z.eq_dec (size_to_class n) 44) as [E44|N44]; [rewrite E44; specialize (H44 Hs E44); lia| specialize (A (size_to_class n)); specialize (Hc Hs N44); lia].
Qed.

Lemma creq_Q : forall X n, 0 <= n -> mspecL (fun s mo => Q X s mo /\ malok X n) (creq raw_malloc n) (fun p => Q ((p, n) :: X)).
Proof.
  intros X n Hn. unfold creq. eapply mspecL_bind; [apply malloc_Q; exact Hn|].
  intros [p|]; cbn beta iota; [apply mspecL_ret; intros s mo [H _]; exact H| apply mspecL_munr].
Qed.
Lemma zreq_Q : forall X n, 0 <= n -> mspecL (fun s mo => Q X s mo /\ malok X n) (zreq raw_malloc fresh_topb n) (fun p => Q ((p, n) :: X)).
Proof.
  intros X n Hn. unfold zreq.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  eapply mspecL_bind; [eapply mspecL_pre; [apply malloc_Q; exact Hn|]; intros s mo [-> H]; exact H|].
  intros [p|]; cbn beta iota; [| apply mspecL_munr].
  eapply mspecL_bind; [apply mspecL_get|]. intros s1.
  apply mspecL_if; intros _; [apply mspecL_ret; intros s mo (-> & H & _); exact H| eapply mspecL_pre; [apply mspecL_munr| intros s mo (-> & _ & _); exact I]].
Qed.
Lemma diag_zerr_Q : forall X msg e, mspecL (Q X) (diag_zerr msg e) (fun _ => Q X).
Proof. intros X msg e. unfold diag_zerr. apply fprintf_Q. Qed.
Lemma cls_5968 : size_to_class 5968 = 30. Proof. vm_compute. reflexivity. Qed.
Lemma cls_65536 : size_to_class 65536 = 44. Proof. vm_compute. reflexivity. Qed.
Lemma cls_7176 : size_to_class 7176 = 31. Proof. vm_compute. reflexivity. Qed.
Lemma cls_32768 : size_to_class 32768 = 40. Proof. vm_compute. reflexivity. Qed.
Lemma bigb_small n : n < MMAP_THRESHOLD -> bigb n = 0.
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.
Lemma CLEN_range : forall n, 0 <= n <= 2^20 -> n + 126 <= CLEN n < 2^22.
Proof.
  intros n Hn. pose proof (CLEN_lt32 n Hn). unfold CLEN, cbound in *.
  pose proof (Z.div_pos n 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 16384 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 33554432 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma HOLD_cons_small : forall X lc l44 nb rb p n, HOLD X lc l44 nb rb -> 0 <= n < MMAP_THRESHOLD ->
  HOLD ((p, n) :: X) (lc + 1) (l44 + (if size_to_class n =? 44 then 1 else 0)) nb rb.
Proof.
  intros X lc l44 nb rb p n (A & B & C & D & E) Hn. unfold HOLD. rewrite !LRX_cons, n63X_cons, R63X_cons, bigb_small by lia.
  replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb andb].
  splits; [intros c; specialize (A c); rewrite LRX_cons; destruct (_ && _); lia| destruct (size_to_class n =? 44); lia| lia| lia| constructor; [cbn; unfold MMAP_THRESHOLD in Hn; lia| exact E]].
Qed.
Lemma HOLD_cons_z : forall X lc l44 nb rb p n, HOLD X lc l44 nb rb -> n = 5968 \/ n = 7176 \/ n = 32768 ->
  HOLD ((p, n) :: X) (lc + 1) l44 nb rb.
Proof.
  intros X lc l44 nb rb p n H Hn. pose proof (HOLD_cons_small X lc l44 nb rb p n H ltac:(unfold MMAP_THRESHOLD; lia)) as H1.
  destruct Hn as [-> |[-> | ->]]; [rewrite cls_5968 in H1| rewrite cls_7176 in H1| rewrite cls_32768 in H1]; cbn [Z.eqb Pos.eqb] in H1; rewrite Z.add_0_r in H1; exact H1.
Qed.
Lemma HOLD_cons_65536 : forall X lc l44 nb rb p, HOLD X lc l44 nb rb -> HOLD ((p, 65536) :: X) (lc + 1) (l44 + 1) nb rb.
Proof.
  intros X lc l44 nb rb p H. pose proof (HOLD_cons_small X lc l44 nb rb p 65536 H ltac:(unfold MMAP_THRESHOLD; lia)) as H1.
  rewrite cls_65536 in H1. cbn [Z.eqb Pos.eqb] in H1. exact H1.
Qed.

Definition ENTRY_L (X0 : list (bptr * Z)) : Prop := HOLD X0 4 2 2 (2 * (2^26 + 8192)).

Lemma test_flush_Q : forall X0 cp cb up n d, ENTRY_L X0 -> 0 <= n <= 2^20 -> n <= cb < 2^22 ->
  mspecL (Q ((up, n) :: (cp, cb) :: X0)) (test_flush_m FM raw_malloc raw_free fresh_topb d n) (fun _ => Q ((up, n) :: (cp, cb) :: X0)).
Proof.
  intros X0 cp cb up n d HE Hn Hcb. unfold test_flush_m, DSTATE_N, DBLK_N.
  pose proof (HOLD_cons _ _ _ _ _ up n (HOLD_cons _ _ _ _ _ cp cb HE ltac:(lia)) ltac:(lia)) as H2.
  pose proof (bigb_le cb (2^22) ltac:(lia)) as R1. pose proof (bigb_le n (2^20) ltac:(lia)) as R2.
  set (X := (up, n) :: (cp, cb) :: X0) in *.
  assert (HX : HOLD X 6 4 4 RHOLD).
  { eapply HOLD_weak; [exact H2| lia| | lia| unfold RHOLD, W; lia].
    destruct (negb (MMAP_THRESHOLD <=? cb) && (size_to_class cb =? 44)); destruct (negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? 44)); lia. }
  Local Ltac hreq HX := eapply mspecL_pre; [apply zreq_Q; lia|]; intros s mo HQ; split; [exact HQ|];
    eapply (malok_HOLD _ _ _ _ _ _ HX); [lia| | | lia| unfold RHOLD, W; lia].
  eapply mspecL_bind. { hreq HX; rewrite cls_5968; intros; lia. } intros sp.
  pose proof (HOLD_cons_z _ _ _ _ _ sp 5968 HX ltac:(lia)) as H3.
  eapply mspecL_bind. { hreq H3; rewrite ?cls_65536; intros; lia. } intros w.
  pose proof (HOLD_cons_65536 _ _ _ _ _ w H3) as H4.
  eapply mspecL_bind. { hreq H4; rewrite ?cls_65536; intros; lia. } intros pv.
  pose proof (HOLD_cons_65536 _ _ _ _ _ pv H4) as H5.
  eapply mspecL_bind. { hreq H5; rewrite ?cls_65536; intros; lia. } intros hd.
  pose proof (HOLD_cons_65536 _ _ _ _ _ hd H5) as H6.
  eapply mspecL_bind. { hreq H6; rewrite ?cls_65536; intros; lia. } intros pb.
  eapply mspecL_seq; [apply free_Q|]. intros _. eapply mspecL_seq; [apply free_Q|]. intros _.
  eapply mspecL_seq; [apply free_Q|]. intros _. eapply mspecL_seq; [apply free_Q|]. intros _.
  eapply mspecL_seq; [apply free_Q|]. intros _.
  apply mspecL_if; intros _; [| ret_Q].
  eapply mspecL_seq; [apply diag_zerr_Q|]. intros _. ret_Q.
Qed.

Definition leak_shape (LK : list (bptr * Z)) : Prop :=
  LK = [] \/ (exists p, LK = [(p, 7176)]) \/ (exists p w, LK = [(w, 32768); (p, 7176)]).

Lemma finish_sync_Q : forall X p (w : option bptr) rc,
  mspecL (Q (match w with Some wd => [(wd, 32768)] | None => [] end ++ (p, 7176) :: X)) (finish_sync raw_free p w rc)
         (fun _ s mo => exists LK, Q (LK ++ X) s mo /\ leak_shape LK).
Proof.
  intros X p w rc. unfold finish_sync. apply mspecL_if; intros _.
  - eapply mspecL_post.
    { destruct w as [wd|]; cbn [app]; unfold inflate_end; [eapply mspecL_seq; [apply free_Q|]; intros _; apply free_Q | apply free_Q]. }
    cbv beta. intros _ s mo H. exists []. split; [exact H | left; reflexivity].
  - eapply mspecL_post; [apply fwrite_Q|]. cbv beta. intros _ s mo H.
    destruct w as [wd|]; cbn [app] in H.
    + exists [(wd, 32768); (p, 7176)]. split; [exact H | right; right; exists p, wd; reflexivity].
    + exists [(p, 7176)]. split; [exact H | right; left; exists p; reflexivity].
Qed.

Lemma test_sync_Q : forall X0 cp cb up n c clen, ENTRY_L X0 -> 0 <= n <= 2^20 -> n <= cb < 2^22 ->
  mspecL (Q ((up, n) :: (cp, cb) :: X0)) (test_sync_m FM raw_malloc raw_free fresh_topb c clen n)
         (fun _ s mo => exists LK, Q (LK ++ (up, n) :: (cp, cb) :: X0) s mo /\ leak_shape LK).
Proof.
  intros X0 cp cb up n c clen HE Hn Hcb. unfold test_sync_m, ISTATE_N, WIN_N.
  pose proof (HOLD_cons _ _ _ _ _ up n (HOLD_cons _ _ _ _ _ cp cb HE ltac:(lia)) ltac:(lia)) as H2.
  pose proof (bigb_le cb (2^22) ltac:(lia)) as R1. pose proof (bigb_le n (2^20) ltac:(lia)) as R2.
  set (X := (up, n) :: (cp, cb) :: X0) in *.
  assert (HX : HOLD X 6 4 4 RHOLD).
  { eapply HOLD_weak; [exact H2| lia| | lia| unfold RHOLD, W; lia].
    destruct (negb (MMAP_THRESHOLD <=? cb) && (size_to_class cb =? 44)); destruct (negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? 44)); lia. }
  eapply mspecL_bind. { hreq HX; rewrite cls_7176; intros; lia. } intros p. cbv beta.
  pose proof (HOLD_cons_z _ _ _ _ _ p 7176 HX ltac:(lia)) as H3.
  destruct (fm_i1 FM c n) as [|e].
  - destruct (fm_is FM c clen n) as [|e].
    + destruct (fm_i2 FM c clen n) as [|rc].
      * eapply mspecL_bind. { hreq H3; rewrite cls_32768; intros; lia. } intros wd. cbv beta.
        apply (finish_sync_Q X p (Some wd)).
      * apply (finish_sync_Q X p None).
    + eapply mspecL_post; [apply diag_zerr_Q|]. cbv beta. intros _ s mo H. exists [(p, 7176)]. split; [exact H| right; left; eexists; reflexivity].
  - eapply mspecL_post; [apply diag_zerr_Q|]. cbv beta. intros _ s mo H. exists [(p, 7176)]. split; [exact H| right; left; eexists; reflexivity].
Qed.

Lemma fuzz_one_m_Q : forall X0 d, ENTRY_L X0 ->
  mspecL (Q X0) (fuzz_one_m FM raw_malloc raw_free fresh_topb d) (fun _ s mo => exists LK, Q (LK ++ X0) s mo /\ leak_shape LK).
Proof.
  intros X0 d HE. unfold fuzz_one_m.
  apply mspecL_if; intros SK.
  { apply mspecL_ret. intros s mo H. exists []. split; [exact H| left; reflexivity]. }
  unfold fuzz_skip, KMAX in SK. apply Bool.orb_false_iff in SK as [SK1 SK2]. apply Z.leb_gt in SK1. apply Z.ltb_ge in SK2.
  assert (Hn : 0 <= zlength d <= 2^20) by (unfold zlength in *; lia).
  pose proof (CLEN_range (zlength d) Hn) as Hcb.
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply creq_Q; lia|]. intros s mo HQ. split; [exact HQ|].
    eapply (malok_HOLD _ _ _ _ _ _ HE); [lia| intros; lia| intros; lia| lia| unfold RHOLD, W; lia]. }
  intros cp.
  pose proof (HOLD_cons _ _ _ _ _ cp (CLEN (zlength d)) HE ltac:(lia)) as H1.
  pose proof (bigb_le (CLEN (zlength d)) (2^22) ltac:(lia)) as R1.
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply creq_Q; lia|]. intros s mo HQ. split; [exact HQ|].
    eapply (malok_HOLD _ _ _ _ _ _ H1); [lia| intros; lia| intros; destruct (_ && _); lia| lia| unfold RHOLD, W; lia]. }
  intros up.
  eapply mspecL_bind; [apply (test_flush_Q X0 cp _ up _ d HE Hn); lia|]. intros clen.
  eapply mspecL_bind; [apply (test_sync_Q X0 cp _ up _ _ clen HE Hn); lia|]. intros u. cbv beta.
  apply mspecL_exI. intros LK.
  eapply mspecL_pre with (P := fun s mo => Q ((cp, CLEN (zlength d)) :: (up, zlength d) :: LK ++ X0) s mo /\ leak_shape LK).
  2:{ intros s mo [H HL]. split; [| exact HL]. eapply Q_perm; [| exact H].
      change ((cp, CLEN (zlength d)) :: (up, zlength d) :: LK ++ X0) with ([(cp, CLEN (zlength d)); (up, zlength d)] ++ (LK ++ X0)).
      change (LK ++ (up, zlength d) :: (cp, CLEN (zlength d)) :: X0) with (LK ++ [(up, zlength d); (cp, CLEN (zlength d))] ++ X0).
      rewrite !app_assoc. apply Permutation_app_tail. etransitivity; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply perm_swap. }
  apply mspecL_pure. intros HL.
  eapply mspecL_seq; [apply free_Q|]. intros _. eapply mspecL_seq; [apply free_Q|]. intros _.
  apply mspecL_ret. intros s mo H. exists LK. split; [exact H| exact HL].
Qed.

Lemma fuzz_oneC_Q : forall X0 d, ENTRY_L X0 ->
  cspecL (Q X0) (ProgC.fuzz_oneC FM d) (fun _ s mo => exists LK, Q (LK ++ X0) s mo /\ leak_shape LK).
Proof. intros X0 d HE. unfold ProgC.fuzz_oneC, HarnessC.fuzz_one. apply cspecL_lift. apply fuzz_one_m_Q. exact HE. Qed.

Definition CALLS_L (X : list (bptr * Z)) (ncalls : nat) : Prop :=
  (forall c, c <> 44 -> LRX X c + Z.of_nat ncalls <= 5) /\ HOLD X 5 2 2 (2 * (2^26 + 8192)).

Lemma leak_HOLD : forall LK X lc l44 nb rb, leak_shape LK -> HOLD X lc l44 nb rb ->
  HOLD (LK ++ X) (lc + 1) l44 nb rb /\ (forall c, LRX (LK ++ X) c <= LRX X c + 1) /\ LRX (LK ++ X) 44 = LRX X 44.
Proof.
  intros LK X lc l44 nb rb HL H. pose proof H as (A & B & C & D & E).
  destruct HL as [-> |[[p ->]|[p [w ->]]]]; cbn [app].
  - split; [eapply HOLD_weak; [exact H| lia| lia| lia| lia]|]. split; [intros c; lia| reflexivity].
  - split; [exact (HOLD_cons_z X lc l44 nb rb p 7176 H ltac:(lia))|].
    split; [intros c| ]; rewrite !LRX_cons, cls_7176; replace (MMAP_THRESHOLD <=? 7176) with false by reflexivity; cbn [negb andb];
      [destruct (31 =? c); lia| change (if 31 =? 44 then 1 else 0) with 0; lia].
  - unfold HOLD. rewrite !LRX_cons, !n63X_cons, !R63X_cons, cls_7176, cls_32768, !bigb_small by (unfold MMAP_THRESHOLD; lia).
    replace (MMAP_THRESHOLD <=? 7176) with false by reflexivity. replace (MMAP_THRESHOLD <=? 32768) with false by reflexivity. cbn [negb andb].
    change (if 40 =? 44 then 1 else 0) with 0. change (if 31 =? 44 then 1 else 0) with 0.
    splits; try lia.
    + intros c. specialize (A c). rewrite !LRX_cons, cls_7176, cls_32768.
      replace (MMAP_THRESHOLD <=? 7176) with false by reflexivity. replace (MMAP_THRESHOLD <=? 32768) with false by reflexivity. cbn [negb andb].
      destruct (Z.eqb_spec 40 c); destruct (Z.eqb_spec 31 c); lia.
    + constructor; [cbn; lia| constructor; [cbn; lia| exact E]].
    + intros c. rewrite !LRX_cons, cls_7176, cls_32768.
      replace (MMAP_THRESHOLD <=? 7176) with false by reflexivity. replace (MMAP_THRESHOLD <=? 32768) with false by reflexivity. cbn [negb andb].
      destruct (Z.eqb_spec 40 c); destruct (Z.eqb_spec 31 c); lia.
Qed.

Lemma run_callsC_Q : forall ncalls X payload rc, CALLS_L X ncalls ->
  cspecL (Q X) (AdapterC.run_calls (ProgC.fuzz_oneC FM) (io_emit io) ncalls payload rc) (fun _ s mo => exists LK, Q (LK ++ X) s mo).
Proof.
  induction ncalls as [|nc IH]; intros X payload rc [A HX]; cbn [AdapterC.run_calls].
  - apply cspecL_ret. intros s mo H. exists []. exact H.
  - eapply cspecL_bind.
    { apply fuzz_oneC_Q. destruct HX as (B1 & B2 & B3 & B4 & B5). unfold ENTRY_L, HOLD. splits; auto.
      intros c. destruct (Z.eq_dec c 44) as [->|N]; [lia|]. specialize (A c N). lia. }
    intros rc'. apply cspecL_exI. intros LK. apply cspecL_pure. intros HL.
    destruct (leak_HOLD LK X _ _ _ _ HL HX) as (HX' & G1 & G2).
    eapply cspecL_seq; [apply cspecL_lift, emit_Q|]. intros _.
    eapply cspecL_post; [apply (IH (LK ++ X))|].
    {
      assert (A2 : forall c, c <> 44 -> LRX (LK ++ X) c + Z.of_nat nc <= 5) by (intros c Hc; specialize (A c Hc); specialize (G1 c); lia).
      split; [exact A2|]. destruct HX' as (_ & B' & C' & D' & E'). destruct HX as (_ & B & _).
      split; [| split; [lia| split; [exact C'| split; [exact D'| exact E']]]].
      intros c. destruct (Z.eq_dec c 44) as [->|N]; [rewrite G2; lia| specialize (A2 c N); lia]. }
    cbv beta. intros _ s mo (LK2 & H). exists (LK2 ++ LK). rewrite <- app_assoc. exact H.
Qed.

Lemma runC_QP : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> (cap = 65536 \/ MMAP_THRESHOLD <= cap) -> zlength payload <= MAX_INPUT ->
  cspecL (Q [(b, cap)]) (ProgC.runC FM cfg payload) (fun _ s mo => exists LK, Q ((b, cap) :: LK) s mo).
Proof.
  intros b cap cfg payload Hcap Hshape Hp. unfold ProgC.runC, AdapterC.target_run.
  assert (NC : Z.of_nat (Z.to_nat (1 + Z.land cfg 3)) <= 4).
  { assert (E : Z.land cfg 3 = cfg mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound cfg 4 ltac:(lia)). rewrite E. rewrite Z2Nat.id; lia. }
  assert (HB : HOLD [(b, cap)] 1 1 1 (2^26 + 8192)).
  { pose proof (bigb_le cap (2^26 + 64) ltac:(unfold MAX_INPUT in *; lia)) as HBB.
    assert (H0 : HOLD [] 0 0 0 0) by (unfold HOLD, LRX, n63X, R63X; rewrite !zcount_nil; cbn [map zsum fold_right]; splits; [intros; rewrite zcount_nil; lia| lia| lia| rewrite ?zsum_nil; lia| constructor]).
    pose proof (HOLD_cons [] 0 0 0 0 b cap H0 ltac:(unfold MAX_INPUT in *; lia)) as H1.
    eapply HOLD_weak; [exact H1| lia| destruct (negb (MMAP_THRESHOLD <=? cap) && (size_to_class cap =? 44)); lia| lia| lia]. }
  assert (HB44 : forall c, c <> 44 -> LRX [(b, cap)] c = 0).
  { intros c Hc. rewrite LRX_cons. unfold LRX. rewrite zcount_nil.
    destruct (Z.leb_spec MMAP_THRESHOLD cap); cbn [negb andb]; [lia|].
    assert (cap = 65536) by (destruct Hshape; [assumption| lia]). subst cap. rewrite cls_65536. destruct (Z.eqb_spec 44 c); [lia| reflexivity]. }
  eapply cspecL_bind with (Q1 := fun a s mo => match a with
                                               | None => Q [(b, cap)] s mo
                                               | Some None => Q [(b, cap)] s mo
                                               | Some (Some p) => Q [(p, zlength payload); (b, cap)] s mo
                                               end).
  { apply cspecL_lift. unfold AdapterC.payload_copy. apply mspecL_if; intros _; [ret_Q|].
    eapply mspecL_bind.
    - eapply mspecL_pre; [apply malloc_Q; unfold zlength; lia|]. intros s mo HQ. split; [exact HQ|].
      eapply (malok_HOLD _ _ _ _ _ _ HB); unfold MAX_INPUT, RHOLD, W, zlength in *; intros; lia.
    - intros [p|]; apply mspecL_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply cspecL_bind.
    { apply run_callsC_Q. split.
      - intros c Hc. rewrite LRX_cons, (HB44 c Hc). destruct (_ && _); lia.
      - pose proof (HOLD_cons _ _ _ _ _ p (zlength payload) HB ltac:(unfold MAX_INPUT, zlength in *; lia)) as H1.
        eapply HOLD_weak; [exact H1| lia| destruct (_ && _); lia| lia| pose proof (bigb_le (zlength payload) (2^26 + 64) ltac:(unfold MAX_INPUT, zlength in *; lia)); lia]. }
    intros rc. apply cspecL_exI. intros LK.
    eapply cspecL_seq.
    { apply cspecL_lift. eapply mspecL_pre; [apply (free_Q ((b, cap) :: LK) p (zlength payload))|].
      intros s mo H. eapply Q_perm; [| exact H]. symmetry. apply Permutation_cons_app. apply Permutation_cons_append. }
    intros _. apply cspecL_ret. intros s mo H. exists LK. exact H.
  - eapply cspecL_bind.
    { apply run_callsC_Q. split; [intros c Hc; rewrite (HB44 c Hc); lia| eapply HOLD_weak; [exact HB| lia| lia| lia| lia]]. }
    intros rc. apply cspecL_exI. intros LK.
    eapply cspecL_seq; [apply cspecL_lift; ret_Q|]. intros _. apply cspecL_ret. intros s mo H. exists LK.
    eapply Q_perm; [| exact H]. symmetry. apply Permutation_cons_append.
  - apply cspecL_ret. intros s mo H. exists []. exact H.
Qed.
End TARGETP.

Definition Qamb (X : list (bptr * Z)) : assn PState := QI X Pamb.
Definition Qrun (X : list (bptr * Z)) : assn PState := fun s mo =>
  exists P, (forall c, P c <= Penv c) /\ (forall c, validc c = true -> AMBC <= P c) /\ QI X P s mo.

Lemma Qamb_Qrun X s mo : Qamb X s mo -> Qrun X s mo.
Proof. intros H. exists Pamb. split; [exact Pamb_le_Penv|]. split; [exact Pamb_amb| exact H]. Qed.
Lemma Qamb_minv X s mo : Qamb X s mo -> minv mo /\ m_halted mo = None. Proof. apply QI_minv. Qed.
Lemma Qamb_fds X s mo mo' : Qamb X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> Qamb X s mo'. Proof. apply QI_fds. Qed.
Lemma Qamb_live X s mo : Qamb X s mo -> live mo <= LBUDGET. Proof. apply QI_live. Qed.
Lemma Qamb_perm X Y s mo : Permutation X Y -> Qamb X s mo -> Qamb Y s mo. Proof. apply QI_perm. Qed.
Lemma Qrun_live X s mo : Qrun X s mo -> live mo <= LBUDGET. Proof. intros (P & _ & _ & H). eapply QI_live. exact H. Qed.
Lemma Qrun_so X s mo v : Qrun X s mo -> Qrun X (set_so_ps v s) mo.
Proof. intros (P & H1 & H2 & H). exists P. split; [exact H1|]. split; [exact H2|]. apply QI_set_so. exact H. Qed.

Definition malokA (X : list (bptr * Z)) (n : Z) : Prop :=
  forall P, (forall c, P c <= Penv c) -> (forall c, validc c = true -> AMBC <= P c) -> malok P X n.

Lemma malloc_Qamb : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => Qamb X s mo /\ malokA X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Qamb ((p, n) :: X) s mo /\ n < 2^63 | None => Qamb X s mo end).
Proof. intros X n Hn. eapply mspecL_pre; [apply (malloc_Q Pamb X n Hn)|]. intros s mo [HQ HM]. split; [exact HQ|]. apply HM; [exact Pamb_le_Penv| exact Pamb_amb]. Qed.
Lemma free_Qamb : forall X p n, mspecL LBUDGET (Qamb ((p, n) :: X)) (raw_free p) (fun _ => Qamb X).
Proof. intros. unfold Qamb. apply raw_free_LQ. Qed.
Lemma free_Qrun : forall X p n, mspecL LBUDGET (Qrun ((p, n) :: X)) (raw_free p) (fun _ => Qrun X).
Proof.
  intros X p n s mo (P & H1 & H2 & H). eapply etwl_mono; [apply (raw_free_LQ X P p n s mo H)|].
  intros [u s'] mo' HQ. cbn in HQ |- *. exists P. auto.
Qed.

Theorem runC_Q : forall FM b cap cfg payload, 65536 <= cap <= MAX_INPUT -> (cap = 65536 \/ MMAP_THRESHOLD <= cap) -> zlength payload <= MAX_INPUT ->
  cspecL LBUDGET (Qamb [(b, cap)]) (ProgC.runC FM cfg payload) (fun _ s mo => exists LK, Qrun ((b, cap) :: LK) s mo).
Proof.
  intros FM b cap cfg payload Hcap Hshape Hp.
  eapply cspecL_conseq; [apply (runC_QP FM Pamb Pamb_le_Penv Pamb_amb b cap cfg payload Hcap Hshape Hp)| intros s mo H; exact H|].
  cbv beta. intros a s mo [LK H]. exists LK. exists Pamb. split; [exact Pamb_le_Penv|]. split; [exact Pamb_amb| exact H].
Qed.
