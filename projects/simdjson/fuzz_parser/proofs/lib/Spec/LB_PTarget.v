(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjStage1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe STree Malloc KStep MI_Inv MI_Cnt Stdio HarnessP Adapter Driver PState ProgP StepB
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc LB_PCaps LB_Hist LB_Amb LB_PStdio.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Keeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Local Notation mspecL := (mspecL LBUDGET).
Local Ltac ret_Q := apply mspecL_ret; intros ? ? HH; exact HH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_step_keeps_fa : forall atop e, keeps ps_fa (ev_step atop e).
Proof.
  intros atop e. destruct e; cbn [ev_step]; try apply keeps_unr.
  - destruct (_ =? 0); keeps_tac.
  - destruct (negb _); [keeps_tac|]. destruct (_ =? 0); keeps_tac.
  - keeps_tac.
  - keeps_tac.
Qed.

Lemma membed_keeps_fa : forall {R} atop (t : stree ev Z R), keeps ps_fa (membed atop t).
Proof.
  intros R atop t. induction t as [r|e k IH]; cbn [membed]; [apply keeps_ret|].
  apply keeps_bind; [apply ev_step_keeps_fa| exact IH].
Qed.

Lemma raw_malloc_keeps_fa : forall n, keeps ps_fa (raw_malloc n).
Proof.
  intros n. unfold raw_malloc. apply keeps_getk. intros s0. apply keeps_bind; [apply membed_keeps_fa|].
  intros [st' p]. keeps_tac.
Qed.

Lemma raw_free_keeps_fa : forall p, keeps ps_fa (raw_free p).
Proof.
  intros p. unfold raw_free. apply keeps_getk. intros s0. apply keeps_bind; [apply membed_keeps_fa|].
  intros st'. keeps_tac.
Qed.

(* [comment removed for export] *)
Lemma twl_tall : forall {A} B (t : itree node (exc A)) mo (Qm : A -> Model -> Prop) (Phi : A -> Prop),
  etwl B t mo Qm -> tall Phi t -> etwl B t mo (fun a mo' => Qm a mo' /\ Phi a).
Proof.
  intros A B t. induction t as [r|n k IH]; intros mo Qm Phi He Ht.
  - destruct r as [a|]; cbn in *; auto.
  - cbn -[NF] in *. destruct He as [HN He]. split; [exact HN|]. intros rsp mo' evs Hst. destruct (He rsp mo' evs Hst) as [HB He']. split; [exact HB|]. apply IH; [exact He'| apply Ht].
Qed.

Lemma mspecL_tall {A} (P0 : assn PState) (m : Monad.M PState A) (R : A -> assn PState) (Phi : A * PState -> Prop) :
  mspecL P0 m R -> (forall s, tall Phi (m s)) -> mspecL P0 m (fun a s mo => R a s mo /\ Phi (a, s)).
Proof.
  intros Hm Ht s mo HP. eapply etwl_mono; [apply (twl_tall LBUDGET (m s) mo _ Phi (Hm s mo HP) (Ht s))|]. intros [a s'] mo' [H1 H2]. cbn. auto.
Qed.

(* [comment removed for export] *)
Lemma mspecL_keeps_fa {A} (c : option bptr) (P0 : assn PState) (m : Monad.M PState A) (R : A -> assn PState) :
  mspecL P0 m R -> keeps ps_fa m ->
  mspecL (fun s mo => P0 s mo /\ ps_fa s = c) m (fun a s mo => R a s mo /\ ps_fa s = c).
Proof.
  intros Hm Hk s mo [HP Hc].
  eapply etwl_mono; [apply (twl_tall LBUDGET (m s) mo _ (fun p => ps_fa (snd p) = ps_fa s) (Hm s mo HP) (Hk s))|].
  intros [a s'] mo' [H1 H2]. cbn in *. split; [exact H1| congruence].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMBP : Z := 16.
Definition PambP (c : Z) : Z := if validc c then AMBP else 0.

Lemma PambP_nonneg c : 0 <= PambP c.
Proof. unfold PambP, AMBP. destruct (validc c); lia. Qed.

Lemma PambP_ok : PQOK PambP.
Proof. vm_compute. split; discriminate. Qed.

Lemma PHI_PambP : PHI PambP <= 2^28.      (* [comment removed for export] *)
Proof. vm_compute. discriminate. Qed.

Lemma PHI_PambP_budget : PHI PambP <= LBUDGET.
Proof. pose proof PHI_PambP. unfold LBUDGET. lia. Qed.

Definition Qamb (X : list (bptr * Z)) : assn PState := QI X PambP.

Lemma Qamb_minv X s mo : Qamb X s mo -> minv mo /\ m_halted mo = None. Proof. apply QI_minv. Qed.
Lemma Qamb_fds X s mo mo' : Qamb X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> Qamb X s mo'.
Proof. apply QI_fds. Qed.
Lemma Qamb_live X s mo : Qamb X s mo -> live mo <= LBUDGET. Proof. apply QI_live. Qed.
Lemma Qamb_so X s mo v : Qamb X s mo -> Qamb X (set_so_ps v s) mo. Proof. apply QI_set_so. Qed.
Lemma Qamb_perm X Y s mo : Permutation X Y -> Qamb X s mo -> Qamb Y s mo. Proof. apply QI_perm. Qed.

(* [comment removed for export] *)
Definition malok (X : list (bptr * Z)) (n : Z) : Prop := ROOMX X PambP n /\ PHI PambP + R63X X + bigb n <= LBUDGET /\ n <= NREQ.
Definition malokA (X : list (bptr * Z)) (n : Z) : Prop := malok X n.

(* [comment removed for export] *)
Definition zsz (X : list (bptr * Z)) : Z := zsum (map snd X).
Lemma zsz_cons p n X : zsz ((p, n) :: X) = n + zsz X.
Proof. reflexivity. Qed.
Lemma zsz_app X Y : zsz (X ++ Y) = zsz X + zsz Y.
Proof. unfold zsz. rewrite map_app. apply zsum_app. Qed.

Lemma bigb_le : forall n, 0 <= n -> bigb n <= n + 4116.
Proof.
  intros n Hn. unfold bigb. destruct (_ <=? _); [|lia].
  rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
  pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia.
Qed.

Lemma counts_le : forall X, Forall (fun b => 0 <= snd b) X ->
  (forall c, LRX X c <= Z.of_nat (length X)) /\ n63X X <= Z.of_nat (length X) /\ R63X X <= zsz X + 4116 * Z.of_nat (length X).
Proof.
  induction X as [|[p n] X IH]; intros HF.
  - unfold LRX, n63X, R63X, zsz, zsum, zcount, zlen. cbn. repeat split; intros; lia.
  - apply Forall_cons_iff in HF as [Hn HF]. cbn [snd] in Hn. destruct (IH HF) as (A1 & A2 & A3). cbn [length]. rewrite Nat2Z.inj_succ.
    rewrite zsz_cons. split; [| split].
    + intros c. rewrite LRX_cons. specialize (A1 c). destruct (_ && _); lia.
    + rewrite n63X_cons. destruct (_ <=? _); lia.
    + rewrite R63X_cons. pose proof (bigb_le n Hn). lia.
Qed.

Lemma malok_sum : forall X n, (length X <= 15)%nat -> Forall (fun b => 0 <= snd b) X -> 0 <= n <= NREQ -> zsz X + n <= 2^30 -> malok X n.
Proof.
  intros X n HL HF Hn HS. destruct (counts_le X HF) as (A1 & A2 & A3). pose proof (bigb_le n ltac:(lia)) as Bb. pose proof PHI_PambP as PH.
  assert (ZX : 0 <= zsz X).
  { clear -HF. induction X as [|[p m] X IH]; [unfold zsz; cbn; lia|]. apply Forall_cons_iff in HF as [Hm HF]. rewrite zsz_cons. cbn [snd] in Hm. pose proof (IH HF). lia. }
  split; [| split; [unfold LBUDGET; lia| lia]].
  split.
  - intros Hsmall. pose proof (validc_cls n ltac:(lia)) as Vc. specialize (A1 (size_to_class n)). unfold PambP. rewrite Vc. unfold AMBP. lia.
  - intros Hbig. unfold PambP. rewrite validc_63. unfold AMBP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma malloc_Qamb : forall X n, 0 <= n ->
  mspecL (fun s mo => Qamb X s mo /\ malokA X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Qamb ((p, n) :: X) s mo /\ n < 2^63 | None => Qamb X s mo end).
Proof.
  intros X n Hn. eapply mspecL_pre; [apply (raw_malloc_LQ X PambP n Hn)|].
  intros s mo [HQ (H1 & H2 & H3)]. auto.
Qed.

Lemma free_Qamb : forall X p n, mspecL (Qamb ((p, n) :: X)) (raw_free p) (fun _ => Qamb X).
Proof. intros X p n. apply (raw_free_LQ X PambP p n). Qed.

Lemma emit_Qamb : forall X v, mspecL (Qamb X) (io_emit io v) (fun _ => Qamb X).
Proof. intros X v. cbn [io io_emit io_S]. apply (s_emit_L LBUDGET (Qamb X) (Qamb_live X) (Qamb_so X)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DRV (A : list (bptr * Z)) : Prop := (length A <= 2)%nat /\ Forall (fun b => 0 <= snd b <= MAX_INPUT) A.

Lemma zsz_le_len : forall A M, Forall (fun b => 0 <= snd b <= M) A -> zsz A <= Z.of_nat (length A) * M.
Proof.
  induction A as [|[p n] A IH]; intros M HF; [unfold zsz; cbn; lia|].
  apply Forall_cons_iff in HF as [Hn HF]. rewrite zsz_cons. cbn [length snd] in *. pose proof (IH M HF). lia.
Qed.

Lemma DRV_facts : forall A, DRV A -> (length A <= 2)%nat /\ Forall (fun b => 0 <= snd b) A /\ zsz A <= 2 * MAX_INPUT.
Proof.
  intros A [HL HF]. split; [exact HL|]. split; [eapply Forall_impl; [| exact HF]; intros b Hb; cbv beta in *; lia|].
  pose proof (zsz_le_len A MAX_INPUT HF). unfold MAX_INPUT in *. nia.
Qed.

(* [comment removed for export] *)
Lemma psum_ok : forall len, 0 <= len <= MAX_INPUT ->
  0 < SB_BYTES len /\ 0 < TAPE_BYTES len /\ 0 < IMPL_BYTES /\ 0 < SIDX_BYTES len /\ 0 < OC_BYTES /\ 0 < ISARR_BYTES /\ 0 < COPY_BYTES len
  /\ SB_BYTES len + TAPE_BYTES len + IMPL_BYTES + SIDX_BYTES len + OC_BYTES + ISARR_BYTES <= 2^30 - 2^27 - 2^22
  /\ SB_BYTES len <= 2^29 /\ TAPE_BYTES len <= 2^29 + 1024 /\ SIDX_BYTES len <= 2^29.
Proof.
  intros len Hl. pose proof (sizes_pos len ltac:(lia)) as P. pose proof (sizes_upper len ltac:(lia)) as U.
  assert (C : HarnessP.CAP len <= MAX_INPUT) by (unfold HarnessP.CAP, MAX_INPUT in *; lia).
  pose proof (Z.div_le_upper_bound (HarnessP.CAP len) 3 (MAX_INPUT / 3 + 1) ltac:(lia) ltac:(unfold MAX_INPUT in *; cbn; lia)).
  unfold MAX_INPUT in *. cbn in *. lia.
Qed.

Lemma copy_made_le : forall len, copy_made len = true -> COPY_BYTES len <= 2^20.
Proof. intros len H. unfold copy_made, COPY_LIMIT in H. apply Z.leb_le in H. exact H. Qed.

Lemma opnew_Q : forall X n, 0 < n -> malok X n ->
  mspecL (Qamb X) (HarnessP.opnew raw_malloc new_handler n) (fun p => Qamb ((p, n) :: X)).
Proof.
  intros X n Hn HM. unfold HarnessP.opnew. cbv zeta. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  eapply mspecL_bind.
  - eapply mspecL_pre; [apply (malloc_Qamb X n); lia|]. intros s mo H. split; [exact H| exact HM].
  - intros [p|]; cbn beta iota.
    + apply mspecL_ret. intros s mo [H _]. exact H.
    + eapply mspecL_bind; [unfold new_handler; apply (mspecL_munr LBUDGET _ (fun _ _ _ => False))|]. intros [].
Qed.

Lemma opdelete_Q : forall X p n, mspecL (Qamb ((p, n) :: X)) (HarnessP.opdelete raw_free p) (fun _ => Qamb X).
Proof. intros X p n. unfold HarnessP.opdelete. apply free_Qamb. Qed.

(* [comment removed for export] *)
Definition pblQ (len : Z) (b : bptr * bptr * (bptr * bptr * bptr * bptr) * option bptr) : list (bptr * Z) :=
  let '(sb, tp, (im, si, oc, ia), lb) := b in
  match lb with Some p => [(p, COPY_BYTES len)] | None => [] end
  ++ [(sb, SB_BYTES len); (tp, TAPE_BYTES len); (ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES)].

Lemma pblQ_perm : forall (x1 x2 x3 x4 x5 x6 : bptr * Z) (X : list (bptr * Z)),
  Permutation ([x6; x5; x4; x3; x2; x1] ++ X) ([x1; x2; x6; x5; x4; x3] ++ X).
Proof.
  intros x1 x2 x3 x4 x5 x6 X. apply Permutation_app_tail.
  change [x1; x2; x6; x5; x4; x3] with ([x1; x2] ++ [x6; x5; x4; x3]). change [x6; x5; x4; x3; x2; x1] with ([x6; x5; x4; x3] ++ [x2; x1]).
  eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply perm_swap.
Qed.

Ltac mal_ok := apply malok_sum; [ cbn [length app] in *; lia
                                | cbn [app]; repeat (apply Forall_cons; [cbn [snd]; lia|]); assumption
                                | unfold NREQ, IMPL_BYTES, OC_BYTES, ISARR_BYTES, MAX_DEPTH in *; cbn [snd] in *; unfold MAX_INPUT in *; lia
                                | cbn [app]; rewrite ?zsz_cons; cbn [snd] in *; unfold MAX_INPUT in *; lia ].

Lemma parse_into_doc_Q : forall A data, DRV A -> zlength data <= MAX_INPUT ->
  mspecL (Qamb A) (parse_into_doc raw_malloc raw_free new_handler data) (fun b => Qamb (pblQ (zlength data) b ++ A)).
Proof.
  intros A data HA Hl. assert (H0 : 0 <= zlength data) by (unfold zlength; lia).
  destruct (DRV_facts A HA) as (AL & AF & AZ).
  destruct (psum_ok (zlength data) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & SS & B1 & B2 & B3).
  unfold parse_into_doc. cbv zeta.
  eapply mspecL_bind with (Q1 := fun dd => Qamb ((snd dd, TAPE_BYTES (zlength data)) :: (fst dd, SB_BYTES (zlength data)) :: A)).
  { unfold doc_allocate. eapply mspecL_bind; [apply opnew_Q; [exact S1| mal_ok]|]. intros sb.
    eapply mspecL_bind; [apply opnew_Q; [exact S2| mal_ok]|]. intros tp. apply mspecL_ret. intros s mo H; exact H. }
  intros [sb tp]. cbn [fst snd].
  eapply mspecL_bind with (Q1 := fun ii => match ii with (im, si, oc, ia) =>
     Qamb ((ia, ISARR_BYTES) :: (oc, OC_BYTES) :: (si, SIDX_BYTES (zlength data)) :: (im, IMPL_BYTES)
           :: (tp, TAPE_BYTES (zlength data)) :: (sb, SB_BYTES (zlength data)) :: A) end).
  { unfold impl_create, impl_set_capacity, impl_set_max_depth.
    eapply mspecL_bind; [apply opnew_Q; [exact S3| mal_ok]|]. intros im.
    eapply mspecL_bind; [apply opnew_Q; [exact S4| mal_ok]|]. intros si.
    eapply mspecL_bind with (Q1 := fun oi => match oi with (oc, ia) =>
       Qamb ((ia, ISARR_BYTES) :: (oc, OC_BYTES) :: (si, SIDX_BYTES (zlength data)) :: (im, IMPL_BYTES)
             :: (tp, TAPE_BYTES (zlength data)) :: (sb, SB_BYTES (zlength data)) :: A) end).
    - eapply mspecL_bind; [apply opnew_Q; [exact S5| mal_ok]|]. intros oc.
      eapply mspecL_bind; [apply opnew_Q; [exact S6| mal_ok]|]. intros ia. apply mspecL_ret. intros s mo H; exact H.
    - intros [oc ia]. cbv beta iota. apply mspecL_ret. intros s mo H; exact H. }
  intros [[[im si] oc] ia]. cbv beta iota.
  eapply mspecL_bind with (Q1 := fun lb s mo =>
     Qamb (match lb with Some p => [(p, COPY_BYTES (zlength data))] | None => [] end
           ++ (ia, ISARR_BYTES) :: (oc, OC_BYTES) :: (si, SIDX_BYTES (zlength data)) :: (im, IMPL_BYTES)
           :: (tp, TAPE_BYTES (zlength data)) :: (sb, SB_BYTES (zlength data)) :: A) s mo
     /\ (lb <> None -> copy_made (zlength data) = true)).
  { unfold padded_alloc. destruct (copy_made (zlength data)) eqn:CM.
    - pose proof (copy_made_le (zlength data) CM) as CL.
      eapply mspecL_bind; [apply opnew_Q; [exact S7| mal_ok]|]. intros p. apply mspecL_ret. intros s mo H. split; [exact H| intros _; reflexivity].
    - apply mspecL_ret. intros s mo H. split; [exact H| intros C; exfalso; apply C; reflexivity]. }
  intros lb.
  eapply mspecL_seq with (R := Qamb (match lb with Some p => [(p, COPY_BYTES (zlength data))] | None => [] end
           ++ (ia, ISARR_BYTES) :: (oc, OC_BYTES) :: (si, SIDX_BYTES (zlength data)) :: (im, IMPL_BYTES)
           :: (tp, TAPE_BYTES (zlength data)) :: (sb, SB_BYTES (zlength data)) :: A)).
  - destruct lb as [p|]; cbv beta.
    + apply mspecL_pure. intros CMi. pose proof (copy_made_le (zlength data) (CMi ltac:(discriminate))) as CL.
      unfold parse_impl, root_copy. destruct (root_number_alloc data) as [n|] eqn:E.
      * pose proof (root_number_alloc_bound data n E) as RB. change (Z.of_nat (length data)) with (zlength data) in RB.
        pose proof CL as CL'. unfold COPY_BYTES, PADDING in CL'.
        eapply mspecL_bind; [apply opnew_Q; [lia| mal_ok]|]. intros q. apply opdelete_Q.
      * apply mspecL_ret. intros s mo H. exact H.
    + apply mspecL_ret. intros s mo [H _]. exact H.
  - intros _. apply mspecL_ret. intros s mo H. cbn [pblQ]. rewrite <- app_assoc.
    eapply Qamb_perm; [| exact H]. apply Permutation_app_head. apply pblQ_perm.
Qed.

Lemma parser_dtor_Q : forall A len b, mspecL (Qamb (pblQ len b ++ A)) (parser_dtor raw_free b) (fun _ => Qamb A).
Proof.
  intros A len [[[sb tp] [[[im si] oc] ia]] lb]. unfold parser_dtor, pblQ. cbv beta iota.
  eapply mspecL_seq with (R := Qamb ([(sb, SB_BYTES len); (tp, TAPE_BYTES len); (ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES)] ++ A)).
  { destruct lb as [p|]; unfold odelete; [apply opdelete_Q| apply mspecL_ret; intros s mo H; exact H]. }
  intros _. eapply mspecL_seq with (R := Qamb ([(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES)] ++ A)).
  { unfold doc_dtor. eapply mspecL_seq; [apply opdelete_Q|]. intros _. apply opdelete_Q. }
  intros _. unfold impl_dtor.
  eapply mspecL_seq; [apply opdelete_Q|]. intros _.
  eapply mspecL_seq; [apply opdelete_Q|]. intros _.
  eapply mspecL_seq; [apply opdelete_Q|]. intros _.
  apply opdelete_Q.
Qed.

Lemma fuzz_one_Q : forall A data, DRV A -> zlength data <= MAX_INPUT ->
  mspecL (Qamb A) (fuzz_one data) (fun _ => Qamb A).
Proof.
  intros A data HA Hl. unfold fuzz_one, HarnessP.fuzz_one.
  eapply mspecL_bind; [apply parse_into_doc_Q; assumption|]. intros b.
  eapply mspecL_seq; [apply parser_dtor_Q|]. intros _. ret_Q.
Qed.

Lemma client_exit_Q : forall X, mspecL (Qamb X) client_exit (fun _ => Qamb X).
Proof. intros X. unfold client_exit, HarnessP.client_exit. ret_Q. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_Q : forall A n payload rc, DRV A -> zlength payload <= MAX_INPUT ->
  mspecL (Qamb A) (run_calls fuzz_one (io_emit io) n payload rc) (fun _ => Qamb A).
Proof.
  intros A n. induction n as [|n IH]; intros payload rc HA Hl; cbn [run_calls]; [ret_Q|].
  eapply mspecL_seq; [apply fuzz_one_Q; assumption|]. intros rc'.
  eapply mspecL_seq; [apply emit_Qamb|]. intros _. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Theorem run_Q : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL (Qamb [(b, cap)]) (run cfg payload) (fun _ => Qamb [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hp. unfold run, target_run.
  assert (HA1 : DRV [(b, cap)]) by (split; [cbn; lia| constructor; [cbn; lia| constructor]]).
  eapply mspecL_bind with (Q1 := fun a s mo => match a with
                                               | None => Qamb [(b, cap)] s mo
                                               | Some None => Qamb [(b, cap)] s mo
                                               | Some (Some p) => Qamb [(p, zlength payload); (b, cap)] s mo
                                               end).
  { apply mspecL_if; intros _; [ret_Q|].
    eapply mspecL_bind.
    - eapply mspecL_pre; [apply malloc_Qamb; unfold zlength; lia|]. intros s mo HQ. split; [exact HQ|].
      apply malok_sum; [cbn; lia| constructor; [cbn; lia| constructor]| unfold NREQ, MAX_INPUT in *; unfold zlength in *; lia|].
      unfold zsz. cbn. unfold MAX_INPUT in *. lia.
    - intros [p|]; apply mspecL_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecL_seq; [apply run_calls_Q; [split; [cbn; lia| constructor; [cbn; unfold zlength in *; lia| exact (proj2 HA1)]]| exact Hp]|]. intros rc.
    eapply mspecL_seq; [apply free_Qamb|]. intros _. ret_Q.
  - eapply mspecL_seq; [apply run_calls_Q; [exact HA1| exact Hp]|]. intros rc. eapply mspecL_seq; [ret_Q|]. intros _. ret_Q.
  - ret_Q.
Qed.

(* [comment removed for export] *)
Lemma OK_firstQ : malokA [] 65536.
Proof. apply malok_sum; [cbn; lia| constructor| unfold NREQ; lia| unfold zsz; cbn; lia]. Qed.

Lemma OK_growQ : forall b k, (k <= 9)%nat -> malokA [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
  intros b k Hk. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as Hq.
  assert (Hp : 2 ^ Z.of_nat k <= 512). { change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia. }
  apply malok_sum; [cbn; lia| constructor; [cbn; lia| constructor]| unfold NREQ; lia| unfold zsz; cbn; lia].
Qed.
