(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Decode NodesCfg DecodeCfg NodesCfgA. Import NodesCfgA.A.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad MSafeA STree Malloc Stdio Harness Target TargetSafe Driver Prog KInv KStep KStepC MallocSome.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Image.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation nstep := NodesCfgA.nstep_a (only parsing).
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DriverSpec.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable rstage : Z.            (* [comment removed for export] *)
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> Monad.M St Z.
Variable alloc_count : Monad.M St Z.
(* [comment removed for export] *)
Variable own : list ptr -> assn St.

(* [comment removed for export] *)
Definition diag_ok (d : diag_msg) : Prop :=
  match d with
  | DUsage a | DCannotOpen a | DReadError a => zlength a < 2^32
  | _ => True
  end.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspec (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, diag_ok d -> mspec (own X) (io_diag io d) (fun _ => own X).
Hypothesis Hexit : forall X, mspec (own X) (io_exit io) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspec (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspec (own X) alloc_count (fun _ => own X).
Hypothesis Hrun : forall X cfg payload, zlength payload <= MAX_INPUT ->
  mspec (own X) (run cfg payload) (fun _ s mo => exists Y, own (Y ++ X) s mo).   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
  m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.

Lemma own_after_node : forall X s mo n rsp mo' evs,
  own X s mo -> nsafe n mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> own X s mo'.
Proof.
  intros X s mo n rsp mo' evs Ho Hsafe Hst Hvm. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hsafe Hst) as [Hh' Hmi']. eapply Hown_fds; eauto.
Qed.

(* [comment removed for export] *)
Definition rd_inv (X : list ptr) (st : rd_st) : assn St := fun s mo =>
  own (rd_buf st :: X) s mo
  /\ zlength (rd_content st) <= rd_cap st
  /\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k)).

Definition rd_meas (st : @rd_st ptr) : nat := Z.to_nat (MAX_INPUT + 1 - zlength (rd_content st)).

Lemma zlength_app {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_u8s : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.

Lemma pow2_le_1024 : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof.
  intros k Hk. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia.
Qed.

Lemma read_loop_body_spec : forall X fd path st,
  zlength path < 2^32 -> 0 <= fd ->
  mspec (rd_inv X st) (read_loop_body io drv_malloc drv_free rstage fd path st)
        (fun r s mo => match r with
                       | inl st' => rd_inv X st' s mo /\ (rd_meas st' < rd_meas st)%nat
                       | inr RdExit => exists X', own X' s mo
                       | inr (RdDone buf content) => own (buf :: X) s mo /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros X fd path st Hpath Hfd. unfold read_loop_body.
  eapply mspec_bind with
    (Q1 := fun g s mo => match g with
                         | None => exists X', own X' s mo
                         | Some st1 => rd_inv X st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                         end).
  { apply mspec_if_pre.
    - apply mspec_if_pre.
      + eapply mspec_seq; [eapply mspec_pre; [apply Hdiag; exact I|]|].
        { intros s mo [[[Ho _] _] _]. exact Ho. }
        intros _. apply mspec_ret. intros s mo Ho. exists (rd_buf st :: X). exact Ho.
      + apply mspec_pointwise. intros s0 mo0 [[(Ho0 & Hlen & k & Hk & Hcap) Heq] Hlt].
        apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
        pose proof (pow2_le_1024 k Hk) as Hp.
        eapply mspec_bind. { eapply mspec_pre; [apply Hdm; lia|]. intros s mo [-> ->]. exact Ho0. }
        intros [nb|]; cbn beta iota.
        * apply mspec_pure. intros _. eapply mspec_seq.
          { eapply mspec_pre; [apply (Hdf (nb :: X) (rd_buf st))|].
            intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
          intros _. apply mspec_ret. intros s mo Ho. cbn. unfold rd_inv. cbn. splits; auto; try lia.
          exists (S k). split; [unfold MAX_INPUT in Hlt; assert (k <> 10)%nat by (intros ->; cbn in Hcap; lia); lia|].
          rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
        * eapply mspec_seq; [apply Hdiag; exact I|]. intros _. apply mspec_ret. intros s mo Ho. exists (rd_buf st :: X). exact Ho.
    - apply mspec_ret. intros s mo [[Ho [Hlen Hk]] Hne]. apply Z.eqb_neq in Hne. split; [|split; [reflexivity|lia]]. split; [exact Ho|]. auto. }
  intros [st1|]; cbn beta iota.
  2:{ apply mspec_ret. intros s mo H. exact H. }
  eapply mspec_bind; [apply mspec_get|]. intros sg. cbn beta iota.
  apply mspec_pointwise. intros s1 mo1 [Hsg ((Ho & Hlen & k & Hk & Hcap) & Hct & Hlt)]. subst sg.
  pose proof (pow2_le_1024 k Hk) as Hp.
  apply mspec_bind with (Q1 := fun a s mo => s = s1 /\ own (rd_buf st1 :: X) s mo /\
                       match a with RdErr _ => True | RdData bs => zlength bs <= rd_cap st1 - zlength (rd_content st) end).
  { apply mspec_sys. intros s mo [-> ->]. split; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (nstep_dec_read fd _ (Z.min (rd_cap st1 - zlength (rd_content st)) 65536) mo1 rsp mo' evs ltac:(unfold MAX_INPUT, zlength in *; lia) Hst) as (_ & a & Hdec & Ha).
    exists a. split; [exact Hdec|].
    cbn beta. split; [reflexivity|].
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
    { destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
      destruct Ha as (p & off & data & _ & _ & _ & ->). reflexivity. }
    split; [eapply own_after_node; eauto; exact I|].
    destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
    unfold zlength. pose proof (length_file_read_le_count data off (Z.min (rd_cap st1 - Z.of_nat (length (rd_content st))) 65536) ltac:(unfold zlength, MAX_INPUT in *; lia)). lia. }
  intros [e|bs]; cbn beta iota.
  - eapply mspec_seq. { eapply mspec_pre; [apply Hdiag; exact Hpath|]. intros s mo (_ & Ho' & _). exact Ho'. }
    intros _. apply mspec_ret. intros s mo Ho'. exists (rd_buf st1 :: X). exact Ho'.
  - apply mspec_if; intros C.
    + apply mspec_ret. intros s mo (-> & Ho' & _). split; [exact Ho'|]. rewrite Hct. unfold MAX_INPUT in *. lia.
    + apply mspec_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
      assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
      split.
      * unfold rd_inv. cbn. split; [exact Ho'|]. rewrite zlength_app, zlength_u8s, Hct. split; [lia|]. exists k. auto.
      * unfold rd_meas. cbn. rewrite zlength_app, zlength_u8s, Hct. unfold MAX_INPUT in *. lia.
Qed.

Lemma m_vmmaps_with_fds : forall f mo, m_vmmaps (with_fds f mo) = m_vmmaps mo.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma read_all_spec : forall X path, zlength path < 2^32 -> path_okZ path ->
  mspec (own X) (read_all io drv_malloc drv_free rstage path)
        (fun r s mo => match r with
                       | RdExit => exists X', own X' s mo
                       | RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros X path Hpath Hpok. unfold read_all.
  apply mspec_bind with (Q1 := fun r s mo => own X s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
  { apply mspec_sys. intros s mo Ho. split; [exact Hpok|]. intros rsp mo' evs Hst.
    destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
    pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
    exists a. split; [exact Hdec|]. cbn beta.
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo).
    { destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). reflexivity. }
    split; [eapply own_after_node; eauto; exact Hpok|]. destruct a as [e|fd]; [exact I|]. lia. }
  intros [e|fd]; cbn beta iota.
  - apply mspec_pure. intros _. eapply mspec_seq; [apply Hdiag; exact Hpath|]. intros _. apply mspec_ret. intros s mo Ho. exists X. exact Ho.
  - apply mspec_pure. intros Hfd. eapply mspec_bind; [apply Hdm; lia|]. intros [buf|]; cbn beta iota.
    2:{ eapply mspec_seq; [apply Hdiag; exact I|]. intros _. apply mspec_ret. intros s mo Ho. exists X. exact Ho. }
    apply mspec_pure. intros _.
    eapply mspec_bind.
    + eapply mspec_pre.
      * apply (mspec_loop (read_loop_body io drv_malloc drv_free rstage fd path) (rd_inv X)
                 (fun r s mo => match r with RdExit => exists X', own X' s mo
                                | RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT end)
                 rd_meas).
        { intros st. eapply mspec_post; [apply read_loop_body_spec; [exact Hpath| exact Hfd]|].
          intros [st'|[|b c]] s mo H; exact H. }
        unfold rd_meas, READ_FUEL. cbn [rd_content]. unfold zlength. cbn [length Z.of_nat]. unfold MAX_INPUT. lia.
      * intros s mo Ho. unfold rd_inv. cbn. split; [exact Ho|]. split; [unfold zlength; cbn; lia|]. exists 0%nat. split; [lia|reflexivity].
    + intros [|buf' content]; cbn beta iota; [apply mspec_ret; intros s mo H; exact H|].
      apply mspec_pointwise. intros s1 mo1 [Ho1 Hlen].
      eapply mspec_bind with (Q1 := fun _ s mo => own (buf' :: X) s mo).
      * apply mspec_sys. intros s mo [-> ->]. split; [exact I|]. intros rsp mo' evs Hst.
        pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
        exists a. split; [exact Hdec|]. cbn beta.
        assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
        { destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). reflexivity. }
        eapply own_after_node; eauto; exact I.
      * intros _. apply mspec_ret. intros s mo Ho. split; [exact Ho| exact Hlen].
Qed.

Lemma skipn_length_le {A} (n : nat) (l : list A) : (length (skipn n l) <= length l)%nat.
Proof. rewrite length_skipn. lia. Qed.

Lemma main_model_spec : forall X argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspec (own X) (main_model io drv_malloc drv_free rstage alloc_init run alloc_count argv)
        (fun _ s mo => exists X', own X' s mo).
Proof.
  intros X argv Hargv Hpaths. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) < 2^32).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength; cbn; lia].
    exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
  apply mspec_if; intros Hlen2.
  { eapply mspec_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply mspec_ret. intros s mo Ho. exists X; exact Ho. }
  assert (Hp1 : path_okZ (nth 1 argv [])).
  { apply Bool.negb_false_iff in Hlen2. apply Z.eqb_eq in Hlen2.
    destruct argv as [|a0 [|a1 rest]]; cbn in Hlen2; try lia. cbn. inversion Hpaths; assumption. }
  eapply mspec_bind; [apply read_all_spec; [apply Hnth| exact Hp1]|].
  intros [|buf content]; cbn beta iota; [apply mspec_ret; intros s mo H; exact H|].
  apply mspec_pure. intros Hlen.
  apply mspec_if; intros _.
  { eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
  apply mspec_if; intros _.
  { eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
  eapply mspec_seq; [apply Hinit|]. intros _.
  eapply mspec_seq; [apply Hrun; etransitivity; [| exact Hlen]; unfold zlength; rewrite length_skipn; lia|]. intros status.
  apply mspec_exI. intros Y.
  eapply mspec_seq with (R := own (Y ++ buf :: X)).
  { destruct (Z.testbit _ 15); [|apply mspec_ret; intros s mo H; exact H].
    eapply mspec_seq; [apply Hcount|]. intros n. apply mspec_ret. intros s mo H; exact H. }
  intros status'. eapply mspec_seq.
  { eapply mspec_pre; [apply (Hdf (Y ++ X) buf)|]. intros s mo H. eapply Hperm; [|exact H]. apply Permutation_sym, Permutation_middle. }
  intros _. apply mspec_ret. intros s mo Ho. exists (Y ++ X). exact Ho.
Qed.

Lemma exit_model_spec : forall code,
  mspec (fun s mo => exists X, own X s mo) (exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold exit_model. eapply mspec_seq with (R := fun s mo => exists X, own X s mo).
  - apply mspec_exI. intros X. eapply mspec_post; [apply Hexit|]. intros a s mo Ho. exists X. exact Ho.
  - intros _. apply mspec_sys. intros s mo _. split; [exact I|]. intros rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End DriverSpec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition so_ok (so : stdout_st) : Prop := zlength (so_buf so) <= STDOUT_BUFSIZ.
Definition Gso : PState -> Model -> Prop := fun s _ => so_ok (ps_so s).

Lemma frame_ok_Gso : frame_ok Gso.
Proof. intros s s' mo mo' _ Hso _ H. unfold Gso in *. rewrite Hso. exact H. Qed.

Definition GI (X : list bptr) : assn PState := OWN X Gso.

Lemma KL_fds : forall L pbrk mo mo',
  KL L pbrk mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' K Hvm Hmi Hh. destruct K. constructor; try (rewrite Hvm); auto.
Qed.

Lemma GI_minv : forall X s mo, GI X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo [(L & _ & K & _) _]. split; [exact (kl_minv _ _ _ K)| exact (kl_halt _ _ _ K)]. Qed.

Lemma GI_fds : forall X s mo mo', GI X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> GI X s mo'.
Proof.
  intros X s mo mo' [(L & Hc & K & Hi) [Hnd HG]] Hvm Hmi Hh. split; [|split; [exact Hnd| exact HG]].
  exists L. split; [exact Hc|]. split; [eapply KL_fds; eauto| exact Hi].
Qed.

Lemma GI_perm : forall X Y s mo, Permutation X Y -> GI X s mo -> GI Y s mo.
Proof. intros. eapply OWN_perm; eauto. Qed.

Lemma GI_after_node : forall X s mo n rsp mo' evs,
  GI X s mo -> nsafe n mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> GI X s mo'.
Proof.
  intros X s mo n rsp mo' evs Ho Hsafe Hst Hvm. destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hsafe Hst) as [Hh' Hmi']. eapply GI_fds; eauto.
Qed.

(* [comment removed for export] *)
Lemma GI_set_so : forall X s mo v, GI X s mo -> so_ok v -> GI X (set_so_ps v s) mo.
Proof. intros X s mo v H Hv. eapply OWN_other; [exact H|reflexivity|reflexivity| exact Hv]. Qed.

(* [comment removed for export] *)
Lemma raw_malloc_GI : forall X n, 0 <= n ->
  mspec (GI X) (raw_malloc n) (fun r s mo => match r with Some p => GI (p :: X) s mo /\ n < 2^63 | None => GI X s mo end).
Proof. intros. apply mspec_of_c. apply raw_malloc_spec_c; [apply frame_ok_Gso| assumption]. Qed.
Lemma raw_free_GI : forall X p, mspec (GI (p :: X)) (raw_free p) (fun _ => GI X).
Proof. intros. apply mspec_of_c. apply raw_free_spec_c. apply frame_ok_Gso. Qed.

(* [comment removed for export] *)
Lemma raw_malloc_GI_some : forall X n, 0 <= n < 2^62 ->
  mspec (GI X) (raw_malloc n) (fun r s mo => exists p, r = Some p /\ GI (p :: X) s mo).
Proof.
  intros X n Hn.
  eapply mspec_post; [apply (mspec_path (GI X) (raw_malloc n) _ (fun r _ _ => r <> None) (raw_malloc_GI X n ltac:(lia)))|].
  - intros s mo HG tr a s' mo' Hp. destruct (GI_minv _ _ _ HG) as [Hmi Hh].
    apply (raw_malloc_some_path n s mo tr a s' mo'); [unfold size_overflows; apply Z.leb_gt; lia| | exact Hmi| exact Hh| exact Hp].
    exact (twf_tsafe _ _ _ (raw_malloc_GI X n ltac:(lia) s mo HG)).
  - intros [p|] s mo [H Hne]; [exists p; split; [reflexivity| exact (proj1 H)]| contradiction].
Qed.

Lemma alloc_init_GI : forall X bm, mspec (GI X) (alloc_init bm) (fun _ => GI X).
Proof. intros. unfold alloc_init. apply mspec_ret. intros s mo H; exact H. Qed.
Lemma alloc_count_GI : forall X, mspec (GI X) alloc_count (fun _ => GI X).
Proof. intros. unfold alloc_count. apply mspec_ret. intros s mo H; exact H. Qed.

Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

(* [comment removed for export] *)
Lemma startup_GI : forall X, mspec (GI X) startup (fun _ => GI X).
Proof.
  intros X. unfold startup. eapply mspec_seq; [|intros _; apply mspec_ret; intros s mo H; exact H].
  apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
  pose proof (nstep_dec_set_tid mo rsp mo' evs Hmi Hst) as (_ & t & Hdec & _ & Hmo).
  exists t. split; [exact Hdec|]. eapply GI_after_node; [exact Ho| | exact Hst|]; [exact I|].
  destruct Hmo as [[_ ->]|[_ ->]]; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zlength_app' {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_skipn_le : forall {A} n (l : list A), zlength (skipn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite length_skipn. lia. Qed.
Lemma zlength_firstn_le : forall {A} n (l : list A), zlength (firstn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite length_firstn. lia. Qed.
Lemma zlength_zdrop : forall n (l : list Z), 0 <= n <= zlength l -> zlength (zdrop n l) = zlength l - n.
Proof. intros. unfold zdrop, zlength in *. rewrite length_skipn. lia. Qed.

Lemma zlength_concat_to_bytes : forall iovs,
  Z.of_nat (length (concat (map to_bytes iovs))) = iov_total iovs.
Proof.
  intros iovs. unfold iov_total, zlength. induction iovs as [|a iovs IH]; cbn [map concat]; [reflexivity|].
  rewrite !length_app, length_to_bytes. lia.
Qed.

Lemma iov_total_nonneg : forall iovs, 0 <= iov_total iovs.
Proof. intros. unfold iov_total, zlength. lia. Qed.

Lemma iov_total_cons : forall a rest, iov_total (a :: rest) = zlength a + iov_total rest.
Proof. intros. unfold iov_total. cbn [concat]. rewrite zlength_app'. reflexivity. Qed.
Lemma iov_total_nil : iov_total [] = 0.
Proof. reflexivity. Qed.

Lemma iov_total_advance : forall iovs k, (length iovs <= 2)%nat -> 0 <= k < iov_total iovs ->
  iov_total (iov_advance iovs k) = iov_total iovs - k /\ (length (iov_advance iovs k) <= 2)%nat.
Proof.
  intros [|a [|b [|c rest]]] k Hn Hk; cbn [length] in Hn; try lia.
  - rewrite iov_total_nil in Hk. lia.
  - unfold iov_advance. rewrite iov_total_cons, iov_total_nil in *.
    destruct (Z.ltb_spec (zlength a) k); [lia|].
    rewrite iov_total_cons, iov_total_nil. rewrite zlength_zdrop; [|lia]. cbn [length]. lia.
  - unfold iov_advance. rewrite !iov_total_cons, iov_total_nil in *.
    assert (0 <= zlength b) by (unfold zlength; lia). assert (0 <= zlength a) by (unfold zlength; lia).
    destruct (Z.ltb_spec (zlength a) k).
    + rewrite iov_total_cons, iov_total_nil. rewrite zlength_zdrop; [|lia]. cbn [length]. lia.
    + rewrite !iov_total_cons, iov_total_nil. rewrite zlength_zdrop; [|lia]. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Lemma wv_body_GI : forall X fd iovs, iov_total iovs < 2^63 -> (length iovs <= 2)%nat ->
  mspec (GI X) (wv_body fd iovs)
        (fun r s mo => GI X s mo /\
           match r with
           | inl iovs' => iov_total iovs' < iov_total iovs /\ 0 <= iov_total iovs' /\ (length iovs' <= 2)%nat
           | inr _ => True
           end).
Proof.
  intros X fd iovs Hlen Hn. unfold wv_body.
  apply mspec_bind with (Q1 := fun k s mo => GI X s mo /\ ((iov_total iovs = 0 /\ k = 0) \/ 1 <= k <= iov_total iovs)).
  - apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
    pose proof (iov_total_nonneg iovs) as Hnn.
    assert (Hb : Z.of_nat (length (concat (map to_bytes iovs))) < 2^64) by (rewrite zlength_concat_to_bytes; lia).
    pose proof (nstep_dec_writev fd _ mo rsp mo' evs Hb Hst) as (-> & k & Hdec & Hk & Hk0 & _).
    rewrite zlength_concat_to_bytes in Hdec. exists (Z.of_nat k). split; [exact Hdec|].
    split; [exact Ho|].
    pose proof (zlength_concat_to_bytes iovs) as Ht.
    destruct (Nat.eq_dec k 0) as [->|NE].
    + left. split; [|reflexivity]. destruct Hk0 as [Hk0 _]. rewrite (Hk0 eq_refl) in Ht. cbn in Ht. lia.
    + right. lia.
  - intros k. apply mspec_if; intros C.
    + apply mspec_ret. intros s mo [Ho _]. split; [exact Ho| exact I].
    + apply Z.eqb_neq in C. apply mspec_ret. intros s mo [Ho Hk]. split; [exact Ho|].
      destruct Hk as [[H0 ->]|Hk]; [lia|].
      destruct (iov_total_advance iovs k Hn ltac:(lia)) as [E Hn']. rewrite E. splits; lia.
Qed.

Lemma stdio_writev_GI : forall X fd buf bs, zlength buf + zlength bs < 2^63 ->
  mspec (GI X) (stdio_writev fd buf bs) (fun _ => GI X).
Proof.
  intros X fd buf bs Hlen. unfold stdio_writev.
  assert (Ht : iov_total (iov_start buf bs) = zlength buf + zlength bs /\ (length (iov_start buf bs) <= 2)%nat).
  { unfold iov_start. destruct buf; rewrite ?iov_total_cons, ?iov_total_nil; cbn [length]; split; try lia.
    change (zlength (@nil Z)) with 0. lia. }
  destruct Ht as [Ht Hn].
  eapply mspec_pre.
  - apply (mspec_loop (wv_body fd) (fun iovs st mo => GI X st mo /\ iov_total iovs <= zlength buf + zlength bs /\ 0 <= iov_total iovs /\ (length iovs <= 2)%nat)
             (fun _ => GI X) (fun iovs => Z.to_nat (iov_total iovs))).
    + intros iovs. apply mspec_pointwise. intros s0 mo0 (Ho & Hle & Hnn & Hn2).
      eapply mspec_conseq; [apply wv_body_GI; [lia| exact Hn2]| intros s' mo' [-> ->]; exact Ho|].
      intros [iovs'|[]] s' mo' [Ho' Hr]; [|exact Ho'].
      split; [splits; [exact Ho'| lia | lia | lia]| lia].
    + unfold WV_FUEL. lia.
  - intros s0 mo Ho. split; [exact Ho|]. rewrite Ht. pose proof (iov_total_nonneg (iov_start buf bs)). splits; [lia| lia| exact Hn].
Qed.

Lemma upd_so_GI : forall X f,
  mspec (fun s mo => GI X s mo /\ so_ok (f (ps_so s))) (upd_so ps_so set_so_ps f)
        (fun _ s mo => GI X s mo /\ exists so0, ps_so s = f so0).
Proof.
  intros X f. unfold upd_so. apply mspec_upd'. intros s mo [Ho Hok]. split; [apply GI_set_so; [exact Ho| exact Hok]|]. cbn. eauto.
Qed.

Lemma rd_so_GI : forall (X : list bptr) (P : assn PState), mspec P (rd_so ps_so) (fun so s mo => P s mo /\ so = ps_so s).
Proof.
  intros X P. unfold rd_so. eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret.
  intros s mo [-> Ho]. split; [exact Ho| reflexivity].
Qed.

Lemma GI_so_ok : forall X s mo, GI X s mo -> so_ok (ps_so s).
Proof. intros X s mo H. exact (OWN_G _ _ _ _ H). Qed.

(* [comment removed for export] *)
Lemma stdout_stdio_write_GI : forall X s, zlength s < 2^62 ->
  mspec (GI X) (stdout_stdio_write ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
  intros X s Hs. unfold stdout_stdio_write. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok, STDOUT_BUFSIZ in Hok.
  eapply mspec_seq. { eapply mspec_pre; [apply stdio_writev_GI; unfold zlength in *; lia|]. intros s' mo' [-> ->]; exact Ho. }
  intros _. eapply mspec_conseq; [apply upd_so_GI| |].
  - intros s' mo' Ho'. split; [exact Ho'|]. unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
  - intros [] s' mo' [Ho' [so0 ->]]. split; [exact Ho'| reflexivity].
Qed.

Lemma stdout_writefn_GI : forall X s, zlength s < 2^62 ->
  mspec (GI X) (stdout_writefn ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
  intros X s Hs. unfold stdout_writefn. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->].
  eapply mspec_seq with (R := GI X).
  - destruct (so_first (ps_so s1)).
    + eapply mspec_seq.
      { eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [-> ->]; split; [exact Ho| exact (GI_so_ok _ _ _ Ho)]| intros [] s' mo' [H _]; exact H]. }
      intros _. eapply mspec_bind with (Q1 := fun r s mo => GI X s mo /\ match r with SErr _ => True | SVal _ => False end).
      * apply mspec_sys. intros s' mo' Ho'. split; [exact I|]. intros rsp mo'' evs Hst.
        pose proof (nstep_dec_ioctl 1 TIOCGWINSZ mo' rsp mo'' evs Hst) as (Hdec & -> & _).
        eexists. split; [exact Hdec|]. split; [exact Ho'| exact I].
      * intros [e|v]; [| intros s' mo' [_ []]].
        eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [H _]; split; [exact H| exact (GI_so_ok _ _ _ H)]| intros [] s' mo' [H _]; exact H].
    + apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
  - intros _. apply stdout_stdio_write_GI. exact Hs.
Qed.

Lemma stdout_towrite_GI : forall X, mspec (GI X) (stdout_towrite ps_so set_so_ps) (fun _ => GI X).
Proof.
  intros X. unfold stdout_towrite. eapply mspec_conseq; [apply upd_so_GI| |].
  - intros s mo Ho. split; [exact Ho|]. pose proof (GI_so_ok _ _ _ Ho) as Hok. destruct (so_active (ps_so s)); [exact Hok|].
    unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
  - intros [] s mo [H _]; exact H.
Qed.

Lemma stdout_fwritex_GI : forall X s, zlength s < 2^62 ->
  mspec (GI X) (stdout_fwritex ps_so set_so_ps s) (fun _ => GI X).
Proof.
  intros X s Hs. unfold stdout_fwritex.
  eapply mspec_seq; [apply stdout_towrite_GI|]. intros _.
  eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok, STDOUT_BUFSIZ in Hok.
  apply mspec_if; intros C1.
  { eapply mspec_conseq; [apply stdout_writefn_GI; exact Hs| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H]. }
  apply Z.ltb_ge in C1.
  destruct (so_lbf_nl (ps_so s1)).
  - set (i := after_last_nl s).
    eapply mspec_seq with (R := fun s' mo => GI X s' mo /\ zlength (so_buf (ps_so s')) + zlength (skipn (Z.to_nat i) s) <= STDOUT_BUFSIZ).
    + destruct (0 <? i).
      * eapply mspec_conseq; [apply stdout_writefn_GI; pose proof (zlength_firstn_le (Z.to_nat i) s); lia| intros s' mo' [-> ->]; exact Ho|].
        intros [] s' mo' [H Hb]. split; [exact H|]. rewrite Hb. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold zlength, STDOUT_BUFSIZ in *; cbn; lia.
      * apply mspec_ret. intros s' mo' [-> ->]. split; [exact Ho|]. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold STDOUT_BUFSIZ in *; lia.
    + intros _. eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
      intros s' mo' [H Hb]. split; [exact H|]. unfold so_ok. cbn. rewrite zlength_app'. exact Hb.
  - eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
    intros s' mo' [-> ->]. split; [exact Ho|]. unfold so_ok. cbn. rewrite zlength_app'. unfold STDOUT_BUFSIZ in *; lia.
Qed.

Lemma out_pieces_GI : forall X ps, Forall (fun p => zlength p < 2^62) ps ->
  mspec (GI X) (out_pieces ps_so set_so_ps ps) (fun _ => GI X).
Proof.
  intros X ps Hps. induction Hps as [|p ps Hp Hps IH]; cbn [out_pieces].
  - apply mspec_ret. intros s mo H; exact H.
  - eapply mspec_seq; [apply stdout_fwritex_GI; exact Hp|]. intros _. exact IH.
Qed.

Lemma stdout_vprintf_GI : forall X ps, Forall (fun p => zlength p < 2^62) ps ->
  mspec (GI X) (stdout_vprintf ps_so set_so_ps ps) (fun _ => GI X).
Proof.
  intros X ps Hps. unfold stdout_vprintf. eapply mspec_seq; [apply stdout_towrite_GI|]. intros _. apply out_pieces_GI. exact Hps.
Qed.

Lemma stdout_exit_flush_GI : forall X, mspec (GI X) (stdout_exit_flush ps_so set_so_ps) (fun _ => GI X).
Proof.
  intros X. unfold stdout_exit_flush. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->]. destruct (0 <? _).
  - eapply mspec_conseq; [apply stdout_writefn_GI; unfold zlength; cbn; lia| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H].
  - apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
Qed.

Lemma stderr_pieces_GI : forall X ps buf, zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p < 2^62) ps ->
  mspec (GI X) (stderr_pieces buf ps) (fun buf' s mo => GI X s mo /\ zlength buf' <= INTERNAL_BUFSIZ).
Proof.
  intros X ps. induction ps as [|p ps IH]; intros buf Hbuf Hps; cbn [stderr_pieces].
  - apply mspec_ret. intros s mo H. auto.
  - inversion Hps; subst. unfold INTERNAL_BUFSIZ in *. apply mspec_if; intros C.
    + eapply mspec_seq; [apply stdio_writev_GI; unfold zlength in *; lia|]. intros _. apply IH; [unfold zlength; cbn; lia| assumption].
    + apply Z.ltb_ge in C. apply IH; [rewrite zlength_app'; lia| assumption].
Qed.

Lemma stderr_fprintf_GI : forall X ps, Forall (fun p => zlength p < 2^62) ps ->
  mspec (GI X) (stderr_fprintf ps) (fun _ => GI X).
Proof.
  intros X ps Hps. unfold stderr_fprintf. eapply mspec_bind; [apply stderr_pieces_GI; [unfold zlength, INTERNAL_BUFSIZ; cbn; lia| exact Hps]|].
  intros buf. apply mspec_pointwise. intros s1 mo1 [Ho Hb]. unfold INTERNAL_BUFSIZ in Hb.
  eapply mspec_pre; [apply stdio_writev_GI; unfold zlength in *; cbn; lia|]. intros s mo [-> ->]; exact Ho.
Qed.

Lemma stderr_fwrite_GI : forall X s, zlength s < 2^62 -> mspec (GI X) (stderr_fwrite s) (fun _ => GI X).
Proof.
  intros X s Hs. unfold stderr_fwrite. apply mspec_if; intros _; [|apply mspec_ret; intros s0 mo H; exact H].
  apply stdio_writev_GI. unfold zlength in *; cbn; lia.
Qed.

Lemma s_diag_GI : forall X d, diag_ok d -> mspec (GI X) (s_diag d) (fun _ => GI X).
Proof.
  intros X d Hd. unfold s_diag. destruct d; cbn in Hd.
  all: try (apply stderr_fprintf_GI; repeat constructor; unfold zlength in *; cbn; lia).
  all: apply stderr_fwrite_GI; unfold zlength; cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_GI : forall X cfg payload, zlength payload <= MAX_INPUT ->
  mspec (GI X) (run cfg payload) (fun _ s mo => exists Y, GI (Y ++ X) s mo).
Proof.
  intros X cfg payload Hpl. unfold run. apply (target_run_mspec raw_malloc raw_free ps_so set_so_ps GI).
  - apply raw_malloc_GI_some. - apply raw_free_GI.
  - intros X'. apply stdout_vprintf_GI. unfold pieces_emit_0. repeat constructor; unfold zlength; cbn; lia.
  - apply GI_perm.
  - unfold MAX_INPUT in Hpl. lia.
Qed.

Lemma prog_with_GI : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspec (GI []) (prog_with rstage argv) (fun _ _ _ => False).
Proof.
  intros rstage argv Hargv Hpaths. unfold prog_with.
  eapply mspec_seq; [apply startup_GI|]. intros _.
  eapply mspec_bind.
  - eapply (main_model_spec io raw_malloc raw_free rstage alloc_init run alloc_count GI);
      (* [comment removed for export] *)
      [ apply raw_malloc_GI | apply raw_free_GI | apply GI_perm | (intros; apply s_diag_GI; assumption)
      | apply alloc_init_GI | apply alloc_count_GI | apply run_GI | apply GI_minv | apply GI_fds | exact Hargv | exact Hpaths ].
  - intros code. eapply (exit_model_spec io GI); first [apply stdout_exit_flush_GI | apply GI_minv | apply GI_fds].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Lemma GI_init : forall segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  bv_unsigned sp - stack_max_size = alloc_ceiling ->     (* [comment removed for export] *)
  GI [] (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos Hceil Htop. unfold GI, OWN. split; [|split; [apply List.NoDup_nil| unfold Gso, so_ok; cbn [ps_so ps_init so_buf stdout_init]; unfold zlength, STDOUT_BUFSIZ; cbn; lia]].
  exists (led_init (reservedZ segs)). split; [apply creach_init|]. split; [|intros c []].
  constructor; rewrite ?m_vmmaps_init_model; cbn -[Z.pow Z.mul Z.add init_model].
  - apply minv_init.
  - reflexivity.
  - split; [intros e []| apply pwdisj_nil].
  - reflexivity.
  - intros e Hin. pose proof (reserved_top_ge _ _ Hin). unfold ehi. lia.
  - unfold PGSZ in *. unfold page_size in Hal. lia.
  - intros b l [].
  - intros b l k [].
  - apply List.NoDup_nil.
  - intros b l H. discriminate.
  - split; reflexivity.
  - exact Htop.
Qed.

Lemma argv_Z_short : forall argv, valid_argv argv -> Forall (fun a => zlength a < 2^32) (argv_Z argv).
Proof.
  intros argv (_ & _ & HF & _). unfold argv_Z. apply Forall_map. eapply Forall_impl; [|exact HF].
  intros a Ha. unfold zlength in *. rewrite length_map. lia.
Qed.

(* [comment removed for export] *)
Lemma map_Z_to_bv_unsigned : forall (a : list byte), map (Z_to_bv 8) (map bv_unsigned a) = a.
Proof. induction a as [|b a IH]; [reflexivity|]. cbn. rewrite Z_to_bv_bv_unsigned, IH. reflexivity. Qed.

Lemma argv_Z_paths : forall argv, valid_argv argv -> Forall path_okZ (tl (argv_Z argv)).
Proof.
  intros argv (_ & _ & _ & _ & HF). unfold argv_Z. destruct argv as [|a0 rest]; [constructor|]. cbn [map tl] in *.
  apply Forall_map. eapply Forall_impl; [|exact HF]. intros a [H1 H2]. unfold path_okZ. rewrite map_Z_to_bv_unsigned. auto.
Qed.

(* [comment removed for export] *)
Definition segs_low (segs : list Segment) : Prop :=
  0 < reserved_top (segments_reserved segs) /\ reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33.

Lemma segs_low_psegs : segs_low psegs.
Proof. split; vm_compute; [reflexivity| discriminate]. Qed.
Lemma segs_low_usegs : segs_low usegs.
Proof. split; vm_compute; [reflexivity| discriminate]. Qed.

Lemma ceil_low : forall segs, segs_low segs -> reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling.
Proof. intros segs [_ H]. pose proof alloc_ceiling_ge. unfold PGSZ. lia. Qed.

(* [comment removed for export] *)
Theorem prog_model_ok : forall segs rstage pc ph lim en inp,
  segs_low segs ->
  valid_entry (mkImage segs pc ph) en inp ->
  valid_input_w inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  leaves_unreachable_m nstep (prog segs rstage (in_argv inp)) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (prog segs rstage (in_argv inp)) (mo0 segs lim en inp).
Proof.
  intros segs rstage pc ph lim [sp brk0 mbase] inp Hsegs Hve Hvi Htop.
  destruct Hve as (_ & Hbrk & _). destruct Hvi as (Hargv & _).
  unfold prog, mo0. cbn [en_brk en_mmap_base en_sp] in *.
  apply (mspec_program (GI []) (prog_with rstage (argv_Z (in_argv inp)))).
  - apply prog_with_GI; [apply argv_Z_short| apply argv_Z_paths]; exact Hargv.
  - unfold reservedZ. cbn [img_segments] in Hbrk.
    apply (GI_init segs); [exact Hbrk| exact (proj1 Hsegs)| exact (ceil_low segs Hsegs)| exact Htop].
Qed.

End WithCeiling.
