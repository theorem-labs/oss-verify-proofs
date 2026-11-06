(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad MSafe Stdio Driver Prog KStep LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section DriverL.
Context {St ptr : Type}.
Variable B : Z.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable rstage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> Monad.M St Z.
Variable alloc_count : Monad.M St Z.

Variable own : list (ptr * Z) -> assn St.

Variable mal_ok : list (ptr * Z) -> Z -> Prop.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecL B (fun s mo => own X s mo /\ mal_ok X n) (drv_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p n, mspecL B (own ((p, n) :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, mspecL B (own X) (io_diag io d) (fun _ => own X).
Hypothesis Hexit : forall X, mspecL B (own X) (io_exit io) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspecL B (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspecL B (own X) alloc_count (fun _ => own X).

Hypothesis Hrun : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL B (own [(b, cap)]) (run cfg payload) (fun _ => own [(b, cap)]).
Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
  m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.
Hypothesis Hown_live : forall X s mo, own X s mo -> live mo <= B.

Hypothesis OK_first : mal_ok [] 65536.
Hypothesis OK_grow : forall b k, (k <= 9)%nat -> mal_ok [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).

Lemma own_after_nodeL : forall X s mo n rsp mo' evs,
  own X s mo -> nstep n mo rsp mo' evs -> nsafe n mo -> m_vmmaps mo' = m_vmmaps mo -> own X s mo' /\ live mo' <= B.
Proof.
  intros X s mo n rsp mo' evs Ho Hst Hsafe Hvm. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hsafe Hst) as [Hh' Hmi'].
  assert (Ho' : own X s mo') by (eapply Hown_fds; eauto). split; [exact Ho'| exact (Hown_live _ _ _ Ho')].
Qed.

Definition rd_invL (st : rd_st) : assn St := fun s mo =>
  own [(rd_buf st, rd_cap st)] s mo
  /\ zlength (rd_content st) <= rd_cap st
  /\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k)).

Lemma zlength_app {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_u8s : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.
Lemma pow2_le_1024 : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof. intros k Hk. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia. Qed.

Lemma read_loop_body_L : forall fd path st,
  zlength path < 2^32 -> 0 <= fd ->
  mspecL B (rd_invL st) (read_loop_body io drv_malloc drv_free rstage fd path st)
        (fun r s mo => match r with
                       | inl st' => rd_invL st' s mo
                       | inr RdExit => exists X', own X' s mo
                       | inr (RdDone buf content) => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
                                                     /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros fd path st Hpath Hfd. unfold read_loop_body.
  eapply mspecL_bind with
    (Q1 := fun g s mo => match g with
                         | None => exists X', own X' s mo
                         | Some st1 => rd_invL st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                         end).
  { apply mspecL_if_pre.
    - apply mspecL_if_pre.
      + eapply mspecL_seq; [eapply mspecL_pre; [apply Hdiag|]|].
        { intros s mo [[[Ho _] _] _]. exact Ho. }
        intros _. apply mspecL_ret. intros s mo Ho. exists [(rd_buf st, rd_cap st)]. exact Ho.
      + apply mspecL_pointwise. intros s0 mo0 [[(Ho0 & Hlen & k & Hk & Hcap) Heq] Hlt].
        apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
        pose proof (pow2_le_1024 k Hk) as Hp.
        assert (Hk9 : (k <= 9)%nat) by (unfold MAX_INPUT in Hlt; assert (k <> 10)%nat by (intros ->; cbn in Hcap; lia); lia).
        eapply mspecL_bind. { eapply mspecL_pre; [apply Hdm; lia|]. intros s mo [-> ->]. split; [exact Ho0|]. rewrite Hcap. apply OK_grow. exact Hk9. }
        intros [nb|]; cbn beta iota.
        * apply mspecL_pure. intros _. eapply mspecL_seq.
          { eapply mspecL_pre; [apply (Hdf [(nb, rd_cap st * 2)] (rd_buf st) (rd_cap st))|].
            intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
          intros _. apply mspecL_ret. intros s mo Ho. cbn. unfold rd_invL. cbn. splits; auto; try lia.
          exists (S k). split; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
        * eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists [(rd_buf st, rd_cap st)]. exact Ho.
    - apply mspecL_ret. intros s mo [[Ho [Hlen Hk]] Hne]. apply Z.eqb_neq in Hne. split; [|split; [reflexivity|lia]]. split; [exact Ho|]. auto. }
  intros [st1|]; cbn beta iota.
  2:{ apply mspecL_ret. intros s mo H. exact H. }
  eapply mspecL_bind; [apply mspecL_get|]. intros sg. cbn beta iota.
  apply mspecL_pointwise. intros s1 mo1 [Hsg ((Ho & Hlen & k & Hk & Hcap) & Hct & Hlt)]. subst sg.
  pose proof (pow2_le_1024 k Hk) as Hp.
  apply mspecL_bind with (Q1 := fun a s mo => s = s1 /\ own [(rd_buf st1, rd_cap st1)] s mo /\
                       match a with RdErr _ => True | RdData bs => zlength bs <= rd_cap st1 - zlength (rd_content st) end).
  { apply mspecL_sys; [intros; exact Logic.I|]. intros s mo [-> ->].
    intros rsp mo' evs Hst.
    pose proof (nstep_dec_read fd _ (Z.min (rd_cap st1 - zlength (rd_content st)) 65536) mo1 rsp mo' evs ltac:(unfold MAX_INPUT, zlength in *; lia) Hst) as (_ & a & Hdec & Ha).
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
    { destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
      destruct Ha as (p & off & data & _ & _ & _ & ->). reflexivity. }
    destruct (own_after_nodeL _ _ _ _ _ _ _ Ho Hst I Hvm) as [Ho' LB]. split; [exact LB|].
    intros a' Ha'. rewrite Hdec in Ha'. inversion Ha'. subst a'.
    cbn beta. split; [reflexivity|]. split; [exact Ho'|].
    destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
    unfold zlength. pose proof (length_file_read_le_count data off (Z.min (rd_cap st1 - Z.of_nat (length (rd_content st))) 65536) ltac:(unfold zlength, MAX_INPUT in *; lia)). lia. }
  intros [e|bs]; cbn beta iota.
  - eapply mspecL_seq. { eapply mspecL_pre; [apply Hdiag|]. intros s mo (_ & Ho' & _). exact Ho'. }
    intros _. apply mspecL_ret. intros s mo Ho'. exists [(rd_buf st1, rd_cap st1)]. exact Ho'.
  - apply mspecL_if; intros C.
    + apply mspecL_ret. intros s mo (-> & Ho' & _). split; [| rewrite Hct; unfold MAX_INPUT in *; lia].
      exists k. split; [exact Hk|]. rewrite <- Hcap. split; [exact Ho'|]. rewrite Hct. lia.
    + apply mspecL_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
      assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
      unfold rd_invL. cbn. split; [exact Ho'|]. rewrite zlength_app, zlength_u8s, Hct. split; [lia|]. exists k. auto.
Qed.

Lemma read_all_L : forall path, zlength path < 2^32 -> path_okZ path ->
  mspecL B (own []) (read_all io drv_malloc drv_free rstage path)
        (fun r s mo => match r with
                       | RdExit => exists X', own X' s mo
                       | RdDone buf content => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
                                               /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros path Hpath Hpok. unfold read_all.
  apply mspecL_bind with (Q1 := fun r s mo => own [] s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
  { apply mspecL_sys; [intros; exact Logic.I|]. intros s mo Ho. intros rsp mo' evs Hst.
    destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
    pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo).
    { destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). reflexivity. }
    destruct (own_after_nodeL _ _ _ _ _ _ _ Ho Hst Hpok Hvm) as [Ho' LB]. split; [exact LB|].
    intros a' Ha'. rewrite Hdec in Ha'. inversion Ha'. subst a'. cbn beta.
    split; [exact Ho'|]. destruct a as [e|fd]; [exact I|]. lia. }
  intros [e|fd]; cbn beta iota.
  - apply mspecL_pure. intros _. eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho.
  - apply mspecL_pure. intros Hfd. eapply mspecL_bind; [eapply mspecL_pre; [apply Hdm; lia| intros s mo Ho; split; [exact Ho| exact OK_first]]|]. intros [buf|]; cbn beta iota.
    2:{ eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho. }
    apply mspecL_pure. intros _.
    eapply mspecL_bind.
    + eapply mspecL_pre.
      * apply (mspecL_loop B (read_loop_body io drv_malloc drv_free rstage fd path) rd_invL
                 (fun r s mo => match r with RdExit => exists X', own X' s mo
                                | RdDone buf content => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
                                                        /\ zlength content <= MAX_INPUT end)).
        intros st. eapply mspecL_post; [apply read_loop_body_L; [exact Hpath| exact Hfd]|].
        intros [st'|[|b c]] s mo H; exact H.
      * intros s mo Ho. unfold rd_invL. cbn. split; [exact Ho|]. split; [unfold zlength; cbn; lia|]. exists 0%nat. split; [lia|reflexivity].
    + intros [|buf' content]; cbn beta iota; [apply mspecL_ret; intros s mo H; exact H|].
      apply mspecL_pointwise. intros s1 mo1 [(k & Hk & Ho1 & Hck) Hlen].
      eapply mspecL_bind with (Q1 := fun _ s mo => own [(buf', 65536 * 2 ^ Z.of_nat k)] s mo).
      * apply mspecL_sys; [intros; exact Logic.I|]. intros s mo [-> ->]. intros rsp mo' evs Hst.
        pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
        assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
        { destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). reflexivity. }
        destruct (own_after_nodeL _ _ _ _ _ _ _ Ho1 Hst I Hvm) as [Ho' LB]. split; [exact LB|]. intros; exact Ho'.
      * intros _. apply mspecL_ret. intros s mo Ho. split; [| exact Hlen]. exists k. auto.
Qed.

Lemma main_model_L : forall argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecL B (own []) (main_model io drv_malloc drv_free rstage alloc_init run alloc_count argv)
        (fun _ s mo => exists X', own X' s mo).
Proof.
  intros argv Hargv Hpaths. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) < 2^32).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength; cbn; lia].
    exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
  apply mspecL_if; intros Hlen2.
  { eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []; exact Ho. }
  assert (Hp1 : path_okZ (nth 1 argv [])).
  { apply Bool.negb_false_iff in Hlen2. apply Z.eqb_eq in Hlen2.
    destruct argv as [|a0 [|a1 rest]]; cbn in Hlen2; try lia. cbn. inversion Hpaths; assumption. }
  eapply mspecL_bind; [apply read_all_L; [apply Hnth| exact Hp1]|].
  intros [|buf content]; cbn beta iota; [apply mspecL_ret; intros s mo H; exact H|].
  apply mspecL_pure. intros Hlen. apply mspecL_exI. intros k. apply mspecL_pure_l. intros Hk.
  apply (mspecL_pre B _ (fun s mo => own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)); [| intros s mo H; exact H].
  apply mspecL_pointwise. intros s0 mo0 [Ho0 Hck]. apply (mspecL_pre B _ (own [(buf, 65536 * 2 ^ Z.of_nat k)])); [| intros s mo [-> ->]; exact Ho0].
  pose proof (pow2_le_1024 k Hk) as Hp.
  apply mspecL_if; intros _.
  { eapply mspecL_seq; [apply Hdiag|]. intros _. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho; exists []; exact Ho. }
  apply mspecL_if; intros _.
  { eapply mspecL_seq; [apply Hdiag|]. intros _. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho; exists []; exact Ho. }
  eapply mspecL_seq; [apply Hinit|]. intros _.
  assert (Hcap : 65536 <= 65536 * 2 ^ Z.of_nat k <= MAX_INPUT) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)); unfold MAX_INPUT; lia).
  eapply mspecL_seq; [apply Hrun; [exact Hcap| etransitivity; [| exact Hlen]; unfold zlength; rewrite length_skipn; lia]|]. intros status.
  eapply mspecL_seq with (R := own [(buf, 65536 * 2 ^ Z.of_nat k)]).
  { destruct (Z.testbit _ 15); [|apply mspecL_ret; intros s mo H; exact H].
    eapply mspecL_seq; [apply Hcount|]. intros n. apply mspecL_ret. intros s mo H; exact H. }
  intros status'. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho.
Qed.

Lemma exit_model_L : forall code,
  mspecL B (fun s mo => exists X, own X s mo) (exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold exit_model. eapply mspecL_seq with (R := fun s mo => exists X, own X s mo).
  - apply mspecL_exI. intros X. eapply mspecL_post; [apply Hexit|]. intros a s mo Ho. exists X. exact Ho.
  - intros _. apply mspecL_sys; [intros; exact Logic.I|]. intros s mo _. intros rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End DriverL.

Section NodeL.
Context {St : Type}.
Variable B : Z.
Variable I : assn St.
Hypothesis I_minv : forall s mo, I s mo -> minv mo /\ m_halted mo = None.
Hypothesis I_fds : forall s mo mo', I s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> I s mo'.
Hypothesis I_live : forall s mo, I s mo -> live mo <= B.

Lemma I_after_node : forall s mo n rsp mo' evs,
  I s mo -> nstep n mo rsp mo' evs -> nsafe n mo -> m_vmmaps mo' = m_vmmaps mo -> I s mo' /\ live mo' <= B.
Proof.
  intros s mo n rsp mo' evs Ho Hst Hsafe Hvm. destruct (I_minv _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hsafe Hst) as [Hh' Hmi'].
  assert (Ho' : I s mo') by (eapply I_fds; eauto). split; [exact Ho'| exact (I_live _ _ Ho')].
Qed.

Lemma writev_L : forall fd bufs (dec : resp -> option Z), mspecL B I (msys (NWritev fd bufs) dec) (fun _ => I).
Proof.
  intros fd bufs dec. apply mspecL_sys; [intros; exact Logic.I|]. intros s mo Ho rsp mo' evs Hst.
  pose proof Hst as [-> _]. split; [exact (I_live _ _ Ho)|]. intros; exact Ho.
Qed.

Lemma ioctl_L : forall fd req, mspecL B I (msys (NIoctl fd req) dec_ioctl) (fun _ => I).
Proof.
  intros fd req. apply mspecL_sys; [intros; exact Logic.I|]. intros s mo Ho rsp mo' evs Hst.
  destruct Hst as (-> & -> & ->). split; [exact (I_live _ _ Ho)|]. intros; exact Ho.
Qed.
End NodeL.

Section StdioL.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Variable B : Z.
Variable I : assn St.
Hypothesis I_so : forall s mo v, I s mo -> I (set_so v s) mo.
Hypothesis Hwv : forall fd bufs (dec : resp -> option Z), mspecL B I (msys (NWritev fd bufs) dec) (fun _ => I).
Hypothesis Hio : forall fd req, mspecL B I (msys (NIoctl fd req) dec_ioctl) (fun _ => I).

Lemma upd_so_L : forall f, mspecL B I (upd_so get_so set_so f) (fun _ => I).
Proof. intros f. unfold upd_so. apply mspecL_upd'. intros s mo Ho. apply I_so. exact Ho. Qed.

Lemma rd_so_L : mspecL B I (rd_so get_so) (fun _ => I).
Proof. unfold rd_so. eapply mspecL_bind; [apply mspecL_get|]. intros s'. apply mspecL_ret. intros s mo [_ H]. exact H. Qed.

Lemma stdio_writev_L : forall fd buf s, mspecL B I (stdio_writev fd buf s) (fun _ => I).
Proof.
  intros fd buf s. unfold stdio_writev.
  apply (mspecL_loop B (wv_body fd) (fun _ => I) (fun _ => I)). intros x. unfold wv_body.
  eapply mspecL_seq; [apply Hwv|]. intros k. apply mspecL_if; intros _; apply mspecL_ret; auto.
Qed.

Lemma stdout_stdio_write_L : forall s, mspecL B I (stdout_stdio_write get_so set_so s) (fun _ => I).
Proof.
  intros s. unfold stdout_stdio_write. eapply mspecL_seq; [apply rd_so_L|]. intros so.
  eapply mspecL_seq; [apply stdio_writev_L|]. intros u. apply upd_so_L.
Qed.

Lemma stdout_writefn_L : forall s, mspecL B I (stdout_writefn get_so set_so s) (fun _ => I).
Proof.
  intros s. unfold stdout_writefn. eapply mspecL_seq; [apply rd_so_L|]. intros so.
  eapply mspecL_seq; [| intros u; apply stdout_stdio_write_L].
  apply mspecL_if; intros _; [| apply mspecL_ret; auto].
  eapply mspecL_seq; [apply upd_so_L|]. intros u.
  eapply mspecL_bind; [apply Hio|]. intros [e|v]; [apply upd_so_L| apply mspecL_munr].
Qed.

Lemma stdout_towrite_L : mspecL B I (stdout_towrite get_so set_so) (fun _ => I).
Proof. unfold stdout_towrite. apply upd_so_L. Qed.

Lemma stdout_fwritex_L : forall s, mspecL B I (stdout_fwritex get_so set_so s) (fun _ => I).
Proof.
  intros s. unfold stdout_fwritex. eapply mspecL_seq; [apply stdout_towrite_L|]. intros u.
  eapply mspecL_seq; [apply rd_so_L|]. intros so.
  apply mspecL_if; intros _; [apply stdout_writefn_L|].
  apply mspecL_if; intros _; [| apply upd_so_L].
  eapply mspecL_seq; [| intros u'; apply upd_so_L].
  apply mspecL_if; intros _; [apply stdout_writefn_L| apply mspecL_ret; auto].
Qed.

Lemma out_pieces_L : forall ps, mspecL B I (out_pieces get_so set_so ps) (fun _ => I).
Proof.
  induction ps as [|p ps IH]; cbn [out_pieces]; [apply mspecL_ret; auto|].
  eapply mspecL_seq; [apply stdout_fwritex_L| intros u; exact IH].
Qed.

Lemma stdout_vprintf_L : forall ps, mspecL B I (stdout_vprintf get_so set_so ps) (fun _ => I).
Proof. intros ps. unfold stdout_vprintf. eapply mspecL_seq; [apply stdout_towrite_L| intros u; apply out_pieces_L]. Qed.

Lemma stdout_exit_flush_L : mspecL B I (stdout_exit_flush get_so set_so) (fun _ => I).
Proof.
  unfold stdout_exit_flush. eapply mspecL_seq; [apply rd_so_L|]. intros so.
  apply mspecL_if; intros _; [apply stdout_writefn_L| apply mspecL_ret; auto].
Qed.

Lemma stderr_pieces_L : forall ps buf, mspecL B I (stderr_pieces (St:=St) buf ps) (fun _ => I).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply mspecL_ret; auto|].
  apply mspecL_if; intros _; [| apply IH].
  eapply mspecL_seq; [apply stdio_writev_L| intros u; apply IH].
Qed.

Lemma stderr_fprintf_L : forall ps, mspecL B I (stderr_fprintf (St:=St) ps) (fun _ => I).
Proof. intros ps. unfold stderr_fprintf. eapply mspecL_seq; [apply stderr_pieces_L|]. intros buf. apply stdio_writev_L. Qed.

Lemma stderr_fwrite_L : forall s, mspecL B I (stderr_fwrite (St:=St) s) (fun _ => I).
Proof. intros s. unfold stderr_fwrite. apply mspecL_if; intros _; [apply stdio_writev_L| apply mspecL_ret; auto]. Qed.

Lemma s_diag_L : forall d, mspecL B I (s_diag d) (fun _ => I).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_L | apply stderr_fwrite_L]. Qed.
End StdioL.

Section StartupL.
Variable B : Z.
Variable I : assn PState.
Hypothesis I_minv : forall s mo, I s mo -> minv mo /\ m_halted mo = None.
Hypothesis I_fds : forall s mo mo', I s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> I s mo'.
Hypothesis I_live : forall s mo, I s mo -> live mo <= B.

Lemma startup_L : mspecL B I startup (fun _ => I).
Proof.
  unfold startup. eapply mspecL_seq; [|intros _; apply mspecL_ret; intros s mo H; exact H].
  apply mspecL_sys; [intros; exact Logic.I|]. intros s mo Ho. intros rsp mo' evs Hst.
  destruct (I_minv _ _ Ho) as [Hmi Hh].
  pose proof (nstep_dec_set_tid mo rsp mo' evs Hmi Hst) as (_ & t & Hdec & _ & Hmo).
  assert (Hvm : m_vmmaps mo' = m_vmmaps mo) by (destruct Hmo as [[_ ->]|[_ ->]]; reflexivity).
  destruct (I_after_node B I I_minv I_fds I_live _ _ _ _ _ _ Ho Hst Logic.I Hvm) as [Ho' LB]. split; [exact LB|]. intros; exact Ho'.
Qed.

End StartupL.
