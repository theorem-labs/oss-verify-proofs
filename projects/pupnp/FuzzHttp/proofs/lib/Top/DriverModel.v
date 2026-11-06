(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad MSafe Stdio Driver Prog KInv KStepK KStepC.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import StdioShape.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition DINV (mo0 : Model) : PState -> Model -> Prop :=
  fun s mo => (length (so_buf (ps_so s)) <= 1024)%nat /\ m_fs mo = m_fs mo0.

Definition G0 : PState -> Model -> Prop := fun _ _ => True.

Lemma DINV_frame_ok : forall mo0, frame_ok (DINV mo0).
Proof.
  intros mo0 s s' mo mo' Efa Eso (F1 & F2 & F3 & F4 & F5) [D1 D2]. split; [rewrite Eso; exact D1| congruence].
Qed.

Definition ap_blocks (ap : at_parser (ptr:=bptr)) : list bptr :=
  match ap_owned ap with Some p => [p; ap_buf ap] | None => [ap_buf ap] end.

Definition ap_facts (ap : at_parser (ptr:=bptr)) : Prop :=
  1 <= ap_calls ap <= 4 /\ 0 <= ap_config_len ap < 32768
  /\ HDR_MIN + ap_config_len ap <= zlength (ap_content ap) <= MAX_INPUT
  /\ (ap_owned ap = None <-> ap_payload_len ap = 0).

Section DM.
  Variable rs_addr : Z.
  Variable mo0 : Model.
  Notation io := (io_S ps_so set_so_ps).
  Notation OW X := (OWN X (DINV mo0)).

  #[using="Type"] Lemma OW_minv : forall X s mo, OW X s mo -> minv mo.
  Proof. intros X s mo [(L & _ & HK & _) _]. exact (kl_minv _ _ _ HK). Qed.
  #[using="Type"] Lemma OW_halt : forall X s mo, OW X s mo -> m_halted mo = None.
  Proof. intros X s mo [(L & _ & HK & _) _]. exact (kl_halt _ _ _ HK). Qed.

  Definition fdstep (mo mo' : Model) : Prop :=
    minv mo' /\ m_halted mo' = None /\ m_vmmaps mo' = m_vmmaps mo /\ m_fs mo' = m_fs mo.

  #[using="Type"] Lemma OW_fdstep : forall X s mo mo', OW X s mo -> fdstep mo mo' -> OW X s mo'.
  Proof.
    intros X s mo mo' [(L & Hc & HK & Hi) [Hnd [D1 D2]]] (M1 & M2 & M3 & M4).
    split; [| split; [exact Hnd| split; [exact D1| congruence]]].
    exists L. split; [exact Hc|]. split; [| exact Hi].
    eapply KL_vm_eq; [exact HK| exact M1| exact M2| rewrite M3; reflexivity| rewrite M3; reflexivity| rewrite M3; reflexivity| rewrite M3; reflexivity| rewrite M3; reflexivity| rewrite M3; reflexivity].
  Qed.

  #[using="Type"] Lemma OW_so : forall X s mo so, OW X s mo -> (length (so_buf so) <= 1024)%nat -> OW X (set_so_ps so s) mo.
  Proof.
    intros X s mo so H Hl. eapply OWN_other; [exact H| destruct s; reflexivity| destruct s; reflexivity|].
    destruct H as [_ [_ [D1 D2]]]. split; [destruct s; cbn; exact Hl| exact D2].
  Qed.

  #[using="Type"] Lemma fdstep_same : forall mo, minv mo -> m_halted mo = None -> fdstep mo mo.
  Proof. intros mo M H. split; [exact M|]. split; [exact H|]. split; reflexivity. Qed.
  #[using="Type"] Lemma fdstep_with_fds : forall mo f, minv (with_fds f mo) -> m_halted mo = None -> fdstep mo (with_fds f mo).
  Proof. intros mo f M H. split; [exact M|]. rewrite m_halted_with_fds. split; [exact H|]. destruct mo; split; reflexivity. Qed.

  #[using="Type"] Lemma nstep_fdstep : forall n mo rsp mo' evs,
    match n with NOpen _ | NRead _ _ _ | NClose _ | NWritev _ _ | NIoctl _ _ => True | _ => False end ->
    minv mo -> m_halted mo = None -> nstep n mo rsp mo' evs -> fdstep mo mo'.
  Proof.
    intros n mo rsp mo' evs Hn M H ST.
    destruct (minv_preserved n mo rsp mo' evs ltac:(intros; subst; contradiction) M H ST) as [H' M'].
    destruct n; try contradiction; cbn [nstep] in ST.
    -   destruct ST as [-> _]. apply fdstep_same; assumption.
    -   destruct ST as [_ ST].
      destruct (path_max <=? length path)%nat; [destruct ST as [_ ->]; apply fdstep_same; assumption|].
      destruct path as [|c p']; [destruct ST as [_ ->]; apply fdstep_same; assumption|].
      assert (OR : forall ent, open_result mo ent rsp mo' -> fdstep mo mo').
      { intros ent [(e & _ & _ & ->)|(_ & _ & ->)]; [apply fdstep_same; assumption|]. apply fdstep_with_fds; [exact M'| exact H]. }
      destruct (path_is_dirref (c :: p')); [exact (OR _ ST)|].
      destruct (fs_lookup (m_fs mo) (c :: p')); [exact (OR _ ST)| destruct ST as [_ ->]; apply fdstep_same; assumption].
    -   destruct ST as [_ ST].
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid wr|dnr dnw| ]|]; try contradiction.
      + destruct (fs_lookup (m_fs mo) p); [| contradiction]. destruct ST as [_ ->]. apply fdstep_with_fds; [exact M'| exact H].
      + destruct ST as [_ ->]. apply fdstep_same; assumption.
      + destruct ST as [_ ->]. apply fdstep_same; assumption.
      + destruct ST as [_ ->]. apply fdstep_same; assumption.
    -   destruct ST as (_ & _ & ST). destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); destruct ST as [_ ->]; [apply fdstep_with_fds; [exact M'| exact H]| apply fdstep_same; assumption].
    -   destruct ST as (_ & _ & ->). apply fdstep_same; assumption.
  Qed.

  #[using="Type"] Lemma mspec_stderr_fprintf : forall X ps, Z.of_nat (length (concat ps)) < 2^64 ->
    mspec (OW X) (stderr_fprintf ps) (fun _ => OW X).
  Proof.
    intros X ps B s mo H. unfold etwf. apply twfP_stderr_fprintf; [exact (OW_minv _ _ _ H)| exact B| exact H].
  Qed.

  #[using="Type"] Lemma mspec_stderr_fwrite : forall X bs, Z.of_nat (length bs) < 2^64 ->
    mspec (OW X) (stderr_fwrite bs) (fun _ => OW X).
  Proof.
    intros X bs B s mo H. unfold etwf. apply twfP_stderr_fwrite; [exact (OW_minv _ _ _ H)| exact B| exact H].
  Qed.

  #[using="Type"] Lemma ps_get_set : forall (s : PState) so, ps_so (set_so_ps so s) = so.
  Proof. intros [] so. reflexivity. Qed.
  #[using="Type"] Lemma ps_set_set : forall (s : PState) so so', set_so_ps so' (set_so_ps so s) = set_so_ps so' s.
  Proof. intros [] so so'. reflexivity. Qed.
  #[using="Type"] Lemma ps_set_get : forall (s : PState), set_so_ps (ps_so s) s = s.
  Proof. intros []. reflexivity. Qed.

  #[using="Type"] Lemma mspec_stdout_exit_flush : forall X,
    mspec (OW X) (stdout_exit_flush ps_so set_so_ps) (fun _ => OW X).
  Proof.
    intros X s mo H. pose proof H as [_ [_ [D1 _]]]. unfold etwf.
    apply (twfP_stdout_exit_flush ps_so set_so_ps ps_get_set ps_set_set ps_set_get); [exact (OW_minv _ _ _ H)| lia|]. cbn beta iota.
    apply OW_so; [exact H|]. unfold exit_flush_run. destruct (0 <? zlength (so_buf (ps_so s))); cbn beta iota delta [fst snd]; [| exact D1].
    unfold so_after_write. cbn beta iota delta [so_buf length]. lia.
  Qed.

  #[using="Type"] Lemma str_length : forall s, length (str s) = String.length s.
  Proof.
    intros s. unfold str. rewrite length_map. induction s as [|c s IH]; cbn; [reflexivity| rewrite IH; reflexivity].
  Qed.

  #[using="Type"] Lemma mspec_s_diag : forall X d,
    match d with DUsage a | DCannotOpen a | DReadError a => Z.of_nat (length a) < 2^32 | _ => True end ->
    mspec (OW X) (io_diag io d) (fun _ => OW X).
  Proof.
    intros X d Hd. destruct d; cbn [io_diag io_S s_diag].
    1,2,3,5: apply mspec_stderr_fprintf; cbn [pieces_usage pieces_cannot_open pieces_read_error pieces_too_big concat];
             rewrite ?app_nil_r, !length_app, ?str_length; cbn [String.length length Z.of_nat Nat.add Pos.of_succ_nat Pos.succ Pos.add]; lia.
    all: apply mspec_stderr_fwrite; cbn [pieces_oom pieces_short_hdr pieces_cfg_overrun concat]; rewrite ?app_nil_r, !length_app, ?str_length; cbn [String.length length Z.of_nat Nat.add Pos.of_succ_nat Pos.succ Pos.add]; lia.
  Qed.

  #[using="Type"] Lemma mspec_exit_k : forall X {A} code (Q : A -> assn PState), mspec (OW X) (exit_k io code) Q.
  Proof.
    intros X A code Q. unfold exit_k, exit_model. cbn [io_exit io_S].
    eapply mspec_bind with (Q1 := fun _ _ _ => False).
    - eapply mspec_seq; [apply mspec_stdout_exit_flush|]. intros _.
      apply mspec_sys. intros s mo H. split; [exact I|]. intros rsp mo' evs ST. exfalso. exact (nstep_exit_none _ _ _ _ _ ST).
    - intros e. destruct e.
  Qed.

  Definition rd_inv (X : list bptr) (st : rd_st (ptr:=bptr)) : assn PState :=
    fun s mo => OW (rd_buf st :: X) s mo
      /\ 0 <= zlength (rd_content st) <= rd_cap st /\ 65536 <= rd_cap st <= MAX_INPUT
      /\ (exists k, 0 <= k /\ rd_cap st = 2 ^ k).

  Definition rd_meas (st : rd_st (ptr:=bptr)) : nat := Z.to_nat (MAX_INPUT - zlength (rd_content st)).

  #[using="Type"] Lemma pow2_double_le : forall k c, 0 <= k -> c = 2 ^ k -> c < MAX_INPUT -> c * 2 <= MAX_INPUT.
  Proof.
    intros k c Hk -> Hc. unfold MAX_INPUT in *. change 67108864 with (2 ^ 26) in Hc |- *.
    apply Z.pow_lt_mono_r_iff in Hc; [| lia| lia].
    replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia.
  Qed.

  #[using="Type"] Lemma mspec_expose {A} (P : assn PState) (phi : Prop) (m : M PState A) (Q : A -> assn PState) :
    (forall s mo, P s mo -> phi) -> (phi -> mspec P m Q) -> mspec P m Q.
  Proof. intros H1 H2 s mo HP. exact (H2 (H1 _ _ HP) s mo HP). Qed.

  #[using="Type"] Lemma mspec_read_loop_body : forall X fd path st, Z.of_nat (length path) < 2^32 ->
    mspec (rd_inv X st) (read_loop_body io raw_malloc raw_free rs_addr fd path st)
          (fun r s mo => match r with
                         | inl st' => rd_inv X st' s mo /\ (rd_meas st' < rd_meas st)%nat
                         | inr RdExit => exists Y, OW Y s mo
                         | inr (RdDone buf content) => OW (buf :: X) s mo /\ 0 <= zlength content <= MAX_INPUT
                         end).
  Proof.
    intros X fd path st Hpath. unfold read_loop_body.
    apply (mspec_expose _ (0 <= zlength (rd_content st) <= rd_cap st /\ 65536 <= rd_cap st <= MAX_INPUT /\ exists k, 0 <= k /\ rd_cap st = 2 ^ k));
      [intros s mo (_ & B & C & K); auto|]. intros (B & C & k & Hk & Ek).

    eapply mspec_bind with (Q1 := fun g s mo => match g with
                                              | None => exists Y, OW Y s mo
                                              | Some st1 => rd_inv X st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                                              end).
    { apply mspec_if; intros E.
      - apply mspec_if; intros E2.
        + eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag (rd_buf st :: X) DTooBig I)| intros s mo [H _]; exact H]|].
          intros _. apply mspec_ret. intros s mo H. exists (rd_buf st :: X). exact H.
        + apply Z.eqb_eq in E. apply Z.leb_gt in E2.
          eapply mspec_bind.
          { eapply mspec_pre; [apply (raw_malloc_spec_c (rd_buf st :: X) (DINV mo0) (rd_cap st * 2) (DINV_frame_ok mo0)); lia|].
            intros s mo [H _]. exact H. }
          intros [nb|]; cbn beta iota.
          * eapply mspec_seq.
            { eapply mspec_pre; [apply (raw_free_spec_c (nb :: X) (DINV mo0) (rd_buf st) (DINV_frame_ok mo0))|].
              intros s mo [H _]. eapply OWN_perm; [apply perm_swap| exact H]. }
            intros _. apply mspec_ret. intros s mo H. unfold rd_inv. cbn [rd_buf rd_cap rd_content].
            pose proof (pow2_double_le k _ Hk Ek E2) as D2.
            split; [| split; [reflexivity| lia]]. split; [exact H|]. split; [lia|]. split; [lia|].
            exists (k + 1). split; [lia|]. rewrite Ek, Z.pow_add_r by lia. lia.
          * eapply mspec_seq; [apply (mspec_s_diag (rd_buf st :: X) DOom I)|]. intros _. apply mspec_ret. intros s mo H. exists (rd_buf st :: X). exact H.
      - apply mspec_ret. intros s mo H. apply Z.eqb_neq in E. unfold rd_inv in *. split; [exact H|]. split; [reflexivity| lia]. }
    intros [st1|]; cbn beta iota.
    2:{ apply mspec_ret. intros s mo H. exact H. }

    cbv zeta.
    set (cnt := Z.min (rd_cap st1 - zlength (rd_content st)) READ_CHUNK).
    set (bufa := rs_addr).
    apply (mspec_expose _ (0 <= zlength (rd_content st1) <= rd_cap st1 /\ 65536 <= rd_cap st1 <= MAX_INPUT /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1));
      [intros s mo ((_ & B1 & C1 & _) & E1 & L1); auto|]. intros (B1 & C1 & E1 & L1).
    assert (CNT : 0 < cnt <= rd_cap st1 - zlength (rd_content st) /\ cnt <= 65536) by (subst cnt; unfold READ_CHUNK; lia).
    eapply mspec_bind with (Q1 := fun a s mo => rd_inv X st1 s mo /\ match a with RdData bs => Z.of_nat (length bs) <= cnt | RdErr _ => True end).
    { apply mspec_sys. intros s0 mo [HI _]. split; [exact I|]. intros rsp mo' evs ST.
      pose proof HI as (HO & HI').
      destruct (nstep_dec_read fd bufa cnt mo rsp mo' evs ltac:(lia) ST) as (_ & a & D & Ha).
      exists a. split; [exact D|].
      assert (HO' : OW (rd_buf st1 :: X) s0 mo').
      { eapply OW_fdstep; [exact HO|]. eapply (nstep_fdstep (NRead fd bufa cnt)); [exact I| exact (OW_minv _ _ _ HO)| exact (OW_halt _ _ _ HO)| exact ST]. }
      split; [split; [exact HO'| exact HI']|].
      destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
      pose proof (length_file_read_le_count data off cnt ltac:(lia)). lia. }
    intros [e|bs]; cbn beta iota.
    - eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag (rd_buf st1 :: X) (DReadError path) Hpath)| intros s mo [[H _] _]; exact H]|].
      intros _. apply mspec_ret. intros s mo H. exists (rd_buf st1 :: X). exact H.
    - apply mspec_if; intros Ebs; apply mspec_ret; intros s mo [[HO (B2 & C2 & K2)] LBS].
      + split; [exact HO|]. lia.
      + apply Nat.eqb_neq in Ebs. unfold rd_inv, rd_meas. cbn [rd_buf rd_cap rd_content].
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = zlength (rd_content st1) + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. lia. }
        rewrite LEN'. rewrite E1 in *.
        split; [| lia]. split; [exact HO|]. split; [lia|]. split; [lia| exact K2].
  Qed.

  #[using="Type"] Lemma mspec_read_all : forall X path, Z.of_nat (length path) < 2^32 ->
    mspec (OW X) (read_all io raw_malloc raw_free rs_addr path)
          (fun r s mo => match r with
                         | RdExit => exists Y, OW Y s mo
                         | RdDone buf content => OW (buf :: X) s mo /\ 0 <= zlength content <= MAX_INPUT
                         end).
  Proof.
    intros X path Hpath. unfold read_all.
    eapply mspec_bind with (Q1 := fun _ => OW X).
    { apply mspec_sys. intros s mo HO. split; [exact I|]. intros rsp mo' evs ST.
      destruct (nstep_dec_open _ mo rsp mo' evs (OW_minv _ _ _ HO) ST) as (_ & a & D & _).
      exists a. split; [exact D|].
      eapply OW_fdstep; [exact HO|]. eapply (nstep_fdstep (NOpen _)); [exact I| exact (OW_minv _ _ _ HO)| exact (OW_halt _ _ _ HO)| exact ST]. }
    intros [e|fd]; cbn beta iota.
    { eapply mspec_seq; [apply (mspec_s_diag X (DCannotOpen path) Hpath)|]. intros _. apply mspec_ret. intros s mo H. exists X. exact H. }
    eapply mspec_bind; [apply (raw_malloc_spec_c X (DINV mo0) 65536 (DINV_frame_ok mo0)); lia|].
    intros [buf|]; cbn beta iota.
    2:{ eapply mspec_seq; [apply (mspec_s_diag X DOom I)|]. intros _. apply mspec_ret. intros s mo H. exists X. exact H. }
    eapply mspec_bind.
    { eapply mspec_pre.
      - apply (mspec_loop (read_loop_body io raw_malloc raw_free rs_addr fd path) (rd_inv X)
                 (fun v s mo => match v with RdExit => exists Y, OW Y s mo | RdDone buf content => OW (buf :: X) s mo /\ 0 <= zlength content <= MAX_INPUT end)
                 rd_meas).
        + intros st. apply (mspec_read_loop_body X fd path st Hpath).
        + unfold rd_meas, READ_FUEL, MAX_INPUT. cbn [rd_content]. replace (zlength (@nil Z)) with 0 by reflexivity. lia.
      - intros s mo [HO _]. unfold rd_inv. cbn [rd_buf rd_cap rd_content]. replace (zlength (@nil Z)) with 0 by reflexivity. unfold MAX_INPUT.
        split; [exact HO|]. split; [lia|]. split; [lia|]. exists 16. split; [lia| reflexivity]. }
    intros [|buf' content]; cbn beta iota.
    - apply mspec_ret. intros s mo H. exact H.
    - eapply mspec_bind with (Q1 := fun _ s mo => OW (buf' :: X) s mo /\ 0 <= zlength content <= MAX_INPUT).
      { apply mspec_sys. intros s mo [HO HB]. split; [exact I|]. intros rsp mo' evs ST.
        destruct (nstep_dec_close fd mo rsp mo' evs ST) as (_ & a & D & _).
        exists a. split; [exact D|]. split; [| exact HB].
        eapply OW_fdstep; [exact HO|]. eapply (nstep_fdstep (NClose fd)); [exact I| exact (OW_minv _ _ _ HO)| exact (OW_halt _ _ _ HO)| exact ST]. }
      intros _. apply mspec_ret. intros s mo H. exact H.
  Qed.

  #[using="Type"] Lemma land3_range : forall a, 0 <= Z.land a 3 <= 3.
  Proof.
    intros a. change (Z.land a 3) with (Z.land a (Z.ones 2)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound a (2 ^ 2) ltac:(lia)). lia.
  Qed.
  #[using="Type"] Lemma land15_range : forall a, 0 <= Z.land a 32767 < 32768.
  Proof.
    intros a. change (Z.land a 32767) with (Z.land a (Z.ones 15)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound a (2 ^ 15) ltac:(lia)). lia.
  Qed.

  #[using="Type"] Theorem drv_pre_mspec : forall X argv, Forall (fun a => Z.of_nat (length a) < 2^32) argv ->
    mspec (OW X) (drv_pre io raw_malloc raw_free rs_addr argv)
          (fun ap s mo => OW (ap_blocks ap ++ X) s mo /\ ap_facts ap).
  Proof.
    intros X argv HA.
    assert (Hnth : forall i, Z.of_nat (length (nth i argv [])) < 2^32).
    { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) HA _ Hin)| cbn; lia]. }
    unfold drv_pre.
    apply mspec_if; intros E.
    { eapply mspec_seq; [apply (mspec_s_diag X (DUsage _) (Hnth 0%nat))|]. intros _. apply mspec_exit_k. }
    eapply mspec_bind; [apply (mspec_read_all X _ (Hnth 1%nat))|].
    intros [|buf content]; cbn beta iota.
    {   apply (mspec_exI (fun Y => OW Y)). intros Y. apply mspec_exit_k. }
    apply (mspec_expose _ (0 <= zlength content <= MAX_INPUT)); [intros s mo [_ B]; exact B|]. intros B.
    apply mspec_if; intros E1.
    { eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag (buf :: X) DShortHdr I)| intros s mo [H _]; exact H]|]. intros _.
      eapply mspec_seq; [apply (raw_free_spec_c X (DINV mo0) buf (DINV_frame_ok mo0))|]. intros _. apply mspec_exit_k. }
    apply mspec_if; intros E2.
    { eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag (buf :: X) DCfgOverrun I)| intros s mo [H _]; exact H]|]. intros _.
      eapply mspec_seq; [apply (raw_free_spec_c X (DINV mo0) buf (DINV_frame_ok mo0))|]. intros _. apply mspec_exit_k. }
    apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. unfold HDR_MIN in *.
    pose proof (land15_range (le16 content)) as L15.
    pose proof (land3_range (if 0 <? Z.land (le16 content) 32767 then znth content 2 else 0)) as L3.
    eapply mspec_bind with (Q1 := fun copy s mo => match copy with
                                                  | None => exists Y, OW (Y ++ buf :: X) s mo
                                                  | Some owned => OW (match owned with Some p => [p; buf] | None => [buf] end ++ X) s mo
                                                                  /\ (owned = None <-> zlength content - 6 - Z.land (le16 content) 32767 = 0)
                                                  end).
    { apply mspec_if; intros E3.
      - apply Z.ltb_lt in E3. eapply mspec_bind; [eapply mspec_pre; [apply (raw_malloc_spec_c (buf :: X) (DINV mo0) _ (DINV_frame_ok mo0)); lia| intros s mo [H _]; exact H]|].
        intros [p|]; cbn beta iota; apply mspec_ret.
        + intros s mo [H _]. split; [exact H|]. split; [intros X0; discriminate X0| intros; lia].
        + intros s mo H. exists []. exact H.
      - apply Z.ltb_ge in E3. apply mspec_ret. intros s mo [H _]. split; [exact H|]. split; [intros _; lia| reflexivity].
    }
    intros [owned|]; cbn beta iota.
    - apply mspec_ret. intros s mo [H HO]. unfold ap_blocks, ap_facts, ap_payload_len. cbn [ap_owned ap_buf ap_calls ap_config_len ap_content]. unfold HDR_MIN.
      split; [exact H|]. split; [lia|]. split; [lia|]. split; [lia| exact HO].
    - apply mspec_exI. intros Y. eapply mspec_seq.
      + eapply mspec_pre; [apply (raw_free_spec_c (Y ++ X) (DINV mo0) buf (DINV_frame_ok mo0))|].
        intros s mo H. eapply OWN_perm; [| exact H]. apply Permutation_sym. apply Permutation_middle.
      + intros _. apply mspec_exit_k.
  Qed.
End DM.

Corollary drv_pre_twf : forall (rs_addr : Z) X argv s mo,
  Forall (fun a => Z.of_nat (length a) < 2^32) argv ->
  OWN X G0 s mo -> (length (so_buf (ps_so s)) <= 1024)%nat ->
  twf (drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free rs_addr argv s) mo
      (fun r mo' => match r with
                    | Unr => False
                    | Ok (ap, s') => OWN (ap_blocks ap ++ X) G0 s' mo' /\ (length (so_buf (ps_so s')) <= 1024)%nat
                                     /\ m_fs mo' = m_fs mo /\ ap_facts ap
                    end).
Proof.
  intros rs_addr X argv s mo HA HO HB.
  pose proof (drv_pre_mspec rs_addr mo X argv HA s mo) as M.
  eapply twf_mono.
  - apply M. eapply OWN_weakG; [exact HO|]. intros _. split; [exact HB| reflexivity].
  - intros [|[ap s']] mo1; cbn; [intros F; exact F|]. intros [H F]. pose proof (OWN_G _ _ _ _ H) as [D1 D2].
    split; [eapply OWN_weakG; [exact H| intros _; exact I]|]. split; [exact D1|]. split; [exact D2| exact F].
Qed.

Corollary drv_pre_tsafe : forall (rs_addr : Z) X argv s mo,
  Forall (fun a => Z.of_nat (length a) < 2^32) argv ->
  OWN X G0 s mo -> (length (so_buf (ps_so s)) <= 1024)%nat ->
  tsafe nstep nsafe (drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free rs_addr argv s) mo.
Proof. intros rs_addr X argv s mo HA HO HB. eapply twf_tsafe. exact (drv_pre_twf rs_addr X argv s mo HA HO HB). Qed.

