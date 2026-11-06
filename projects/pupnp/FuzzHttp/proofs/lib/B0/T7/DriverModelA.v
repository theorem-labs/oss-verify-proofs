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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad MSafe Stdio Driver Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import StdioShape DriverModel.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import A0Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition ap_factsA (ap : at_parser (ptr:=unit)) : Prop :=
  1 <= ap_calls ap <= 4 /\ 0 <= ap_config_len ap < 32768
  /\ HDR_MIN + ap_config_len ap <= zlength (ap_content ap) <= MAX_INPUT
  /\ (ap_owned ap = None <-> ap_payload_len ap = 0).

Definition INVm (fs0 : Fs.Fs) : assn ASt :=
  fun so mo => minv mo /\ m_halted mo = None /\ m_fs mo = fs0 /\ (length (so_buf so) <= 1024)%nat.

Lemma aget_set : forall (s : ASt) so, aget_so (aset_so so s) = so. Proof. reflexivity. Qed.
Lemma aset_set : forall (s : ASt) so so', aset_so so' (aset_so so s) = aset_so so' s. Proof. reflexivity. Qed.
Lemma aset_get : forall (s : ASt), aset_so (aget_so s) s = s. Proof. reflexivity. Qed.

Section DMA.
  Variable rs_addr : Z.
  Variable fs0 : Fs.Fs.
  Notation IV := (INVm fs0).

  #[using="Type"] Lemma IV_minv : forall so mo, IV so mo -> minv mo. Proof. intros so mo (M & _); exact M. Qed.
  #[using="Type"] Lemma IV_halt : forall so mo, IV so mo -> m_halted mo = None. Proof. intros so mo (_ & H & _); exact H. Qed.
  #[using="Type"] Lemma IV_fdstep : forall so mo mo', IV so mo -> fdstep mo mo' -> IV so mo'.
  Proof. intros so mo mo' (M & H & F & B) (M1 & M2 & M3 & M4). split; [exact M1|]. split; [exact M2|]. split; [congruence| exact B]. Qed.
  #[using="Type"] Lemma IV_so : forall so mo so', IV so mo -> (length (so_buf so') <= 1024)%nat -> IV so' mo.
  Proof. intros so mo so' (M & H & F & _) B. split; [exact M|]. split; [exact H|]. split; [exact F| exact B]. Qed.

  #[using="Type"] Lemma mspec_expose {A} (P : assn ASt) (phi : Prop) (m : M ASt A) (Q : A -> assn ASt) :
    (forall s mo, P s mo -> phi) -> (phi -> mspec P m Q) -> mspec P m Q.
  Proof. intros H1 H2 s mo HP. exact (H2 (H1 _ _ HP) s mo HP). Qed.
  #[using="Type"] Lemma mspec_mret_bind {A B} (a : A) (f : A -> M ASt B) (P : assn ASt) (Q : B -> assn ASt) :
    mspec P (f a) Q -> mspec P (mbind (mret a) f) Q.
  Proof. intros H. exact H. Qed.

  #[using="Type"] Lemma mspec_stderr_fprintf : forall ps, Z.of_nat (length (concat ps)) < 2^64 -> mspec IV (stderr_fprintf ps) (fun _ => IV).
  Proof. intros ps B s mo H. unfold etwf. apply twfP_stderr_fprintf; [exact (IV_minv _ _ H)| exact B| exact H]. Qed.
  #[using="Type"] Lemma mspec_stderr_fwrite : forall bs, Z.of_nat (length bs) < 2^64 -> mspec IV (stderr_fwrite bs) (fun _ => IV).
  Proof. intros bs B s mo H. unfold etwf. apply twfP_stderr_fwrite; [exact (IV_minv _ _ H)| exact B| exact H]. Qed.

  #[using="Type"] Lemma mspec_stdout_exit_flush : mspec IV (stdout_exit_flush aget_so aset_so) (fun _ => IV).
  Proof.
    intros s mo H. pose proof H as (_ & _ & _ & B). unfold etwf.
    apply (twfP_stdout_exit_flush aget_so aset_so aget_set aset_set aset_get); [exact (IV_minv _ _ H)| unfold aget_so; lia|].
    cbn [fst snd]. unfold aget_so, aset_so.
    eapply IV_so; [exact H|]. unfold exit_flush_run. destruct (0 <? zlength (so_buf s)); cbn [fst snd]; [| exact B].
    unfold so_after_write. cbn [so_buf length]. lia.
  Qed.

  #[using="Type"] Lemma mspec_s_diag : forall d,
    match d with DUsage a | DCannotOpen a | DReadError a => Z.of_nat (length a) < 2^32 | _ => True end ->
    mspec IV (io_diag ioA d) (fun _ => IV).
  Proof.
    intros d Hd. destruct d; cbn [io_diag ioA io_S s_diag].
    1,2,3,5: apply mspec_stderr_fprintf; cbn [pieces_usage pieces_cannot_open pieces_read_error pieces_too_big concat];
             rewrite ?app_nil_r, !length_app, ?str_length; cbn [String.length length Z.of_nat Nat.add Pos.of_succ_nat Pos.succ Pos.add]; lia.
    all: apply mspec_stderr_fwrite; cbn [pieces_oom pieces_short_hdr pieces_cfg_overrun concat]; rewrite ?app_nil_r, !length_app, ?str_length; cbn [String.length length Z.of_nat Nat.add Pos.of_succ_nat Pos.succ Pos.add]; lia.
  Qed.

  #[using="Type"] Lemma mspec_exit_k : forall {A} code (Q : A -> assn ASt), mspec IV (exit_k ioA code) Q.
  Proof.
    intros A code Q. unfold exit_k, exit_model. cbn [io_exit ioA io_S].
    eapply mspec_bind with (Q1 := fun _ _ _ => False).
    - eapply mspec_seq; [apply mspec_stdout_exit_flush|]. intros _.
      apply mspec_sys. intros s mo H. split; [exact I|]. intros rsp mo' evs ST. exfalso. exact (nstep_exit_none _ _ _ _ _ ST).
    - intros e. destruct e.
  Qed.

  Definition rd_invA (st : rd_st (ptr:=unit)) : assn ASt :=
    fun s mo => IV s mo /\ 0 <= zlength (rd_content st) <= rd_cap st /\ 65536 <= rd_cap st <= MAX_INPUT /\ (exists k, 0 <= k /\ rd_cap st = 2 ^ k).
  Definition rd_measA (st : rd_st (ptr:=unit)) : nat := Z.to_nat (MAX_INPUT - zlength (rd_content st)).

  #[using="Type"] Lemma mspec_read_loop_body : forall fd path st, Z.of_nat (length path) < 2^32 ->
    mspec (rd_invA st) (read_loop_body ioA amalloc0 afree0 rs_addr fd path st)
          (fun r s mo => match r with
                         | inl st' => rd_invA st' s mo /\ (rd_measA st' < rd_measA st)%nat
                         | inr RdExit => IV s mo
                         | inr (RdDone buf content) => IV s mo /\ 0 <= zlength content <= MAX_INPUT
                         end).
  Proof.
    intros fd path st Hpath. unfold read_loop_body.
    apply (mspec_expose _ (0 <= zlength (rd_content st) <= rd_cap st /\ 65536 <= rd_cap st <= MAX_INPUT /\ exists k, 0 <= k /\ rd_cap st = 2 ^ k));
      [intros s mo (_ & B & C & K); auto|]. intros (B & C & k & Hk & Ek).

    eapply mspec_bind with (Q1 := fun g s mo => match g with
                                              | None => IV s mo
                                              | Some st1 => rd_invA st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                                              end).
    { apply mspec_if; intros E.
      - apply mspec_if; intros E2.
        + eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag DTooBig I)| intros s mo [H _]; exact H]|].
          intros _. apply mspec_ret. intros s mo H. exact H.
        + apply Z.eqb_eq in E. apply Z.leb_gt in E2.
          unfold amalloc0, afree0. apply mspec_ret. intros s mo [H _]. cbn beta iota.
          unfold rd_invA. cbn [rd_buf rd_cap rd_content].
          pose proof (pow2_double_le k _ Hk Ek E2) as D2.
          split; [| split; [reflexivity| lia]]. split; [exact H|]. split; [lia|]. split; [lia|].
          exists (k + 1). split; [lia|]. rewrite Ek, Z.pow_add_r by lia. lia.
      - apply mspec_ret. intros s mo H. apply Z.eqb_neq in E. unfold rd_invA in *. split; [exact H|]. split; [reflexivity| lia]. }
    intros [st1|]; cbn beta iota.
    2:{ apply mspec_ret. intros s mo H. exact H. }

    cbv zeta.
    set (cnt := Z.min (rd_cap st1 - zlength (rd_content st)) READ_CHUNK).
    apply (mspec_expose _ (0 <= zlength (rd_content st1) <= rd_cap st1 /\ 65536 <= rd_cap st1 <= MAX_INPUT /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1));
      [intros s mo ((_ & B1 & C1 & _) & E1 & L1); auto|]. intros (B1 & C1 & E1 & L1).
    assert (CNT : 0 < cnt <= rd_cap st1 - zlength (rd_content st) /\ cnt <= 65536) by (subst cnt; unfold READ_CHUNK; lia).
    eapply mspec_bind with (Q1 := fun a s mo => rd_invA st1 s mo /\ match a with RdData bs => Z.of_nat (length bs) <= cnt | RdErr _ => True end).
    { apply mspec_sys. intros s0 mo [HI _]. split; [exact I|]. intros rsp mo' evs ST.
      pose proof HI as (HO & HI').
      destruct (nstep_dec_read fd rs_addr cnt mo rsp mo' evs ltac:(lia) ST) as (_ & a & D & Ha).
      exists a. split; [exact D|].
      assert (HO' : IV s0 mo').
      { eapply IV_fdstep; [exact HO|]. eapply (nstep_fdstep (NRead fd rs_addr cnt)); [exact I| exact (IV_minv _ _ HO)| exact (IV_halt _ _ HO)| exact ST]. }
      split; [split; [exact HO'| exact HI']|].
      destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
      pose proof (length_file_read_le_count data off cnt ltac:(lia)). lia. }
    intros [e|bs]; cbn beta iota.
    - eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag (DReadError path) Hpath)| intros s mo [[H _] _]; exact H]|].
      intros _. apply mspec_ret. intros s mo H. exact H.
    - apply mspec_if; intros Ebs; apply mspec_ret; intros s mo [[HO (B2 & C2 & K2)] LBS].
      + split; [exact HO|]. lia.
      + apply Nat.eqb_neq in Ebs. unfold rd_invA, rd_measA. cbn [rd_buf rd_cap rd_content].
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = zlength (rd_content st1) + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. lia. }
        rewrite LEN'. rewrite E1 in *.
        split; [| lia]. split; [exact HO|]. split; [lia|]. split; [lia| exact K2].
  Qed.

  #[using="Type"] Lemma mspec_read_all : forall path, Z.of_nat (length path) < 2^32 ->
    mspec IV (read_all ioA amalloc0 afree0 rs_addr path)
          (fun r s mo => match r with
                         | RdExit => IV s mo
                         | RdDone buf content => IV s mo /\ 0 <= zlength content <= MAX_INPUT
                         end).
  Proof.
    intros path Hpath. unfold read_all.
    eapply mspec_bind with (Q1 := fun _ => IV).
    { apply mspec_sys. intros s mo HO. split; [exact I|]. intros rsp mo' evs ST.
      destruct (nstep_dec_open _ mo rsp mo' evs (IV_minv _ _ HO) ST) as (_ & a & D & _).
      exists a. split; [exact D|].
      eapply IV_fdstep; [exact HO|]. eapply (nstep_fdstep (NOpen _)); [exact I| exact (IV_minv _ _ HO)| exact (IV_halt _ _ HO)| exact ST]. }
    intros [e|fd]; cbn beta iota.
    { eapply mspec_seq; [apply (mspec_s_diag (DCannotOpen path) Hpath)|]. intros _. apply mspec_ret. intros s mo H. exact H. }
    unfold amalloc0 at 1. apply mspec_mret_bind. cbv beta iota.
    eapply mspec_bind.
    { eapply mspec_pre.
      - apply (mspec_loop (read_loop_body ioA amalloc0 afree0 rs_addr fd path) rd_invA
                 (fun v s mo => match v with RdExit => IV s mo | RdDone buf content => IV s mo /\ 0 <= zlength content <= MAX_INPUT end)
                 rd_measA).
        + intros st. apply (mspec_read_loop_body fd path st Hpath).
        + unfold rd_measA, READ_FUEL, MAX_INPUT. cbn [rd_content]. replace (zlength (@nil Z)) with 0 by reflexivity. lia.
      - intros s mo HO. unfold rd_invA. cbn [rd_buf rd_cap rd_content]. replace (zlength (@nil Z)) with 0 by reflexivity. unfold MAX_INPUT.
        split; [exact HO|]. split; [lia|]. split; [lia|]. exists 16. split; [lia| reflexivity]. }
    intros [|buf' content]; cbn beta iota.
    - apply mspec_ret. intros s mo H. exact H.
    - eapply mspec_bind with (Q1 := fun _ s mo => IV s mo /\ 0 <= zlength content <= MAX_INPUT).
      { apply mspec_sys. intros s mo [HO HB]. split; [exact I|]. intros rsp mo' evs ST.
        destruct (nstep_dec_close fd mo rsp mo' evs ST) as (_ & a & D & _).
        exists a. split; [exact D|]. split; [| exact HB].
        eapply IV_fdstep; [exact HO|]. eapply (nstep_fdstep (NClose fd)); [exact I| exact (IV_minv _ _ HO)| exact (IV_halt _ _ HO)| exact ST]. }
      intros _. apply mspec_ret. intros s mo H. exact H.
  Qed.

  #[using="Type"] Theorem drv_preA_mspec : forall argv, Forall (fun a => Z.of_nat (length a) < 2^32) argv ->
    mspec IV (drv_preA rs_addr argv) (fun ap s mo => IV s mo /\ ap_factsA ap).
  Proof.
    intros argv HA.
    assert (Hnth : forall i, Z.of_nat (length (nth i argv [])) < 2^32).
    { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) HA _ Hin)| cbn; lia]. }
    unfold drv_preA, drv_pre.
    apply mspec_if; intros E.
    { eapply mspec_seq; [apply (mspec_s_diag (DUsage _) (Hnth 0%nat))|]. intros _. apply mspec_exit_k. }
    eapply mspec_bind; [apply (mspec_read_all _ (Hnth 1%nat))|].
    intros [|buf content]; cbn beta iota.
    { apply mspec_exit_k. }
    apply (mspec_expose _ (0 <= zlength content <= MAX_INPUT)); [intros s mo [_ B]; exact B|]. intros B.
    apply mspec_if; intros E1.
    { eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag DShortHdr I)| intros s mo [H _]; exact H]|]. intros _.
      unfold afree0. apply mspec_mret_bind. apply mspec_exit_k. }
    apply mspec_if; intros E2.
    { eapply mspec_seq; [eapply mspec_pre; [apply (mspec_s_diag DCfgOverrun I)| intros s mo [H _]; exact H]|]. intros _.
      unfold afree0. apply mspec_mret_bind. apply mspec_exit_k. }
    apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. unfold HDR_MIN in *.
    pose proof (land15_range (le16 content)) as L15.
    pose proof (land3_range (if 0 <? Z.land (le16 content) 32767 then znth content 2 else 0)) as L3.
    eapply mspec_bind with (Q1 := fun copy s mo => IV s mo /\ match copy with
                                                             | None => False
                                                             | Some owned => (owned = None <-> zlength content - 6 - Z.land (le16 content) 32767 = 0)
                                                             end).
    { apply mspec_if; intros E3.
      - apply Z.ltb_lt in E3. unfold amalloc0. apply mspec_mret_bind. cbv beta iota. apply mspec_ret. intros s mo [H _]. split; [exact H|]. split; [intros X0; discriminate X0| intros; lia].
      - apply Z.ltb_ge in E3. apply mspec_ret. intros s mo [H _]. split; [exact H|]. split; [intros _; lia| reflexivity]. }
    intros [owned|]; cbn beta iota.
    - apply mspec_ret. intros s mo [H HO]. unfold ap_factsA, ap_payload_len. cbn [ap_owned ap_buf ap_calls ap_config_len ap_content]. unfold HDR_MIN.
      split; [exact H|]. split; [lia|]. split; [lia|]. split; [lia| exact HO].
    - eapply mspec_pre; [apply mspec_exit_k| intros s mo [_ F]; destruct F].
  Qed.
End DMA.

Corollary drv_preA_twf : forall (rs_addr : Z) (fs0 : Fs.Fs) argv (so : ASt) mo,
  Forall (fun a => Z.of_nat (length a) < 2^32) argv -> INVm fs0 so mo ->
  twf (drv_preA rs_addr argv so) mo
      (fun r mo' => match r with
                    | Unr => False
                    | Ok (ap, so') => INVm fs0 so' mo' /\ ap_factsA ap
                    end).
Proof.
  intros rs_addr fs0 argv so mo HA HI.
  pose proof (drv_preA_mspec rs_addr fs0 argv HA so mo HI) as M. unfold etwf in M.
  eapply twf_mono; [exact M|]. intros [|[ap so']] mo'; cbn [fst snd]; auto.
Qed.
