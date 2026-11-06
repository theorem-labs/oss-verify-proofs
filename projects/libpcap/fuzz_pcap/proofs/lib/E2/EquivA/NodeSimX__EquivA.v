(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX USimX.
From Stdlib Require NArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RelSpec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AcctCore ExecF ModelX MmXfer ITreeA NodesA NodesSil NodesMmSh NodesAS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module NodeSimX.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mqX (moG moC : Model) : Prop :=
  m_fds moC = m_fds moG /\ m_fs moC = m_fs moG /\ m_halted moC = m_halted moG.

Lemma mq_vm_onlyX moG moC : vm_only moG moC -> mqX moG moC.
Proof. unfold mqX, vm_only. tauto. Qed.

Lemma mq_reflX mo : mqX mo mo.
Proof. repeat split; reflexivity. Qed.
Lemma mq_symX a b : mqX a b -> mqX b a.
Proof. intros (H1 & H2 & H3). repeat split; congruence. Qed.
Lemma mq_transX a b c : mqX a b -> mqX b c -> mqX a c.
Proof. intros (H1 & H2 & H3) (G1 & G2 & G3). repeat split; congruence. Qed.

(* [comment removed for export] *)
Lemma mq_vm_lX moG moG' moC : vm_only moG moG' -> mqX moG moC -> mqX moG' moC.
Proof. intros HV HQ. apply mq_vm_onlyX in HV. exact (mq_transX _ _ _ (mq_symX _ _ HV) HQ). Qed.
Lemma mq_vm_rX moG moC moC' : vm_only moC moC' -> mqX moG moC -> mqX moG moC'.
Proof. intros HV HQ. apply mq_vm_onlyX in HV. exact (mq_transX _ _ _ HQ HV). Qed.

Lemma mq_with_fdsX f moG moC : mqX moG moC -> mqX (with_fds f moG) (with_fds f moC).
Proof. intros (H1 & H2 & H3). unfold mqX. autorewrite with model. repeat split; congruence. Qed.
Lemma mq_with_fsX f moG moC : mqX moG moC -> mqX (with_fs f moG) (with_fs f moC).
Proof. intros (H1 & H2 & H3). unfold mqX. autorewrite with model. repeat split; congruence. Qed.
Lemma mq_with_tidX t moG moC : mqX moG moC -> mqX (with_tid t moG) (with_tid t moC).
Proof. intros (H1 & H2 & H3). unfold mqX. autorewrite with model. repeat split; congruence. Qed.
Lemma mq_with_haltedX c moG moC : mqX moG moC -> mqX (with_halted c moG) (with_halted c moC).
Proof. intros (H1 & H2 & H3). unfold mqX. autorewrite with model. repeat split; congruence. Qed.

Lemma mq_fdsX moG moC : mqX moG moC -> m_fds moC = m_fds moG. Proof. intros H; exact (proj1 H). Qed.
Lemma mq_fsX moG moC : mqX moG moC -> m_fs moC = m_fs moG. Proof. intros H; exact (proj1 (proj2 H)). Qed.
Lemma mq_haltedX moG moC : mqX moG moC -> m_halted moC = m_halted moG. Proof. intros H; exact (proj2 (proj2 H)). Qed.

(* [comment removed for export] *)
Lemma vmmaps_with_fdsX f mo : m_vmmaps (with_fds f mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.
Lemma vmmaps_with_fsX f mo : m_vmmaps (with_fs f mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.
Lemma vmmaps_with_tidX t mo : m_vmmaps (with_tid t mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.
Lemma vmmaps_with_haltedX c mo : m_vmmaps (with_halted c mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fdnodeX (n : node) : Prop :=
  match n with
  | NWrite _ _ | NWritev _ _ | NOpen _ | NClose _ | NIoctl _ _ | NOpenW _ _ | NWritevF _ _
  | NLseek _ _ _ | NUnlink _ _ => True
  | _ => False
  end.

(* [comment removed for export] *)
Definition xstepX (moG moC moG' moC' : Model) : Prop :=
  mqX moG' moC' /\ m_vmmaps moG' = m_vmmaps moG /\ m_vmmaps moC' = m_vmmaps moC.

Lemma xstep_sameX moG moC : mqX moG moC -> xstepX moG moC moG moC.
Proof. intros HQ. split; [exact HQ| split; reflexivity]. Qed.
Lemma xstep_fdsX moG moC f : mqX moG moC -> xstepX moG moC (with_fds f moG) (with_fds f moC).
Proof. intros HQ. split; [apply mq_with_fdsX; exact HQ| split; apply vmmaps_with_fdsX]. Qed.
Lemma xstep_fs_fdsX moG moC g f : mqX moG moC -> xstepX moG moC (with_fds f (with_fs g moG)) (with_fds f (with_fs g moC)).
Proof. intros HQ. split; [apply mq_with_fdsX; apply mq_with_fsX; exact HQ| split; rewrite vmmaps_with_fdsX, vmmaps_with_fsX; reflexivity]. Qed.
Lemma xstep_fsX moG moC g : mqX moG moC -> xstepX moG moC (with_fs g moG) (with_fs g moC).
Proof. intros HQ. split; [apply mq_with_fsX; exact HQ| split; apply vmmaps_with_fsX]. Qed.
Lemma xstep_tidX moG moC t : mqX moG moC -> xstepX moG moC (with_tid t moG) (with_tid t moC).
Proof. intros HQ. split; [apply mq_with_tidX; exact HQ| split; apply vmmaps_with_tidX]. Qed.

Lemma open_result_crossX moG moC ent rsp moG' : mqX moG moC -> open_result moG ent rsp moG' ->
  exists moC', open_result moC ent rsp moC' /\ xstepX moG moC moG' moC'.
Proof.
  intros HQ [(e & He & -> & ->)|(Hlk & -> & ->)].
  - exists moC. split; [left; exists e; auto| apply xstep_sameX; exact HQ].
  - exists (with_fds (fd_insert (m_fds moC) (alloc_fd (m_fds moC)) ent) moC). rewrite (mq_fdsX _ _ HQ). split; [right| apply xstep_fdsX; exact HQ].
    rewrite (mq_fdsX _ _ HQ). auto.
Qed.

Lemma lseek_result_crossX moG moC fd mk base off rsp moG' : mqX moG moC -> lseek_result moG fd mk base off rsp moG' ->
  exists moC', lseek_result moC fd mk base off rsp moC' /\ xstepX moG moC moG' moC'.
Proof.
  intros HQ H. unfold lseek_result in *. destruct base as [b|]; [| destruct H].
  destruct (lseek_dest b (Z_to_bv 64 off)) as [r|].
  - destruct H as [-> ->]. exists (with_fds (fd_insert (m_fds moC) (Z_to_bv 64 fd) (mk r)) moC). split; [auto|]. rewrite (mq_fdsX _ _ HQ). apply xstep_fdsX. exact HQ.
  - destruct H as [-> ->]. exists moC. split; [auto| apply xstep_sameX; exact HQ].
Qed.

Theorem nstep_crossX n moG moC rsp moG' evs :
  fdnodeX n -> mqX moG moC -> nstep n moG rsp moG' evs ->
  exists moC', nstep n moC rsp moC' evs /\ xstepX moG moC moG' moC'.
Proof.
  intros Hn HQ H. pose proof (mq_fdsX _ _ HQ) as EF. pose proof (mq_fsX _ _ HQ) as ES.
  destruct n; cbn [fdnodeX] in Hn; try destruct Hn; cbn [nstep] in H |- *.
  - (* [comment removed for export] *) destruct H as (-> & k & Hk & -> & ->). exists moC. split; [| apply xstep_sameX; exact HQ]. split; [reflexivity|]. exists k. auto.
  - (* [comment removed for export] *) destruct H as (-> & k & Hk & -> & ->). exists moC. split; [| apply xstep_sameX; exact HQ]. split; [reflexivity|]. exists k. auto.
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?ES.
    destruct (path_max <=? length path)%nat; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]|].
    destruct path as [|c path']; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]|].
    destruct (path_eqb (c :: path') dot_path).
    + destruct (open_result_crossX moG moC FdDir rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
    + destruct (fs_lookup (m_fs moG) (c :: path')); [| destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]].
      destruct (open_result_crossX moG moC _ rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
  - (* [comment removed for export] *) destruct H as (-> & Hfd & H). rewrite ?EF. destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)).
    + destruct H as [-> ->]. exists (with_fds (fd_remove (m_fds moG) (Z_to_bv 64 fd)) moC). split; [| apply xstep_fdsX; exact HQ]. auto.
    + destruct H as [-> ->]. exists moC. split; [auto| apply xstep_sameX; exact HQ].
  - (* [comment removed for export] *) destruct H as (-> & -> & H). exists moC. rewrite ?EF. split; [| apply xstep_sameX; exact HQ]. split; [reflexivity|]. split; [reflexivity|]. exact H.
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?ES, ?EF.
    destruct (path_max <=? length path)%nat; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]|].
    destruct path as [|c path']; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]|].
    (* [comment removed for export] *)
    destruct (path_eqb (c :: path') devnull_path).
    { destruct (open_result_crossX moG moC FdNull rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto. }
    destruct (path_has_slash (c :: path')); [destruct H|].
    unfold write_dirref in H |- *. rewrite ?ES.
    destruct (path_is_dirref (c :: path') || fs_under (m_fs moG) (c :: path')); [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]|].
    unfold openw_result in H |- *. rewrite ?EF, ?ES.
    destruct H as [(e & He & -> & ->)|(Hlk & -> & ->)].
    + exists moC. split; [split; [reflexivity| left; exists e; auto]| apply xstep_sameX; exact HQ].
    + eexists. split; [split; [reflexivity| right; split; [exact Hlk| split; [reflexivity| reflexivity]]]|].
      apply xstep_fs_fdsX. exact HQ.
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?EF, ?ES.
    destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|]; try (destruct H; fail).
    + destruct (fs_lookup (m_fs moG) p) as [data|]; [| destruct H]. destruct H as [-> ->].
      eexists. split; [split; [reflexivity| split; [reflexivity| reflexivity]]|].
      rewrite ?EF, ?ES. apply xstep_fs_fdsX. exact HQ.
    + (* [comment removed for export] *) destruct H as [-> ->]. exists moC. split; [auto| apply xstep_sameX; exact HQ].
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?ES, ?EF.
    destruct (path_has_slash path); [destruct H|].     (* [comment removed for export] *)
    destruct (fs_under (m_fs moG) path); [destruct H|].
    destruct (fs_lookup (m_fs moG) path); [| destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]].
    destruct rmdir; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_sameX; exact HQ]|].
    destruct H as [(e & He & -> & ->)|(Hn & -> & ->)].
    + exists moC. split; [split; [reflexivity| left; exists e; auto]| apply xstep_sameX; exact HQ].
    + exists (with_fs (fs_remove (m_fs moG) path) moC). split; [split; [reflexivity| right; auto]| apply xstep_fsX; exact HQ].
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?EF, ?ES.
    destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p cur|p cur|p cur|p cur| |sk|pid w|[|] [|]| ]|]; try (destruct H; fail).
    + destruct (fs_lookup (m_fs moG) p) as [data|]; [| destruct H].
      destruct (lseek_result_crossX moG moC fd _ _ off rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
    + destruct (fs_lookup (m_fs moG) p) as [data|]; [| destruct H].
      destruct (lseek_result_crossX moG moC fd _ _ off rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
    + (* [comment removed for export] *) destruct H as [-> ->]. exists moC. split; [auto| apply xstep_sameX; exact HQ].
    + destruct H as [-> ->]. exists moC. split; [auto| apply xstep_sameX; exact HQ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dec_read_xaddrX bufG bufC count r bs :
  dec_read bufC count (mkEffect r (delivered_writes (Z_to_bv 64 bufC) bs) []) =
  dec_read bufG count (mkEffect r (delivered_writes (Z_to_bv 64 bufG) bs) []).
Proof.
  unfold dec_read. destruct bs as [|b bs']; cbn [delivered_writes core]; [reflexivity|].
  rewrite !bv_eqb_refl. reflexivity.
Qed.

Theorem nstep_cross_readX fd bufG bufC count moG moC rspG moG' evs :
  mqX moG moC -> nstep (NRead fd bufG count) moG rspG moG' evs ->
  exists rspC moC', nstep (NRead fd bufC count) moC rspC moC' evs /\ xstepX moG moC moG' moC'
    /\ dec_read bufC count rspC = dec_read bufG count rspG.
Proof.
  intros HQ H. pose proof (mq_fdsX _ _ HQ) as EF. pose proof (mq_fsX _ _ HQ) as ES.
  cbn [nstep] in H |- *. rewrite EF, ES. destruct H as [-> H].
  destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try (exfalso; exact H).
  - (* [comment removed for export] *)
    destruct (fs_lookup (m_fs moG) p) as [data|] eqn:Hfs; [| destruct H]. destruct H as [-> ->].
    eexists _, _. split; [split; [reflexivity| split; [reflexivity| reflexivity]]|]. split; [apply xstep_fdsX; exact HQ|].
    apply dec_read_xaddrX.
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EISDIR), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
Qed.

Lemma dsts_total_map_sndX dstsG dstsC : map snd dstsC = map snd dstsG -> dsts_total dstsC = dsts_total dstsG.
Proof.
  revert dstsC. induction dstsG as [|[a l] dG IH]; intros [|[a' l'] dC] Hl; cbn in *; try discriminate; [reflexivity|].
  injection Hl as -> Hl'. rewrite (IH dC Hl'). reflexivity.
Qed.

Lemma iovs_total_map_sndX dstsG dstsC : map snd dstsC = map snd dstsG -> iovs_total (iovs_of dstsC) = iovs_total (iovs_of dstsG).
Proof.
  revert dstsC. induction dstsG as [|[a l] dG IH]; intros [|[a' l'] dC] Hl; cbn -[Z_to_bv bv_unsigned] in *; try discriminate; [reflexivity|].
  injection Hl as -> Hl'. unfold iovs_of in IH. rewrite (IH dC Hl'). reflexivity.
Qed.

(* [comment removed for export] *)
Definition lens_okX (dsts : list (Z * Z)) : Prop := Forall (fun d => 0 <= snd d < 2^64) dsts.

Lemma match_scatter_stuckX dsts ws n : n <= 0 -> ws <> [] -> Forall (fun d => 0 <= snd d) dsts -> match_scatter dsts ws n = None.
Proof.
  intros Hn Hws HF. induction dsts as [|[a l] rest IH]; cbn [match_scatter].
  - destruct ws; [exfalso; apply Hws; reflexivity| reflexivity].
  - apply Forall_cons_iff in HF as [Hl HF]. cbn [snd] in Hl.
    replace (Z.min n l <=? 0) with true by (symmetry; apply Z.leb_le; lia). apply IH. exact HF.
Qed.

Lemma match_scatter_xaddrX dstsG dstsC : map snd dstsC = map snd dstsG -> lens_okX dstsG ->
  forall bs n, match_scatter dstsC (scatterw (iovs_of dstsC) bs) n = match_scatter dstsG (scatterw (iovs_of dstsG) bs) n.
Proof.
  revert dstsC. induction dstsG as [|[aG l] restG IH]; intros [|[aC l'] restC] Hl HF bs n; cbn [map snd] in Hl; try discriminate.
  - reflexivity.
  - injection Hl as -> Hl'. apply Forall_cons_iff in HF as [Hl0 HF]. cbn [snd] in Hl0.
    assert (HF0 : Forall (fun d => 0 <= snd d) restG) by (eapply Forall_impl; [| exact HF]; intros d Hd; cbn in Hd; lia).
    assert (HF0C : Forall (fun d => 0 <= snd d) restC).
    { clear -Hl' HF0. revert restC Hl'. induction restG as [|[? ?] rg IH]; intros [|[? ?] rc] Hl; cbn in Hl; try discriminate; [constructor|].
      injection Hl as -> Hl''. apply Forall_cons_iff in HF0 as [H0 HF0]. constructor; [exact H0| exact (IH HF0 rc Hl'')]. }
    destruct bs as [|b bs'].
    + cbn [scatterw iovs_of map]. fold (iovs_of restC) (iovs_of restG).
      specialize (IH restC Hl' HF [] n). cbn [scatterw] in IH |- *. cbn [match_scatter].
      destruct (Z.min n l <=? 0); [| reflexivity].
      destruct restC, restG; cbn [iovs_of map scatterw] in IH; exact IH.
    + cbn [iovs_of map fst snd scatterw]. fold (iovs_of restC) (iovs_of restG).
      rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. rewrite unsigned_lit by lia.
      set (n0 := Nat.min (Z.to_nat l) (length (b :: bs'))).
      destruct (Z.eq_dec l 0) as [->|Hlnz].
      * replace n0 with 0%nat by (subst n0; cbn; lia). cbn [firstn skipn].
        cbn [match_scatter]. replace (Z.min n 0 <=? 0) with true by (symmetry; apply Z.leb_le; lia).
        apply IH; [exact Hl'| exact HF].
      * assert (Hn0 : (1 <= n0 <= length (b :: bs'))%nat) by (subst n0; cbn [length] in *; lia).
        destruct (firstn n0 (b :: bs')) as [|h here'] eqn:Eh.
        { exfalso. assert (length (firstn n0 (b :: bs')) = n0) by (apply firstn_length_le; lia). rewrite Eh in H. cbn in H. lia. }
        cbn [match_scatter]. destruct (Z.min n l <=? 0) eqn:Hk.
        -- (* [comment removed for export] *)
           apply Z.leb_le in Hk. rewrite !match_scatter_stuckX; [reflexivity| lia| discriminate| exact HF0| lia| discriminate| exact HF0C].
        -- rewrite !bv_eqb_refl. cbn [andb]. destruct (Z.of_nat (length (h :: here')) =? Z.min n l); [| reflexivity].
           rewrite (IH restC Hl' HF). reflexivity.
Qed.

Lemma dec_readv_xaddrX dstsG dstsC r bs : map snd dstsC = map snd dstsG -> lens_okX dstsG ->
  dec_readv dstsC (mkEffect r (scatterw (iovs_of dstsC) bs) []) = dec_readv dstsG (mkEffect r (scatterw (iovs_of dstsG) bs) []).
Proof.
  intros Hl HF. unfold dec_readv. cbn [core].
  rewrite !iovs_total_Z_dsts, (dsts_total_map_sndX dstsG dstsC Hl).
  destruct (errno_of r) as [e|].
  - destruct bs as [|b bs']; [| ]. 
    + destruct dstsC, dstsG; cbn; reflexivity.
    + (* [comment removed for export] *)
      assert (SH : forall ds ds', map snd ds' = map snd ds -> (scatterw (iovs_of ds') (b :: bs') = [] <-> scatterw (iovs_of ds) (b :: bs') = [])).
      { clear. intros ds. generalize (b :: bs') as l. induction ds as [|[a ln] rest IH]; intros l0 [|[a' ln'] rest'] Hm; cbn in Hm; try discriminate; [destruct l0; cbn; tauto|].
        injection Hm as -> Hm'. destruct l0 as [|x xs]; [cbn; tauto|]. cbn [scatterw iovs_of map fst snd]. fold (iovs_of rest') (iovs_of rest).
        destruct (firstn _ (x :: xs)); [apply IH; exact Hm'| split; intros; discriminate]. }
      destruct (scatterw (iovs_of dstsC) (b :: bs')) eqn:EC; destruct (scatterw (iovs_of dstsG) (b :: bs')) eqn:EG; try reflexivity.
      * apply (proj1 (SH dstsG dstsC Hl)) in EC. congruence.
      * apply (proj2 (SH dstsG dstsC Hl)) in EG. congruence.
  - destruct (bv_unsigned r <=? dsts_total dstsG); [| reflexivity]. rewrite (match_scatter_xaddrX dstsG dstsC Hl HF). reflexivity.
Qed.

Theorem nstep_cross_readvX fd dstsG dstsC moG moC rspG moG' evs :
  map snd dstsC = map snd dstsG -> lens_okX dstsG ->
  mqX moG moC -> nstep (NReadv fd dstsG) moG rspG moG' evs ->
  exists rspC moC', nstep (NReadv fd dstsC) moC rspC moC' evs /\ xstepX moG moC moG' moC'
    /\ dec_readv dstsC rspC = dec_readv dstsG rspG.
Proof.
  intros Hl HF HQ H. pose proof (mq_fdsX _ _ HQ) as EF. pose proof (mq_fsX _ _ HQ) as ES.
  pose proof (iovs_total_map_sndX dstsG dstsC Hl) as EI.
  cbn [nstep] in H |- *. rewrite EF, ES, EI. destruct H as [-> H].
  destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try (exfalso; exact H).
  - destruct (fs_lookup (m_fs moG) p) as [data|] eqn:Hfs; [| destruct H]. cbv zeta in H. destruct H as [-> ->].
    eexists _, _. split; [split; [reflexivity| split; [reflexivity| reflexivity]]|]. split; [apply xstep_fdsX; exact HQ|].
    apply dec_readv_xaddrX; [exact Hl| exact HF].
  - destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
  - destruct H as [-> ->]. exists (efferr EISDIR), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
  - destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
  - destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_sameX; exact HQ| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem nexit_crossX c moG moC code moG' :
  mqX moG moC -> nexit (NExit c) moG code moG' ->
  exists moC', nexit (NExit c) moC code moC' /\ m_fs moC' = m_fs moG'.
Proof.
  intros HQ [-> ->]. exists (with_halted (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) moC). split; [split; reflexivity|].
  autorewrite with model. exact (mq_fsX _ _ HQ).
Qed.

(* [comment removed for export] *)
Lemma nexit_onlyX n mo code mo' : nexit n mo code mo' -> exists c, n = NExit c.
Proof. destruct n; cbn; intros H; try destruct H; eauto. Qed.
End NodeSimX.

(* [comment removed for export] *)
Module UFrameX.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX USimX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section FrameX.
Context {G : Type}.
Variable nsafeP : node -> G -> Model -> Prop.
Variable gstepP : node -> resp -> G -> G.
Variable I : Model -> Prop.
Hypothesis HI : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> I mo -> I mo'.

#[using="HI"] Lemma tpathX_frame {R} (t : itree node R) : forall g mo tr r g' mo',
  tpathX gstepP t g mo tr r g' mo' -> I mo -> I mo'.
Proof.
  induction t as [r0|n k IH]; intros g mo tr r g' mo' HP Hi; cbn in HP.
  - destruct HP as (_ & _ & -> & _). exact Hi.
  - destruct HP as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    exact (IH rsp _ mo1 tr' r g' mo' Hp (HI _ _ _ _ _ Hst Hi)).
Qed.

Context {StG StC : Type}.
Variable npk : node -> option (machine_state -> resp).
#[local] Notation relX := (USimX.relX G StG StC).
#[local] Notation usimS := (usimX nsafeP gstepP npk).

(* [comment removed for export] *)
Definition framedX (R : relX) : relX := fun g sG moG sC moC => R g sG moG sC moC /\ I moG.

#[using="HI"] Theorem usimX_frame {A B} (R : relX) (mG : M StG A) (mC : M StC B) (Q : A -> B -> relX) :
  usimS R mG mC Q -> usimS (framedX R) mG mC (fun a b => framedX (Q a b)).
Proof.
  intros H g sG moG sC moC [HR Hi]. destruct (H _ _ _ _ _ HR) as (HP & HE & HS). split; [| split; [exact HE| exact HS]].
  intros trG a sG' g' moG' Hp. eapply wreach_mono; [exact (HP _ _ _ _ _ Hp)|].
  intros tr r mo' (b & sC' & -> & -> & HQ). exists b, sC'. split; [reflexivity|]. split; [reflexivity|]. split; [exact HQ|].
  exact (tpathX_frame _ _ _ _ _ _ _ Hp Hi).
Qed.

#[using="Type"] Lemma framedX_pre {A B} (R R' : relX) (mG : M StG A) (mC : M StC B) Q :
  usimS (framedX R') mG mC Q -> (forall g sG moG sC moC, R g sG moG sC moC -> R' g sG moG sC moC) -> usimS (framedX R) mG mC Q.
Proof. intros H HR. eapply usimX_pre; [exact H|]. intros ? ? ? ? ? [X Y]. exact (conj (HR _ _ _ _ _ X) Y). Qed.

#[using="Type"] Lemma framedX_exI {A B X} (R : X -> relX) (mG : M StG A) (mC : M StC B) Q :
  (forall x, usimS (framedX (R x)) mG mC Q) -> usimS (framedX (fun g sG moG sC moC => exists x, R x g sG moG sC moC)) mG mC Q.
Proof.
  intros H. eapply usimX_pre; [apply (usimX_exI nsafeP gstepP npk (fun x => framedX (R x))); exact H|].
  intros ? ? ? ? ? [[x HR] Hi]. exists x. exact (conj HR Hi).
Qed.

#[using="Type"] Lemma framedX_pure {A B} (R : relX) (phi : Prop) (mG : M StG A) (mC : M StC B) Q :
  (phi -> usimS (framedX R) mG mC Q) -> usimS (framedX (fun g sG moG sC moC => phi /\ R g sG moG sC moC)) mG mC Q.
Proof.
  intros H. eapply usimX_pre; [apply (usimX_pure nsafeP gstepP npk (framedX R) phi); exact H|].
  intros ? ? ? ? ? [[Hp HR] Hi]. exact (conj Hp (conj HR Hi)).
Qed.

#[using="Type"] Lemma framedX_use {A B} (R : relX) (mG : M StG A) (mC : M StC B) Q :
  (forall g sG moG sC moC, R g sG moG sC moC -> I moG -> usimS (framedX R) mG mC Q) -> usimS (framedX R) mG mC Q.
Proof.
  intros H. apply usimX_pointwise. intros g sG moG sC moC [HR Hi].
  eapply usimX_pre; [exact (H _ _ _ _ _ HR Hi)|]. intros ? ? ? ? ? (-> & -> & -> & -> & ->). exact (conj HR Hi).
Qed.

End FrameX.

(* [comment removed for export] *)
Lemma ND_nstepX p : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> ND p mo -> ND p mo'.
Proof. intros n mo rsp mo' evs Hst H. unfold ND. rewrite (nstep_fs_under _ _ _ _ _ Hst p). exact H. Qed.

Definition usimX_ND {G} nsafeP gstepP {StG StC A B} p npk (R : USimX.relX G StG StC) (mG : M StG A) (mC : M StC B) Q :=
  @usimX_frame G nsafeP gstepP (ND p) (ND_nstepX p) StG StC npk A B R mG mC Q.
End UFrameX.

(* [comment removed for export] *)
Module ProgT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ProgMain.
Context {H hptr : Type} (HO : HeapOps H hptr).

Definition prog_main (FO : FrameOps (H:=H) (hptr:=hptr)) (stk : stack_site -> Z) (argv : list (list Z)) : M (PState H hptr) Empty_set :=
  code <- main_prog HO FO stk argv ;;
  exit_model s_stdio_exit code.

#[using="Type"] Lemma prog_split : forall tb FO stk argv,
  prog HO tb FO stk argv = (startup_model (set_tls_pin HO) tb ;;; prog_main FO stk argv).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition prog_main_itree (FO : FrameOps (H:=H) (hptr:=hptr)) (stk : stack_site -> Z) (argv : list (list byte)) (s : PState H hptr)
  : itree node (exc unit) :=
  ebind (prog_main FO stk (argv_Z argv) s) (fun p => match fst p : Empty_set with end).
End ProgMain.
End ProgT.

(* [comment removed for export] *)
Module DecodeX.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ModelX MmXfer ITreeA NodesA NodesSil NodesMmSh NodesAS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition minvX (mo : Model) : Prop := minv (lf mo).

(* [comment removed for export] *)
Definition xnode (n : node) : Prop :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ | NMmapNR _ _ => False
  | _ => True
  end.

(* [comment removed for export] *)
Lemma lf_setvm : forall mo, lf mo = setvm (m_vm (lf mo)) mo.
Proof. intros [fd vm io fs pr lm tm]. reflexivity. Qed.

Lemma nstep_lf : forall n mo rsp mo' evs, fsnode n -> nstep n mo rsp mo' evs -> nstep n (lf mo) rsp (lf mo') evs.
Proof.
  intros n mo rsp mo' evs Hfs Hst. pose proof (nstep_vm_same n mo rsp mo' evs Hfs Hst) as EV.
  rewrite (lf_setvm mo), (lf_setvm mo'). replace (m_vm (lf mo')) with (m_vm (lf mo)).
  - apply nstep_setvm; assumption.
  - destruct mo as [fd vm io fs pr lm tm], mo' as [fd' vm' io' fs' pr' lm' tm']. cbn in EV. subst vm'. reflexivity.
Qed.

Lemma m_fds_lf' : forall mo, m_fds (lf mo) = m_fds mo. Proof. reflexivity. Qed.
Lemma m_fs_lf' : forall mo, m_fs (lf mo) = m_fs mo. Proof. reflexivity. Qed.

Lemma alloc_fd_rangeX : forall mo,
  minvX mo -> fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096.
Proof. intros mo H. exact (alloc_fd_range (lf mo) H). Qed.

Lemma lf_with_tid : forall t m, lf (with_tid t m) = with_tid t (lf m). Proof. intros t [fd vm io fs pr lm tm]. reflexivity. Qed.

Lemma minvX_preserved : forall n mo eff mo' evs,
  xnode n -> node_static_ok n ->
  minvX mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minvX mo'.
Proof.
  intros n mo eff mo' evs Hx Hok Hm Hh Hst.
  assert (FS : fsnode n -> m_halted mo' = None /\ minvX mo').
  { intros Hfs. pose proof (nstep_lf _ _ _ _ _ Hfs Hst) as Hst'. exact (minv_preserved n (lf mo) eff (lf mo') evs Hok Hm Hh Hst'). }
  destruct n; try (apply FS; exact I); try (exfalso; exact Hx).
  - (* [comment removed for export] *) apply (minv_preserved NSetTid (lf mo) eff (lf mo') evs Hok Hm Hh).
    cbn [nstep] in Hst |- *. destruct Hst as (-> & t & -> & H). split; [reflexivity|]. exists t. split; [reflexivity|].
    change (m_tid (lf mo)) with (m_tid mo). destruct (m_tid mo); destruct H as [H1 ->]; (split; [exact H1|]); [reflexivity| apply lf_with_tid].
  - (* [comment removed for export] *) destruct Hst.
  - (* [comment removed for export] *) destruct Hst as (-> & _). split; assumption.
Qed.

Lemma minvX_peek : forall a mo eff mo' evs, nstep (NPeek a) mo eff mo' evs -> mo' = mo.
Proof. intros a mo eff mo' evs (-> & _). reflexivity. Qed.

(* [comment removed for export] *)
Lemma lf_eq_inv : forall a b, lf a = lf b -> m_vm a = m_vm b -> a = b.
Proof.
  intros [fd vm io fs pr lm tm] [fd' vm' io' fs' pr' lm' tm'] H1 H2. cbn in H2. subst vm'.
  unfold lf, with_vm_backing in H1. cbn in H1. inversion H1; subst. reflexivity.
Qed.

Lemma vm_with_fds : forall f m, m_vm (with_fds f m) = m_vm m. Proof. intros f [fd vm io fs pr lm tm]. reflexivity. Qed.
Lemma vm_with_fs : forall f m, m_vm (with_fs f m) = m_vm m. Proof. intros f [fd vm io fs pr lm tm]. reflexivity. Qed.
Lemma lf_with_fs : forall x m, lf (with_fs x m) = with_fs x (lf m). Proof. intros x [fd vm io fs pr lm tm]. reflexivity. Qed.

Lemma nstep_dec_openX : forall path mo rsp mo' evs,
  minvX mo ->
  nstep (NOpen path) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_open rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0))
         /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo
  end.
Proof.
  intros path mo rsp mo' evs Hm Hst. pose proof (nstep_vm_same (NOpen path) _ _ _ _ I Hst) as EV.
  destruct (nstep_dec_open path (lf mo) rsp (lf mo') evs Hm (nstep_lf (NOpen path) _ _ _ _ I Hst)) as (-> & a & Hd & X).
  split; [reflexivity|]. exists a. split; [exact Hd|]. destruct a as [e|fd].
  - destruct X as [E He]. split; [apply lf_eq_inv; assumption| exact He].
  - destruct X as (X1 & X2 & X3 & ent & X4 & X5). rewrite !m_fds_lf' in *. repeat (split; [assumption|]).
    exists ent. split; [exact X4|]. apply lf_eq_inv; [rewrite X5, lf_with_fds; reflexivity| rewrite vm_with_fds; exact EV].
Qed.

Lemma nstep_dec_openwX : forall path mode mo rsp mo' evs,
  minvX mo ->
  nstep (NOpenW path mode) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_openw rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ (path_max <=? length path)%nat = false /\ path <> []
      /\ ((path = devnull_path /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) FdNull) mo)
          \/ (path <> devnull_path /\ write_dirref path mo = false /\ path <> dot_path
              /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW path (Z_to_bv 64 0)))
                         (with_fs (fs_set (m_fs mo) path []) mo)))
  end.
Proof.
  intros path mode mo rsp mo' evs Hm Hst. pose proof (nstep_vm_same (NOpenW path mode) _ _ _ _ I Hst) as EV.
  destruct (nstep_dec_openw path mode (lf mo) rsp (lf mo') evs Hm (nstep_lf (NOpenW path mode) _ _ _ _ I Hst)) as (-> & a & Hd & X).
  split; [reflexivity|]. exists a. split; [exact Hd|]. destruct a as [e|fd].
  - destruct X as [E He]. split; [apply lf_eq_inv; assumption| exact He].
  - destruct X as (X1 & X2 & X3 & X4 & X5 & X6). rewrite !m_fds_lf' in *. repeat (split; [assumption|]).
    destruct X6 as [[Ep E]|(Ep & Ew & Ed & E)]; [left| right].
    + split; [exact Ep|]. apply lf_eq_inv; [rewrite E, lf_with_fds; reflexivity| rewrite vm_with_fds; exact EV].
    + split; [exact Ep|]. split; [exact Ew|]. split; [exact Ed|].
      apply lf_eq_inv; [rewrite E, lf_with_fds, lf_with_fs; reflexivity| rewrite vm_with_fds, vm_with_fs; exact EV].
Qed.
End DecodeX.
