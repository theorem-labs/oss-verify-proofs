(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

Definition mq (moG moC : Model) : Prop :=
  m_fds moC = m_fds moG /\ m_fs moC = m_fs moG /\ m_halted moC = m_halted moG /\
  m_tid moC = m_tid moG /\ m_stdin moC = m_stdin moG.

Lemma mq_vm_only moG moC : mq moG moC <-> vm_only moG moC.
Proof. unfold mq, vm_only. tauto. Qed.

Lemma mq_refl mo : mq mo mo.
Proof. repeat split; reflexivity. Qed.
Lemma mq_sym a b : mq a b -> mq b a.
Proof. intros (H1 & H2 & H3 & H4 & H5). repeat split; congruence. Qed.
Lemma mq_trans a b c : mq a b -> mq b c -> mq a c.
Proof. intros (H1 & H2 & H3 & H4 & H5) (G1 & G2 & G3 & G4 & G5). repeat split; congruence. Qed.

(* [comment removed for export] *)
Lemma mq_vm_l moG moG' moC : vm_only moG moG' -> mq moG moC -> mq moG' moC.
Proof. intros HV HQ. apply mq_vm_only in HV. exact (mq_trans _ _ _ (mq_sym _ _ HV) HQ). Qed.
Lemma mq_vm_r moG moC moC' : vm_only moC moC' -> mq moG moC -> mq moG moC'.
Proof. intros HV HQ. apply mq_vm_only in HV. exact (mq_trans _ _ _ HQ HV). Qed.

Lemma mq_with_fds f moG moC : mq moG moC -> mq (with_fds f moG) (with_fds f moC).
Proof. intros (H1 & H2 & H3 & H4 & H5). unfold mq. autorewrite with model. repeat split; congruence. Qed.
Lemma mq_with_fs f moG moC : mq moG moC -> mq (with_fs f moG) (with_fs f moC).
Proof. intros (H1 & H2 & H3 & H4 & H5). unfold mq. autorewrite with model. repeat split; congruence. Qed.
Lemma mq_with_tid t moG moC : mq moG moC -> mq (with_tid t moG) (with_tid t moC).
Proof. intros (H1 & H2 & H3 & H4 & H5). unfold mq. autorewrite with model. repeat split; congruence. Qed.
Lemma mq_with_halted c moG moC : mq moG moC -> mq (with_halted c moG) (with_halted c moC).
Proof. intros (H1 & H2 & H3 & H4 & H5). unfold mq. autorewrite with model. repeat split; congruence. Qed.

Lemma mq_fds moG moC : mq moG moC -> m_fds moC = m_fds moG. Proof. intros H; exact (proj1 H). Qed.
Lemma mq_fs moG moC : mq moG moC -> m_fs moC = m_fs moG. Proof. intros H; exact (proj1 (proj2 H)). Qed.
Lemma mq_halted moG moC : mq moG moC -> m_halted moC = m_halted moG. Proof. intros H; exact (proj1 (proj2 (proj2 H))). Qed.
Lemma mq_tid moG moC : mq moG moC -> m_tid moC = m_tid moG. Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.

(* [comment removed for export] *)
Lemma vmmaps_with_fds f mo : m_vmmaps (with_fds f mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.
Lemma vmmaps_with_fs f mo : m_vmmaps (with_fs f mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.
Lemma vmmaps_with_tid t mo : m_vmmaps (with_tid t mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.
Lemma vmmaps_with_halted c mo : m_vmmaps (with_halted c mo) = m_vmmaps mo. Proof. autorewrite with model. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fdnode (n : node) : Prop :=
  match n with
  | NWrite _ _ | NWritev _ _ | NOpen _ | NClose _ | NIoctl _ _ | NSetTid | NOpenW _ _ | NWritevF _ _
  | NLseek _ _ _ | NUnlink _ _ => True
  | _ => False
  end.

(* [comment removed for export] *)
Definition xstep (moG moC moG' moC' : Model) : Prop :=
  mq moG' moC' /\ m_vmmaps moG' = m_vmmaps moG /\ m_vmmaps moC' = m_vmmaps moC.

Lemma xstep_same moG moC : mq moG moC -> xstep moG moC moG moC.
Proof. intros HQ. split; [exact HQ| split; reflexivity]. Qed.
Lemma xstep_fds moG moC f : mq moG moC -> xstep moG moC (with_fds f moG) (with_fds f moC).
Proof. intros HQ. split; [apply mq_with_fds; exact HQ| split; apply vmmaps_with_fds]. Qed.
Lemma xstep_fs_fds moG moC g f : mq moG moC -> xstep moG moC (with_fds f (with_fs g moG)) (with_fds f (with_fs g moC)).
Proof. intros HQ. split; [apply mq_with_fds; apply mq_with_fs; exact HQ| split; rewrite vmmaps_with_fds, vmmaps_with_fs; reflexivity]. Qed.
Lemma xstep_fs moG moC g : mq moG moC -> xstep moG moC (with_fs g moG) (with_fs g moC).
Proof. intros HQ. split; [apply mq_with_fs; exact HQ| split; apply vmmaps_with_fs]. Qed.
Lemma xstep_tid moG moC t : mq moG moC -> xstep moG moC (with_tid t moG) (with_tid t moC).
Proof. intros HQ. split; [apply mq_with_tid; exact HQ| split; apply vmmaps_with_tid]. Qed.

Lemma open_result_cross moG moC ent rsp moG' : mq moG moC -> open_result moG ent rsp moG' ->
  exists moC', open_result moC ent rsp moC' /\ xstep moG moC moG' moC'.
Proof.
  intros HQ [(e & He & -> & ->)|(Hlk & -> & ->)].
  - exists moC. split; [left; exists e; auto| apply xstep_same; exact HQ].
  - exists (with_fds (fd_insert (m_fds moC) (alloc_fd (m_fds moC)) ent) moC). rewrite (mq_fds _ _ HQ). split; [right| apply xstep_fds; exact HQ].
    rewrite (mq_fds _ _ HQ). auto.
Qed.

Lemma lseek_result_cross moG moC fd mk base off rsp moG' : mq moG moC -> lseek_result moG fd mk base off rsp moG' ->
  exists moC', lseek_result moC fd mk base off rsp moC' /\ xstep moG moC moG' moC'.
Proof.
  intros HQ H. unfold lseek_result in *. destruct base as [b|]; [| destruct H].
  destruct (lseek_dest b (Z_to_bv 64 off)) as [r|].
  - destruct H as [-> ->]. exists (with_fds (fd_insert (m_fds moC) (Z_to_bv 64 fd) (mk r)) moC). split; [auto|]. rewrite (mq_fds _ _ HQ). apply xstep_fds. exact HQ.
  - destruct H as [-> ->]. exists moC. split; [auto| apply xstep_same; exact HQ].
Qed.

Theorem nstep_cross n moG moC rsp moG' evs :
  fdnode n -> mq moG moC -> nstep n moG rsp moG' evs ->
  exists moC', nstep n moC rsp moC' evs /\ xstep moG moC moG' moC'.
Proof.
  intros Hn HQ H. pose proof (mq_fds _ _ HQ) as EF. pose proof (mq_fs _ _ HQ) as ES. pose proof (mq_tid _ _ HQ) as ET.
  destruct n; cbn [fdnode] in Hn; try destruct Hn; cbn [nstep] in H |- *.
  - (* [comment removed for export] *) destruct H as (-> & k & Hk & -> & ->). exists moC. split; [| apply xstep_same; exact HQ]. split; [reflexivity|]. exists k. auto.
  - (* [comment removed for export] *) destruct H as (-> & k & Hk & -> & ->). exists moC. split; [| apply xstep_same; exact HQ]. split; [reflexivity|]. exists k. auto.
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?ES.
    destruct (path_max <=? length path)%nat; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]|].
    destruct path as [|c path']; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]|].
    destruct (path_eqb (c :: path') dot_path).
    + destruct (open_result_cross moG moC FdDir rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
    + destruct (fs_lookup (m_fs moG) (c :: path')); [| destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]].
      destruct (open_result_cross moG moC _ rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
  - (* [comment removed for export] *) destruct H as (-> & Hfd & H). rewrite ?EF. destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)).
    + destruct H as [-> ->]. exists (with_fds (fd_remove (m_fds moG) (Z_to_bv 64 fd)) moC). split; [| apply xstep_fds; exact HQ]. auto.
    + destruct H as [-> ->]. exists moC. split; [auto| apply xstep_same; exact HQ].
  - (* [comment removed for export] *) destruct H as (-> & -> & H). exists moC. rewrite ?EF. split; [| apply xstep_same; exact HQ]. split; [reflexivity|]. split; [reflexivity|]. exact H.
  - (* [comment removed for export] *) destruct H as (-> & t & -> & H). rewrite ?ET. destruct (m_tid moG) as [t0|].
    + destruct H as [-> ->]. exists moC. split; [| apply xstep_same; exact HQ]. split; [reflexivity|]. exists t0. auto.
    + destruct H as [Ht ->]. exists (with_tid t moC). split; [| apply xstep_tid; exact HQ]. split; [reflexivity|]. exists t. auto.
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?ES, ?EF.
    destruct (path_max <=? length path)%nat; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]|].
    destruct path as [|c path']; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]|].
    (* [comment removed for export] *)
    destruct (path_eqb (c :: path') devnull_path).
    { destruct (open_result_cross moG moC FdNull rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto. }
    destruct (path_has_slash (c :: path')); [destruct H|].
    unfold write_dirref in H |- *. rewrite ?ES.
    destruct (path_is_dirref (c :: path') || fs_under (m_fs moG) (c :: path')); [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]|].
    unfold openw_result in H |- *. rewrite ?EF, ?ES.
    destruct H as [(e & He & -> & ->)|(Hlk & -> & ->)].
    + exists moC. split; [split; [reflexivity| left; exists e; auto]| apply xstep_same; exact HQ].
    + eexists. split; [split; [reflexivity| right; split; [exact Hlk| split; [reflexivity| reflexivity]]]|].
      apply xstep_fs_fds. exact HQ.
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?EF, ?ES.
    destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|]; try (destruct H; fail).
    + destruct (fs_lookup (m_fs moG) p) as [data|]; [| destruct H]. destruct H as [-> ->].
      eexists. split; [split; [reflexivity| split; [reflexivity| reflexivity]]|].
      rewrite ?EF, ?ES. apply xstep_fs_fds. exact HQ.
    + (* [comment removed for export] *) destruct H as [-> ->]. exists moC. split; [auto| apply xstep_same; exact HQ].
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?ES, ?EF.
    destruct (path_has_slash path); [destruct H|].     (* [comment removed for export] *)
    destruct (fs_under (m_fs moG) path); [destruct H|].
    destruct (fs_lookup (m_fs moG) path); [| destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]].
    destruct rmdir; [destruct H as [-> ->]; exists moC; split; [auto| apply xstep_same; exact HQ]|].
    destruct H as [(e & He & -> & ->)|(Hn & -> & ->)].
    + exists moC. split; [split; [reflexivity| left; exists e; auto]| apply xstep_same; exact HQ].
    + exists (with_fs (fs_remove (m_fs moG) path) moC). split; [split; [reflexivity| right; auto]| apply xstep_fs; exact HQ].
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite ?EF, ?ES.
    destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p cur|p cur|p cur|p cur| |sk|pid w|[|] [|]| ]|]; try (destruct H; fail).
    + destruct (fs_lookup (m_fs moG) p) as [data|]; [| destruct H].
      destruct (lseek_result_cross moG moC fd _ _ off rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
    + destruct (fs_lookup (m_fs moG) p) as [data|]; [| destruct H].
      destruct (lseek_result_cross moG moC fd _ _ off rsp moG' HQ H) as (moC' & H' & X). exists moC'. auto.
    + (* [comment removed for export] *) destruct H as [-> ->]. exists moC. split; [auto| apply xstep_same; exact HQ].
    + destruct H as [-> ->]. exists moC. split; [auto| apply xstep_same; exact HQ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dec_read_xaddr bufG bufC count r bs :
  dec_read bufC count (mkEffect r (delivered_writes (Z_to_bv 64 bufC) bs) []) =
  dec_read bufG count (mkEffect r (delivered_writes (Z_to_bv 64 bufG) bs) []).
Proof.
  unfold dec_read. destruct bs as [|b bs']; cbn [delivered_writes core]; [reflexivity|].
  rewrite !bv_eqb_refl. reflexivity.
Qed.

Theorem nstep_cross_read fd bufG bufC count moG moC rspG moG' evs :
  mq moG moC -> nstep (NRead fd bufG count) moG rspG moG' evs ->
  exists rspC moC', nstep (NRead fd bufC count) moC rspC moC' evs /\ xstep moG moC moG' moC'
    /\ dec_read bufC count rspC = dec_read bufG count rspG.
Proof.
  intros HQ H. pose proof (mq_fds _ _ HQ) as EF. pose proof (mq_fs _ _ HQ) as ES.
  cbn [nstep] in H |- *. rewrite EF, ES. destruct H as [-> H].
  destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try (exfalso; exact H).
  - (* [comment removed for export] *)
    destruct (fs_lookup (m_fs moG) p) as [data|] eqn:Hfs; [| destruct H]. destruct H as [-> ->].
    eexists _, _. split; [split; [reflexivity| split; [reflexivity| reflexivity]]|]. split; [apply xstep_fds; exact HQ|].
    apply dec_read_xaddr.
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EISDIR), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
  - (* [comment removed for export] *) destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
Qed.

Lemma dsts_total_map_snd dstsG dstsC : map snd dstsC = map snd dstsG -> dsts_total dstsC = dsts_total dstsG.
Proof.
  revert dstsC. induction dstsG as [|[a l] dG IH]; intros [|[a' l'] dC] Hl; cbn in *; try discriminate; [reflexivity|].
  injection Hl as -> Hl'. rewrite (IH dC Hl'). reflexivity.
Qed.

Lemma iovs_total_map_snd dstsG dstsC : map snd dstsC = map snd dstsG -> iovs_total (iovs_of dstsC) = iovs_total (iovs_of dstsG).
Proof.
  revert dstsC. induction dstsG as [|[a l] dG IH]; intros [|[a' l'] dC] Hl; cbn -[Z_to_bv bv_unsigned] in *; try discriminate; [reflexivity|].
  injection Hl as -> Hl'. unfold iovs_of in IH. rewrite (IH dC Hl'). reflexivity.
Qed.

(* [comment removed for export] *)
Definition lens_ok (dsts : list (Z * Z)) : Prop := Forall (fun d => 0 <= snd d < 2^64) dsts.

Lemma match_scatter_stuck dsts ws n : n <= 0 -> ws <> [] -> Forall (fun d => 0 <= snd d) dsts -> match_scatter dsts ws n = None.
Proof.
  intros Hn Hws HF. induction dsts as [|[a l] rest IH]; cbn [match_scatter].
  - destruct ws; [exfalso; apply Hws; reflexivity| reflexivity].
  - apply Forall_cons_iff in HF as [Hl HF]. cbn [snd] in Hl.
    replace (Z.min n l <=? 0) with true by (symmetry; apply Z.leb_le; lia). apply IH. exact HF.
Qed.

Lemma match_scatter_xaddr dstsG dstsC : map snd dstsC = map snd dstsG -> lens_ok dstsG ->
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
           apply Z.leb_le in Hk. rewrite !match_scatter_stuck; [reflexivity| lia| discriminate| exact HF0| lia| discriminate| exact HF0C].
        -- rewrite !bv_eqb_refl. cbn [andb]. destruct (Z.of_nat (length (h :: here')) =? Z.min n l); [| reflexivity].
           rewrite (IH restC Hl' HF). reflexivity.
Qed.

Lemma dec_readv_xaddr dstsG dstsC r bs : map snd dstsC = map snd dstsG -> lens_ok dstsG ->
  dec_readv dstsC (mkEffect r (scatterw (iovs_of dstsC) bs) []) = dec_readv dstsG (mkEffect r (scatterw (iovs_of dstsG) bs) []).
Proof.
  intros Hl HF. unfold dec_readv. cbn [core].
  rewrite !iovs_total_Z_dsts, (dsts_total_map_snd dstsG dstsC Hl).
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
  - destruct (bv_unsigned r <=? dsts_total dstsG); [| reflexivity]. rewrite (match_scatter_xaddr dstsG dstsC Hl HF). reflexivity.
Qed.

Theorem nstep_cross_readv fd dstsG dstsC moG moC rspG moG' evs :
  map snd dstsC = map snd dstsG -> lens_ok dstsG ->
  mq moG moC -> nstep (NReadv fd dstsG) moG rspG moG' evs ->
  exists rspC moC', nstep (NReadv fd dstsC) moC rspC moC' evs /\ xstep moG moC moG' moC'
    /\ dec_readv dstsC rspC = dec_readv dstsG rspG.
Proof.
  intros Hl HF HQ H. pose proof (mq_fds _ _ HQ) as EF. pose proof (mq_fs _ _ HQ) as ES.
  pose proof (iovs_total_map_snd dstsG dstsC Hl) as EI.
  cbn [nstep] in H |- *. rewrite EF, ES, EI. destruct H as [-> H].
  destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try (exfalso; exact H).
  - destruct (fs_lookup (m_fs moG) p) as [data|] eqn:Hfs; [| destruct H]. cbv zeta in H. destruct H as [-> ->].
    eexists _, _. split; [split; [reflexivity| split; [reflexivity| reflexivity]]|]. split; [apply xstep_fds; exact HQ|].
    apply dec_readv_xaddr; [exact Hl| exact HF].
  - destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
  - destruct H as [-> ->]. exists (efferr EISDIR), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
  - destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
  - destruct H as [-> ->]. exists (efferr EBADF), moC. split; [auto|]. split; [apply xstep_same; exact HQ| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem nexit_cross c moG moC code moG' :
  mq moG moC -> nexit (NExit c) moG code moG' ->
  exists moC', nexit (NExit c) moC code moC' /\ m_fs moC' = m_fs moG'.
Proof.
  intros HQ [-> ->]. exists (with_halted (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) moC). split; [split; reflexivity|].
  autorewrite with model. exact (mq_fs _ _ HQ).
Qed.

(* [comment removed for export] *)
Lemma nexit_only n mo code mo' : nexit n mo code mo' -> exists c, n = NExit c.
Proof. destruct n; cbn; intros H; try destruct H; eauto. Qed.
