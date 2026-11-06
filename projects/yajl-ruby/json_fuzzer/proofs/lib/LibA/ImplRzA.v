(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA LazyModel ITreeA NodesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition merase (mo : Model) : Model := with_vm_backing (m_vm_lazy mo) [] mo.

Definition mequiv (mo1 mo2 : Model) : Prop := merase mo1 = merase mo2.

Lemma mequiv_refl : forall mo, mequiv mo mo. Proof. intros; reflexivity. Qed.
Lemma mequiv_sym : forall a b, mequiv a b -> mequiv b a. Proof. intros a b H; unfold mequiv in *; congruence. Qed.
Lemma mequiv_trans : forall a b c, mequiv a b -> mequiv b c -> mequiv a c. Proof. intros; unfold mequiv in *; congruence. Qed.

Lemma magree_mequiv : forall mo mo', magree mo mo' -> mequiv mo mo'.
Proof. intros mo mo' [M' ->]. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mequiv_frame : forall mo1 mo2, mequiv mo1 mo2 ->
  m_fds mo2 = m_fds mo1 /\ m_fd mo2 = m_fd mo1 /\ m_vmmaps mo2 = m_vmmaps mo1 /\ m_vm_lazy mo2 = m_vm_lazy mo1 /\
  m_io mo2 = m_io mo1 /\ m_fsys mo2 = m_fsys mo1 /\ m_proc mo2 = m_proc mo1 /\ m_lim mo2 = m_lim mo1 /\
  m_time mo2 = m_time mo1 /\
  m_fs mo2 = m_fs mo1 /\ m_halted mo2 = m_halted mo1 /\ m_tid mo2 = m_tid mo1 /\ m_stdin mo2 = m_stdin mo1.
Proof.
  intros [fd1 [maps1 lazy1 mat1] io1 fs1 proc1 lim1 tm1] [fd2 [maps2 lazy2 mat2] io2 fs2 proc2 lim2 tm2] H.
  unfold mequiv, merase in H. cbn in H. inversion H; subst. repeat split; reflexivity.
Qed.

Lemma mequiv_intro : forall mo1 mo2,
  m_fd mo2 = m_fd mo1 -> m_vmmaps mo2 = m_vmmaps mo1 -> m_vm_lazy mo2 = m_vm_lazy mo1 ->
  m_io mo2 = m_io mo1 -> m_fsys mo2 = m_fsys mo1 -> m_proc mo2 = m_proc mo1 -> m_lim mo2 = m_lim mo1 ->
  m_time mo2 = m_time mo1 -> mequiv mo1 mo2.
Proof.
  intros [fd1 [maps1 lazy1 mat1] io1 fs1 proc1 lim1 tm1] [fd2 [maps2 lazy2 mat2] io2 fs2 proc2 lim2 tm2].
  unfold mequiv, merase, with_vm_backing, m_vmmaps, m_vm_lazy, m_fd, m_io, m_fsys, m_proc, m_lim, m_time. cbn.
  intros; subst. reflexivity.
Qed.

End RC__1.
Ltac mequiv_crush H :=
  unfold mequiv, merase, with_vm_backing, with_fds, with_tid, with_halted, m_vmmaps, m_vm_lazy, m_fd, m_fds, m_pipes,
         m_io, m_fsys, m_proc, m_lim, m_time, m_halted, m_killed, m_tid, m_creds, m_setsid_succeeded in *;
  cbn in *; inversion H; subst; reflexivity.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma mequiv_with_fds : forall v mo1 mo2, mequiv mo1 mo2 -> mequiv (with_fds v mo1) (with_fds v mo2).
Proof.
  intros v [fd1 [maps1 lazy1 mat1] io1 fs1 proc1 lim1 tm1] [fd2 [maps2 lazy2 mat2] io2 fs2 proc2 lim2 tm2] H.
  mequiv_crush H.
Qed.

Lemma mequiv_with_tid : forall v mo1 mo2, mequiv mo1 mo2 -> mequiv (with_tid v mo1) (with_tid v mo2).
Proof.
  intros v [fd1 [maps1 lazy1 mat1] io1 fs1 [h1 t1 c1 ss1 sm1 ch1 ut1 sa1 kl1 ap1 at1 sp1] lim1 tm1]
           [fd2 [maps2 lazy2 mat2] io2 fs2 [h2 t2 c2 ss2 sm2 ch2 ut2 sa2 kl2 ap2 at2 sp2] lim2 tm2] H.
  mequiv_crush H.
Qed.

Lemma mequiv_with_halted : forall v mo1 mo2, mequiv mo1 mo2 -> mequiv (with_halted v mo1) (with_halted v mo2).
Proof.
  intros v [fd1 [maps1 lazy1 mat1] io1 fs1 [h1 t1 c1 ss1 sm1 ch1 ut1 sa1 kl1 ap1 at1 sp1] lim1 tm1]
           [fd2 [maps2 lazy2 mat2] io2 fs2 [h2 t2 c2 ss2 sm2 ch2 ut2 sa2 kl2 ap2 at2 sp2] lim2 tm2] H.
  mequiv_crush H.
Qed.

(* [comment removed for export] *)
Lemma nstep_xfer : forall n mo1 mo2 rsp mo1' evs,
  neutral_node n -> mequiv mo1 mo2 -> nstep n mo1 rsp mo1' evs ->
  exists mo2', nstep n mo2 rsp mo2' evs /\ mequiv mo1' mo2'.
Proof.
  intros n mo1 mo2 rsp mo1' evs Hn Heq H. pose proof (mequiv_frame _ _ Heq) as F.
  assert (Ef : m_fds mo2 = m_fds mo1) by tauto. assert (Es : m_fs mo2 = m_fs mo1) by tauto.
  assert (Et : m_tid mo2 = m_tid mo1) by tauto.
  destruct n; try contradiction; cbn [nstep] in H |- *.
  - (* [comment removed for export] *) unfold chan_write in *. destruct H as [-> HW].
    exists mo2. split; [|exact Heq]. split; [reflexivity|]. exact HW.
  - (* [comment removed for export] *) unfold chan_write in *. destruct H as [-> HW].
    exists mo2. split; [|exact Heq]. split; [reflexivity|]. exact HW.
  - (* [comment removed for export] *) destruct H as [-> H]. unfold open_result in *. rewrite <- Es, <- Ef in H.
    destruct (path_max <=? length path)%nat. { destruct H as [-> ->]. exists mo2. split; [split; [reflexivity| auto]| exact Heq]. }
    destruct path as [|c p]. { destruct H as [-> ->]. exists mo2. split; [split; [reflexivity| auto]| exact Heq]. }
    destruct (path_is_dirref (c :: p)).
    { destruct H as [(e & He & -> & ->) | (Hl & -> & ->)].
      - exists mo2. split; [split; [reflexivity| left; eauto]| exact Heq].
      - exists (with_fds (fd_insert (m_fds mo2) (alloc_fd (m_fds mo2)) FdDir) mo2).
        split; [split; [reflexivity| right; auto]| rewrite Ef; apply mequiv_with_fds; exact Heq]. }
    destruct (fs_lookup (m_fs mo2) (c :: p)).
    + destruct H as [(e & He & -> & ->) | (Hl & -> & ->)].
      * exists mo2. split; [split; [reflexivity| left; eauto]| exact Heq].
      * exists (with_fds (fd_insert (m_fds mo2) (alloc_fd (m_fds mo2)) (FdFile (c :: p) (Z_to_bv 64 0))) mo2).
        split; [split; [reflexivity| right; auto]| rewrite Ef; apply mequiv_with_fds; exact Heq].
    + destruct H as [-> ->]. exists mo2. split; [split; [reflexivity| auto]| exact Heq].
  - (* [comment removed for export] *) destruct H as [-> H]. rewrite <- Ef, <- Es in H.
    destruct (fd_lookup (m_fds mo2) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]|] eqn:Hlk; try contradiction.
    + destruct (fs_lookup (m_fs mo2) p) eqn:Hfs; [|contradiction]. destruct H as [-> ->].
      eexists. split.
      * split; [reflexivity|]. cbn [nstep]. rewrite ?Hlk, ?Hfs. split; reflexivity.
      * rewrite Ef. apply mequiv_with_fds. exact Heq.
    + destruct H as [-> ->]. exists mo2. split; [|exact Heq]. split; [reflexivity|]. cbn [nstep]. rewrite ?Hlk. auto.
    + destruct H as [-> ->]. exists mo2. split; [|exact Heq]. split; [reflexivity|]. cbn [nstep]. rewrite ?Hlk. auto.
  - (* [comment removed for export] *) destruct H as (-> & Hfd & H). rewrite <- Ef in H.
    destruct (fd_lookup (m_fds mo2) (Z_to_bv 64 fd)) eqn:Hlk.
    + destruct H as [-> ->]. eexists. split.
      * split; [reflexivity|]. split; [exact Hfd|]. rewrite ?Hlk. split; reflexivity.
      * rewrite Ef. apply mequiv_with_fds. exact Heq.
    + destruct H as [-> ->]. exists mo2. split; [|exact Heq]. split; [reflexivity|]. split; [exact Hfd|]. rewrite ?Hlk. auto.
  - (* [comment removed for export] *) destruct H as (-> & -> & ->). exists mo2. split; [|exact Heq]. repeat split; reflexivity.
  - (* [comment removed for export] *) destruct H as (-> & t & -> & Ht). rewrite <- Et in Ht.
    destruct (m_tid mo2) eqn:Etid.
    + destruct Ht as [-> ->]. exists mo2. split; [|exact Heq]. split; [reflexivity|]. eexists. rewrite ?Etid. eauto.
    + destruct Ht as [Hr ->]. exists (with_tid t mo2). split; [|apply mequiv_with_tid; exact Heq].
      split; [reflexivity|]. exists t. rewrite ?Etid. auto.
Qed.

Lemma nexit_xfer : forall c mo1 mo2 code mo1',
  mequiv mo1 mo2 -> nexit (NExit c) mo1 code mo1' ->
  nexit (NExit c) mo2 code (with_halted code mo2) /\ mequiv mo1' (with_halted code mo2) /\ m_fs mo1' = m_fs (with_halted code mo2).
Proof.
  intros c mo1 mo2 code mo1' Heq [-> ->]. split; [split; reflexivity|]. split; [apply mequiv_with_halted; exact Heq|].
  rewrite !m_fs_with_halted. symmetry. apply (mequiv_frame _ _ Heq).
Qed.

Lemma KIA_mequiv_minvA : forall mo1 mo2, mequiv mo1 mo2 -> minvA mo1 -> minvA mo2.
Proof.
  intros mo1 mo2 Heq H. pose proof (mequiv_frame _ _ Heq) as F. eapply minvA_by_fields; [| | | |exact H]; try tauto.
  destruct F as (_ & _ & -> & _). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_node (n : node) : Prop := neutral_node n \/ exists c, n = NExit c.

Section TrzA.
Variable segs : list Segment.

Local Notation ans_idxN := (ans_idx node nstep nexit).

Definition ansA (n : node) (mo : Model) (TT : resp -> Model -> list event -> TSet) (i : ans_idxN n mo) : TSet :=
  match i with
  | inl (exist _ p _) => t_emit (snd p) (TT (fst (fst p)) (snd (fst p)) (snd p))
  | inr (exist _ q _) => t_emit [ExitEv (fst q) (m_fs (snd q))] t_nil
  end.

Inductive trzA {R : Type} : itree node R -> Model -> (R -> Model -> TSet) -> TSet -> Prop :=
| trzA_ret : forall r mo K,
    trzA (Ret r) mo K (K r mo)
| trzA_vis : forall n (k : resp -> itree node R) mo K (TT : resp -> Model -> list event -> TSet) (i0 : ans_idxN n mo),
    minvA mo -> tree_node n ->
    (forall rsp mo' evs, nstep n mo rsp mo' evs -> trzA (k rsp) mo' K (TT rsp mo' evs)) ->
    trzA (Vis n k) mo K (t_alt (ansA n mo TT))
| trzA_conseq : forall t mo K T T',
    trzA t mo K T -> t_eq T T' -> trzA t mo K T'.

(* [comment removed for export] *)
Lemma trzA_vis_silent : forall {R} n (k : resp -> itree node R) mo K T,
  minvA mo -> tree_node n ->
  (exists rsp mo' evs, nstep n mo rsp mo' evs) ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ trzA (k rsp) mo' K T) ->
  (forall code mo', ~ nexit n mo code mo') ->
  T [] ->
  trzA (Vis n k) mo K T.
Proof.
  intros R n k mo K T Hmi Htn (rsp0 & mo0 & evs0 & H0) Hk Hnx HT0.
  eapply trzA_conseq.
  - apply (trzA_vis n k mo K (fun _ _ _ => T) (inl (exist _ (rsp0, mo0, evs0) H0)) Hmi Htn).
    intros rsp mo' evs H. destruct (Hk rsp mo' evs H) as [_ Ht]. exact Ht.
  - intros tr. split.
    + intros [i Hi]. destruct i as [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn in Hi.
      * destruct (Hk rsp mo' evs Hst) as [-> _].
        destruct Hi as [Hp | (tr' & -> & Ht)]; [| exact Ht].
        apply is_prefix_nil_r in Hp. subst tr. exact HT0.
      * exfalso. exact (Hnx code mo' Hxt).
    + intros Ht. exists (inl (exist _ (rsp0, mo0, evs0) H0)). cbn.
      destruct (Hk rsp0 mo0 evs0 H0) as [-> _]. right. exists tr. split; [reflexivity | exact Ht].
Qed.

Lemma trzA_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (K1 : A -> Model -> TSet) K T,
  trzA t mo K1 T ->
  (forall a mo', trzA (f a) mo' K (K1 a mo')) ->
  trzA (bind node t f) mo K T.
Proof.
  intros A B t f mo K1 K T Ht. induction Ht as [r mo K1 | n k mo K1 TT i0 Hmi Htn Hk IH | t mo K1 T T' Ht IH Heq];
    intros Hf.
  - cbn. apply Hf.
  - cbn. apply (trzA_vis n (fun x => bind node (k x) f) mo K TT i0 Hmi Htn).
    intros rsp mo' evs H. apply (IH rsp mo' evs H). exact Hf.
  - eapply trzA_conseq; [apply IH; exact Hf | exact Heq].
Qed.

Lemma trzA_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo
                         (K1 : exc A -> Model -> TSet) K T,
  trzA t mo K1 T ->
  (forall a mo', trzA (f a) mo' K (K1 (Ok a) mo')) ->
  (forall mo', K1 Unr mo' = K Unr mo') ->
  trzA (ebind t f) mo K T.
Proof.
  intros A B t f mo K1 K T Ht Hf Hunr. unfold ebind. eapply trzA_bind; [exact Ht|].
  intros [|a] mo'; cbn.
  - rewrite Hunr. apply trzA_ret.
  - apply Hf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Variables (S : word -> Prop) (N : nat) (EB : Z).
Variable P : acc -> Prop.

(* [comment removed for export] *)
Definition KIP (mo : Model) : Prop := KIA S N EB mo /\ forall x, P x -> acc_ok (m_vm_lazy mo) S x.

Lemma KIP_KIA : forall mo, KIP mo -> KIA S N EB mo. Proof. intros mo [H _]; exact H. Qed.


Lemma rzA_seg : forall (Q : machine_state -> Prop) ms mo T,
  evtA segs P Q ms -> KIP mo ->
  (forall ms' mo', Q ms' -> magree mo mo' -> KIP mo' -> realizes segs (mkCfg ms' mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros Q ms mo T Hev [(HLI & Hmi & Hh) HPS] HK.
  eapply (rzA_evt segs S N EB (m_vm_lazy mo)); [ | exact Hh | exact HLI | reflexivity |].
  - eapply evtA_weaken; [|exact Hev]. exact HPS.
  - intros ms' mo' HQ Hag HLI' Hh'. apply HK; [exact HQ| exact Hag|]. split.
    + split; [exact HLI'|]. split; [eapply minvA_magree; eauto| exact Hh'].
    + rewrite (magree_lazy _ _ Hag). exact HPS.
Qed.

(* [comment removed for export] *)
Lemma rzA_seg_cfg : forall (Q : machine_state -> Prop) ms mo T,
  evtA segs P Q ms -> KIP mo ->
  (forall ms' mo', Q ms' -> magree mo mo' -> KIP mo' -> realizes_cfg acfg segs (mkCfg ms' mo') T) ->
  realizes_cfg acfg segs (mkCfg ms mo) T.
Proof.
  intros Q ms mo T Hev [(HLI & Hmi & Hh) HPS] HK.
  eapply (rzA_evt_cfg segs acfg S N EB (m_vm_lazy mo)); [ | exact Hh | exact HLI | reflexivity |].
  - eapply evtA_weaken; [|exact Hev]. exact HPS.
  - intros ms' mo' HQ Hag HLI' Hh'. apply HK; [exact HQ| exact Hag|]. split.
    + split; [exact HLI'|]. split; [eapply minvA_magree; eauto| exact Hh'].
    + rewrite (magree_lazy _ _ Hag). exact HPS.
Qed.

(* [comment removed for export] *)
Record nsucc (n : node) (ms : machine_state) (mot moa : Model) : Type := mkNsucc {
  su_rsp : resp; su_mot' : Model; su_evs : list event; su_moa'' : Model;
  su_nstep_t : nstep n mot su_rsp su_mot' su_evs;              (* [comment removed for export] *)
  su_ok : exists moa', nstep n moa su_rsp moa' su_evs /\ mequiv su_mot' moa' /\ magree moa' su_moa''
          /\ KIP su_moa'' /\ sstep segs (mkCfg ms moa) su_evs (SNext (mkCfg (nret ms su_rsp) su_moa'')) }.

Record xsucc (n : node) (ms : machine_state) (mot moa : Model) : Type := mkXsucc {
  sx_code : word; sx_mot' : Model;
  sx_nexit_t : nexit n mot sx_code sx_mot';
  sx_ok : nexit n moa sx_code (with_halted sx_code moa) /\ m_fs sx_mot' = m_fs (with_halted sx_code moa)
          /\ sstep segs (mkCfg ms moa) [ExitEv sx_code (m_fs (with_halted sx_code moa))] (SNext (mkCfg ms (with_halted sx_code moa))) }.

Arguments su_rsp {n ms mot moa} _.  Arguments su_mot' {n ms mot moa} _.  Arguments su_evs {n ms mot moa} _.
Arguments su_moa'' {n ms mot moa} _. Arguments su_nstep_t {n ms mot moa} _. Arguments su_ok {n ms mot moa} _.
Arguments sx_code {n ms mot moa} _. Arguments sx_mot' {n ms mot moa} _. Arguments sx_nexit_t {n ms mot moa} _.
Arguments sx_ok {n ms mot moa} _.

Definition succ_evs n ms mot moa (i : nsucc n ms mot moa + xsucc n ms mot moa) : list event :=
  match i with inl s => su_evs s | inr x => [ExitEv (sx_code x) (m_fs (with_halted (sx_code x) moa))] end.
Definition succ_cfg n ms mot moa (i : nsucc n ms mot moa + xsucc n ms mot moa) : config :=
  match i with inl s => mkCfg (nret ms (su_rsp s)) (su_moa'' s) | inr x => mkCfg ms (with_halted (sx_code x) moa) end.
Definition succ_T n ms mot moa (TT : resp -> Model -> list event -> TSet) (i : nsucc n ms mot moa + xsucc n ms mot moa) : TSet :=
  match i with inl s => TT (su_rsp s) (su_mot' s) (su_evs s) | inr x => t_nil end.

(* [comment removed for export] *)
Lemma node_okA : forall n ms mot moa,
  tree_node n -> at_nodeA segs P n ms -> mequiv mot moa -> KIP moa ->
  node_ok segs (mkCfg ms moa) (nsucc n ms mot moa + xsucc n ms mot moa)
          (succ_evs n ms mot moa) (succ_cfg n ms mot moa)
  /\ inhabited (nsucc n ms mot moa + xsucc n ms mot moa)
  /\ (forall i : ans_idxN n mot, exists j : nsucc n ms mot moa + xsucc n ms mot moa,
        match i, j with
        | inl (exist _ p _), inl s => su_rsp s = fst (fst p) /\ su_mot' s = snd (fst p) /\ su_evs s = snd p
        | inr (exist _ q _), inr x => sx_code x = fst q /\ m_fs (sx_mot' x) = m_fs (snd q)
        | _, _ => False
        end).
Proof.
  intros n ms mot moa Htn [Hat Hpol] Heq [HK HPS]. pose proof HK as (HLI & Hmi & Hh).
  destruct Htn as [Hneu | [c ->]].
  - (* [comment removed for export] *)
    pose proof (neutral_factsA segs n ms moa Hneu Hat Hmi Hh) as NF.
    destruct (neutral_kit segs S N EB P n ms moa NF Hpol HPS HK) as (Hcomp & Hsound & Hprog).
    (* [comment removed for export] *)
    assert (PSX : forall rsp moa' evs moa'', nstep n moa rsp moa' evs -> magree moa' moa'' ->
              forall x, P x -> acc_ok (m_vm_lazy moa'') S x).
    { intros rsp moa' evs moa'' Hn Hag. rewrite (magree_lazy _ _ Hag).
      destruct NF as (x8 & Hsvc & Hcmp & Hsnd & _).
      destruct (Hsnd _ _ _ Hn) as [ci Hc]. destruct (Hcmp _ _ _ Hc) as (_ & Hvm & _).
      rewrite (lazy_vm_same _ _ Hvm). exact HPS. }
    split; [|split].
    + split.
      * intros [s|x]; cbn.
        -- destruct (su_ok s) as (moa' & _ & _ & _ & _ & Hss). exact Hss.
        -- destruct (sx_ok x) as (Hx & _). exfalso. destruct n; try contradiction; exact Hx.
      * intros e st Hss. destruct (Hcomp e st Hss) as (rsp & moa' & moa'' & -> & Hn & Hag & HK'').
        destruct (nstep_xfer n moa mot rsp moa' e Hneu (mequiv_sym _ _ Heq) Hn) as (mot' & Hnt & Heqt).
        unshelve eexists (inl (mkNsucc n ms mot moa rsp mot' e moa'' Hnt _)).
        { exists moa'. split; [exact Hn|]. split; [apply mequiv_sym; exact Heqt|]. split; [exact Hag|]. split; [|exact Hss].
          split; [exact HK''|]. eapply PSX; eauto. }
        split; reflexivity.
    + destruct Hprog as (rsp & moa' & evs & Hn).
      destruct (nstep_xfer n moa mot rsp moa' evs Hneu (mequiv_sym _ _ Heq) Hn) as (mot' & Hnt & Heqt).
      destruct (Hsound _ _ _ Hn) as (moa'' & Hag & HK'' & Hss).
      constructor. unshelve refine (inl (mkNsucc n ms mot moa rsp mot' evs moa'' Hnt _)).
      exists moa'. split; [exact Hn|]. split; [apply mequiv_sym; exact Heqt|]. split; [exact Hag|]. split; [|exact Hss].
      split; [exact HK''|]. eapply PSX; eauto.
    + intros [[[[rsp mot'] evs] Hnt] | [[code mot'] Hxt]]; cbn.
      * destruct (nstep_xfer n mot moa rsp mot' evs Hneu Heq Hnt) as (moa' & Hn & Heqa).
        destruct (Hsound _ _ _ Hn) as (moa'' & Hag & HK'' & Hss).
        unshelve eexists (inl (mkNsucc n ms mot moa rsp mot' evs moa'' Hnt _)); [|cbn; auto].
        exists moa'. split; [exact Hn|]. split; [exact Heqa|]. split; [exact Hag|]. split; [|exact Hss].
        split; [exact HK''|]. eapply PSX; eauto.
      * exfalso. destruct n; try contradiction; exact Hxt.
  - (* [comment removed for export] *)
    pose proof Hat as [Hsvc' Ha0].
    assert (Hx8 : exists x8, ms_svc_pending ms = Some x8) by (destruct Hsvc' as [E|E]; eexists; exact E).
    destruct Hx8 as [x8 Hsvc].
    destruct (exit_kitA segs ms moa c x8 Hat Hsvc Hh) as [Hcomp Hstep].
    set (code := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) in *.
    assert (HX1 : nexit (NExit c) mot code (with_halted code mot)) by (split; reflexivity).
    assert (HX2 : nexit (NExit c) moa code (with_halted code moa) /\ m_fs (with_halted code mot) = m_fs (with_halted code moa)
                  /\ sstep segs (mkCfg ms moa) [ExitEv code (m_fs (with_halted code moa))] (SNext (mkCfg ms (with_halted code moa)))).
    { split; [split; reflexivity|]. split; [|exact Hstep].
      rewrite !m_fs_with_halted. symmetry. apply (mequiv_frame _ _ Heq). }
    pose (X := mkXsucc (NExit c) ms mot moa code (with_halted code mot) HX1 HX2).
    split; [|split].
    + split.
      * intros [s|x]; cbn.
        -- exfalso. exact (su_nstep_t s).
        -- destruct (sx_ok x) as ([E _] & Hfs & Hss). exact Hss.
      * intros e st Hss. destruct (Hcomp e st Hss) as [-> ->].
        exists (inr X). cbn. rewrite m_fs_with_halted. split; reflexivity.
    + exact (inhabits (inr X)).
    + intros [[[[rsp mot'] evs] Hnt] | [[code' mot'] [E1 E2]]]; cbn.
      * exfalso. exact Hnt.
      * exists (inr X). cbn. cbn in E1, E2. subst. split; [reflexivity|].
        rewrite !m_fs_with_halted. reflexivity.
Qed.



(* [comment removed for export] *)
Lemma tree_node_off : forall n, tree_node n -> node_off acfg n = false.
Proof. intros n [Hn | [c ->]]; [destruct n; try reflexivity; destruct Hn| reflexivity]. Qed.

Lemma tree_node_sstep_cfg : forall n ms mo evs X,
  tree_node n -> at_node segs n ms ->
  sstep segs (mkCfg ms mo) evs X -> sstep_cfg segs acfg (mkCfg ms mo) evs X.
Proof.
  intros n ms mo evs X Htn Hat Hss. apply sstep_cfg_of_sstep; [exact Hss|].
  intros x8 eff m' evs' Hsvc _ _ (Hoff & _).
  rewrite (node_off_link segs acfg n ms x8 Hat Hsvc), (tree_node_off n Htn) in Hoff. discriminate Hoff.
Qed.

Lemma node_okA_cfg : forall n ms mot moa,
  tree_node n -> at_nodeA segs P n ms ->
  node_ok segs (mkCfg ms moa) (nsucc n ms mot moa + xsucc n ms mot moa) (succ_evs n ms mot moa) (succ_cfg n ms mot moa) ->
  node_ok_cfg acfg segs (mkCfg ms moa) (nsucc n ms mot moa + xsucc n ms mot moa) (succ_evs n ms mot moa) (succ_cfg n ms mot moa).
Proof.
  intros n ms mot moa Htn [Hat _] Hnode. apply node_ok_cfg_lift; [exact Hnode|].
  intros i. apply (tree_node_sstep_cfg n); [exact Htn| exact Hat| exact (proj1 Hnode i)].
Qed.

Theorem implA_trzA_realizes : forall {R} (t : itree node R) Q ms mot moa (K : R -> Model -> TSet) T,
  implA segs (at_nodeA segs) P t Q ms ->
  trzA t mot K T ->
  mequiv mot moa -> KIP moa ->
  (forall r ms' mot' moa', Q r ms' -> leaf t mot r mot' -> mequiv mot' moa' -> KIP moa' ->
     realizes segs (mkCfg ms' moa') (K r mot')) ->
  realizes segs (mkCfg ms moa) T.
Proof.
  intros R t Q ms mot moa K T Himpl Htrz. revert ms moa Himpl.
  induction Htrz as [r mo K | n k mo K TT i0 Hminv Htn Hk IH | t mo K T T' Ht IH Heq];
    intros ms moa Himpl Heqm HKP HK.
  - cbn in Himpl. eapply rzA_seg; [exact Himpl| exact HKP|].
    intros ms' moa' HQ Hag HKP'. apply HK; [exact HQ| constructor| | exact HKP'].
    eapply mequiv_trans; [exact Heqm| apply magree_mequiv; exact Hag].
  - cbn in Himpl. eapply rzA_seg; [exact Himpl| exact HKP|].
    intros ms1 moa1 [Hat Hcont] Hag HKP1.
    assert (Heq1 : mequiv mo moa1) by (eapply mequiv_trans; [exact Heqm| apply magree_mequiv; exact Hag]).
    destruct (node_okA n ms1 mo moa1 Htn Hat Heq1 HKP1) as (Hnode & [j0] & Hcov).
    eapply rz_conseq.
    + apply (rz_node segs (mkCfg ms1 moa1) _ (succ_evs n ms1 mo moa1) (succ_cfg n ms1 mo moa1)
               (succ_T n ms1 mo moa1 TT) j0 Hnode).
      intros [s|x]; cbn.
      * destruct (su_ok s) as (moa' & Hn & Heq' & Hag' & HKP'' & _).
        apply (IH (su_rsp s) (su_mot' s) (su_evs s) (su_nstep_t s) (nret ms1 (su_rsp s)) (su_moa'' s) (Hcont _)).
        -- eapply mequiv_trans; [exact Heq'| apply magree_mequiv; exact Hag'].
        -- exact HKP''.
        -- intros r ms' mot' moa2 HQ Hl Heq'' HKP'''. apply HK; auto. econstructor; [exact (su_nstep_t s)| exact Hl].
      * apply rz_halt. cbn. rewrite m_halted_with_halted. discriminate.
    + intros tr. split.
      * intros [[s|x] Hi]; cbn in Hi.
        -- exists (inl (exist _ (su_rsp s, su_mot' s, su_evs s) (su_nstep_t s))). cbn. exact Hi.
        -- destruct (sx_ok x) as (_ & Hfs & _).
           exists (inr (exist _ (sx_code x, sx_mot' x) (sx_nexit_t x))). cbn. rewrite Hfs. exact Hi.
      * intros [i Hi]. destruct (Hcov i) as [j Hj]. exists j.
        destruct i as [[[[rsp mot'] evs] Hnt] | [[code mot'] Hxt]]; destruct j as [s|x]; try contradiction; cbn in *.
        -- destruct Hj as (-> & -> & ->). exact Hi.
        -- destruct (sx_ok x) as (_ & Hfs2 & _). destruct Hj as [<- Hfs]. rewrite <- Hfs2, Hfs. exact Hi.
  - eapply rz_conseq; [apply IH; assumption | exact Heq].
Qed.

Theorem implA_trzA_realizes_cfg : forall {R} (t : itree node R) Q ms mot moa (K : R -> Model -> TSet) T,
  implA segs (at_nodeA segs) P t Q ms ->
  trzA t mot K T ->
  mequiv mot moa -> KIP moa ->
  (forall r ms' mot' moa', Q r ms' -> leaf t mot r mot' -> mequiv mot' moa' -> KIP moa' ->
     realizes_cfg acfg segs (mkCfg ms' moa') (K r mot')) ->
  realizes_cfg acfg segs (mkCfg ms moa) T.
Proof.
  intros R t Q ms mot moa K T Himpl Htrz. revert ms moa Himpl.
  induction Htrz as [r mo K | n k mo K TT i0 Hminv Htn Hk IH | t mo K T T' Ht IH Heq];
    intros ms moa Himpl Heqm HKP HK.
  - cbn in Himpl. eapply rzA_seg_cfg; [exact Himpl| exact HKP|].
    intros ms' moa' HQ Hag HKP'. apply HK; [exact HQ| constructor| | exact HKP'].
    eapply mequiv_trans; [exact Heqm| apply magree_mequiv; exact Hag].
  - cbn in Himpl. eapply rzA_seg_cfg; [exact Himpl| exact HKP|].
    intros ms1 moa1 [Hat Hcont] Hag HKP1.
    assert (Heq1 : mequiv mo moa1) by (eapply mequiv_trans; [exact Heqm| apply magree_mequiv; exact Hag]).
    destruct (node_okA n ms1 mo moa1 Htn Hat Heq1 HKP1) as (Hnode & [j0] & Hcov).
    eapply rz_conseq_cfg.
    + apply (rz_node_cfg acfg segs (mkCfg ms1 moa1) _ (succ_evs n ms1 mo moa1) (succ_cfg n ms1 mo moa1)
               (succ_T n ms1 mo moa1 TT) j0 (node_okA_cfg n ms1 mo moa1 Htn Hat Hnode)).
      intros [s|x]; cbn.
      * destruct (su_ok s) as (moa' & Hn & Heq' & Hag' & HKP'' & _).
        apply (IH (su_rsp s) (su_mot' s) (su_evs s) (su_nstep_t s) (nret ms1 (su_rsp s)) (su_moa'' s) (Hcont _)).
        -- eapply mequiv_trans; [exact Heq'| apply magree_mequiv; exact Hag'].
        -- exact HKP''.
        -- intros r ms' mot' moa2 HQ Hl Heq'' HKP'''. apply HK; auto. econstructor; [exact (su_nstep_t s)| exact Hl].
      * apply rz_halt_cfg. cbn. rewrite m_halted_with_halted. discriminate.
    + intros tr. split.
      * intros [[s|x] Hi]; cbn in Hi.
        -- exists (inl (exist _ (su_rsp s, su_mot' s, su_evs s) (su_nstep_t s))). cbn. exact Hi.
        -- destruct (sx_ok x) as (_ & Hfs & _).
           exists (inr (exist _ (sx_code x, sx_mot' x) (sx_nexit_t x))). cbn. rewrite Hfs. exact Hi.
      * intros [i Hi]. destruct (Hcov i) as [j Hj]. exists j.
        destruct i as [[[[rsp mot'] evs] Hnt] | [[code mot'] Hxt]]; destruct j as [s|x]; try contradiction; cbn in *.
        -- destruct Hj as (-> & -> & ->). exact Hi.
        -- destruct (sx_ok x) as (_ & Hfs2 & _). destruct Hj as [<- Hfs]. rewrite <- Hfs2, Hfs. exact Hi.
  - eapply rz_conseq_cfg; [apply IH; assumption | exact Heq].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma leaf_enode : forall {A} n (dec : resp -> option A) mo r mo',
  leaf (enode n dec) mo r mo' ->
  exists rsp evs, nstep n mo rsp mo' evs /\ r = match dec rsp with Some a => Ok a | None => Unr end.
Proof.
  intros A n dec mo r mo' H. unfold enode in H. inversion H; subst.
  match goal with Hn : nstep _ _ ?rsp _ ?evs, Hl : leaf _ _ _ _ |- _ =>
    exists rsp, evs; destruct (dec rsp); apply leaf_ret_inv in Hl as [-> ->]; auto end.
Qed.

(* [comment removed for export] *)

Lemma rzA_enode : forall {A} n (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo
    (Rm : A -> Model -> Prop) (K : TSet),
  implA segs (at_nodeA segs) P (enode n dec) (epost Q) ms ->
  tree_node n -> KIP mo -> K [] ->
  (exists rsp mo1 evs, nstep n mo rsp mo1 evs) ->
  (forall rsp mo1 evs, nstep n mo rsp mo1 evs -> evs = [] /\ exists a, dec rsp = Some a /\ Rm a mo1) ->
  (forall code mo1, ~ nexit n mo code mo1) ->
  (forall a mo1 moa ms', Rm a mo1 -> Q a ms' -> mequiv mo1 moa -> KIP moa -> realizes segs (mkCfg ms' moa) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros A n dec Q ms mo Rm K IM Htn HKP HK Hex Hall Hnx CONT.
  apply (implA_trzA_realizes (enode n dec) (epost Q) ms mo mo (fun _ _ => K) K IM).
  - unfold enode. apply trzA_vis_silent; try assumption.
    + exact (proj1 (proj2 (KIP_KIA _ HKP))).
    + intros rsp mo1 evs H. destruct (Hall _ _ _ H) as (-> & a & D & _). split; [reflexivity|].
      destruct (dec rsp); apply trzA_ret.
  - apply mequiv_refl.
  - exact HKP.
  - intros r ms' mo1 moa HQ L Heq HKP'. apply leaf_enode in L as (rsp & evs & Hst & ->).
    destruct (Hall _ _ _ Hst) as (_ & a & D & HR). rewrite D in HQ. cbn in HQ.
    exact (CONT a mo1 moa ms' HR HQ Heq HKP').
Qed.

Lemma rzA_enode_cfg : forall {A} n (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo
    (Rm : A -> Model -> Prop) (K : TSet),
  implA segs (at_nodeA segs) P (enode n dec) (epost Q) ms ->
  tree_node n -> KIP mo -> K [] ->
  (exists rsp mo1 evs, nstep n mo rsp mo1 evs) ->
  (forall rsp mo1 evs, nstep n mo rsp mo1 evs -> evs = [] /\ exists a, dec rsp = Some a /\ Rm a mo1) ->
  (forall code mo1, ~ nexit n mo code mo1) ->
  (forall a mo1 moa ms', Rm a mo1 -> Q a ms' -> mequiv mo1 moa -> KIP moa -> realizes_cfg acfg segs (mkCfg ms' moa) K) ->
  realizes_cfg acfg segs (mkCfg ms mo) K.
Proof.
  intros A n dec Q ms mo Rm K IM Htn HKP HK Hex Hall Hnx CONT.
  apply (implA_trzA_realizes_cfg (enode n dec) (epost Q) ms mo mo (fun _ _ => K) K IM).
  - unfold enode. apply trzA_vis_silent; try assumption.
    + exact (proj1 (proj2 (KIP_KIA _ HKP))).
    + intros rsp mo1 evs H. destruct (Hall _ _ _ H) as (-> & a & D & _). split; [reflexivity|].
      destruct (dec rsp); apply trzA_ret.
  - apply mequiv_refl.
  - exact HKP.
  - intros r ms' mo1 moa HQ L Heq HKP'. apply leaf_enode in L as (rsp & evs & Hst & ->).
    destruct (Hall _ _ _ Hst) as (_ & a & D & HR). rewrite D in HQ. cbn in HQ.
    exact (CONT a mo1 moa ms' HR HQ Heq HKP').
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nsafeA (n : node) (mo : Model) : Prop := tree_node n.

End TrzA.
End RC__2.
