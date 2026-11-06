(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad MSafe Sim MPaths Adapter Driver Stdio StepB EquivShared.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section More.
Context {StG StC : Type} (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Local Notation fsim := (fsim debtG debtC stepG).
Local Notation fsimeq := (fsimeq debtG debtC stepG).

(* [comment removed for export] *)
Lemma fsim_bind_get {A B} (R : rel StG StC) (kG : StG -> M StG A) (kC : StC -> M StC B) Q :
  (forall sG moG sC moC, R sG moG sC moC ->
     fsim (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) (kG sG) (kC sC) Q) ->
  fsim R (mbind mget kG) (mbind mget kC) Q.
Proof.
  intros H sG moG sC moC HR. specialize (H _ _ _ _ HR). unfold mbind, mget. cbn [ebind fst snd].
  apply H. repeat split; reflexivity.
Qed.

End More.

Section More1.
Context {St : Type} (dG dC : St -> list event) (stepG : node -> Model -> resp -> Model -> list event -> Prop).
(* [comment removed for export] *)
Lemma fsimeq_drop {A} (R : rel St St) (phi : Prop) (m : M St A) Q :
  fsimeq dG dC stepG R m m Q -> fsimeq dG dC stepG (fun sG moG sC moC => R sG moG sC moC /\ phi) m m Q.
Proof. intros H. eapply fsimeq_pre; [exact H|]. intros ? ? ? ? [HR _]. exact HR. Qed.
End More1.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DriverSim.
Context {St ptr : Type}.
Variables (debtG debtC : St -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Variables (ioG ioC : IOStyle St).
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variables (rsG rsC : Z).   (* [comment removed for export] *)
Variable alloc_init : Z -> M St unit.
Variables (runG runC : Z -> list Z -> M St Z).
Variable alloc_count : M St Z.
(* [comment removed for export] *)
Variables (R0 R1 : list ptr -> rel St St).
Local Notation fsimeq := (fsimeq debtG debtC stepG).
Local Notation fsim := (fsim debtG debtC stepG).

Hypothesis H01 : forall X sG moG sC moC, R0 X sG moG sC moC -> R1 X sG moG sC moC.
Hypothesis Hdm0 : forall X n, 0 <= n ->
  fsimeq (R0 X) (drv_malloc n) (drv_malloc n)
         (fun r => match r with Some p => fun sG moG sC moC => R0 (p :: X) sG moG sC moC /\ n < 2^63 | None => R0 X end).
Hypothesis Hdf0 : forall X p, fsimeq (R0 (p :: X)) (drv_free p) (drv_free p) (fun _ => R0 X).
Hypothesis Hdf1 : forall X p, fsimeq (R1 (p :: X)) (drv_free p) (drv_free p) (fun _ => R1 X).
Hypothesis Hperm0 : forall X Y sG moG sC moC, Permutation X Y -> R0 X sG moG sC moC -> R0 Y sG moG sC moC.
Hypothesis Hdiag0 : forall X d, diag_short d -> fsimeq (R0 X) (io_diag ioG d) (io_diag ioC d) (fun _ => R0 X).
Hypothesis Hinit : forall X bm, fsimeq (R0 X) (alloc_init bm) (alloc_init bm) (fun _ => R0 X).
Hypothesis Hcount : forall X, fsimeq (R1 X) alloc_count alloc_count (fun _ => R1 X).
Hypothesis Hrun : forall X cfg payload, fsimeq (R1 X) (runG cfg payload) (runC cfg payload) (fun _ => R1 X).
Hypothesis Hopen : forall X path, fsimeq (R0 X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => R0 X).
Hypothesis Hclose : forall X fd, fsimeq (R0 X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => R0 X).
Hypothesis Hread : forall X fd bufG bufC cnt, 0 <= cnt < 2^64 ->
  fsimeq (R0 X) (msys (NRead fd bufG cnt) (dec_read bufG cnt)) (msys (NRead fd bufC cnt) (dec_read bufC cnt))
         (fun a => match a with RdData bs => fun sG moG sC moC => R0 X sG moG sC moC /\ zlength bs <= cnt | RdErr _ => R0 X end).

(* [comment removed for export] *)
Definition rd_rel (X : list ptr) (st : @rd_st ptr) : rel St St := fun sG moG sC moC =>
  R0 (rd_buf st :: X) sG moG sC moC /\ zlength (rd_content st) <= rd_cap st /\ 0 < rd_cap st <= 2 * MAX_INPUT.

Lemma zlength_app' {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_u8s' : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.

Local Ltac ret_same := apply fsimeq_ret; intros ? ? ? ? HH; exact HH.

Lemma read_loop_body_sim : forall X fd path st, zlength path <= PIECE_MAX ->
  fsimeq (rd_rel X st) (read_loop_body ioG drv_malloc drv_free rsG fd path st) (read_loop_body ioC drv_malloc drv_free rsC fd path st)
         (fun r => match r with
                   | inl st' => rd_rel X st'
                   | inr RdExit => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                   | inr (RdDone buf content) => R0 (buf :: X)
                   end).
Proof.
  intros X fd path st Hpath. unfold read_loop_body.
  eapply fsimeq_bind with
    (Q1 := fun g => match g with
                    | None => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                    | Some st1 => fun sG moG sC moC => rd_rel X st1 sG moG sC moC /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                    end).
  { apply fsimeq_pointwise. intros sG0 moG0 sC0 moC0 (Ho0 & Hlen & Hcap).
    destruct (Z.eqb_spec (zlength (rd_content st)) (rd_cap st)) as [Heq|Hne].
    - destruct (Z.leb_spec MAX_INPUT (rd_cap st)) as [Hbig|Hsmall].
      + eapply fsimeq_seq; [eapply fsimeq_pre; [apply Hdiag0; exact I| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]|].
        intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists (rd_buf st :: X). exact Ho.
      + eapply fsimeq_bind. { eapply fsimeq_pre; [apply Hdm0; lia| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]. }
        intros [nb|]; cbn beta iota.
        * eapply fsimeq_seq.
          { eapply fsimeq_pre; [apply (Hdf0 (nb :: X) (rd_buf st))|]. intros sG moG sC moC [Ho _]. eapply Hperm0; [apply perm_swap| exact Ho]. }
          intros _. apply fsimeq_ret. intros sG moG sC moC Ho. cbn. unfold rd_rel. cbn. unfold MAX_INPUT in *. splits; auto; lia.
        * eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists (rd_buf st :: X). exact Ho.
    - apply fsimeq_ret. intros sG moG sC moC (-> & -> & -> & ->). unfold rd_rel. splits; auto; lia. }
  intros [st1|]; cbn beta iota.
  2:{ ret_same. }
  (* [comment removed for export] *)
  apply fsimeq_pointwise. intros sG1 moG1 sC1 moC1 ((Ho & Hlen & Hcap) & Hct & Hlt).
  set (want0 := rd_cap st1 - zlength (rd_content st)).
  set (want := if 65536 <? want0 then 65536 else want0).
  assert (Hwant : 0 <= want <= want0 /\ want < 2^64). { subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); unfold MAX_INPUT in *; lia. }
  eapply fsimeq_bind.
  { eapply fsimeq_pre; [apply (Hread (rd_buf st1 :: X) fd _ _ want); lia|].
    intros ? ? ? ? (-> & -> & -> & ->). exact Ho. }
  intros [e|bs]; cbn beta iota.
  - eapply fsimeq_seq; [apply Hdiag0; exact Hpath|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho'. exists (rd_buf st1 :: X). exact Ho'.
  - destruct (length bs =? 0)%nat eqn:C.
    + apply fsimeq_ret. intros sG moG sC moC [Ho' _]. exact Ho'.
    + apply fsimeq_ret. intros sG moG sC moC [Ho' Hbs]. unfold rd_rel. cbn. rewrite zlength_app', zlength_u8s', Hct. splits; auto; lia.
Qed.

Lemma read_all_sim : forall X path, zlength path <= PIECE_MAX ->
  fsimeq (R0 X) (read_all ioG drv_malloc drv_free rsG path) (read_all ioC drv_malloc drv_free rsC path)
         (fun r => match r with
                   | RdExit => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                   | RdDone buf content => R0 (buf :: X)
                   end).
Proof.
  intros X path Hpath. unfold read_all.
  eapply fsimeq_bind; [apply Hopen|]. intros [e|fd]; cbn beta iota.
  - eapply fsimeq_seq; [apply Hdiag0; exact Hpath|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. exact Ho.
  - eapply fsimeq_bind; [apply Hdm0; lia|]. intros [buf|]; cbn beta iota.
    2:{ eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. exact Ho. }
    eapply fsimeq_bind.
    + eapply fsimeq_pre.
      * apply (fsimeq_loop debtG debtC stepG (rd_rel X)
                 (fun r => match r with RdExit => fun sG moG sC moC => exists X', R0 X' sG moG sC moC
                                        | RdDone buf content => R0 (buf :: X) end)).
        intros st0. eapply fsimeq_post; [apply read_loop_body_sim; exact Hpath|]. intros [st'|[|b c]] sG moG sC moC H; exact H.
      * intros sG moG sC moC [Ho _]. unfold rd_rel. cbn. split; [exact Ho|]. unfold zlength, MAX_INPUT; cbn. lia.
    + intros [|buf' content]; cbn beta iota; [ret_same|].
      eapply fsimeq_seq; [apply Hclose|]. intros _. ret_same.
Qed.

Lemma main_model_sim : forall X argv, Forall (fun a => zlength a <= PIECE_MAX) argv ->
  fsimeq (R0 X) (main_model ioG drv_malloc drv_free rsG alloc_init runG alloc_count argv)
               (main_model ioC drv_malloc drv_free rsC alloc_init runC alloc_count argv)
         (fun _ sG moG sC moC => exists X', R1 X' sG moG sC moC).
Proof.
  intros X argv Hargv. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) <= PIECE_MAX).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) Hargv _ Hin)| unfold zlength, PIECE_MAX; cbn; lia]. }
  apply fsimeq_if; intros C.
  { eapply fsimeq_seq; [apply Hdiag0; cbn; apply Hnth|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. apply H01. exact Ho. }
  eapply fsimeq_bind; [apply read_all_sim; apply Hnth|]. intros [|buf content]; cbn beta iota.
  { apply fsimeq_ret. intros sG moG sC moC [X' Ho]. exists X'. apply H01. exact Ho. }
  apply fsimeq_if; intros C1.
  { eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. eapply fsimeq_seq; [apply Hdf0|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. apply H01. exact Ho. }
  apply fsimeq_if; intros C2.
  { eapply fsimeq_seq; [apply Hdiag0; exact I|]. intros _. eapply fsimeq_seq; [apply Hdf0|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. apply H01. exact Ho. }
  eapply fsimeq_seq; [apply Hinit|]. intros _.
  eapply fsimeq_seq; [eapply fsimeq_pre; [apply (Hrun (buf :: X))| intros; apply H01; assumption]|]. intros status.
  eapply fsimeq_bind with (Q1 := fun _ => R1 (buf :: X)).
  { destruct (Z.testbit _ 15).
    - eapply fsimeq_seq; [apply Hcount|]. intros n. apply fsimeq_ret. auto.
    - apply fsimeq_ret. auto. }
  intros status'. eapply fsimeq_seq; [apply Hdf1|]. intros _. apply fsimeq_ret. intros sG moG sC moC Ho. exists X. exact Ho.
Qed.
End DriverSim.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_self : forall mo, with_fds (m_fds mo) mo = mo.
Proof. intros [[t p] ? ? ? ? ? ?]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_open_xfer : forall path moG rsp moG' evs moC,
  nstep (NOpen path) moG rsp moG' evs -> m_fds moG = m_fds moC -> m_fs moG = m_fs moC ->
  nstep (NOpen path) moC rsp (with_fds (m_fds moG') moC) evs /\ moG' = with_fds (m_fds moG') moG.
Proof.
  intros path moG rsp moG' evs moC H Ef Es. cbn [nstep] in H |- *. destruct H as [-> H].
  rewrite <- Es.
  destruct (path_max <=? length path)%nat; [destruct H as [-> ->]; rewrite (with_fds_self moG), Ef, with_fds_self; repeat split; reflexivity|].
  destruct path as [|c p]; [destruct H as [-> ->]; rewrite (with_fds_self moG), Ef, with_fds_self; repeat split; reflexivity|].
  assert (OR : forall ent, open_result moG ent rsp moG' -> open_result moC ent rsp (with_fds (m_fds moG') moC) /\ moG' = with_fds (m_fds moG') moG).
  { intros ent [(e & He & -> & ->)|(Hlk & -> & ->)].
    - rewrite (with_fds_self moG), Ef, with_fds_self. split; [left; exists e; auto| reflexivity].
    - split; [right|reflexivity]. unfold open_result. rewrite !m_fds_with_fds, <- Ef. repeat split; auto. }
  destruct (Open.path_is_dirref (c :: p)); [split; [split; [reflexivity| exact (proj1 (OR _ H))]| exact (proj2 (OR _ H))]|].
  destruct (Fs.fs_lookup (m_fs moG) (c :: p)); [|destruct H as [-> ->]; rewrite (with_fds_self moG), Ef, with_fds_self; repeat split; reflexivity].
  split; [split; [reflexivity| exact (proj1 (OR _ H))]| exact (proj2 (OR _ H))].
Qed.

Lemma nstep_close_xfer : forall fd moG rsp moG' evs moC,
  nstep (NClose fd) moG rsp moG' evs -> m_fds moG = m_fds moC ->
  nstep (NClose fd) moC rsp (with_fds (m_fds moG') moC) evs /\ moG' = with_fds (m_fds moG') moG.
Proof.
  intros fd moG rsp moG' evs moC (-> & Hfd & H) Ef. cbn [nstep]. rewrite <- Ef.
  destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)); destruct H as [-> ->]; rewrite ?m_fds_with_fds; [|rewrite (with_fds_self moG), Ef, with_fds_self]; repeat split; auto; lia.
Qed.

Lemma nstep_read_xfer : forall fd bufG bufC cnt moG rsp moG' evs moC,
  nstep (NRead fd bufG cnt) moG rsp moG' evs -> m_fds moG = m_fds moC -> m_fs moG = m_fs moC ->
  exists rspC, nstep (NRead fd bufC cnt) moC rspC (with_fds (m_fds moG') moC) evs /\ moG' = with_fds (m_fds moG') moG
    /\ dec_read bufC cnt rspC = dec_read bufG cnt rsp.
Proof.
  intros fd bufG bufC cnt moG rsp moG' evs moC [-> H] Ef Es. cbn [nstep]. rewrite <- Ef, <- Es.
  destruct (fd_lookup (m_fds moG) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id wr|rd wr| ]|].
  - destruct H.
  - destruct (Fs.fs_lookup (m_fs moG) p) as [data|]; [|destruct H]. destruct H as [-> ->].
    eexists. split; [split; [reflexivity|]; split; [reflexivity| rewrite m_fds_with_fds; reflexivity]|]. split; [rewrite m_fds_with_fds; reflexivity|].
    unfold dec_read. cbn. unfold Uaccess.delivered_writes. destruct (Fs.file_read data off (Z_to_bv 64 cnt)); cbn; [reflexivity|].
    rewrite !bv_eqb_refl. reflexivity.
  - destruct H.
  - destruct H.
  - destruct H.
  - destruct H as [-> ->]. exists (efferr EISDIR). rewrite (with_fds_self moG), Ef, with_fds_self. repeat split; reflexivity.
  - destruct H.
  - destruct H.
  - destruct H.   (* [comment removed for export] *)
  - destruct H.   (* [comment removed for export] *)
  - destruct H as [-> ->]. exists (efferr EBADF). rewrite (with_fds_self moG), Ef, with_fds_self. repeat split; reflexivity.
Qed.

Section FdNodes.
Context {St : Type} (debtG debtC : St -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Hypothesis stepG_sub : forall n mo r mo' e, ~ nf_node n -> stepG n mo r mo' e -> nstep n mo r mo' e.   (* [comment removed for export] *)
Variable R : rel St St.
Local Notation fsimeq := (fsimeq debtG debtC stepG).
Local Notation fsim := (fsim debtG debtC stepG).
Hypothesis Rmodels : forall sG moG sC moC, R sG moG sC moC ->
  minv moG /\ minv moC /\ m_halted moG = None /\ m_halted moC = None /\ m_fds moG = m_fds moC /\ m_fs moG = m_fs moC.
Hypothesis Rtables : forall sG moG sC moC moG' moC', R sG moG sC moC ->
  m_vmmaps moG' = m_vmmaps moG -> m_vmmaps moC' = m_vmmaps moC ->
  minv moG' -> minv moC' -> m_halted moG' = None -> m_halted moC' = None ->
  m_fds moG' = m_fds moC' -> m_fs moG' = m_fs moC' -> R sG moG' sC moC'.

Lemma R_fds : forall sG moG sC moC moG', R sG moG sC moC ->
  moG' = with_fds (m_fds moG') moG -> minv moG' -> minv (with_fds (m_fds moG') moC) ->
  m_halted moG' = None -> m_halted (with_fds (m_fds moG') moC) = None ->
  R sG moG' sC (with_fds (m_fds moG') moC).
Proof.
  intros sG moG sC moC moG' HR E MG MC HG HC. pose proof (Rmodels _ _ _ _ HR) as (_ & _ & _ & _ & Hfds & Hfs).
  eapply Rtables; [exact HR| rewrite E; apply m_vmmaps_with_fds| apply m_vmmaps_with_fds| exact MG| exact MC| exact HG| exact HC| rewrite m_fds_with_fds; reflexivity| rewrite E, !m_fs_with_fds; exact Hfs].
Qed.

Lemma open_sim : forall path,
  fsimeq R (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => R).
Proof.
  intros path. unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. split; [left; exact (proj1 Hst)|].
    destruct (nstep_open_xfer _ _ _ _ _ moC Hst Hfds Hfs) as [HstC E].
    pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    exists rspG, (with_fds (m_fds moG') moC), a. split; [exact HstC|]. split; [exact Hd|]. split; [reflexivity|]. eapply R_fds; eauto.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.

Lemma close_sim : forall fd,
  fsimeq R (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => R).
Proof.
  intros fd. unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. split; [left; exact (proj1 Hst)|].
    destruct (nstep_close_xfer _ _ _ _ _ moC Hst Hfds) as [HstC E].
    pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    exists rspG, (with_fds (m_fds moG') moC), a. split; [exact HstC|]. split; [exact Hd|]. split; [reflexivity|]. eapply R_fds; eauto.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.

Lemma read_sim : forall fd bufG bufC cnt, 0 <= cnt < 2^64 ->
  fsimeq R (msys (NRead fd bufG cnt) (dec_read bufG cnt)) (msys (NRead fd bufC cnt) (dec_read bufC cnt))
         (fun a => match a with RdData bs => fun sG moG sC moC => R sG moG sC moC /\ zlength bs <= cnt | RdErr _ => R end).
Proof.
  intros fd bufG bufC cnt Hcnt. unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. split; [left; exact (proj1 Hst)|].
    destruct (nstep_read_xfer fd bufG bufC cnt _ _ _ _ moC Hst Hfds Hfs) as (rspC & HstC & E & HdC).
    pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    exists rspC, (with_fds (m_fds moG') moC), a. split; [exact HstC|]. split; [rewrite HdC; exact Hd|]. split; [reflexivity|].
    pose proof (R_fds sG moG sC moC moG' HR E HmG HmC HhG' HhC') as HR'.
    destruct a as [e|bs]; [exact HR'|]. split; [exact HR'|].
    pose proof (nstep_dec_read fd bufG cnt _ _ _ _ Hcnt Hst) as (_ & a' & Hd' & Ha'). rewrite Hd in Hd'. injection Hd' as <-.
    destruct Ha' as (p & off & data & _ & _ & -> & _). unfold zlength.
    pose proof (length_file_read_le_count data off cnt Hcnt). lia.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma settid_sim :
  fsim R (msys NSetTid dec_set_tid) (msys NSetTid dec_set_tid) (fun _ _ => R).
Proof.
  apply fsim_sys. intros sG moG sC moC HR. pose proof (Rmodels _ _ _ _ HR) as (MiG & MiC & HhG & HhC & Hfds & Hfs). split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. pose proof (minv_preserved _ _ _ _ _ MiG HhG Hst) as [HhG' HmG].
    destruct Hst as (-> & t & -> & Ht). split; [left; reflexivity|].
    (* [comment removed for export] *)
    set (tC := match m_tid moC with Some t0 => t0 | None => Z_to_bv 64 1 end).
    set (moC' := match m_tid moC with Some _ => moC | None => with_tid tC moC end).
    assert (HstC : nstep NSetTid moC (eff0 tC) moC' []).
    { cbn [nstep]. split; [reflexivity|]. exists tC. split; [reflexivity|]. subst tC moC'. destruct (m_tid moC); [auto|].
      rewrite unsigned_lit by lia. unfold Fork.PID_MAX_ENVELOPE. split; [lia| reflexivity]. }
    pose proof (minv_preserved _ _ _ _ _ MiC HhC HstC) as [HhC' HmC].
    pose proof (nstep_dec_set_tid moC _ _ _ MiC HstC) as (_ & tz & HdC & _ & _).
    exists (eff0 tC), moC', tz. split; [exact HstC|]. split; [exact HdC|].
    assert (EG : m_vmmaps moG' = m_vmmaps moG /\ m_fds moG' = m_fds moG /\ m_fs moG' = m_fs moG).
    { destruct (m_tid moG); [destruct Ht as [_ ->]| destruct Ht as [_ ->]]; [auto|]. rewrite m_vmmaps_with_tid, m_fds_with_tid, m_fs_with_tid. auto. }
    assert (EC : m_vmmaps moC' = m_vmmaps moC /\ m_fds moC' = m_fds moC /\ m_fs moC' = m_fs moC).
    { subst moC'. destruct (m_tid moC); [auto|]. rewrite m_vmmaps_with_tid, m_fds_with_tid, m_fs_with_tid. auto. }
    destruct EG as (EG1 & EG2 & EG3). destruct EC as (EC1 & EC2 & EC3).
    eapply Rtables; eauto; congruence.
  - intros code moG' Hx. cbn in Hx. destruct Hx.
Qed.
End FdNodes.
