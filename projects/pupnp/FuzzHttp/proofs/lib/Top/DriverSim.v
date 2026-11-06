(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Uaccess.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite Namei Open.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad MSafe Stdio Driver Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim MSim DriverModel.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Notation tsh := (tshape node nstep nexit).

Definition fdupd2 (moA moA' moB moB' : Model) : Prop :=
  (moA' = moA /\ moB' = moB) \/ (exists fds, moA' = with_fds fds moA /\ moB' = with_fds fds moB).

Definition fdnode (n : node) : Prop :=
  match n with NOpen _ | NRead _ _ _ | NClose _ | NWritev _ _ | NIoctl _ _ => True | _ => False end.

Lemma fd_transfer : forall n moA moB rsp moA' evs,
  fdnode n -> m_fds moA = m_fds moB -> m_fs moA = m_fs moB ->
  nstep n moA rsp moA' evs -> exists moB', nstep n moB rsp moB' evs /\ fdupd2 moA moA' moB moB'.
Proof.
  intros n moA moB rsp moA' evs Hn EF ES ST.
  assert (SAME : moA' = moA -> exists moB', moB' = moB /\ fdupd2 moA moA' moB moB').
  { intros ->. exists moB. split; [reflexivity| left; auto]. }
  destruct n; try contradiction; cbn [nstep] in ST |- *.
  -   destruct ST as [-> H]. exists moB. split; [split; [reflexivity| exact H]| left; auto].
  -   destruct ST as [-> H].
    assert (OR : forall ent mo', open_result moA ent rsp mo' ->
              exists moB', open_result moB ent rsp moB' /\ fdupd2 moA mo' moB moB').
    { intros ent mo' [(e & HIn & Hs & ->)|(Hlk & Hs & ->)].
      - exists moB. split; [left; exists e; auto| left; auto].
      - exists (with_fds (fd_insert (m_fds moB) (alloc_fd (m_fds moB)) ent) moB). rewrite EF in Hlk, Hs |- *.
        split; [right; auto| right; eexists; split; reflexivity]. }
    destruct (path_max <=? length path)%nat.
    { destruct H as [Hs ->]. exists moB. split; [split; [reflexivity| auto]| left; auto]. }
    destruct path as [|c p'].
    { destruct H as [Hs ->]. exists moB. split; [split; [reflexivity| auto]| left; auto]. }
    destruct (path_is_dirref (c :: p')).
    { destruct (OR _ _ H) as (moB' & H' & U). exists moB'. split; [split; [reflexivity| exact H']| exact U]. }
    rewrite ES in H. destruct (fs_lookup (m_fs moB) (c :: p')).
    { destruct (OR _ _ H) as (moB' & H' & U). exists moB'. split; [split; [reflexivity| exact H']| exact U]. }
    destruct H as [Hs ->]. exists moB. split; [split; [reflexivity| auto]| left; auto].
  -   destruct ST as [-> H]. rewrite EF, ES in H.
    destruct (fd_lookup (m_fds moB) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid wr|dnr dnw| ]|]; try contradiction.
    + destruct (fs_lookup (m_fs moB) p); [| contradiction]. destruct H as [Hs ->].
      eexists. split; [split; [reflexivity| split; [exact Hs| reflexivity]]| right; eexists; split; reflexivity].
    + destruct H as [Hs ->]. exists moB. split; [split; [reflexivity| auto]| left; auto].
    + destruct H as [Hs ->]. exists moB. split; [split; [reflexivity| auto]| left; auto].
    + destruct H as [Hs ->]. exists moB. split; [split; [reflexivity| auto]| left; auto].
  -   destruct ST as (-> & Hfd & H). rewrite EF in H.
    destruct (fd_lookup (m_fds moB) (Z_to_bv 64 fd)); destruct H as [Hs ->].
    + eexists. split; [split; [reflexivity| split; [exact Hfd| split; [exact Hs| reflexivity]]]| right; eexists; split; reflexivity].
    + exists moB. split; [split; [reflexivity| split; [exact Hfd| auto]]| left; auto].
  -   destruct ST as (-> & Hs & ->). exists moB. split; [repeat split; auto| left; auto].
Qed.

Definition fsnode (n : node) : Prop :=
  match n with NOpenW _ | NIoctlF _ | NWritevF _ _ | NLseek _ _ _ | NReadv _ _ _ _ _ | NUnlink _ => True | _ => False end.

Definition fsupd2 (moA moA' moB moB' : Model) : Prop :=
  exists (F : option (list (word * FdEntry))) (G : option Fs.Fs),
    let ap := fun mo => match G with Some g => with_fs g mo | None => mo end in
    let bp := fun mo => match F with Some f => with_fds f mo | None => mo end in
    moA' = bp (ap moA) /\ moB' = bp (ap moB).

Lemma fsupd2_refl : forall moA moB, fsupd2 moA moA moB moB.
Proof. intros. exists None, None. split; reflexivity. Qed.
Lemma fsupd2_fds : forall moA moB f, fsupd2 moA (with_fds f moA) moB (with_fds f moB).
Proof. intros. exists (Some f), None. split; reflexivity. Qed.
Lemma fsupd2_fs : forall moA moB g, fsupd2 moA (with_fs g moA) moB (with_fs g moB).
Proof. intros. exists None, (Some g). split; reflexivity. Qed.
Lemma fsupd2_both : forall moA moB f g, fsupd2 moA (with_fds f (with_fs g moA)) moB (with_fds f (with_fs g moB)).
Proof. intros. exists (Some f), (Some g). split; reflexivity. Qed.

Lemma fs_transfer : forall n moA moB rsp moA' evs,
  fsnode n -> m_fds moA = m_fds moB -> m_fs moA = m_fs moB ->
  nstep n moA rsp moA' evs -> exists moB', nstep n moB rsp moB' evs /\ fsupd2 moA moA' moB moB'.
Proof.
  intros n moA moB rsp moA' evs Hn EF ES ST.
  destruct n; try contradiction; cbn [nstep] in ST |- *.
  -   destruct ST as [-> H]. unfold create_result in *. rewrite ES, EF in H.
    destruct (path_is_dirref path); [destruct H as [Hs ->]; exists moB; split; [auto| apply fsupd2_refl]|].
    destruct (fs_under (m_fs moB) path); [destruct H as [Hs ->]; exists moB; split; [auto| apply fsupd2_refl]|].
    destruct H as [(e & HIn & Hs & ->)|(Hlk & Hs & ->)].
    + exists moB. split; [split; [reflexivity| left; exists e; auto]| apply fsupd2_refl].
    + eexists. split; [split; [reflexivity| right; split; [exact Hlk| split; [exact Hs| reflexivity]]]| apply fsupd2_both].
  -   destruct ST as (-> & -> & H). rewrite EF in H. exists moB. split; [repeat split; auto| apply fsupd2_refl].
  -   destruct ST as (-> & p & off & data & Hlk & Hfs & Hs & ->). rewrite EF in Hlk. rewrite ES in Hfs. rewrite EF, ES.
    eexists. split; [split; [reflexivity| exists p, off, data; repeat split; auto]| apply fsupd2_both].
  -   destruct ST as (-> & e & p & cur & data & Hlk & He & Hfs & H). rewrite EF in Hlk. rewrite ES in Hfs.
    destruct (lseek_dest _ _) as [r|] eqn:Hd; destruct H as [Hs ->]; rewrite ?EF.
    + eexists. split; [split; [reflexivity| exists e, p, cur, data; rewrite Hd; repeat split; auto]| apply fsupd2_fds].
    + exists moB. split; [split; [reflexivity| exists e, p, cur, data; rewrite Hd; repeat split; auto]| apply fsupd2_refl].
  -   destruct ST as (-> & p & off & data & Hlk & Hfs & Hs & ->). rewrite EF in Hlk. rewrite ES in Hfs. rewrite EF.
    eexists. split; [split; [reflexivity| exists p, off, data; repeat split; auto]| apply fsupd2_fds].
  -   destruct ST as [-> H]. rewrite ES, EF in H.
    destruct (fs_lookup (m_fs moB) path).
    + destruct H as [(e & HIn & Hs & ->)|(Hn' & Hs & ->)].
      * exists moB. split; [split; [reflexivity| left; exists e; auto]| apply fsupd2_refl].
      * eexists. split; [split; [reflexivity| right; repeat split; auto]| apply fsupd2_fs].
    + destruct H as [Hs ->]. exists moB. split; [split; [reflexivity| auto]| apply fsupd2_refl].
Qed.

Lemma fdupd2_sym : forall moA moA' moB moB', fdupd2 moA moA' moB moB' -> fdupd2 moB moB' moA moA'.
Proof. intros moA moA' moB moB' [[-> ->]|(f & -> & ->)]; [left; auto| right; exists f; auto]. Qed.

Lemma fdupd2_fds : forall moA moA' moB moB', m_fds moA = m_fds moB -> fdupd2 moA moA' moB moB' -> m_fds moA' = m_fds moB'.
Proof. intros moA moA' moB moB' E [[-> ->]|(f & -> & ->)]; [exact E| destruct moA, moB; reflexivity]. Qed.

Section DS.

  Variables (rsA rsB : Z).

  Variable MR : nat -> list bptr -> PState -> Model -> PState -> Model -> Prop.
  Variable NMAX : Z.
  Hypothesis HNMAX : 2^26 <= NMAX.
  Hypothesis MR_fds : forall k X sA moA sB moB, MR k X sA moA sB moB ->
    m_fds moA = m_fds moB /\ m_fs moA = m_fs moB /\ minv moA /\ minv moB /\ m_halted moA = None /\ m_halted moB = None.
  Hypothesis MR_so : forall k X sA moA sB moB, MR k X sA moA sB moB -> ps_so sA = ps_so sB.
  Hypothesis MR_soupd : forall k X sA moA sB moB so, MR k X sA moA sB moB -> MR k X (set_so_ps so sA) moA (set_so_ps so sB) moB.
  Hypothesis MR_fdupd : forall k X sA moA sB moB moA' moB', MR k X sA moA sB moB ->
    fdupd2 moA moA' moB moB' -> minv moA' -> minv moB' -> m_halted moA' = None -> m_halted moB' = None -> MR k X sA moA' sB moB'.
  Hypothesis MR_perm : forall k X Y sA moA sB moB, Permutation X Y -> MR k X sA moA sB moB -> MR k Y sA moA sB moB.
  Hypothesis MR_weaken : forall k X sA moA sB moB, MR (S k) X sA moA sB moB -> MR k X sA moA sB moB.
  Hypothesis malloc_sim : forall k X n, 0 <= n <= NMAX ->
    msim (MR (S k) X) (raw_malloc n) (raw_malloc n)
         (fun rA rB sA moA sB moB => rA = rB /\ match rA with Some p => MR k (p :: X) sA moA sB moB | None => MR k X sA moA sB moB end).
  Hypothesis free_sim : forall k X p, msim (MR k (p :: X)) (raw_free p) (raw_free p) (fun _ _ => MR k X).

  Notation io := (io_S ps_so set_so_ps).
  Notation EQ k X := (fun (a b : _) sA moA sB moB => a = b /\ MR k X sA moA sB moB).

  #[using="MR_weaken"] Lemma MR_weaken_le : forall j k X sA moA sB moB, (k <= j)%nat -> MR j X sA moA sB moB -> MR k X sA moA sB moB.
  Proof.
    intros j k X sA moA sB moB Hle H. induction Hle as [|j Hle IH]; [exact H|]. apply IH. apply MR_weaken. exact H.
  Qed.

  #[using="MR_fds MR_fdupd"] Lemma msim_fdnode : forall k X {A} (n : node) (dec : resp -> option A), fdnode n ->
    msim (MR k X) (msys n dec) (msys n dec) (EQ k X).
  Proof.
    intros k X A n dec Hn. apply msim_sys. intros sA moA sB moB HR.
    destruct (MR_fds _ _ _ _ _ _ HR) as (EF & ES & MIA & MIB & HA & HB).
    assert (NR : forall addr len prot flags, n = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false)
      by (intros; subst; contradiction).
    split; [| intros code mo' EX; destruct n; contradiction].
    intros rspA moA' evs ST. destruct (fd_transfer n moA moB rspA moA' evs Hn EF ES ST) as (moB' & STB & U).
    exists rspA, moB'. split; [exact STB|].
    destruct (minv_preserved _ _ _ _ _ NR MIA HA ST) as [HA' MIA']. destruct (minv_preserved _ _ _ _ _ NR MIB HB STB) as [HB' MIB'].
    destruct (dec rspA); [| exact I]. split; [reflexivity|]. eapply MR_fdupd; eauto.
  Qed.

  Definition rd_len_ok (cnt : Z) (a : read_ans) : Prop := match a with RdData bs => Z.of_nat (length bs) <= cnt | RdErr _ => True end.

  #[using="MR_fds MR_fdupd"] Lemma msim_read : forall k X fd bufA bufB cnt, 0 <= cnt < 2^64 ->
    msim (MR k X) (msys (NRead fd bufA cnt) (dec_read bufA cnt)) (msys (NRead fd bufB cnt) (dec_read bufB cnt))
         (fun a b sA moA sB moB => a = b /\ MR k X sA moA sB moB /\ rd_len_ok cnt a).
  Proof.
    intros k X fd bufA bufB cnt Hc. apply msim_sys. intros sA moA sB moB HR.
    destruct (MR_fds _ _ _ _ _ _ HR) as (EF & ES & MIA & MIB & HA & HB).
    assert (ONE : forall (b1 b2 : Z) (m1 m2 : Model) (rsp1 : resp) (m1' : Model) (evs : list event) (MRx : Model -> Model -> Prop),
      m_fds m1 = m_fds m2 -> m_fs m1 = m_fs m2 -> minv m1 -> minv m2 -> m_halted m1 = None -> m_halted m2 = None ->
      (forall m1' m2', fdupd2 m1 m1' m2 m2' -> minv m1' -> minv m2' -> m_halted m1' = None -> m_halted m2' = None -> MRx m1' m2') ->
      nstep (NRead fd b1 cnt) m1 rsp1 m1' evs ->
      exists rsp2 m2', nstep (NRead fd b2 cnt) m2 rsp2 m2' evs /\
        match dec_read b1 cnt rsp1, dec_read b2 cnt rsp2 with
        | Some a, Some b => a = b /\ MRx m1' m2' /\ rd_len_ok cnt a
        | None, None => True | _, _ => False end).
    { clear - Hc. intros b1 b2 m1 m2 rsp1 m1' evs MRx EF ES MI1 MI2 H1 H2 HM ST.
      assert (NR : forall addr len prot flags, NRead fd b1 cnt = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false) by (intros; discriminate).
      assert (NR2 : forall addr len prot flags, NRead fd b2 cnt = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false) by (intros; discriminate).
      destruct (minv_preserved _ _ _ _ _ NR MI1 H1 ST) as [H1' MI1'].
      destruct (nstep_dec_read fd b1 cnt m1 rsp1 m1' evs Hc ST) as (-> & a & D1 & Ha). rewrite D1.
      pose proof ST as [_ ST1]. rewrite EF, ES in ST1.
      destruct a as [e|bs].
      - destruct Ha as [-> Hor].
        exists (efferr e), m2. assert (ST2 : nstep (NRead fd b2 cnt) m2 (efferr e) m2 []).
        { split; [reflexivity|]. destruct Hor as [[-> N]|[[-> N]|[-> (pp & oo & N)]]]; rewrite EF in N; rewrite N; split; reflexivity. }
        split; [exact ST2|]. destruct (nstep_dec_read fd b2 cnt m2 _ _ _ Hc ST2) as (_ & b & D2 & Hb). rewrite D2.
        destruct b as [e2|bs2]; [| destruct Hb as (p & off & data & F & _); destruct Hor as [[_ N]|[[_ N]|[_ (pp & oo & N)]]]; rewrite EF in N; rewrite N in F; discriminate F].
        destruct Hb as [_ Hor2]. destruct (minv_preserved _ _ _ _ _ NR2 MI2 H2 ST2) as [H2' MI2'].
        assert (e2 = e) by (destruct Hor as [[-> N]|[[-> N]|[-> (pp & oo & N)]]]; destruct Hor2 as [[-> N2]|[[-> N2]|[-> (pp2 & oo2 & N2)]]]; try reflexivity; rewrite EF in N; rewrite N in N2; discriminate N2).
        subst e2. split; [reflexivity|]. split; [| exact I]. apply HM; auto. left; auto.
      - destruct Ha as (p & off & data & F & FS & Ebs & ->).
        set (rsp2 := mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 b2) bs) []).
        set (m2' := with_fds (fd_insert (m_fds m2) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) m2).
        assert (ST2 : nstep (NRead fd b2 cnt) m2 rsp2 m2' []).
        { split; [reflexivity|]. subst rsp2 m2'. rewrite <- EF, F, <- ES, FS. rewrite <- Ebs. split; reflexivity. }
        exists rsp2, m2'. split; [exact ST2|].
        destruct (nstep_dec_read fd b2 cnt m2 _ _ _ Hc ST2) as (_ & b & D2 & Hb). rewrite D2.
        destruct b as [e2|bs2]; [destruct Hb as [_ [[_ N]|[[_ N]|[_ (pp & oo & N)]]]]; rewrite <- EF, F in N; discriminate N|].
        destruct Hb as (p2 & off2 & data2 & F2 & FS2 & Ebs2 & E2).
        rewrite <- EF, F in F2. injection F2. intros <- <-. rewrite <- ES, FS in FS2. injection FS2. intros <-. rewrite <- Ebs in Ebs2. subst bs2.
        destruct (minv_preserved _ _ _ _ _ NR2 MI2 H2 ST2) as [H2' MI2'].
        split; [reflexivity|]. split.
        + apply HM; auto. right. exists (fd_insert (m_fds m1) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)). split; [reflexivity| subst m2'; rewrite <- EF; reflexivity].
        + cbn. rewrite Ebs. pose proof (length_file_read_le_count data off cnt Hc). lia. }
    split; [| intros code mo' EX; destruct EX].
    intros rspA moA' evs ST.
    destruct (ONE bufA bufB moA moB rspA moA' evs (fun mA mB => MR k X sA mA sB mB) EF ES MIA MIB HA HB
                  ltac:(intros; eapply MR_fdupd; eauto) ST) as (rspB & moB' & STB & M).
    exists rspB, moB'. split; [exact STB| exact M].
  Qed.

  #[using="MR_fds"] Lemma msim_exit : forall k X c, msim (MR k X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) (fun (a b : Empty_set) _ _ _ _ => False).
  Proof.
    intros k X c. apply msim_sys. intros sA moA sB moB HR. destruct (MR_fds _ _ _ _ _ _ HR) as (EF & ES & _).
    split; [intros rspA moA' evs ST; destruct (nstep_exit_none _ _ _ _ _ ST)|].
    intros code mo' [-> ->]; eexists; (split; [split; reflexivity|]); rewrite !m_fs_with_halted; congruence.
  Qed.

  #[using="MR_so"] Lemma msim_rd_so : forall k X, msim (MR k X) (rd_so ps_so) (rd_so ps_so) (EQ k X).
  Proof.
    intros k X. unfold rd_so. eapply msim_bind; [apply msim_get|]. intros a b. apply msim_ret.
    intros sA moA sB moB (-> & -> & HR). split; [exact (MR_so _ _ _ _ _ _ HR)| exact HR].
  Qed.
  #[using="MR_so MR_soupd"] Lemma msim_upd_so : forall k X f, msim (MR k X) (upd_so ps_so set_so_ps f) (upd_so ps_so set_so_ps f) (EQ k X).
  Proof.
    intros k X f. unfold upd_so. apply msim_upd. intros sA moA sB moB HR. split; [reflexivity|].
    rewrite (MR_so _ _ _ _ _ _ HR). apply MR_soupd. exact HR.
  Qed.

  Local Ltac bindE k X := eapply (msim_bind_eq _ _ _ (fun _ => MR k X)).
  Local Ltac retE := apply msim_ret; intros; split; [reflexivity| assumption].

  #[using="MR_fds MR_fdupd"] Lemma msim_stdio_wloop : forall k X fuel fd bufs, msim (MR k X) (stdio_wloop fuel fd bufs) (stdio_wloop fuel fd bufs) (EQ k X).
  Proof.
    intros k X fuel. induction fuel as [|fuel IH]; intros fd bufs; cbn [stdio_wloop]; [apply msim_munr|].
    bindE k X; [apply msim_fdnode; exact I|]. intros j. apply msim_if; intros _; [retE| apply IH].
  Qed.
  #[using="MR_fds MR_fdupd"] Lemma msim_stdio_writev : forall k X fd buf bs, msim (MR k X) (stdio_writev fd buf bs) (stdio_writev fd buf bs) (EQ k X).
  Proof. intros. unfold stdio_writev. apply msim_stdio_wloop. Qed.
  #[using="MR_fds MR_so MR_soupd MR_fdupd"] Lemma msim_stdout_writefn : forall k X bs, msim (MR k X) (stdout_writefn ps_so set_so_ps bs) (stdout_writefn ps_so set_so_ps bs) (EQ k X).
  Proof.
    intros k X bs. unfold stdout_writefn, stdout_stdio_write.
    bindE k X; [apply msim_rd_so|]. intros so.
    bindE k X.
    - apply msim_if; intros _; [| retE].
      bindE k X; [apply msim_upd_so|]. intros _. bindE k X; [apply msim_fdnode; exact I|].
      intros [e|v]; [apply msim_upd_so| apply msim_munr].
    - intros _. bindE k X; [apply msim_rd_so|]. intros so'. bindE k X; [apply msim_stdio_writev|]. intros _. apply msim_upd_so.
  Qed.
  #[using="MR_fds MR_so MR_soupd MR_fdupd"] Lemma msim_stdout_exit_flush : forall k X, msim (MR k X) (stdout_exit_flush ps_so set_so_ps) (stdout_exit_flush ps_so set_so_ps) (EQ k X).
  Proof.
    intros k X. unfold stdout_exit_flush. bindE k X; [apply msim_rd_so|]. intros so.
    apply msim_if; intros _; [apply msim_stdout_writefn| retE].
  Qed.
  #[using="MR_fds MR_fdupd"] Lemma msim_stderr_pieces : forall k X ps buf, msim (MR k X) (stderr_pieces buf ps) (stderr_pieces buf ps) (EQ k X).
  Proof.
    intros k X ps. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [retE|].
    apply msim_if; intros _; [| apply IH]. bindE k X; [apply msim_stdio_writev|]. intros _. apply IH.
  Qed.
  #[using="MR_fds MR_fdupd"] Lemma msim_stderr_fprintf : forall k X ps, msim (MR k X) (stderr_fprintf ps) (stderr_fprintf ps) (EQ k X).
  Proof. intros k X ps. unfold stderr_fprintf. bindE k X; [apply msim_stderr_pieces|]. intros buf. apply msim_stdio_writev. Qed.
  #[using="MR_fds MR_fdupd"] Lemma msim_stderr_fwrite : forall k X bs, msim (MR k X) (stderr_fwrite bs) (stderr_fwrite bs) (EQ k X).
  Proof. intros k X bs. unfold stderr_fwrite. apply msim_if; intros _; [apply msim_stdio_writev| retE]. Qed.
  #[using="MR_fds MR_fdupd"] Lemma msim_s_diag : forall k X d, msim (MR k X) (io_diag io d) (io_diag io d) (EQ k X).
  Proof. intros k X []; cbn [io_diag io_S s_diag]; first [apply msim_stderr_fprintf | apply msim_stderr_fwrite]. Qed.

  #[using="MR_fds MR_fdupd"] Lemma msim_s_diag' : forall k X d (R : rel PState PState), (forall sA moA sB moB, R sA moA sB moB -> MR k X sA moA sB moB) ->
    msim R (io_diag io d) (io_diag io d) (fun _ _ => MR k X).
  Proof. intros k X d R HR. eapply msim_conseq; [apply (msim_s_diag k X d)| exact HR| intros ? ? ? ? ? ? [_ H]; exact H]. Qed.

  #[using="MR_fds MR_so MR_soupd MR_fdupd"] Lemma msim_exit_k : forall k X {A B} code (Q : A -> B -> rel PState PState), msim (MR k X) (exit_k io code) (exit_k io code) Q.
  Proof.
    intros k X A B code Q. unfold exit_k, exit_model. cbn [io_exit io_S].
    eapply msim_bind with (Q1 := fun (a b : Empty_set) _ _ _ _ => False).
    - bindE k X; [apply msim_stdout_exit_flush|]. intros _. apply msim_exit.
    - intros a. destruct a.
  Qed.

  Definition jbud (kR : nat) (j : Z) : nat := (kR + Z.to_nat (26 - j))%nat.

  Definition rdI (kR : nat) (X : list bptr) (stA stB : rd_st (ptr:=bptr)) : rel PState PState :=
    fun sA moA sB moB => stA = stB
      /\ (exists j, 16 <= j <= 26 /\ rd_cap stA = 2 ^ j /\ MR (jbud kR j) (rd_buf stA :: X) sA moA sB moB)
      /\ 0 <= zlength (rd_content stA) <= rd_cap stA /\ rd_cap stA <= MAX_INPUT.

  #[using="Type"] Lemma pow2_lt_26 : forall j, 0 <= j -> 2 ^ j < MAX_INPUT -> j < 26.
  Proof.
    intros j Hj H. unfold MAX_INPUT in H. change 67108864 with (2 ^ 26) in H.
    apply Z.pow_lt_mono_r_iff in H; lia.
  Qed.

  #[using="NMAX HNMAX MR_fds MR_fdupd MR_perm MR_weaken malloc_sim free_sim"] Lemma msim_read_loop_body : forall kR X fd path stA stB,
    msim (rdI kR X stA stB)
         (read_loop_body io raw_malloc raw_free rsA fd path stA) (read_loop_body io raw_malloc raw_free rsB fd path stB)
         (fun rA rB sA moA sB moB => match rA, rB with
                                    | inl xA, inl xB => rdI kR X xA xB sA moA sB moB
                                    | inr a, inr b => a = b /\ match a with RdExit => exists k Y, MR k Y sA moA sB moB
                                                                          | RdDone buf content => MR kR (buf :: X) sA moA sB moB /\ 0 <= zlength content <= MAX_INPUT end
                                    | _, _ => False
                                    end).
  Proof.
    intros kR X fd path stA stB.
    apply (msim_expose _ (stA = stB /\ (exists j, 16 <= j <= 26 /\ rd_cap stA = 2 ^ j) /\ 0 <= zlength (rd_content stA) <= rd_cap stA /\ rd_cap stA <= MAX_INPUT));
      [intros sA moA sB moB (E & (j & Hj & Ej & _) & B); repeat split; auto; try lia; exists j; auto|].
    intros (<- & (j & Hj & Ej) & B & C). set (st := stA) in *.
    assert (PRE : forall sA moA sB moB, rdI kR X st st sA moA sB moB -> MR (jbud kR j) (rd_buf st :: X) sA moA sB moB).
    { intros sA moA sB moB (_ & (j' & Hj' & Ej' & H) & _). replace j with j' ; [exact H|].
      apply (Z.pow_inj_r 2); [lia| lia| lia| rewrite <- Ej, <- Ej'; reflexivity]. }
    unfold read_loop_body.
    eapply msim_bind with (Q1 := fun gA gB sA moA sB moB => gA = gB /\ match gA with
                              | None => exists k Y, MR k Y sA moA sB moB
                              | Some st1 => (exists j1, 16 <= j1 <= 26 /\ rd_cap st1 = 2 ^ j1 /\ MR (jbud kR j1) (rd_buf st1 :: X) sA moA sB moB)
                                            /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1 /\ rd_cap st1 <= MAX_INPUT end).
    { apply msim_if; intros E.
      - apply msim_if; intros E2.
        + eapply msim_seq; [apply (msim_s_diag' (jbud kR j) (rd_buf st :: X)); exact PRE|].
          intros ? ?. apply msim_ret. intros sA moA sB moB H. split; [reflexivity|]. exists (jbud kR j), (rd_buf st :: X). exact H.
        + apply Z.eqb_eq in E. apply Z.leb_gt in E2.
          pose proof (pow2_lt_26 j ltac:(lia) ltac:(rewrite <- Ej; exact E2)) as J26.
          assert (EB : jbud kR j = S (jbud kR (j + 1))) by (unfold jbud; lia).
          pose proof (pow2_double_le j _ ltac:(lia) Ej E2) as D2. unfold MAX_INPUT in D2, C.
          eapply msim_bind; [eapply msim_pre; [apply (malloc_sim (jbud kR (j + 1)) (rd_buf st :: X) (rd_cap st * 2)); lia| intros ? ? ? ? H; rewrite <- EB; exact (PRE _ _ _ _ H)]|].
          intros [nb|] rB; cbn beta iota.
          * apply msim_expose with (phi := rB = Some nb); [intros ? ? ? ? [H _]; symmetry; exact H|]. intros ->.
            eapply msim_seq.
            { eapply msim_pre; [apply (free_sim (jbud kR (j + 1)) (nb :: X) (rd_buf st))|]. intros ? ? ? ? [_ H]. eapply MR_perm; [apply perm_swap| exact H]. }
            intros ? ?. apply msim_ret. intros sA moA sB moB H. cbn [rd_buf rd_cap rd_content]. split; [reflexivity|]. split.
            { exists (j + 1). split; [lia|]. split; [rewrite Ej, Z.pow_add_r by lia; lia| exact H]. }
            split; [reflexivity| unfold MAX_INPUT; lia].
          * apply msim_expose with (phi := rB = None); [intros ? ? ? ? [H _]; symmetry; exact H|]. intros ->.
            eapply msim_seq; [apply (msim_s_diag' (jbud kR (j + 1)) (rd_buf st :: X)); intros ? ? ? ? [_ H]; exact H|].
            intros ? ?. apply msim_ret. intros sA moA sB moB H. split; [reflexivity|]. exists (jbud kR (j + 1)), (rd_buf st :: X). exact H.
      - apply msim_ret. intros sA moA sB moB HI. pose proof HI as (_ & JJ & _). apply Z.eqb_neq in E. split; [reflexivity|]. split; [exact JJ|]. split; [reflexivity| lia]. }
    intros gA gB. apply msim_expose with (phi := gA = gB); [intros ? ? ? ? [H _]; exact H|]. intros <-.
    destruct gA as [st1|]; cbn beta iota.
    2:{ apply msim_ret. intros sA moA sB moB [_ H]. split; [reflexivity| exact H]. }
    apply msim_expose with (phi := (exists j1, 16 <= j1 <= 26 /\ rd_cap st1 = 2 ^ j1) /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1 /\ rd_cap st1 <= MAX_INPUT);
      [intros ? ? ? ? (_ & (j1 & A1 & A2 & _) & H); split; [exists j1; auto| exact H]|]. intros ((j1 & Hj1 & Ej1) & E1 & L1 & C1).
    assert (PRE1 : forall sA moA sB moB, (Some st1 = Some st1 /\ (exists j0, 16 <= j0 <= 26 /\ rd_cap st1 = 2 ^ j0 /\ MR (jbud kR j0) (rd_buf st1 :: X) sA moA sB moB) /\
                      rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1 /\ rd_cap st1 <= MAX_INPUT) -> MR (jbud kR j1) (rd_buf st1 :: X) sA moA sB moB).
    { intros sA moA sB moB (_ & (j' & Hj' & Ej' & H) & _). replace j1 with j'; [exact H|].
      apply (Z.pow_inj_r 2); [lia| lia| lia| rewrite <- Ej1, <- Ej'; reflexivity]. }

    cbv zeta.
    eapply msim_bind.
    { eapply msim_pre; [apply (msim_read (jbud kR j1) (rd_buf st1 :: X)); unfold READ_CHUNK; lia|]. intros ? ? ? ? H. exact (PRE1 _ _ _ _ H). }
    intros a b. apply msim_expose with (phi := a = b /\ rd_len_ok (Z.min (rd_cap st1 - zlength (rd_content st)) READ_CHUNK) a); [intros ? ? ? ? (H & _ & L); auto|]. intros [<- LOK].
    destruct a as [e|bs]; cbn beta iota.
    - eapply msim_seq; [apply (msim_s_diag' (jbud kR j1) (rd_buf st1 :: X)); intros ? ? ? ? (_ & H & _); exact H|].
      intros ? ?. apply msim_ret. intros sA moA sB moB H. split; [reflexivity|]. exists (jbud kR j1), (rd_buf st1 :: X). exact H.
    - apply msim_if; intros Ebs; apply msim_ret; intros sA moA sB moB (_ & H & _).
      + split; [reflexivity|]. split; [| rewrite E1; lia]. eapply MR_weaken_le; [| exact H]. unfold jbud. lia.
      + apply Nat.eqb_neq in Ebs. unfold rdI. cbn [rd_buf rd_cap rd_content]. split; [reflexivity|]. split; [exists j1; auto|].
        cbn [rd_len_ok] in LOK. unfold READ_CHUNK in LOK. rewrite E1.
        assert (LEN' : zlength (rd_content st ++ u8s_of_bytes bs) = zlength (rd_content st) + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. lia. }
        rewrite LEN'. lia.
  Qed.

  #[using="NMAX HNMAX MR_fds MR_fdupd MR_perm MR_weaken malloc_sim free_sim"] Lemma msim_read_all : forall kR X path,
    msim (MR (S (jbud kR 16)) X) (read_all io raw_malloc raw_free rsA path) (read_all io raw_malloc raw_free rsB path)
         (fun rA rB sA moA sB moB => rA = rB /\ match rA with RdExit => exists k Y, MR k Y sA moA sB moB
                                                           | RdDone buf content => MR kR (buf :: X) sA moA sB moB /\ 0 <= zlength content <= MAX_INPUT end).
  Proof.
    intros kR X path. unfold read_all. set (k0 := S (jbud kR 16)).
    bindE k0 X; [apply msim_fdnode; exact I|]. intros [e|fd]; cbn beta iota.
    { eapply msim_seq; [apply (msim_s_diag' k0 X); intros ? ? ? ? H; exact H|]. intros ? ?. apply msim_ret. intros sA moA sB moB H. split; [reflexivity|]. exists k0, X. exact H. }
    eapply msim_bind; [apply (malloc_sim (jbud kR 16) X 65536); lia|]. intros [buf|] rB; cbn beta iota.
    2:{ apply msim_expose with (phi := rB = None); [intros ? ? ? ? [H _]; symmetry; exact H|]. intros ->.
        eapply msim_seq; [apply (msim_s_diag' (jbud kR 16) X); intros ? ? ? ? [_ H]; exact H|]. intros ? ?. apply msim_ret. intros sA moA sB moB H. split; [reflexivity|]. exists (jbud kR 16), X. exact H. }
    apply msim_expose with (phi := rB = Some buf); [intros ? ? ? ? [H _]; symmetry; exact H|]. intros ->. cbn beta iota.
    eapply msim_bind.
    { eapply msim_pre; [apply (msim_loop _ _ (rdI kR X) _ (msim_read_loop_body kR X fd path))|].
      intros sA moA sB moB [_ H]. unfold rdI. cbn [rd_buf rd_cap rd_content]. replace (zlength (@nil Z)) with 0 by reflexivity. unfold MAX_INPUT.
      split; [reflexivity|]. split; [exists 16; split; [lia| split; [reflexivity| exact H]]| lia]. }
    intros rA rB'. apply msim_expose with (phi := rA = rB'); [intros ? ? ? ? [H _]; exact H|]. intros <-.
    destruct rA as [|buf' content]; cbn beta iota.
    - apply msim_ret. intros sA moA sB moB [_ H]. split; [reflexivity| exact H].
    - apply msim_expose with (phi := 0 <= zlength content <= MAX_INPUT); [intros ? ? ? ? (_ & _ & B0); exact B0|]. intros B0.
      eapply msim_bind.
      { eapply msim_pre; [apply (msim_fdnode kR (buf' :: X) (NClose fd) dec_close I)| intros ? ? ? ? [_ [H _]]; exact H]. }
      intros ? ?. apply msim_ret. intros sA moA sB moB [_ H]. split; [reflexivity|]. split; [exact H| exact B0].
  Qed.

  Definition DRV_BUDGET (k : nat) : nat := S (S (jbud k 16)).

  #[using="NMAX HNMAX MR_fds MR_so MR_soupd MR_fdupd MR_perm MR_weaken malloc_sim free_sim"] Theorem drv_pre_sim : forall k X argv,
    msim (MR (DRV_BUDGET k) X) (drv_pre io raw_malloc raw_free rsA argv) (drv_pre io raw_malloc raw_free rsB argv)
         (fun apA apB sA moA sB moB => apA = apB /\ MR k (ap_blocks apA ++ X) sA moA sB moB).
  Proof.
    intros k X argv. unfold drv_pre, DRV_BUDGET. set (k1 := S (jbud (S k) 16)).
    assert (EK : S (S (jbud k 16)) = k1) by (unfold k1, jbud; lia). rewrite EK.
    apply msim_if; intros E.
    { eapply msim_seq; [apply (msim_s_diag' k1 X); intros ? ? ? ? H; exact H|]. intros ? ?. apply msim_exit_k. }
    eapply msim_bind; [apply (msim_read_all (S k) X)|]. intros rA rB. apply msim_expose with (phi := rA = rB); [intros ? ? ? ? [H _]; exact H|]. intros <-.
    destruct rA as [|buf content]; cbn beta iota.
    { apply (msim_pre (fun sA moA sB moB => exists kk Y, MR kk Y sA moA sB moB)); [| intros ? ? ? ? [_ H]; exact H].
      apply msim_exI. intros kk. apply msim_exI. intros Y. apply msim_exit_k. }
    apply msim_expose with (phi := 0 <= zlength content <= MAX_INPUT); [intros ? ? ? ? [_ [_ B]]; exact B|]. intros B.
    apply (msim_pre (MR (S k) (buf :: X))); [| intros ? ? ? ? [_ [H _]]; exact H].
    apply msim_if; intros E1.
    { eapply msim_seq; [apply (msim_s_diag' (S k) (buf :: X)); intros ? ? ? ? H; exact H|]. intros ? ?.
      eapply msim_seq; [apply (free_sim (S k) X buf)|]. intros ? ?. apply msim_exit_k. }
    apply msim_if; intros E2.
    { eapply msim_seq; [apply (msim_s_diag' (S k) (buf :: X)); intros ? ? ? ? H; exact H|]. intros ? ?.
      eapply msim_seq; [apply (free_sim (S k) X buf)|]. intros ? ?. apply msim_exit_k. }
    apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. unfold HDR_MIN in *.
    eapply msim_bind with (Q1 := fun cA cB sA moA sB moB => cA = cB /\ match cA with
                              | None => exists Y, MR k (Y ++ buf :: X) sA moA sB moB
                              | Some owned => MR k (match owned with Some p => [p; buf] | None => [buf] end ++ X) sA moA sB moB end).
    { apply msim_if; intros E3.
      - apply Z.ltb_lt in E3. unfold MAX_INPUT in B. pose proof (land15_range (le16 content)) as L15. eapply msim_bind; [apply (malloc_sim k (buf :: X)); lia|].
        intros [p|] rB'; cbn beta iota; apply msim_ret; intros sA moA sB moB [<- H]; cbn beta iota; (split; [reflexivity|]); [exact H| exists []; exact H].
      - apply msim_ret. intros sA moA sB moB H. split; [reflexivity|]. cbn. apply MR_weaken. exact H. }
    intros cA cB. apply msim_expose with (phi := cA = cB); [intros ? ? ? ? [H _]; exact H|]. intros <-.
    destruct cA as [owned|]; cbn beta iota.
    - apply msim_ret. intros sA moA sB moB [_ H]. split; [reflexivity|]. unfold ap_blocks. cbn [ap_owned ap_buf]. exact H.
    - apply (msim_pre (fun sA moA sB moB => exists Y, MR k (Y ++ buf :: X) sA moA sB moB)); [| intros ? ? ? ? [_ H]; exact H].
      apply msim_exI. intros Y. eapply msim_seq.
      + eapply msim_pre; [apply (free_sim k (Y ++ X) buf)|]. intros ? ? ? ? H. eapply MR_perm; [| exact H]. apply Permutation_sym. apply Permutation_middle.
      + intros ? ?. apply msim_exit_k.
  Qed.

  #[using="NMAX HNMAX MR_fds MR_so MR_soupd MR_fdupd MR_perm MR_weaken malloc_sim free_sim"] Theorem drv_pre_tshape_incl : forall k X argv sA moA sB moB
      (KA KB : exc (at_parser (ptr:=bptr) * PState) -> Model -> TSet),
    MR (DRV_BUDGET k) X sA moA sB moB ->
    (forall ap sA' moA' sB' moB', MR k (ap_blocks ap ++ X) sA' moA' sB' moB' -> t_incl (KA (Ok (ap, sA')) moA') (KB (Ok (ap, sB')) moB')) ->
    (forall moA' moB', t_incl (KA Unr moA') (KB Unr moB')) ->
    t_incl (tsh (drv_pre io raw_malloc raw_free rsA argv sA) moA KA) (tsh (drv_pre io raw_malloc raw_free rsB argv sB) moB KB).
  Proof.
    intros k X argv sA moA sB moB KA KB HR HK HU.
    eapply (msim_tshape _ _ _ _ KA KB sA moA sB moB (drv_pre_sim k X argv) HR); [| exact HU].
    intros a sA' moA' b sB' moB' [<- H]. apply HK. exact H.
  Qed.
End DS.
