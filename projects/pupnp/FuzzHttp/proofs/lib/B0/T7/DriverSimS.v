(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite Namei Open.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe Stdio Driver.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim DriverSim DriverModel.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import TSimS MSimS.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).

Section DSS.
  Context {StA StB ptrA ptrB : Type}.
  Variables (getA : StA -> stdout_st) (setA : stdout_st -> StA -> StA).
  Variables (getB : StB -> stdout_st) (setB : stdout_st -> StB -> StB).
  Variables (mallocA : Z -> Monad.M StA (option ptrA)) (freeA : ptrA -> Monad.M StA unit).
  Variables (mallocB : Z -> Monad.M StB (option ptrB)) (freeB : ptrB -> Monad.M StB unit).
  Variables (rsA rsB : Z).
  Local Notation ioA := (io_S getA setA).
  Local Notation ioB := (io_S getB setB).

  Variable RI : nat -> list (ptrA * ptrB) -> StA -> Model -> StB -> Model -> Prop.
  Variable NMAX : Z.
  Hypothesis HNMAX : 2^26 <= NMAX.
  Hypothesis RI_fds : forall k X sA moA sB moB, RI k X sA moA sB moB ->
    m_fds moA = m_fds moB /\ m_fs moA = m_fs moB /\ minv moA /\ minv moB /\ m_halted moA = None /\ m_halted moB = None.
  Hypothesis RI_so : forall k X sA moA sB moB, RI k X sA moA sB moB -> getA sA = getB sB.
  Hypothesis RI_soupd : forall k X sA moA sB moB so, RI k X sA moA sB moB -> RI k X (setA so sA) moA (setB so sB) moB.
  Hypothesis RI_fdupd : forall k X sA moA sB moB moA' moB', RI k X sA moA sB moB ->
    fdupd2 moA moA' moB moB' -> minv moA' -> minv moB' -> m_halted moA' = None -> m_halted moB' = None -> RI k X sA moA' sB moB'.
  Hypothesis RI_perm : forall k X Y sA moA sB moB, Permutation X Y -> RI k X sA moA sB moB -> RI k Y sA moA sB moB.
  Hypothesis RI_weaken : forall k X sA moA sB moB, RI (S k) X sA moA sB moB -> RI k X sA moA sB moB.
  Hypothesis malloc_simS : forall k X n, 0 <= n <= NMAX ->
    msimS (RI (S k) X) (mallocA n) (mallocB n)
          (fun rA rB sA moA sB moB => exists pA pB, rA = Some pA /\ rB = Some pB /\ RI k ((pA, pB) :: X) sA moA sB moB).
  Hypothesis free_simS : forall k X pA pB, msimS (RI k ((pA, pB) :: X)) (freeA pA) (freeB pB) (fun _ _ => RI k X).

  Local Notation EQ k X := (fun (a b : _) sA moA sB moB => a = b /\ RI k X sA moA sB moB).

  #[using="RI_weaken"] Lemma RI_weaken_le : forall j k X sA moA sB moB, (k <= j)%nat -> RI j X sA moA sB moB -> RI k X sA moA sB moB.
  Proof. intros j k X sA moA sB moB Hle H. induction Hle as [|j Hle IH]; [exact H|]. apply IH. apply RI_weaken. exact H. Qed.

  #[using="RI_fds RI_fdupd"] Lemma msimS_fdnode : forall k X {A} (n : node) (dec : resp -> option A), fdnode n ->
    msimS (RI k X) (msys n dec) (msys n dec) (EQ k X).
  Proof.
    intros k X A n dec Hn. apply msimS_sys. intros sA moA sB moB HR.
    destruct (RI_fds _ _ _ _ _ _ HR) as (EF & ES & MIA & MIB & HA & HB).
    assert (NR : forall addr len prot flags, n = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false)
      by (intros; subst; contradiction).
    split; [| intros code mo' EX; destruct n; contradiction].
    intros rspA moA' evs ST. destruct (fd_transfer n moA moB rspA moA' evs Hn EF ES ST) as (moB' & STB & U).
    exists rspA, moB'. split; [exact STB|].
    destruct (minv_preserved _ _ _ _ _ NR MIA HA ST) as [HA' MIA']. destruct (minv_preserved _ _ _ _ _ NR MIB HB STB) as [HB' MIB'].
    destruct (dec rspA); [| exact I]. split; [reflexivity|]. eapply RI_fdupd; eauto.
  Qed.

  #[using="RI_fds RI_fdupd"] Lemma msimS_read : forall k X fd cnt, 0 <= cnt < 2^64 ->
    msimS (RI k X) (msys (NRead fd rsA cnt) (dec_read rsA cnt)) (msys (NRead fd rsB cnt) (dec_read rsB cnt))
          (fun a b sA moA sB moB => a = b /\ RI k X sA moA sB moB /\ rd_len_ok cnt a).
  Proof.
    intros k X fd cnt Hc. apply msimS_sys. intros sA moA sB moB HR.
    destruct (RI_fds _ _ _ _ _ _ HR) as (EF & ES & MIA & MIB & HA & HB).
    assert (NR : forall b addr len prot flags, NRead fd b cnt = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false) by (intros; discriminate).
    split; [| intros code mo' EX; destruct EX].
    intros rspA moA' evs ST.
    destruct (minv_preserved _ _ _ _ _ (NR rsA) MIA HA ST) as [HA' MIA'].
    destruct (nstep_dec_read fd rsA cnt moA rspA moA' evs Hc ST) as (-> & a & D1 & Ha). rewrite D1.
    destruct a as [e|bs].
    - destruct Ha as [-> Hor].
      assert (ST2 : nstep (NRead fd rsB cnt) moB (efferr e) moB []).
      { split; [reflexivity|]. destruct Hor as [[-> N]|[[-> N]|[-> (pp & oo & N)]]]; rewrite EF in N; rewrite N; split; reflexivity. }
      exists (efferr e), moB. split; [exact ST2|].
      destruct (nstep_dec_read fd rsB cnt moB _ _ _ Hc ST2) as (_ & b & D2 & Hb). rewrite D2.
      destruct b as [e2|bs2]; [| destruct Hb as (p & off & data & F & _); destruct Hor as [[_ N]|[[_ N]|[_ (pp & oo & N)]]]; rewrite EF in N; rewrite N in F; discriminate F].
      destruct Hb as [_ Hor2]. destruct (minv_preserved _ _ _ _ _ (NR rsB) MIB HB ST2) as [HB' MIB'].
      assert (e2 = e) by (destruct Hor as [[-> N]|[[-> N]|[-> (pp & oo & N)]]]; destruct Hor2 as [[-> N2]|[[-> N2]|[-> (pp2 & oo2 & N2)]]]; try reflexivity; rewrite EF in N; rewrite N in N2; discriminate N2).
      subst e2. split; [reflexivity|]. split; [| exact I]. eapply RI_fdupd; eauto. left; auto.
    - destruct Ha as (p & off & data & F & FS & Ebs & ->).
      set (rsp2 := mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 rsB) bs) []).
      set (m2' := with_fds (fd_insert (m_fds moB) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) moB).
      assert (ST2 : nstep (NRead fd rsB cnt) moB rsp2 m2' []).
      { split; [reflexivity|]. subst rsp2 m2'. rewrite <- EF, F, <- ES, FS. rewrite <- Ebs. split; reflexivity. }
      exists rsp2, m2'. split; [exact ST2|].
      destruct (nstep_dec_read fd rsB cnt moB _ _ _ Hc ST2) as (_ & b & D2 & Hb). rewrite D2.
      destruct b as [e2|bs2]; [destruct Hb as [_ [[_ N]|[[_ N]|[_ (pp & oo & N)]]]]; rewrite <- EF, F in N; discriminate N|].
      destruct Hb as (p2 & off2 & data2 & F2 & FS2 & Ebs2 & E2).
      rewrite <- EF, F in F2. injection F2. intros <- <-. rewrite <- ES, FS in FS2. injection FS2. intros <-. rewrite <- Ebs in Ebs2. subst bs2.
      destruct (minv_preserved _ _ _ _ _ (NR rsB) MIB HB ST2) as [HB' MIB'].
      split; [reflexivity|]. split.
      + eapply RI_fdupd; eauto. right. exists (fd_insert (m_fds moA) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)). split; [reflexivity| subst m2'; rewrite <- EF; reflexivity].
      + cbn. rewrite Ebs. pose proof (length_file_read_le_count data off cnt Hc). lia.
  Qed.

  #[using="RI_fds"] Lemma msimS_exit : forall k X c, msimS (RI k X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) (fun (a b : Empty_set) _ _ _ _ => False).
  Proof.
    intros k X c. apply msimS_sys. intros sA moA sB moB HR. destruct (RI_fds _ _ _ _ _ _ HR) as (EF & ES & _).
    split; [intros rspA moA' evs ST; destruct (nstep_exit_none _ _ _ _ _ ST)|].
    intros code mo' [-> ->]; eexists; (split; [split; reflexivity|]); rewrite !m_fs_with_halted; congruence.
  Qed.

  #[using="RI_so"] Lemma msimS_rd_so : forall k X, msimS (RI k X) (rd_so getA) (rd_so getB) (EQ k X).
  Proof.
    intros k X. unfold rd_so. eapply msimS_bind; [apply msimS_get|]. intros a b. apply msimS_ret.
    intros sA moA sB moB (-> & -> & HR). split; [exact (RI_so _ _ _ _ _ _ HR)| exact HR].
  Qed.
  #[using="RI_so RI_soupd"] Lemma msimS_upd_so : forall k X f, msimS (RI k X) (upd_so getA setA f) (upd_so getB setB f) (EQ k X).
  Proof.
    intros k X f. unfold upd_so. apply msimS_upd. intros sA moA sB moB HR. split; [reflexivity|].
    rewrite (RI_so _ _ _ _ _ _ HR). apply RI_soupd. exact HR.
  Qed.

  Local Ltac bindE k X := eapply (msimS_bind_eq _ _ _ (fun _ => RI k X)).
  Local Ltac retE := apply msimS_ret; intros; split; [reflexivity| assumption].

  #[using="RI_fds RI_fdupd"] Lemma msimS_stdio_wloop : forall k X fuel fd bufs, msimS (RI k X) (stdio_wloop fuel fd bufs) (stdio_wloop fuel fd bufs) (EQ k X).
  Proof.
    intros k X fuel. induction fuel as [|fuel IH]; intros fd bufs; cbn [stdio_wloop]; [apply msimS_munr|].
    bindE k X; [apply msimS_fdnode; exact I|]. intros j. apply msimS_if; intros _; [retE| apply IH].
  Qed.
  #[using="RI_fds RI_fdupd"] Lemma msimS_stdio_writev : forall k X fd buf bs, msimS (RI k X) (stdio_writev fd buf bs) (stdio_writev fd buf bs) (EQ k X).
  Proof. intros. unfold stdio_writev. apply msimS_stdio_wloop. Qed.
  #[using="RI_fds RI_so RI_soupd RI_fdupd"] Lemma msimS_stdout_writefn : forall k X bs, msimS (RI k X) (stdout_writefn getA setA bs) (stdout_writefn getB setB bs) (EQ k X).
  Proof.
    intros k X bs. unfold stdout_writefn, stdout_stdio_write.
    bindE k X; [apply msimS_rd_so|]. intros so.
    bindE k X.
    - apply msimS_if; intros _; [| retE].
      bindE k X; [apply msimS_upd_so|]. intros _. bindE k X; [apply msimS_fdnode; exact I|].
      intros [e|v]; [apply msimS_upd_so| apply msimS_munr].
    - intros _. bindE k X; [apply msimS_rd_so|]. intros so'. bindE k X; [apply msimS_stdio_writev|]. intros _. apply msimS_upd_so.
  Qed.
  #[using="RI_fds RI_so RI_soupd RI_fdupd"] Lemma msimS_stdout_exit_flush : forall k X, msimS (RI k X) (stdout_exit_flush getA setA) (stdout_exit_flush getB setB) (EQ k X).
  Proof.
    intros k X. unfold stdout_exit_flush. bindE k X; [apply msimS_rd_so|]. intros so.
    apply msimS_if; intros _; [apply msimS_stdout_writefn| retE].
  Qed.
  #[using="RI_fds RI_fdupd"] Lemma msimS_stderr_pieces : forall k X ps buf, msimS (RI k X) (stderr_pieces buf ps) (stderr_pieces buf ps) (EQ k X).
  Proof.
    intros k X ps. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [retE|].
    apply msimS_if; intros _; [| apply IH]. bindE k X; [apply msimS_stdio_writev|]. intros _. apply IH.
  Qed.
  #[using="RI_fds RI_fdupd"] Lemma msimS_stderr_fprintf : forall k X ps, msimS (RI k X) (stderr_fprintf ps) (stderr_fprintf ps) (EQ k X).
  Proof. intros k X ps. unfold stderr_fprintf. bindE k X; [apply msimS_stderr_pieces|]. intros buf. apply msimS_stdio_writev. Qed.
  #[using="RI_fds RI_fdupd"] Lemma msimS_stderr_fwrite : forall k X bs, msimS (RI k X) (stderr_fwrite bs) (stderr_fwrite bs) (EQ k X).
  Proof. intros k X bs. unfold stderr_fwrite. apply msimS_if; intros _; [apply msimS_stdio_writev| retE]. Qed.
  #[using="RI_fds RI_fdupd"] Lemma msimS_s_diag : forall k X d, msimS (RI k X) (io_diag ioA d) (io_diag ioB d) (EQ k X).
  Proof. intros k X []; cbn [io_diag io_S s_diag]; first [apply msimS_stderr_fprintf | apply msimS_stderr_fwrite]. Qed.
  #[using="RI_fds RI_fdupd"] Lemma msimS_s_diag' : forall k X d (R : rel StA StB), (forall sA moA sB moB, R sA moA sB moB -> RI k X sA moA sB moB) ->
    msimS R (io_diag ioA d) (io_diag ioB d) (fun _ _ => RI k X).
  Proof. intros k X d R HR. eapply msimS_conseq; [apply (msimS_s_diag k X d)| exact HR| intros ? ? ? ? ? ? [_ H]; exact H]. Qed.

  #[using="RI_fds RI_so RI_soupd RI_fdupd"] Lemma msimS_exit_k : forall k X {A B} code (Q : A -> B -> rel StA StB), msimS (RI k X) (exit_k ioA code) (exit_k ioB code) Q.
  Proof.
    intros k X A B code Q. unfold exit_k, exit_model. cbn [io_exit io_S].
    eapply msimS_bind with (Q1 := fun (a b : Empty_set) _ _ _ _ => False).
    - bindE k X; [apply msimS_stdout_exit_flush|]. intros _. apply msimS_exit.
    - intros a. destruct a.
  Qed.

  Definition rdI (kR : nat) (X : list (ptrA * ptrB)) (stA : rd_st (ptr:=ptrA)) (stB : rd_st (ptr:=ptrB)) : rel StA StB :=
    fun sA moA sB moB => rd_cap stA = rd_cap stB /\ rd_content stA = rd_content stB
      /\ (exists j, 16 <= j <= 26 /\ rd_cap stA = 2 ^ j /\ RI (jbud kR j) ((rd_buf stA, rd_buf stB) :: X) sA moA sB moB)
      /\ 0 <= zlength (rd_content stA) <= rd_cap stA /\ rd_cap stA <= MAX_INPUT.

  Definition RDQ (kR : nat) (X : list (ptrA * ptrB)) (a : rd_result (ptr:=ptrA)) (b : rd_result (ptr:=ptrB)) : rel StA StB :=
    fun sA moA sB moB => match a, b with
                         | RdExit, RdExit => exists k Y, RI k Y sA moA sB moB
                         | RdDone bA cA, RdDone bB cB => cA = cB /\ RI kR ((bA, bB) :: X) sA moA sB moB /\ 0 <= zlength cA <= MAX_INPUT
                         | _, _ => False
                         end.

  #[using="NMAX HNMAX RI_fds RI_fdupd RI_perm RI_weaken malloc_simS free_simS"] Lemma msimS_read_loop_body : forall kR X fd path stA stB,
    msimS (rdI kR X stA stB)
          (read_loop_body ioA mallocA freeA rsA fd path stA) (read_loop_body ioB mallocB freeB rsB fd path stB)
          (fun rA rB sA moA sB moB => match rA, rB with
                                     | inl xA, inl xB => rdI kR X xA xB sA moA sB moB
                                     | inr a, inr b => RDQ kR X a b sA moA sB moB
                                     | _, _ => False
                                     end).
  Proof.
    intros kR X fd path stA stB.
    apply (msimS_expose _ (rd_cap stA = rd_cap stB /\ rd_content stA = rd_content stB /\ (exists j, 16 <= j <= 26 /\ rd_cap stA = 2 ^ j)
                           /\ 0 <= zlength (rd_content stA) <= rd_cap stA /\ rd_cap stA <= MAX_INPUT));
      [intros sA moA sB moB (E1 & E2 & (j & Hj & Ej & _) & B); repeat split; auto; try lia; exists j; auto|].
    intros (ECAP & ECNT & (j & Hj & Ej) & B & C).
    assert (PRE : forall sA moA sB moB, rdI kR X stA stB sA moA sB moB -> RI (jbud kR j) ((rd_buf stA, rd_buf stB) :: X) sA moA sB moB).
    { intros sA moA sB moB (_ & _ & (j' & Hj' & Ej' & H) & _). replace j with j' ; [exact H|].
      apply (Z.pow_inj_r 2); [lia| lia| lia| rewrite <- Ej, <- Ej'; reflexivity]. }
    unfold read_loop_body. rewrite <- ECAP, <- ECNT.
    eapply msimS_bind with (Q1 := fun gA gB sA moA sB moB => match gA, gB with
                              | None, None => exists k Y, RI k Y sA moA sB moB
                              | Some st1, Some st2 => rd_cap st1 = rd_cap st2 /\ rd_content st1 = rd_content st2 /\
                                  (exists j1, 16 <= j1 <= 26 /\ rd_cap st1 = 2 ^ j1 /\ RI (jbud kR j1) ((rd_buf st1, rd_buf st2) :: X) sA moA sB moB)
                                  /\ rd_content st1 = rd_content stA /\ zlength (rd_content stA) < rd_cap st1 /\ rd_cap st1 <= MAX_INPUT
                              | _, _ => False end).
    { apply msimS_if; intros E.
      - apply msimS_if; intros E2.
        + eapply msimS_seq; [apply (msimS_s_diag' (jbud kR j) ((rd_buf stA, rd_buf stB) :: X)); exact PRE|].
          intros ? ?. apply msimS_ret. intros sA moA sB moB H. exists (jbud kR j), ((rd_buf stA, rd_buf stB) :: X). exact H.
        + apply Z.eqb_eq in E. apply Z.leb_gt in E2.
          pose proof (pow2_lt_26 j ltac:(lia) ltac:(rewrite <- Ej; exact E2)) as J26.
          assert (EB : jbud kR j = S (jbud kR (j + 1))) by (unfold jbud; lia).
          pose proof (pow2_double_le j _ ltac:(lia) Ej E2) as D2. unfold MAX_INPUT in D2, C.
          eapply msimS_bind; [eapply msimS_pre; [apply (malloc_simS (jbud kR (j + 1)) ((rd_buf stA, rd_buf stB) :: X) (rd_cap stA * 2)); lia| intros ? ? ? ? H; rewrite <- EB; exact (PRE _ _ _ _ H)]|].
          intros rA rB. apply msimS_expose with (phi := exists pA pB, rA = Some pA /\ rB = Some pB); [intros ? ? ? ? (pA & pB & EA & EB' & _); exists pA, pB; auto|].
          intros (pA & pB & -> & ->). cbn beta iota.
          eapply msimS_seq.
          { eapply msimS_pre; [apply (free_simS (jbud kR (j + 1)) ((pA, pB) :: X) (rd_buf stA) (rd_buf stB))|].
            intros ? ? ? ? (pA' & pB' & EA & EB' & H). injection EA as <-. injection EB' as <-. eapply RI_perm; [apply perm_swap| exact H]. }
          intros ? ?. apply msimS_ret. intros sA moA sB moB H. cbn [rd_buf rd_cap rd_content]. split; [reflexivity|]. split; [reflexivity|]. split.
          { exists (j + 1). split; [lia|]. split; [rewrite Ej, Z.pow_add_r by lia; lia| exact H]. }
          split; [reflexivity| unfold MAX_INPUT; lia].
      - apply msimS_ret. intros sA moA sB moB HI. pose proof HI as (_ & _ & JJ & _). apply Z.eqb_neq in E.
        split; [exact ECAP|]. split; [exact ECNT|]. split; [exact JJ|]. split; [reflexivity| lia]. }
    intros gA gB. destruct gA as [st1|]; destruct gB as [st2|]; cbn beta iota; [| apply msimS_false| apply msimS_false|].
    2:{ apply msimS_ret. intros sA moA sB moB H. exact H. }
    apply msimS_expose with (phi := rd_cap st1 = rd_cap st2 /\ rd_content st1 = rd_content st2 /\ (exists j1, 16 <= j1 <= 26 /\ rd_cap st1 = 2 ^ j1)
                                    /\ rd_content st1 = rd_content stA /\ zlength (rd_content stA) < rd_cap st1 /\ rd_cap st1 <= MAX_INPUT);
      [intros ? ? ? ? (E1 & E2 & (j1 & A1 & A2 & _) & H); split; [exact E1| split; [exact E2| split; [exists j1; auto| exact H]]]|].
    intros (ECAP1 & ECNT1 & (j1 & Hj1 & Ej1) & E1 & L1 & C1).
    assert (PRE1 : forall sA moA sB moB,
              (rd_cap st1 = rd_cap st2 /\ rd_content st1 = rd_content st2 /\
               (exists j0, 16 <= j0 <= 26 /\ rd_cap st1 = 2 ^ j0 /\ RI (jbud kR j0) ((rd_buf st1, rd_buf st2) :: X) sA moA sB moB) /\
               rd_content st1 = rd_content stA /\ zlength (rd_content stA) < rd_cap st1 /\ rd_cap st1 <= MAX_INPUT) ->
              RI (jbud kR j1) ((rd_buf st1, rd_buf st2) :: X) sA moA sB moB).
    { intros sA moA sB moB (_ & _ & (j' & Hj' & Ej' & H) & _). replace j1 with j'; [exact H|].
      apply (Z.pow_inj_r 2); [lia| lia| lia| rewrite <- Ej1, <- Ej'; reflexivity]. }
    apply (msimS_pre (RI (jbud kR j1) ((rd_buf st1, rd_buf st2) :: X))); [| exact PRE1].
    cbv zeta. rewrite <- ECAP1, <- ECNT1.
    eapply msimS_bind.
    { apply (msimS_read (jbud kR j1) ((rd_buf st1, rd_buf st2) :: X)); unfold READ_CHUNK; lia. }
    intros a b. apply msimS_expose with (phi := a = b /\ rd_len_ok (Z.min (rd_cap st1 - zlength (rd_content stA)) READ_CHUNK) a); [intros ? ? ? ? (H & _ & L); auto|]. intros [<- LOK].
    destruct a as [e|bs]; cbn beta iota.
    - eapply msimS_seq; [apply (msimS_s_diag' (jbud kR j1) ((rd_buf st1, rd_buf st2) :: X)); intros ? ? ? ? (_ & H & _); exact H|].
      intros ? ?. apply msimS_ret. intros sA moA sB moB H. exists (jbud kR j1), ((rd_buf st1, rd_buf st2) :: X). exact H.
    - apply msimS_if; intros Ebs; apply msimS_ret; intros sA moA sB moB (_ & H & _).
      + split; [reflexivity|]. split; [| rewrite E1; lia]. eapply RI_weaken_le; [| exact H]. unfold jbud. lia.
      + apply Nat.eqb_neq in Ebs. unfold rdI. cbn [rd_buf rd_cap rd_content]. split; [reflexivity|]. split; [reflexivity|]. split; [exists j1; auto|].
        cbn [rd_len_ok] in LOK. unfold READ_CHUNK in LOK. rewrite E1.
        assert (LEN' : zlength (rd_content stA ++ u8s_of_bytes bs) = zlength (rd_content stA) + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. lia. }
        rewrite LEN'. lia.
  Qed.

  #[using="NMAX HNMAX RI_fds RI_fdupd RI_perm RI_weaken malloc_simS free_simS"] Lemma msimS_read_all : forall kR X path,
    msimS (RI (S (jbud kR 16)) X) (read_all ioA mallocA freeA rsA path) (read_all ioB mallocB freeB rsB path) (RDQ kR X).
  Proof.
    intros kR X path. unfold read_all. set (k0 := S (jbud kR 16)).
    bindE k0 X; [apply msimS_fdnode; exact I|]. intros [e|fd]; cbn beta iota.
    { eapply msimS_seq; [apply (msimS_s_diag' k0 X); intros ? ? ? ? H; exact H|]. intros ? ?. apply msimS_ret. intros sA moA sB moB H. exists k0, X. exact H. }
    eapply msimS_bind; [apply (malloc_simS (jbud kR 16) X 65536); lia|]. intros rA rB.
    apply msimS_expose with (phi := exists pA pB, rA = Some pA /\ rB = Some pB); [intros ? ? ? ? (pA & pB & EA & EB & _); exists pA, pB; auto|].
    intros (bufA & bufB & -> & ->). cbn beta iota.
    eapply msimS_bind.
    { eapply msimS_pre; [apply (msimS_loop _ _ (rdI kR X) _ (msimS_read_loop_body kR X fd path))|].
      intros sA moA sB moB (pA' & pB' & EA & EB & H). injection EA as <-. injection EB as <-.
      unfold rdI. cbn [rd_buf rd_cap rd_content]. replace (zlength (@nil Z)) with 0 by reflexivity. unfold MAX_INPUT.
      split; [reflexivity|]. split; [reflexivity|]. split; [exists 16; split; [lia| split; [reflexivity| exact H]]| lia]. }
    intros rA rB'. destruct rA as [|bA cA]; destruct rB' as [|bB cB]; cbn beta iota; [| apply msimS_false| apply msimS_false|].
    - apply msimS_ret. intros sA moA sB moB H. exact H.
    - apply msimS_expose with (phi := cA = cB /\ 0 <= zlength cA <= MAX_INPUT); [intros ? ? ? ? (E & _ & B0); auto|]. intros [<- B0].
      eapply msimS_bind.
      { eapply msimS_pre; [apply (msimS_fdnode kR ((bA, bB) :: X) (NClose fd) dec_close I)| intros ? ? ? ? (_ & H & _); exact H]. }
      intros ? ?. apply msimS_ret. intros sA moA sB moB [_ H]. split; [reflexivity|]. split; [exact H| exact B0].
  Qed.

  Definition ap_rel (apA : at_parser (ptr:=ptrA)) (apB : at_parser (ptr:=ptrB)) : Prop :=
    ap_content apA = ap_content apB /\ ap_count apA = ap_count apB /\ ap_config_len apA = ap_config_len apB /\ ap_calls apA = ap_calls apB
    /\ match ap_owned apA, ap_owned apB with Some _, Some _ | None, None => True | _, _ => False end.

  Definition ap_pairs (apA : at_parser (ptr:=ptrA)) (apB : at_parser (ptr:=ptrB)) : list (ptrA * ptrB) :=
    match ap_owned apA, ap_owned apB with
    | Some pA, Some pB => [(pA, pB); (ap_buf apA, ap_buf apB)]
    | _, _ => [(ap_buf apA, ap_buf apB)]
    end.

  #[using="NMAX HNMAX RI_fds RI_so RI_soupd RI_fdupd RI_perm RI_weaken malloc_simS free_simS"] Theorem drv_pre_simS : forall k X argv,
    msimS (RI (DRV_BUDGET k) X) (drv_pre ioA mallocA freeA rsA argv) (drv_pre ioB mallocB freeB rsB argv)
          (fun apA apB sA moA sB moB => ap_rel apA apB /\ RI k (ap_pairs apA apB ++ X) sA moA sB moB).
  Proof.
    intros k X argv. unfold drv_pre, DRV_BUDGET. set (k1 := S (jbud (S k) 16)).
    assert (EK : S (S (jbud k 16)) = k1) by (unfold k1, jbud; lia). rewrite EK.
    apply msimS_if; intros E.
    { eapply msimS_seq; [apply (msimS_s_diag' k1 X); intros ? ? ? ? H; exact H|]. intros ? ?. apply msimS_exit_k. }
    eapply msimS_bind; [apply (msimS_read_all (S k) X)|]. intros rA rB.
    destruct rA as [|bufA content]; destruct rB as [|bufB contentB]; cbn beta iota; [| apply msimS_false| apply msimS_false|].
    { apply (msimS_pre (fun sA moA sB moB => exists kk Y, RI kk Y sA moA sB moB)); [| intros ? ? ? ? H; exact H].
      apply msimS_exI. intros kk. apply msimS_exI. intros Y. apply msimS_exit_k. }
    apply msimS_expose with (phi := content = contentB /\ 0 <= zlength content <= MAX_INPUT); [intros ? ? ? ? (E1 & _ & B); auto|]. intros [<- B].
    apply (msimS_pre (RI (S k) ((bufA, bufB) :: X))); [| intros ? ? ? ? (_ & H & _); exact H].
    apply msimS_if; intros E1.
    { eapply msimS_seq; [apply (msimS_s_diag' (S k) ((bufA, bufB) :: X)); intros ? ? ? ? H; exact H|]. intros ? ?.
      eapply msimS_seq; [apply (free_simS (S k) X bufA bufB)|]. intros ? ?. apply msimS_exit_k. }
    apply msimS_if; intros E2.
    { eapply msimS_seq; [apply (msimS_s_diag' (S k) ((bufA, bufB) :: X)); intros ? ? ? ? H; exact H|]. intros ? ?.
      eapply msimS_seq; [apply (free_simS (S k) X bufA bufB)|]. intros ? ?. apply msimS_exit_k. }
    apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. unfold HDR_MIN in *.
    eapply msimS_bind with (Q1 := fun cA cB sA moA sB moB => match cA, cB with
                              | Some (Some pA), Some (Some pB) => RI k ([(pA, pB); (bufA, bufB)] ++ X) sA moA sB moB
                              | Some None, Some None => RI k ([(bufA, bufB)] ++ X) sA moA sB moB
                              | _, _ => False end).
    { apply msimS_if; intros E3.
      - apply Z.ltb_lt in E3. unfold MAX_INPUT in B. pose proof (land15_range (le16 content)) as L15. eapply msimS_bind; [apply (malloc_simS k ((bufA, bufB) :: X)); lia|].
        intros rA' rB'. apply msimS_ret. intros sA moA sB moB (pA & pB & -> & -> & H). cbn. exact H.
      - apply msimS_ret. intros sA moA sB moB H. cbn. apply RI_weaken. exact H. }
    intros cA cB. destruct cA as [[pA|]|]; destruct cB as [[pB|]|]; cbn beta iota; try apply msimS_false;
      apply msimS_ret; intros sA moA sB moB H; (split; [repeat split; reflexivity| exact H]).
  Qed.

  #[using="NMAX HNMAX RI_fds RI_so RI_soupd RI_fdupd RI_perm RI_weaken malloc_simS free_simS"] Theorem drv_pre_tshape_incl0 : forall k X argv sA moA sB moB
      (KA : exc (at_parser (ptr:=ptrA) * StA) -> Model -> TSet) (KB : exc (at_parser (ptr:=ptrB) * StB) -> Model -> TSet),
    RI (DRV_BUDGET k) X sA moA sB moB ->
    (forall apA sA' moA' apB sB' moB', ap_rel apA apB -> RI k (ap_pairs apA apB ++ X) sA' moA' sB' moB' ->
       t_incl0 (KA (Ok (apA, sA')) moA') (KB (Ok (apB, sB')) moB')) ->
    (forall moA' moB', t_incl0 (KA Unr moA') (KB Unr moB')) ->
    t_incl0 (tsh (drv_pre ioA mallocA freeA rsA argv sA) moA KA) (tsh (drv_pre ioB mallocB freeB rsB argv sB) moB KB).
  Proof.
    intros k X argv sA moA sB moB KA KB HR HK HU.
    eapply (msimS_tshape _ _ _ _ KA KB sA moA sB moB (drv_pre_simS k X argv) HR); [| exact HU].
    intros a sA' moA' b sB' moB' [HA H]. apply HK; assumption.
  Qed.
End DSS.
