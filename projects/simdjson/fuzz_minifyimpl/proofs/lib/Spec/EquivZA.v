(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad MSafe MPaths STree Stdio HarnessM Adapter Driver
  StepB EquivShared EquivProg RSim RSimProg MI_Inv LB_Inv LB_Sum SizeHist Prog ProgA ProgZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Definition init_fds : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

(* [comment removed for export] *)
Definition PhiZ : node -> Model -> Prop := fun _ _ => True.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ASide.
Variable A : AAlloc.
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.
Variable Phi2 : node -> Model -> Prop.
Variable MI2 : Model -> Prop.
(* [comment removed for export] *)
Variables (rsZ rsA : Z).

Local Notation STOT2 := (STOT (St:=ASt A) step2 (fun R0 => texit (R:=R0) step2 nexit)).

Record AAllocOK : Type := mkAAllocOK {
  (* [comment removed for export] *)
  ok_sub2 : forall n mo r mo' e, ~ nf_node n -> step2 n mo r mo' e -> nstep n mo r mo' e;
  ok_same2 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> step2 n mo r mo e;
  ok_io2 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> step2 n mo r mo' e;
  (* [comment removed for export] *)
  ok_MI2 : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> MI2 mo -> m_halted mo = None -> MI2 mo' /\ m_halted mo' = None;
  (* [comment removed for export] *)
  ok_get_set : forall v s, a_so A (a_set_so A v s) = v;
  ok_set_set : forall v w s, a_set_so A v (a_set_so A w s) = a_set_so A v s;
  ok_set_get : forall s, a_set_so A (a_so A s) s = s;
  ok_addr_so : forall v s p, aptr_addr A (a_set_so A v s) p = aptr_addr A s p;
  (* [comment removed for export] *)
  ok_cl_get_set : forall v s, a_cl A (a_set_cl A v s) = v;
  ok_cl_so : forall v s, a_cl A (a_set_so A v s) = a_cl A s;
  ok_so_cl : forall v s, a_so A (a_set_cl A v s) = a_so A s;
  (* [comment removed for export] *)
  AI : list (aptr A * Z) -> ASt A -> Model -> Prop;
  ok_AI_perm : forall Y Y' s mo, Permutation Y Y' -> AI Y s mo -> AI Y' s mo;
  ok_AI_so : forall Y s mo v, AI Y s mo -> AI Y (a_set_so A v s) mo;
  ok_AI_cl : forall Y s mo v, AI Y s mo -> AI Y (a_set_cl A v s) mo;
  ok_AI_model : forall Y s mo, AI Y s mo -> MI2 mo /\ m_halted mo = None;
  ok_AI_fds : forall Y s mo f, AI Y s mo -> MI2 (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI Y s (with_fds f mo);
  (* [comment removed for export] *)
  ok_malloc : forall Y n s mo, AI Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
      tglob step2 Phi2 (amalloc A n s) mo ->
      STOT2 (amalloc A n s) mo
            (fun r s' mo' => exists q, r = Some q /\ AI ((q, n) :: Y) s' mo' /\ n < 2^63
                             /\ a_so A s' = a_so A s /\ a_cl A s' = a_cl A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo);
  ok_free : forall Y q n s mo, AI ((q, n) :: Y) s mo ->
      tglob step2 Phi2 (afree A q s) mo ->
      STOT2 (afree A q s) mo
            (fun _ s' mo' => AI Y s' mo' /\ a_so A s' = a_so A s /\ a_cl A s' = a_cl A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo);
  ok_annot : forall Y q cap old new s mo, AI Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
      (old = 0 \/ new = 0) ->
      tglob step2 Phi2 (aannot A q cap old new s) mo ->
      STOT2 (aannot A q cap old new s) mo
            (fun _ s' mo' => AI Y s' mo' /\ a_so A s' = a_so A s /\ a_cl A s' = a_cl A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo)
}.

Variable K : AAllocOK.

(* [comment removed for export] *)
Definition AHAND (inp : ProcInput) (sA0 : ASt A) (moA0 : Model) : Prop :=
  AI K [] sA0 moA0 /\ a_so A sA0 = stdout_init /\ a_cl A sA0 = None /\ m_fds moA0 = init_fds /\ m_fs moA0 = in_fs inp
  /\ tglob step2 Phi2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation rel := (rel ZSt (ASt A)).
Local Notation rsim := (rsim nstep step2 nexit nexit PhiZ Phi2).
Local Notation triple := (unit * aptr A * Z)%type.

Definition aX (X : list triple) : list (aptr A * Z) := map (fun b => (snd (fst b), snd b)) X.
(* [comment removed for export] *)
Definition clb (s2 : ASt A) : list (aptr A * Z) :=
  match a_cl A s2 with Some q => [(q, CLIENT_VEC_BYTES)] | None => [] end.

Definition RX (X : list triple) : rel := fun s1 mo1 s2 mo2 =>
  minv mo1 /\ m_halted mo1 = None /\ AI K (clb s2 ++ aX X) s2 mo2 /\ z_so s1 = a_so A s2
  /\ (z_cl s1 = None <-> a_cl A s2 = None) /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.

Lemma aX_app X Y : aX (X ++ Y) = aX X ++ aX Y. Proof. apply map_app. Qed.
Lemma sizes_aX X : map snd (aX X) = map snd X. Proof. unfold aX. rewrite map_map. reflexivity. Qed.
Lemma length_clb s2 : (length (clb s2) <= 1)%nat. Proof. unfold clb. destruct (a_cl A s2); cbn; lia. Qed.
Lemma clb_eq s2 s2' : a_cl A s2' = a_cl A s2 -> clb s2' = clb s2. Proof. unfold clb. intros ->. reflexivity. Qed.

Lemma RX_perm : forall X Y s1 mo1 s2 mo2, Permutation X Y -> RX X s1 mo1 s2 mo2 -> RX Y s1 mo1 s2 mo2.
Proof.
  intros X Y s1 mo1 s2 mo2 HP (M1 & H1 & HA & Hrest). split; [exact M1|]. split; [exact H1|]. split; [| exact Hrest].
  eapply (ok_AI_perm K); [| exact HA]. apply Permutation_app_head. unfold aX. apply Permutation_map. exact HP.
Qed.

Lemma RX_get : forall X s1 mo1 s2 mo2, RX X s1 mo1 s2 mo2 -> z_so s1 = a_so A s2.
Proof. intros X s1 mo1 s2 mo2 (_ & _ & _ & H & _). exact H. Qed.

Lemma RX_set : forall X s1 mo1 s2 mo2 v, RX X s1 mo1 s2 mo2 -> RX X (z_set_so v s1) mo1 (a_set_so A v s2) mo2.
Proof.
  intros X s1 mo1 s2 mo2 v (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs).
  split; [exact M1|]. split; [exact H1|]. split; [| split; [| split; [| split; [exact Hfd| exact Hfs]]]].
  - rewrite (clb_eq s2 (a_set_so A v s2)) by apply (ok_cl_so K). apply (ok_AI_so K). exact HA.
  - rewrite (ok_get_set K). reflexivity.
  - rewrite (ok_cl_so K). cbn [z_cl z_set_so]. exact Hcl.
Qed.

Lemma RX_models : forall X s1 mo1 s2 mo2, RX X s1 mo1 s2 mo2 ->
  minv mo1 /\ MI2 mo2 /\ m_halted mo1 = None /\ m_halted mo2 = None /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
Proof.
  intros X s1 mo1 s2 mo2 (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs). destruct (ok_AI_model K _ _ _ HA) as [M2 H2]. splits; auto.
Qed.

Lemma RX_tables : forall X s1 mo1 s2 mo2 f, RX X s1 mo1 s2 mo2 ->
  minv (with_fds f mo1) -> MI2 (with_fds f mo2) -> m_halted (with_fds f mo1) = None -> m_halted (with_fds f mo2) = None ->
  RX X s1 (with_fds f mo1) s2 (with_fds f mo2).
Proof.
  intros X s1 mo1 s2 mo2 f (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs) M1' M2' H1' H2'. unfold RX. splits; auto.
  apply (ok_AI_fds K); auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma HISTOK_amb3 n (L : list Z) : (length L <= 3)%nat -> HISTOK (n :: L).
Proof. intros HL. apply (HISTOK_amb n [] L); [apply Forall_nil| unfold BCs, zsum; cbn; unfold HB; lia| unfold N4s, N24s, zcount, zlen; cbn; lia| exact HL]. Qed.

Lemma malloc_pair : forall X n, 0 <= n <= REQMAX -> (length X <= 2)%nat -> HISTOK (n :: map snd X) ->
  rsim (RX X) (amalloc AAllocZ n) (amalloc A n) (Qm RX X n).
Proof.
  intros X n Hn HL _. apply rsim_silent. intros s1 mo1 s2 mo2 (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs) G1 G2.
  eexists _, _. split; [| split].
  - cbn [amalloc AAllocZ]. unfold zmalloc. apply STOT_ret.
  - apply (ok_malloc K (clb s2 ++ aX X) n s2 mo2 HA Hn); [| exact G2].
    apply HISTOK_amb3. rewrite length_map, length_app. pose proof (length_clb s2). unfold aX. rewrite length_map. lia.
  - intros a s1' mo1' b s2' mo2' (-> & -> & ->) (q & -> & HA' & Hn63 & Hso2 & Hcl2 & Hfd2 & Hfs2). cbn [Qm].
    split; [| exact Hn63]. unfold RX. splits; auto; try congruence; try (rewrite Hcl2; exact Hcl).
    rewrite (clb_eq s2 s2' Hcl2). eapply (ok_AI_perm K); [| exact HA']. cbn [aX map fst snd]. apply Permutation_middle.
Qed.

Lemma free_pair : forall X p q n, rsim (RX ((p, q, n) :: X)) (afree AAllocZ p) (afree A q) (fun _ _ => RX X).
Proof.
  intros X p q n. apply rsim_silent. intros s1 mo1 s2 mo2 (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs) G1 G2.
  assert (HA0 : AI K ((q, n) :: clb s2 ++ aX X) s2 mo2).
  { eapply (ok_AI_perm K); [| exact HA]. cbn [aX map fst snd]. apply Permutation_sym, Permutation_middle. }
  eexists _, _. split; [| split].
  - cbn [afree AAllocZ]. unfold zfree. apply STOT_ret.
  - apply (ok_free K (clb s2 ++ aX X) q n s2 mo2 HA0 G2).
  - intros a s1' mo1' b s2' mo2' (-> & -> & ->) (HA' & Hso2 & Hcl2 & Hfd2 & Hfs2).
    unfold RX. splits; auto; try congruence; try (rewrite Hcl2; exact Hcl).
    rewrite (clb_eq s2 s2' Hcl2). exact HA'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation cinitZ := (HarnessM.client_init (amalloc AAllocZ) (new_handlerA AAllocZ) (a_cl AAllocZ) (a_set_cl AAllocZ)).
Local Notation cinitA := (HarnessM.client_init (amalloc A) (new_handlerA A) (a_cl A) (a_set_cl A)).

Lemma cinit_some_Z : forall s u, z_cl s = Some u -> cinitZ s = mret tt s.
Proof. intros s u H. unfold HarnessM.client_init, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cinit_none_Z : forall s, z_cl s = None -> cinitZ s = mret tt (z_set_cl (Some tt) s).
Proof. intros s H. unfold HarnessM.client_init, HarnessM.opnew, mbind, mget, mret, mupd. cbn. rewrite H. reflexivity. Qed.
Lemma cinit_some_A : forall s q, a_cl A s = Some q -> cinitA s = mret tt s.
Proof. intros s q H. unfold HarnessM.client_init, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cinit_none_A : forall s, a_cl A s = None ->
  cinitA s = (p <- HarnessM.opnew (amalloc A) (new_handlerA A) CLIENT_VEC_BYTES ;; mupd (a_set_cl A (Some p))) s.
Proof. intros s H. unfold HarnessM.client_init, mbind, mget. cbn. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma opnew8_STOT : forall Y s mo, AI K Y s mo -> (length Y <= 3)%nat ->
  tglob step2 Phi2 (HarnessM.opnew (amalloc A) (new_handlerA A) CLIENT_VEC_BYTES s) mo ->
  STOT2 (HarnessM.opnew (amalloc A) (new_handlerA A) CLIENT_VEC_BYTES s) mo
        (fun q s' mo' => AI K ((q, CLIENT_VEC_BYTES) :: Y) s' mo' /\ a_so A s' = a_so A s /\ a_cl A s' = a_cl A s
                         /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y s mo HA HL G. unfold HarnessM.opnew in *. change (CLIENT_VEC_BYTES =? 0) with false in *. cbn iota in *.
  eapply STOT_bind.
  - apply STOT_path. apply (ok_malloc K Y CLIENT_VEC_BYTES s mo HA); [unfold CLIENT_VEC_BYTES, REQMAX; lia| apply HISTOK_amb3; rewrite length_map; exact HL|].
    exact (tglob_ebind_l _ _ _ _ _ G).
  - intros r s' mo' ((q & -> & HA' & _ & Hso & Hcl & Hfd & Hfs) & _). cbn beta iota.
    eapply STOT_mono; [apply STOT_ret|]. intros q' s'' mo'' (-> & -> & ->). splits; auto.
Qed.

Lemma cinit_pair : forall X, (length X <= 2)%nat -> rsim (RX X) cinitZ cinitA (fun _ _ => RX X).
Proof.
  intros X HL. apply rsim_silent. intros s1 mo1 s2 mo2 (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs) G1 G2.
  destruct (a_cl A s2) as [q|] eqn:E2.
  - (* [comment removed for export] *)
    destruct (z_cl s1) as [u|] eqn:E1; [| exfalso; pose proof (proj1 Hcl eq_refl); discriminate].
    rewrite (cinit_some_Z s1 u E1). rewrite (cinit_some_A s2 q E2).
    eexists _, _. split; [apply STOT_ret| split; [apply STOT_ret|]].
    intros a s1' mo1' b s2' mo2' (-> & -> & ->) (-> & -> & ->). unfold RX. splits; auto. rewrite E1, E2. exact Hcl.
  - assert (E1 : z_cl s1 = None) by (apply (proj2 Hcl); reflexivity).
    rewrite (cinit_none_Z s1 E1). rewrite (cinit_none_A s2 E2) in G2 |- *.
    assert (HA0 : AI K (aX X) s2 mo2) by (unfold clb in HA; rewrite E2 in HA; exact HA).
    eexists _, _. split; [apply STOT_ret| split].
    + eapply STOT_bind.
      * apply STOT_path. apply (opnew8_STOT (aX X) s2 mo2 HA0); [unfold aX; rewrite length_map; lia|]. exact (tglob_ebind_l _ _ _ _ _ G2).
      * intros p s' mo' ((HA' & Hso' & Hcl' & Hfd' & Hfs') & _). cbn beta.
        eapply STOT_mono; [apply STOT_upd|]. intros [] s'' mo'' (-> & ->).
        instantiate (1 := fun _ s'' mo'' => exists p s', s'' = a_set_cl A (Some p) s' /\ AI K ((p, CLIENT_VEC_BYTES) :: aX X) s' mo''
                                                   /\ a_so A s' = a_so A s2 /\ m_fds mo'' = m_fds mo2 /\ m_fs mo'' = m_fs mo2).
        cbn beta. exists p, s'. splits; auto.
    + intros a s1' mo1' b s2' mo2' (-> & -> & ->) (p & s' & -> & HA' & Hso' & Hfd' & Hfs').
      unfold RX. splits; auto; try congruence;
        try (rewrite (ok_so_cl K); cbn; congruence); try (rewrite (ok_cl_get_set K); cbn; split; intros; discriminate).
      unfold clb. rewrite (ok_cl_get_set K). cbn [app]. apply (ok_AI_cl K). exact HA'.
Qed.

Local Notation cexitZ := (HarnessM.client_exit (afree AAllocZ) (a_cl AAllocZ) (a_set_cl AAllocZ)).
Local Notation cexitA := (HarnessM.client_exit (afree A) (a_cl A) (a_set_cl A)).

Lemma cexit_none_Z : forall s, z_cl s = None -> cexitZ s = mret tt s.
Proof. intros s H. unfold HarnessM.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cexit_some_Z : forall s u, z_cl s = Some u -> cexitZ s = mret tt (z_set_cl None s).
Proof. intros s u H. unfold HarnessM.client_exit, HarnessM.opdelete, mbind, mget, mret, mupd. cbn. rewrite H. reflexivity. Qed.
Lemma cexit_none_A : forall s, a_cl A s = None -> cexitA s = mret tt s.
Proof. intros s H. unfold HarnessM.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cexit_some_A : forall s q, a_cl A s = Some q -> cexitA s = (HarnessM.opdelete (afree A) q ;;; mupd (a_set_cl A None)) s.
Proof. intros s q H. unfold HarnessM.client_exit, mbind, mget. cbn. rewrite H. reflexivity. Qed.

Lemma cexit_pair : forall X, rsim (RX X) cexitZ cexitA (fun _ _ => RX X).
Proof.
  intros X. apply rsim_silent. intros s1 mo1 s2 mo2 (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs) G1 G2.
  destruct (a_cl A s2) as [q|] eqn:E2.
  - destruct (z_cl s1) as [u|] eqn:E1; [| exfalso; pose proof (proj1 Hcl eq_refl); discriminate].
    rewrite (cexit_some_Z s1 u E1). rewrite (cexit_some_A s2 q E2) in G2 |- *.
    assert (HA0 : AI K ((q, CLIENT_VEC_BYTES) :: aX X) s2 mo2) by (unfold clb in HA; rewrite E2 in HA; exact HA).
    eexists _, _. split; [apply STOT_ret| split].
    + eapply STOT_bind.
      * apply STOT_path. unfold HarnessM.opdelete. apply (ok_free K (aX X) q CLIENT_VEC_BYTES s2 mo2 HA0). exact (tglob_ebind_l _ _ _ _ _ G2).
      * intros [] s' mo' ((HA' & Hso' & Hcl' & Hfd' & Hfs') & _). cbn beta.
        eapply STOT_mono; [apply STOT_upd|]. intros [] s'' mo'' (-> & ->).
        instantiate (1 := fun _ s'' mo'' => exists s', s'' = a_set_cl A None s' /\ AI K (aX X) s' mo''
                                                 /\ a_so A s' = a_so A s2 /\ m_fds mo'' = m_fds mo2 /\ m_fs mo'' = m_fs mo2).
        cbn beta. exists s'. splits; auto.
    + intros a s1' mo1' b s2' mo2' (-> & -> & ->) (s' & -> & HA' & Hso' & Hfd' & Hfs').
      unfold RX. splits; auto; try congruence;
        try (rewrite (ok_so_cl K); cbn; congruence); try (rewrite (ok_cl_get_set K); cbn; split; reflexivity).
      unfold clb. rewrite (ok_cl_get_set K). cbn [app]. apply (ok_AI_cl K). exact HA'.
  - assert (E1 : z_cl s1 = None) by (apply (proj2 Hcl); reflexivity).
    rewrite (cexit_none_Z s1 E1). rewrite (cexit_none_A s2 E2).
    eexists _, _. split; [apply STOT_ret| split; [apply STOT_ret|]].
    intros a s1' mo1' b s2' mo2' (-> & -> & ->) (-> & -> & ->). unfold RX. splits; auto. rewrite E1, E2. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sub1 : forall n mo r mo' e, ~ nf_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma same1 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstep n mo r mo e. Proof. auto. Qed.
Lemma io1 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> minv mo -> m_halted mo = None -> minv mo' /\ m_halted mo' = None.
Proof. intros n mo rsp mo' evs Hst _ Hmi Hh. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi']. auto. Qed.

Local Notation rsimeq := (rsimeq nstep step2 PhiZ Phi2).
Local Notation ioZ := (ioA AAllocZ).

Lemma diag_pair : forall X d, diag_short d -> rsimeq (RX X) (io_diag ioZ d) (io_diag (ioA A) d) (fun _ => RX X).
Proof. intros X d _. cbn [ioA io_diag io_S]. apply (s_diag_sim nstep step2 PhiZ Phi2 sub1 same1 (ok_sub2 K) (ok_same2 K)). Qed.

Lemma emit_pair : forall X v, rsimeq (RX X) (io_emit ioZ v) (io_emit (ioA A) v) (fun _ => RX X).
Proof.
  intros X v. cbn [ioA io_emit io_S].
  apply (s_emit_sim nstep step2 PhiZ Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) z_so z_set_so (a_so A) (a_set_so A) (RX X) (RX_get X) (RX_set X)).
Qed.

Lemma ioexit_pair : forall X, rsimeq (RX X) (io_exit ioZ) (io_exit (ioA A)) (fun _ => RX X).
Proof.
  intros X. cbn [ioA io_exit io_S].
  apply (stdout_exit_flush_sim nstep step2 PhiZ Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) z_so z_set_so (a_so A) (a_set_so A) (RX X) (RX_get X) (RX_set X)).
Qed.

Lemma exitnode_pair : forall X c (Q : Empty_set -> Empty_set -> rel), rsim (RX X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof. intros X c Q. apply (exit_node_sim nstep step2 PhiZ Phi2 sub1 (ok_sub2 K) minv MI2 (RX X) (RX_models X)). Qed.

Lemma open_pair : forall X path, rsimeq (RX X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => RX X).
Proof. intros X path. apply (open_sim nstep step2 PhiZ Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX X) (RX_models X) (RX_tables X)). Qed.
Lemma close_pair : forall X fd, rsimeq (RX X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => RX X).
Proof. intros X fd. apply (close_sim nstep step2 PhiZ Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX X) (RX_models X) (RX_tables X)). Qed.
Lemma read_pair : forall X fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
  rsimeq (RX X) (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
         (fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => RX X s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => RX X end).
Proof. intros X fd buf1 buf2 cnt Hcnt. apply (read_sim nstep step2 PhiZ Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX X) (RX_models X) (RX_tables X)). exact Hcnt. Qed.

(* [comment removed for export] *)
Lemma malloc_pair_h : forall X n, 0 <= n <= REQMAX -> (forall s2, HISTOK (n :: map snd (clb s2 ++ aX X))) ->
  rsim (RX X) (amalloc AAllocZ n) (amalloc A n) (Qm RX X n).
Proof.
  intros X n Hn HH. apply rsim_silent. intros s1 mo1 s2 mo2 (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs) G1 G2.
  eexists _, _. split; [| split].
  - cbn [amalloc AAllocZ]. unfold zmalloc. apply STOT_ret.
  - apply (ok_malloc K (clb s2 ++ aX X) n s2 mo2 HA Hn); [apply HH | exact G2].
  - intros a s1' mo1' b s2' mo2' (-> & -> & ->) (q & -> & HA' & Hn63 & Hso2 & Hcl2 & Hfd2 & Hfs2). cbn [Qm].
    split; [| exact Hn63]. unfold RX. splits; auto; try congruence; try (rewrite Hcl2; exact Hcl).
    rewrite (clb_eq s2 s2' Hcl2). eapply (ok_AI_perm K); [| exact HA']. cbn [aX map fst snd]. apply Permutation_middle.
Qed.

Lemma opnew_pair_h : forall X n, 0 < n <= REQMAX -> (forall s2, HISTOK (n :: map snd (clb s2 ++ aX X))) ->
  rsim (RX X) (HarnessM.opnew (amalloc AAllocZ) (new_handlerA AAllocZ) n) (HarnessM.opnew (amalloc A) (new_handlerA A) n) (fun p q => RX ((p, q, n) :: X)).
Proof.
  intros X n Hn HH. unfold HarnessM.opnew. replace (if n =? 0 then 1 else n) with n by (destruct (Z.eqb_spec n 0); lia).
  eapply rsim_bind; [apply malloc_pair_h; [lia| exact HH]|].
  intros [p|] [q|]; cbn beta iota; [| apply rsim_false| apply rsim_false|].
  - apply rsim_drop. apply rsim_ret. intros ? ? ? ? HH0. exact HH0.
  - unfold new_handlerA. eapply rsim_bind; [apply rsim_munr with (Q := fun _ _ _ _ _ _ => False)|]. intros [].
Qed.

Lemma sizes_clb : forall s2, map snd (clb s2) = [] \/ map snd (clb s2) = [CLIENT_VEC_BYTES].
Proof. intros s2. unfold clb. destruct (a_cl A s2); cbn; auto. Qed.
Lemma itemsz_8 : itemsz CLIENT_VEC_BYTES. Proof. right. exists 1. unfold CLIENT_VEC_BYTES. lia. Qed.
Lemma itemsz_56 : itemsz ERRSTR_BYTES. Proof. right. exists 13. unfold ERRSTR_BYTES. lia. Qed.

(* [comment removed for export] *)
Lemma HISTOK_client : forall n (c t Zs : list Z), (c = [] \/ c = [CLIENT_VEC_BYTES]) -> (t = [] \/ t = [ERRSTR_BYTES]) -> (length Zs <= 3)%nat ->
  forall M, Permutation M (n :: c ++ t ++ Zs) -> HISTOK M.
Proof.
  intros n c t Zs Hc Ht HL M HP. apply (HISTOK_intro (c ++ t) (n :: Zs)).
  - etransitivity; [exact HP|]. rewrite app_assoc. apply Permutation_middle.
  - apply YWs_app. unfold YWs. split; [destruct Hc as [->| ->]; [apply Forall_nil| apply Forall_cons; [apply itemsz_8| apply Forall_nil]] | destruct Ht as [->| ->]; [apply Forall_nil| apply Forall_cons; [apply itemsz_56| apply Forall_nil]]].
  - destruct Hc as [->| ->]; destruct Ht as [->| ->]; vm_compute; intros; discriminate.
  - destruct Hc as [->| ->]; destruct Ht as [->| ->]; vm_compute; intros; discriminate.
  - cbn [length]. lia.
Qed.
(* [comment removed for export] *)
Lemma HISTOK_client_str : forall (c Zs : list Z), (c = [] \/ c = [CLIENT_VEC_BYTES]) -> (length Zs <= 4)%nat ->
  forall M, Permutation M (ERRSTR_BYTES :: c ++ Zs) -> HISTOK M.
Proof.
  intros c Zs Hc HL M HP. apply (HISTOK_intro (ERRSTR_BYTES :: c) Zs); [exact HP| | | | exact HL].
  - unfold YWs. apply Forall_cons; [apply itemsz_56| destruct Hc as [->| ->]; [apply Forall_nil| apply Forall_cons; [apply itemsz_8| apply Forall_nil]]].
  - destruct Hc as [->| ->]; vm_compute; intros; discriminate.
  - destruct Hc as [->| ->]; vm_compute; intros; discriminate.
Qed.

Local Notation odelZ := (HarnessM.odelete (afree AAllocZ)).
Local Notation odelA := (HarnessM.odelete (afree A)).
(* [comment removed for export] *)
Definition obuf (b1 : option unit) (b2 : option (aptr A)) (n : Z) (X : list triple) : rel :=
  match b1, b2 with
  | Some p, Some q => RX ((p, q, n) :: X)
  | None, None => RX X
  | _, _ => fun _ _ _ _ => False
  end.
Lemma odelete_pair : forall X n b1 b2, rsim (obuf b1 b2 n X) (odelZ b1) (odelA b2) (fun _ _ => RX X).
Proof.
  intros X n [p|] [q|]; cbn [obuf HarnessM.odelete]; [apply free_pair| apply rsim_false| apply rsim_false|].
  apply rsim_ret. intros ? ? ? ? H. exact H.
Qed.

Lemma minify_pair : forall X data, (length X <= 2)%nat -> zlength data <= MAX_INPUT ->
  rsim (RX X) (HarnessM.minify_call (amalloc AAllocZ) (afree AAllocZ) (new_handlerA AAllocZ) data)
              (HarnessM.minify_call (amalloc A) (afree A) (new_handlerA A) data) (fun _ _ => RX X).
Proof.
  intros X data HL Hd. unfold HarnessM.minify_call.
  assert (Hn : Z.of_nat (length data) <= MAX_INPUT) by (unfold zlength in Hd; exact Hd).
  set (n := Z.of_nat (length data)) in *.
  assert (HLX : forall s2 : ASt A, (length (map snd (aX X)) <= 2)%nat) by (intros _; unfold aX; rewrite !length_map; exact HL).
  (* [comment removed for export] *)
  eapply rsim_bind with (Q1 := fun b1 b2 => obuf b1 b2 n X).
  { destruct (Z.eqb_spec n 0) as [E|E].
    - apply rsim_ret. intros ? ? ? ? H. exact H.
    - eapply rsim_bind; [apply (opnew_pair_h X n)|].
      + unfold MAX_INPUT, REQMAX in *. lia.
      + intros s2. rewrite map_app. eapply (HISTOK_client n (map snd (clb s2)) [] (map snd (aX X))); [apply sizes_clb| left; reflexivity| (pose proof (HLX s2); lia) | reflexivity].
      + intros p q. apply rsim_ret. intros ? ? ? ? H. exact H. }
  intros b1 b2. apply rsim_if; intros _; [| apply odelete_pair].
  destruct b1 as [p|], b2 as [q|]; cbn [obuf]; try apply rsim_false.
  - (* [comment removed for export] *)
    eapply rsim_bind; [apply (opnew_pair_h ((p, q, n) :: X) ERRSTR_BYTES)|].
    + unfold ERRSTR_BYTES, REQMAX. lia.
    + intros s2. rewrite map_app. cbn [aX map snd fst]. eapply (HISTOK_client_str (map snd (clb s2)) (n :: map snd (aX X))); [apply sizes_clb| (cbn [length]; pose proof (HLX s2); lia)| reflexivity].
    + intros tp tq. cbn beta.
      eapply rsim_bind with (Q1 := fun b1' b2' s1 mo1 s2 mo2 => exists m, obuf b1' b2' m ((tp, tq, ERRSTR_BYTES) :: X) s1 mo1 s2 mo2).
      { apply rsim_if; intros _.
        - apply rsim_ret. intros ? ? ? ? H. exists n. cbn [obuf]. eapply RX_perm; [apply perm_swap| exact H].
        - eapply rsim_seq; [eapply rsim_pre; [apply (free_pair ((tp, tq, ERRSTR_BYTES) :: X) p q n)|]; intros ? ? ? ? H; eapply RX_perm; [apply perm_swap| exact H]|].
          intros [] []. eapply rsim_bind; [apply (opnew_pair_h ((tp, tq, ERRSTR_BYTES) :: X) ERRMSG_LEN)|].
          + unfold ERRMSG_LEN, REQMAX. lia.
          + intros s2. rewrite map_app. cbn [aX map snd fst].
            eapply (HISTOK_client ERRMSG_LEN (map snd (clb s2)) [ERRSTR_BYTES] (map snd (aX X))); [apply sizes_clb| right; reflexivity| (pose proof (HLX s2); lia)| reflexivity].
          + intros p' q'. apply rsim_ret. intros ? ? ? ? H. exists ERRMSG_LEN. cbn [obuf]. exact H. }
      intros b1' b2'. cbn beta.
      (* [comment removed for export] *)
      destruct b1' as [p'|], b2' as [q'|]; try (apply rsim_pre with (R := fun _ _ _ _ => False); [apply rsim_false| intros ? ? ? ? [m H]; exact H]).
      * apply rsim_exI. intros m. cbn [obuf].
        eapply rsim_seq; [eapply rsim_pre; [apply (free_pair ((p', q', m) :: X) tp tq ERRSTR_BYTES)|]; intros ? ? ? ? H; eapply RX_perm; [apply perm_swap| exact H]|].
        intros [] []. apply (odelete_pair X m (Some p') (Some q')).
      * apply rsim_exI. intros m. cbn [obuf].
        eapply rsim_seq; [apply (free_pair X tp tq ERRSTR_BYTES)|]. intros [] []. apply (odelete_pair X m None None).
  - (* [comment removed for export] *)
    eapply rsim_bind; [apply (opnew_pair_h X ERRSTR_BYTES)|].
    + unfold ERRSTR_BYTES, REQMAX. lia.
    + intros s2. rewrite map_app. eapply (HISTOK_client_str (map snd (clb s2)) (map snd (aX X))); [apply sizes_clb| (pose proof (HLX s2); lia)| reflexivity].
    + intros tp tq. cbn beta.
      eapply rsim_bind with (Q1 := fun b1' b2' s1 mo1 s2 mo2 => exists m, obuf b1' b2' m ((tp, tq, ERRSTR_BYTES) :: X) s1 mo1 s2 mo2).
      { apply rsim_if; intros _.
        - apply rsim_ret. intros ? ? ? ? H. exists n. cbn [obuf]. exact H.
        - cbn [HarnessM.odelete]. eapply rsim_seq; [apply rsim_ret; intros ? ? ? ? H; exact H|].
          intros [] []. eapply rsim_bind; [apply (opnew_pair_h ((tp, tq, ERRSTR_BYTES) :: X) ERRMSG_LEN)|].
          + unfold ERRMSG_LEN, REQMAX. lia.
          + intros s2. rewrite map_app. cbn [aX map snd fst].
            eapply (HISTOK_client ERRMSG_LEN (map snd (clb s2)) [ERRSTR_BYTES] (map snd (aX X))); [apply sizes_clb| right; reflexivity| (pose proof (HLX s2); lia)| reflexivity].
          + intros p' q'. apply rsim_ret. intros ? ? ? ? H. exists ERRMSG_LEN. cbn [obuf]. exact H. }
      intros b1' b2'. cbn beta.
      destruct b1' as [p'|], b2' as [q'|]; try (apply rsim_pre with (R := fun _ _ _ _ => False); [apply rsim_false| intros ? ? ? ? [m H]; exact H]).
      * apply rsim_exI. intros m. cbn [obuf].
        eapply rsim_seq; [eapply rsim_pre; [apply (free_pair ((p', q', m) :: X) tp tq ERRSTR_BYTES)|]; intros ? ? ? ? H; eapply RX_perm; [apply perm_swap| exact H]|].
        intros [] []. apply (odelete_pair X m (Some p') (Some q')).
      * apply rsim_exI. intros m. cbn [obuf].
        eapply rsim_seq; [apply (free_pair X tp tq ERRSTR_BYTES)|]. intros [] []. apply (odelete_pair X m None None).
Qed.

Lemma fuzz_pair : forall X data, (length X <= 2)%nat -> zlength data <= MAX_INPUT ->
  rsimeq (RX X) (fuzz_oneA AAllocZ data) (fuzz_oneA A data) (fun _ => RX X).
Proof.
  intros X data HL Hd. unfold fuzz_oneA, HarnessM.fuzz_one, RSimProg.rsimeq.
  eapply rsim_bind; [apply (cinit_pair X HL)|]. intros [] [].
  eapply rsim_bind; [apply (minify_pair X data HL Hd)|]. intros [] [].
  apply rsim_ret. intros ? ? ? ? H. split; [reflexivity| exact H].
Qed.

(* [comment removed for export] *)
Lemma run_pair : forall X cfg payload, (length X <= 1)%nat -> zlength payload <= MAX_INPUT ->
  rsimeq (RX X) (runA AAllocZ cfg payload) (runA A cfg payload) (fun _ => RX X).
Proof.
  intros X cfg payload HL Hp. unfold runA.
  eapply (target_run_sim nstep step2 PhiZ Phi2 RX); first [exact malloc_pair | exact free_pair | exact fuzz_pair | exact emit_pair | exact HL | exact Hp].
Qed.

(* [comment removed for export] *)
Lemma main_exit_pair : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  rsim (RX []) (progA_main AAllocZ rsZ argv) (progA_main A rsA argv) Q.
Proof.
  intros argv Q Hargv. unfold progA_main, client_exitA.
  eapply (main_exit_sim nstep step2 PhiZ Phi2 ioZ (ioA A));
    first [ exact malloc_pair | exact free_pair | exact RX_perm | exact diag_pair | exact run_pair | exact open_pair | exact close_pair
          | exact read_pair | exact ioexit_pair | exact exitnode_pair | exact Hargv
          | (intros X bm; apply rsimeq_ret; intros ? ? ? ? H; exact H)
          | (intros X; apply rsimeq_ret; intros ? ? ? ? H; exact H)
          | (intros X; unfold RSimProg.rsimeq; eapply rsim_post; [apply cexit_pair|]; intros [] [] ? ? ? ? H; split; [reflexivity| exists X; exact H]) ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma argv_Z_pieces : forall argv, valid_argv argv -> Forall (fun a => zlength a <= PIECE_MAX) (argv_Z argv).
Proof.
  intros argv (_ & _ & HF & _). unfold argv_Z. apply Forall_map. eapply Forall_impl; [|exact HF].
  intros a Ha. unfold zlength, PIECE_MAX in *. rewrite length_map. lia.
Qed.

(* [comment removed for export] *)
Lemma ttrace_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop)
      (t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo tr :
  ttrace step nexit (ebind t f) mo tr <-> ttrace step nexit t mo tr.
Proof.
  rewrite !ttrace_split, texit_ebind. split.
  - intros [[Hx|(tr1 & [[] ?] & _)]|(r & mo' & Hp)]; [left; exact Hx|].
    apply tpath_ebind in Hp as [[Hp ->]|(tr1 & [[] ?] & _)]. right. exists Unr, mo'. exact Hp.
  - intros [Hx|(r & mo' & Hp)]; [left; left; exact Hx|]. right. destruct r as [|[[] ?]]. exists Unr, mo'. apply tpath_ebind. left. auto.
Qed.

Lemma tpath_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop)
      (t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo tr r mo' :
  tpath step (ebind t f) mo tr r mo' -> exists r', tpath step t mo tr r' mo'.
Proof. intros Hp. apply tpath_ebind in Hp as [[Hp ->]|(tr1 & [[] ?] & _)]. exists Unr. exact Hp. Qed.

Lemma tglob_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop) Phi
      (t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo :
  tglob step Phi (ebind t f) mo <-> tglob step Phi t mo.
Proof.
  split; [apply tglob_ebind_l|]. intros H. apply tglob_ebind; [exact H|]. intros tr [[] ?] mo' _.
Qed.

Theorem equiv_core : forall inp sA0 moA0 moZ,
  valid_input_either inp -> AHAND inp sA0 moA0 ->
  minv moZ -> m_halted moZ = None -> m_fds moZ = init_fds -> m_fs moZ = in_fs inp ->
  (forall tr r mo', ~ tpath nstep (progZ_tree rsZ (argv_Z (in_argv inp))) moZ tr r mo') ->
  (forall tr, ttrace nstep nexit (progZ_tree rsZ (argv_Z (in_argv inp))) moZ tr
              <-> ttrace step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros inp sA0 moA0 moZ Hi (HA & Hso & Hcl & Hfd & Hfs & GA) MZ HZ FdZ FsZ NLZ. pose proof Hi as (Hargv & _).
  unfold progZ_tree, progA_tree in *.
  destruct (rsim_ttrace nstep step2 nexit nexit PhiZ Phi2 (RX []) (progA_main AAllocZ rsZ (argv_Z (in_argv inp))) (progA_main A rsA (argv_Z (in_argv inp)))
              (fun _ _ _ _ _ _ => False) sZ_init moZ sA0 moA0
              (main_exit_pair _ _ (argv_Z_pieces _ Hargv))) as [EQ NL2].
  - (* [comment removed for export] *)
    unfold RX. splits; auto; try congruence; try (cbn; symmetry; exact Hso); try (cbn; split; [intros _; exact Hcl| reflexivity]).
    unfold clb. rewrite Hcl. exact HA.
  - apply tglob_trivial. intros; exact I.
  - apply (tglob_after_empty step2 Phi2 _ (fun p => match fst p : Empty_set with end)). exact GA.
  - intros tr r mo' Hp. destruct r as [|[[] ?]]. apply (NLZ tr Unr mo'). apply tpath_ebind. left. auto.
  - split.
    + intros tr. rewrite !ttrace_after_empty. apply EQ.
    + intros tr r mo' Hp. apply tpath_after_empty in Hp as [r' Hp]. exact (NL2 tr r' mo' Hp).
Qed.

End ASide.

(* [comment removed for export] *)
Theorem equiv_ZA (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
    (rsZ rsA : Z) (K : AAllocOK A step2 Phi2 MI2) : forall inp sA0 moA0 moZ,
  valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
  minv moZ -> m_halted moZ = None -> m_fds moZ = init_fds -> m_fs moZ = in_fs inp ->
  (forall tr r mo', ~ tpath nstep (progZ_tree rsZ (argv_Z (in_argv inp))) moZ tr r mo') ->
  (forall tr, (exists full, ttrace nstep nexit (progZ_tree rsZ (argv_Z (in_argv inp))) moZ full /\ is_prefix tr full)
              <-> (exists full, ttrace step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 full /\ is_prefix tr full))
  /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros inp sA0 moA0 moZ Hi HH MZ HZ FdZ FsZ NLZ.
  destruct (equiv_core A step2 Phi2 MI2 rsZ rsA K inp sA0 moA0 moZ Hi HH MZ HZ FdZ FsZ NLZ) as [EQ NL2].
  split; [| exact NL2]. intros tr. split; intros (full & Hf & Hp); exists full; split; auto; apply EQ; exact Hf.
Qed.
