(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe MPaths STree Stdio HarnessP Adapter Driver
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
Definition CLIENT_VEC_BYTES : Z := 8.
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

(* [comment removed for export] *)
Lemma cexit_pair : forall X, rsim (RX X) (@HarnessP.client_exit ZSt) (@HarnessP.client_exit (ASt A)) (fun _ _ => RX X).
Proof. intros X. unfold HarnessP.client_exit. apply rsim_ret. intros ? ? ? ? H. exact H. Qed.

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

Local Notation opnewZ := (HarnessP.opnew (amalloc AAllocZ) (new_handlerA AAllocZ)).
Local Notation opnewA := (HarnessP.opnew (amalloc A) (new_handlerA A)).

Lemma opnew_pair_h : forall X n, 0 < n <= REQMAX -> (forall s2, HISTOK (n :: map snd (clb s2 ++ aX X))) ->
  rsim (RX X) (opnewZ n) (opnewA n) (fun p q => RX ((p, q, n) :: X)).
Proof.
  intros X n Hn HH. unfold HarnessP.opnew. replace (if n =? 0 then 1 else n) with n by (destruct (Z.eqb_spec n 0); lia).
  eapply rsim_bind; [apply malloc_pair_h; [lia| exact HH]|].
  intros [p|] [q|]; cbn beta iota; [| apply rsim_false| apply rsim_false|].
  - apply rsim_drop. apply rsim_ret. intros ? ? ? ? HH0. exact HH0.
  - unfold new_handlerA. eapply rsim_bind; [apply rsim_munr with (Q := fun _ _ _ _ _ _ => False)|]. intros [].
Qed.

(* [comment removed for export] *)
Lemma HISTOK_parser : forall (X C : list triple) n s2, (length X <= 2)%nat -> (length C <= 8)%nat -> 0 <= n ->
  Forall (fun b => 0 <= snd b) C -> n + zsum (map snd C) <= 2^31 - CLIENT_VEC_BYTES ->
  HISTOK (n :: map snd (clb s2 ++ aX (C ++ X))).
Proof.
  intros X C n s2 HX HC Hn HF HS. right.
  exists (map snd (aX X)), (n :: map snd (clb s2) ++ map snd (aX C)). split; [| split; [| split; [| split]]].
  - rewrite aX_app, !map_app. rewrite app_assoc, app_comm_cons. apply Permutation_app_comm.
  - unfold aX. rewrite !length_map. exact HX.
  - cbn [length]. unfold aX. rewrite length_app, !length_map. pose proof (length_clb s2). lia.
  - constructor; [exact Hn|]. apply Forall_app. split.
    + unfold clb. destruct (a_cl A s2); cbn [map snd]; [constructor; [unfold CLIENT_VEC_BYTES; lia| constructor]| constructor].
    + rewrite sizes_aX. apply Forall_map. exact HF.
  - rewrite zsum_cons, zsum_app, sizes_aX. unfold clb. destruct (a_cl A s2); cbn [map snd]; rewrite ?zsum_cons, ?zsum_nil; unfold CLIENT_VEC_BYTES in *; lia.
Qed.

Lemma opnew_step : forall X C n, (length X <= 2)%nat -> (length C <= 7)%nat -> Forall (fun b => 0 <= snd b) C ->
  0 < n <= REQMAX -> n + zsum (map snd C) <= 2^31 - CLIENT_VEC_BYTES ->
  rsim (RX (C ++ X)) (opnewZ n) (opnewA n) (fun p q => RX ((p, q, n) :: C ++ X)).
Proof. intros X C n HX HC HF Hn HS. apply opnew_pair_h; [exact Hn|]. intros s2. apply HISTOK_parser; auto; lia. Qed.

Lemma free_mid : forall l1 X' p q n,
  rsim (RX (l1 ++ (p, q, n) :: X')) (HarnessP.opdelete (afree AAllocZ) p) (HarnessP.opdelete (afree A) q) (fun _ _ => RX (l1 ++ X')).
Proof.
  intros l1 X' p q n. unfold HarnessP.opdelete. eapply rsim_pre; [apply (free_pair (l1 ++ X') p q n)|].
  intros s1 mo1 s2 mo2 H. eapply RX_perm; [| exact H]. apply Permutation_sym, Permutation_middle.
Qed.

(* [comment removed for export] *)
Lemma parser_sizes : forall len, 0 <= len <= MAX_INPUT ->
  0 < SB_BYTES len /\ 0 < TAPE_BYTES len /\ 0 < SIDX_BYTES len /\ 0 < COPY_BYTES len
  /\ SB_BYTES len + TAPE_BYTES len + IMPL_BYTES + SIDX_BYTES len + OC_BYTES + ISARR_BYTES + COPY_BYTES len + (len + 64) <= 2^31 - CLIENT_VEC_BYTES
  /\ TAPE_BYTES len <= REQMAX /\ SB_BYTES len <= REQMAX /\ SIDX_BYTES len <= REQMAX /\ COPY_BYTES len <= REQMAX
  /\ IMPL_BYTES = 96 /\ OC_BYTES = 8192 /\ ISARR_BYTES = 1024.
Proof.
  intros len H. pose proof (sizes_pos len ltac:(lia)) as P. pose proof (sizes_upper len ltac:(lia)) as U.
  assert (C1 : HarnessP.CAP len <= 2^26) by (unfold HarnessP.CAP, MAX_INPUT in *; lia).
  assert (C2 : HarnessP.CAP len / 3 <= HarnessP.CAP len) by (apply Z.div_le_upper_bound; unfold HarnessP.CAP; lia).
  assert (C3 : 0 <= HarnessP.CAP len / 3) by (apply Z.div_pos; unfold HarnessP.CAP; lia).
  unfold REQMAX, CLIENT_VEC_BYTES, MAX_INPUT in *. lia.
Qed.

Local Ltac sz_nonneg := repeat (apply Forall_cons; [cbn [snd]; lia|]); apply Forall_nil.
Local Ltac sz_sum := cbn [map snd fst]; rewrite ?zsum_cons, ?zsum_nil; lia.
Local Ltac side := first [ assumption | (cbn [length]; lia) | sz_nonneg | sz_sum | lia | (unfold REQMAX, MAX_INPUT in *; lia) ].

(* [comment removed for export] *)
Definition pb_rel (len : Z) (X : list triple) (b1 : unit * unit * (unit * unit * unit * unit) * option unit)
    (b2 : aptr A * aptr A * (aptr A * aptr A * aptr A * aptr A) * option (aptr A)) : rel :=
  let '(sb1, tp1, (im1, si1, oc1, ia1), lb1) := b1 in
  let '(sb2, tp2, (im2, si2, oc2, ia2), lb2) := b2 in
  let C := [(ia1, ia2, ISARR_BYTES); (oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES);
            (tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)] in
  match lb1, lb2 with
  | Some l1, Some l2 => RX ((l1, l2, COPY_BYTES len) :: C ++ X)
  | None, None => RX (C ++ X)
  | _, _ => fun _ _ _ _ => False
  end.

Lemma parse_pair : forall X data, (length X <= 2)%nat -> zlength data <= MAX_INPUT ->
  rsim (RX X) (HarnessP.parse_into_doc (amalloc AAllocZ) (afree AAllocZ) (new_handlerA AAllocZ) data)
              (HarnessP.parse_into_doc (amalloc A) (afree A) (new_handlerA A) data) (pb_rel (zlength data) X).
Proof.
  intros X data HX Hd.
  unfold HarnessP.parse_into_doc, HarnessP.doc_allocate, HarnessP.impl_create, HarnessP.impl_set_capacity,
    HarnessP.impl_set_max_depth, HarnessP.padded_alloc, HarnessP.parse_impl, HarnessP.root_copy.
  cbv zeta. assert (H0 : 0 <= zlength data) by (unfold zlength; lia).
  set (len := zlength data) in *.
  destruct (parser_sizes len ltac:(lia)) as (P1 & P2 & P3 & P4 & S & R1 & R2 & R3 & R4 & E1 & E2 & E3).
  (* [comment removed for export] *)
  eapply rsim_bind with (Q1 := fun d1 d2 => RX ((snd d1, snd d2, TAPE_BYTES len) :: (fst d1, fst d2, SB_BYTES len) :: X)).
  { eapply rsim_bind; [apply (opnew_step X [] (SB_BYTES len)); side|]. intros sb1 sb2.
    eapply rsim_bind; [apply (opnew_step X [(sb1, sb2, SB_BYTES len)] (TAPE_BYTES len)); side|]. intros tp1 tp2.
    apply rsim_ret. intros ? ? ? ? H. exact H. }
  intros [sb1 tp1] [sb2 tp2]. cbn [fst snd].
  (* [comment removed for export] *)
  eapply rsim_bind with (Q1 := fun i1 i2 =>
    let '(im1, si1, oc1, ia1) := i1 in let '(im2, si2, oc2, ia2) := i2 in
    RX ([(ia1, ia2, ISARR_BYTES); (oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES);
         (tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)] ++ X)).
  { eapply rsim_bind; [apply (opnew_step X [(tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)] IMPL_BYTES); side|]. intros im1 im2.
    eapply rsim_bind; [apply (opnew_step X [(im1, im2, IMPL_BYTES); (tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)] (SIDX_BYTES len)); side|].
    intros si1 si2.
    eapply rsim_bind with (Q1 := fun o1 o2 => RX ([(snd o1, snd o2, ISARR_BYTES); (fst o1, fst o2, OC_BYTES); (si1, si2, SIDX_BYTES len);
                                                   (im1, im2, IMPL_BYTES); (tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)] ++ X)).
    { eapply rsim_bind; [apply (opnew_step X [(si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES); (tp1, tp2, TAPE_BYTES len);
                                              (sb1, sb2, SB_BYTES len)] OC_BYTES); side|]. intros oc1 oc2.
      eapply rsim_bind; [apply (opnew_step X [(oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES);
                                              (tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)] ISARR_BYTES); side|]. intros ia1 ia2.
      apply rsim_ret. intros ? ? ? ? H. exact H. }
    intros [oc1 ia1] [oc2 ia2]. apply rsim_ret. intros ? ? ? ? H. exact H. }
  intros [[[im1 si1] oc1] ia1] [[[im2 si2] oc2] ia2]. cbv beta iota.
  set (C6 := [(ia1, ia2, ISARR_BYTES); (oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES);
              (tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)]).
  destruct (HarnessP.copy_made len) eqn:CM; cbv beta iota.
  - (* [comment removed for export] *)
    assert (HC : COPY_BYTES len <= 2^20) by (unfold HarnessP.copy_made, HarnessP.COPY_LIMIT in CM; apply Z.leb_le in CM; exact CM).
    eapply rsim_bind with (Q1 := fun l1 l2 => match l1, l2 with
                                              | Some a, Some b => RX ((a, b, COPY_BYTES len) :: C6 ++ X)
                                              | _, _ => fun _ _ _ _ => False end).
    { eapply rsim_bind; [apply (opnew_step X C6 (COPY_BYTES len)); unfold C6; side|]. intros cp1 cp2.
      apply rsim_ret. intros ? ? ? ? H. exact H. }
    intros [cp1|] [cp2|]; cbv beta iota; try apply rsim_false.
    eapply rsim_seq with (R1 := RX ((cp1, cp2, COPY_BYTES len) :: C6 ++ X)).
    { destruct (SjStage1.root_number_alloc data) as [nr|] eqn:RN; cbv beta iota.
      - pose proof (SjStage1.root_number_alloc_bound data nr RN) as RB.
        assert (RB' : 64 < nr <= len + 64) by (unfold len, zlength; lia).
        eapply rsim_bind; [apply (opnew_step X ((cp1, cp2, COPY_BYTES len) :: C6) nr); unfold C6; side|]. intros c1 c2.
        apply (free_mid [] ((cp1, cp2, COPY_BYTES len) :: C6 ++ X) c1 c2 nr).
      - apply rsim_ret. intros ? ? ? ? H. exact H. }
    intros [] []. apply rsim_ret. intros ? ? ? ? H. exact H.
  - eapply rsim_bind with (Q1 := fun l1 l2 => match l1, l2 with None, None => RX (C6 ++ X) | _, _ => fun _ _ _ _ => False end).
    { apply rsim_ret. intros ? ? ? ? H. exact H. }
    intros [cp1|] [cp2|]; cbv beta iota; try apply rsim_false.
    eapply rsim_seq with (R1 := RX (C6 ++ X)); [apply rsim_ret; intros ? ? ? ? H; exact H|].
    intros [] []. apply rsim_ret. intros ? ? ? ? H. exact H.
Qed.

Lemma dtor_pair : forall X len b1 b2,
  rsim (pb_rel len X b1 b2) (HarnessP.parser_dtor (afree AAllocZ) b1) (HarnessP.parser_dtor (afree A) b2) (fun _ _ => RX X).
Proof.
  intros X len [[[sb1 tp1] [[[im1 si1] oc1] ia1]] lb1] [[[sb2 tp2] [[[im2 si2] oc2] ia2]] lb2].
  unfold HarnessP.parser_dtor, HarnessP.doc_dtor, HarnessP.impl_dtor, pb_rel. cbv beta iota zeta.
  eapply rsim_seq with (R1 := RX ([(ia1, ia2, ISARR_BYTES); (oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES);
                                   (tp1, tp2, TAPE_BYTES len); (sb1, sb2, SB_BYTES len)] ++ X)).
  { destruct lb1 as [l1|], lb2 as [l2|]; cbn [HarnessP.odelete]; try apply rsim_false.
    - apply (free_mid [] _ l1 l2 (COPY_BYTES len)).
    - apply rsim_ret. intros ? ? ? ? H. exact H. }
  intros [] [].
  eapply rsim_seq with (R1 := RX ([(ia1, ia2, ISARR_BYTES); (oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES)] ++ X)).
  { eapply rsim_seq; [apply (free_mid [(ia1, ia2, ISARR_BYTES); (oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES);
                                       (tp1, tp2, TAPE_BYTES len)] X sb1 sb2 (SB_BYTES len))|]. intros [] [].
    apply (free_mid [(ia1, ia2, ISARR_BYTES); (oc1, oc2, OC_BYTES); (si1, si2, SIDX_BYTES len); (im1, im2, IMPL_BYTES)] X tp1 tp2 (TAPE_BYTES len)). }
  intros [] [].
  eapply rsim_seq; [apply (free_mid [] _ ia1 ia2 ISARR_BYTES)|]. intros [] [].
  eapply rsim_seq; [apply (free_mid [] _ oc1 oc2 OC_BYTES)|]. intros [] [].
  eapply rsim_seq; [apply (free_mid [] _ si1 si2 (SIDX_BYTES len))|]. intros [] [].
  apply (free_mid [] X im1 im2 IMPL_BYTES).
Qed.

Lemma fuzz_pair : forall X data, (length X <= 2)%nat -> zlength data <= MAX_INPUT ->
  rsimeq (RX X) (fuzz_oneA AAllocZ data) (fuzz_oneA A data) (fun _ => RX X).
Proof.
  intros X data HL Hd. unfold fuzz_oneA, HarnessP.fuzz_one, RSimProg.rsimeq.
  eapply rsim_bind; [apply (parse_pair X data HL Hd)|]. intros b1 b2.
  eapply rsim_seq; [apply (dtor_pair X (zlength data) b1 b2)|]. intros [] [].
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
