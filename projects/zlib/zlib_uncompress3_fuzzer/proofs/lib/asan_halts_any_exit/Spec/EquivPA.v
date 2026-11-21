(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad MSafe MPaths STree Malloc Stdio Client Harness Adapter Driver
  PState Prog StepB KLink KEv ModelInv ImgFacts ModelOK EquivShared EquivProg RSim RSimProg SizeHist PTotal ProgA LB_StmtA LB_Main EquivK_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import CMonad CRSim ProgC ProgAC ModelOKC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require HarnessC AdapterC DriverC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit Require Import TopLevel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Plain Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Definition init_fds : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Lemma m_fds_mo0 : forall segs lim en inp, m_fds (mo0 segs lim en inp) = init_fds.
Proof. intros segs lim [? ? ?] inp. reflexivity. Qed.
Lemma m_fs_mo0 : forall segs lim en inp, m_fs (mo0 segs lim en inp) = in_fs inp.
Proof. intros segs lim [? ? ?] inp. reflexivity. Qed.


Definition CRUNX (q : Z) : Z := RUNX q Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX.
Lemma CRUNX_eq q : CRUNX q = 4 * (2 * (32768 + q)).
Proof. unfold CRUNX, RUNX, FC, Client.CLIENT_MAX_REQS, Client.CLIENT_REQ_MAX. reflexivity. Qed.
Lemma client_nreq : (Client.CLIENT_MAX_REQS <= 2)%nat. Proof. unfold Client.CLIENT_MAX_REQS. lia. Qed.
Lemma client_rmax : 0 <= Client.CLIENT_REQ_MAX <= REQMAX. Proof. unfold Client.CLIENT_REQ_MAX, REQMAX. lia. Qed.

Section ASide.
Variable A : AAlloc.
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.
Variable Phi2 : node -> Model -> Prop.
Variable MI2 : Model -> Prop.
Variables (rsP rsA : Z).

Local Notation STOT2 := (STOT (St:=ASt A) step2 (fun R0 => texit (R:=R0) step2 nexit)).

Record AAllocOK : Type := mkAAllocOK {
  ok_sub2 : forall n mo r mo' e, ~ nf_node n -> step2 n mo r mo' e -> nstep n mo r mo' e;
  ok_same2 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> step2 n mo r mo e;
  ok_io2 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> step2 n mo r mo' e;
  ok_MI2 : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> MI2 mo -> m_halted mo = None -> MI2 mo' /\ m_halted mo' = None;
  ok_get_set : forall v s, a_so A (a_set_so A v s) = v;
  ok_set_set : forall v w s, a_set_so A v (a_set_so A w s) = a_set_so A v s;
  ok_set_get : forall s, a_set_so A (a_so A s) s = s;
  ok_addr_so : forall v s p, aptr_addr A (a_set_so A v s) p = aptr_addr A s p;
  AI : list (aptr A * Z) -> ASt A -> Model -> Prop;
  ok_AI_perm : forall Y Y' s mo, Permutation Y Y' -> AI Y s mo -> AI Y' s mo;
  ok_AI_so : forall Y s mo v, AI Y s mo -> AI Y (a_set_so A v s) mo;
  ok_AI_model : forall Y s mo, AI Y s mo -> MI2 mo /\ m_halted mo = None;
  ok_AI_fds : forall Y s mo f, AI Y s mo -> MI2 (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI Y s (with_fds f mo);
  ok_QOV : Z;
  ok_CMAX : Z;
  ok_QOV0 : 0 <= ok_QOV;
  ok_room : CDONE ok_QOV + MAX_INPUT + ok_QOV + CRUNX ok_QOV <= ok_CMAX;
  ok_cost : ASt A -> Z;
  ok_cost_so : forall v s, ok_cost (a_set_so A v s) = ok_cost s;
  ok_malloc : forall Y n s mo, AI Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
      ok_cost s + n + ok_QOV <= ok_CMAX ->
      tglob step2 Phi2 (amalloc A n s) mo ->
      STOT2 (amalloc A n s) mo
            (fun r s' mo' => exists q, r = Some q /\ AI ((q, n) :: Y) s' mo' /\ n < 2^63
                             /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                             /\ ok_cost s' <= ok_cost s + n + ok_QOV);
  ok_free : forall Y q n s mo, AI ((q, n) :: Y) s mo -> ok_cost s <= ok_CMAX ->
      tglob step2 Phi2 (afree A q s) mo ->
      STOT2 (afree A q s) mo
            (fun _ s' mo' => AI Y s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                             /\ ok_cost s' <= ok_cost s);
  ok_annot : forall Y q cap old new s mo, AI Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
      (old = 0 \/ new = 0) ->
      tglob step2 Phi2 (aannot A q cap old new s) mo ->
      STOT2 (aannot A q cap old new s) mo
            (fun _ s' mo' => AI Y s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                             /\ ok_cost s' <= ok_cost s)
}.

Variable K : AAllocOK.

Variable lim : Z.
Hypothesis Hlim : 2^31 <= lim.

Definition AHAND (inp : ProcInput) (sA0 : ASt A) (moA0 : Model) : Prop :=
  AI K [] sA0 moA0 /\ a_so A sA0 = stdout_init /\ m_fds moA0 = init_fds /\ m_fs moA0 = in_fs inp
  /\ ok_cost K sA0 <= 0
  /\ tglob step2 Phi2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0.


Local Notation rel := (rel PState (ASt A)).
Local Notation rsim := (rsim nstep step2 nexit nexit PhiP Phi2).
Local Notation triple := (bptr * aptr A * Z)%type.

Definition pX (X : list triple) : list bptr := map (fun b => fst (fst b)) X.
Definition aX (X : list triple) : list (aptr A * Z) := map (fun b => (snd (fst b), snd b)) X.
Definition GT : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_GT : frame_ok GT. Proof. intros ? ? ? ? _ _ _ _; exact I. Qed.

Definition RX (C : Z) (X : list triple) : rel := fun s1 mo1 s2 mo2 =>
  OWN (pX X) GT s1 mo1 /\ AI K (aX X) s2 mo2 /\ ps_so s1 = a_so A s2 /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2
  /\ ok_cost K s2 <= C /\ ok_cost K s2 <= ok_CMAX K.

Lemma pX_app X Y : pX (X ++ Y) = pX X ++ pX Y. Proof. apply map_app. Qed.
Lemma aX_app X Y : aX (X ++ Y) = aX X ++ aX Y. Proof. apply map_app. Qed.
Lemma sizes_aX X : map snd (aX X) = map snd X. Proof. unfold aX. rewrite map_map. reflexivity. Qed.

Lemma OWN_minv X s mo : OWN X GT s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(L & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma OWN_fds X s mo f : OWN X GT s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> OWN X GT s (with_fds f mo).
Proof.
  intros [(L & Hc & HK & Hi) [Hnd _]] Hmi Hh. split; [|split; [exact Hnd| exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| apply m_vmmaps_with_fds| exact Hmi| exact Hh].
Qed.

Lemma RX_perm : forall C X Y s1 mo1 s2 mo2, Permutation X Y -> RX C X s1 mo1 s2 mo2 -> RX C Y s1 mo1 s2 mo2.
Proof.
  intros C X Y s1 mo1 s2 mo2 HP (HO & HA & Hso & Hfd & Hfs). split; [| split; [| auto]].
  - eapply OWN_perm; [| exact HO]. unfold pX. apply Permutation_map. exact HP.
  - eapply (ok_AI_perm K); [| exact HA]. unfold aX. apply Permutation_map. exact HP.
Qed.

Lemma RX_mono : forall C C' X s1 mo1 s2 mo2, C <= C' -> RX C X s1 mo1 s2 mo2 -> RX C' X s1 mo1 s2 mo2.
Proof. intros C C' X s1 mo1 s2 mo2 HC (HO & HA & Hso & Hfd & Hfs & Hc & Hm). unfold RX. splits; auto. lia. Qed.

Lemma RX_get : forall C X s1 mo1 s2 mo2, RX C X s1 mo1 s2 mo2 -> ps_so s1 = a_so A s2.
Proof. intros C X s1 mo1 s2 mo2 (_ & _ & H & _). exact H. Qed.

Lemma RX_set : forall C X s1 mo1 s2 mo2 v, RX C X s1 mo1 s2 mo2 -> RX C X (set_so_ps v s1) mo1 (a_set_so A v s2) mo2.
Proof.
  intros C X s1 mo1 s2 mo2 v (HO & HA & Hso & Hfd & Hfs & Hc & Hm). split; [| split; [| split; [| split; [exact Hfd| split; [exact Hfs|]]]]].
  - eapply OWN_other; [exact HO| reflexivity| reflexivity| exact I].
  - apply (ok_AI_so K). exact HA.
  - rewrite (ok_get_set K). destruct s1; reflexivity.
  - rewrite (ok_cost_so K). split; assumption.
Qed.

Lemma RX_models : forall C X s1 mo1 s2 mo2, RX C X s1 mo1 s2 mo2 ->
  minv mo1 /\ MI2 mo2 /\ m_halted mo1 = None /\ m_halted mo2 = None /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
Proof.
  intros C X s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs & _). destruct (OWN_minv _ _ _ HO) as [M1 H1]. destruct (ok_AI_model K _ _ _ HA) as [M2 H2]. splits; auto.
Qed.

Lemma RX_tables : forall C X s1 mo1 s2 mo2 f, RX C X s1 mo1 s2 mo2 ->
  minv (with_fds f mo1) -> MI2 (with_fds f mo2) -> m_halted (with_fds f mo1) = None -> m_halted (with_fds f mo2) = None ->
  RX C X s1 (with_fds f mo1) s2 (with_fds f mo2).
Proof.
  intros C X s1 mo1 s2 mo2 f (HO & HA & Hso & Hfd & Hfs & Hc) M1 M2 H1 H2. split; [| split; [| split; [exact Hso| split; [reflexivity| split; [| exact Hc]]]]].
  - apply OWN_fds; auto.
  - apply (ok_AI_fds K); auto.
  - rewrite !m_fs_with_fds. exact Hfs.
Qed.


Lemma size_overflows_REQMAX n : 0 <= n <= REQMAX -> size_overflows n = false.
Proof. intros Hn. unfold size_overflows, REQMAX in *. apply Z.leb_gt. lia. Qed.

Lemma malloc_pair : forall C X n, 0 <= n <= REQMAX -> HISTOK (n :: map snd X) -> C + n + ok_QOV K <= ok_CMAX K ->
  rsim (RX C X) (raw_malloc n) (amalloc A n) (Qm RX (ok_QOV K) C X n).
Proof.
  intros C X n Hn HH HC. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs & Hc & Hm) G1 G2.
  eexists _, _. split; [| split].
  - apply (raw_malloc_STOT (pX X) GT n s1 mo1 frame_ok_GT HO ltac:(lia) (size_overflows_REQMAX n Hn) G1).
  - apply (ok_malloc K (aX X) n s2 mo2 HA Hn ltac:(rewrite sizes_aX; exact HH) ltac:(lia) G2).
  - intros a s1' mo1' b s2' mo2' (p & -> & HO' & Hn63 & Hso1 & Hfa1 & Hfd1 & Hfs1) (q & -> & HA' & _ & Hso2 & Hfd2 & Hfs2 & Hc2). cbn [Qm].
    split; [| exact Hn63]. split; [exact HO'|]. split; [exact HA'|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; lia.
Qed.

Lemma free_pair : forall C X p q n, rsim (RX C ((p, q, n) :: X)) (raw_free p) (afree A q) (fun _ _ => RX C X).
Proof.
  intros C X p q n. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs & Hc & Hm) G1 G2.
  eexists _, _. split; [| split].
  - apply (raw_free_STOT (pX X) GT p s1 mo1 frame_ok_GT HO G1).
  - apply (ok_free K (aX X) q n s2 mo2 HA Hm G2).
  - intros a s1' mo1' b s2' mo2' (HO' & Hso1 & Hfa1 & Hfd1 & Hfs1) (HA' & Hso2 & Hfd2 & Hfs2 & Hc2).
    split; [exact HO'|]. split; [exact HA'|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; lia.
Qed.

Lemma annot2_pair : forall C X p q c, 0 < c ->
  rsim (RX C ((p, q, c) :: X)) ((fun (_ : bptr) (_ : Z) => mret tt) p c) (aannot A q c c 0 ;;; aannot A q c 0 c) (fun _ _ => RX C ((p, q, c) :: X)).
Proof.
  intros C X p q c Hc. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs & Hcost & Hm) G1 G2.
  eexists _, _. split; [apply STOT_ret| split].
  - eapply STOT_bind.
    + apply STOT_path. apply (ok_annot K (aX ((p, q, c) :: X)) q c c 0 s2 mo2 HA ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(right; reflexivity) (tglob_ebind_l _ _ _ _ _ G2)).
    + intros [] s2' mo2' ((HA' & Hso2 & Hfd2 & Hfs2 & Hc2) & Hp). cbn beta.
      assert (G2' : tglob step2 Phi2 (aannot A q c 0 c s2') mo2').
      { unfold mbind in G2. exact (tglob_ebind_r _ _ _ _ _ _ _ _ G2 Hp). }
      eapply STOT_mono; [apply (ok_annot K (aX ((p, q, c) :: X)) q c 0 c s2' mo2' HA' ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(left; reflexivity) G2')|].
      intros [] s2'' mo2'' (HA'' & Hso3 & Hfd3 & Hfs3 & Hc3). cbn beta.
      instantiate (1 := fun _ s' mo' => AI K (aX ((p, q, c) :: X)) s' mo' /\ a_so A s' = a_so A s2 /\ m_fds mo' = m_fds mo2 /\ m_fs mo' = m_fs mo2
                                        /\ ok_cost K s' <= ok_cost K s2). cbn beta.
      split; [exact HA''|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. lia.
  - intros [] s1' mo1' [] s2' mo2' (_ & -> & ->) (HA' & Hso2 & Hfd2 & Hfs2 & Hc2).
    split; [exact HO|]. split; [exact HA'|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; lia.
Qed.



Lemma sub1 : forall n mo r mo' e, ~ nf_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma same1 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstep n mo r mo e. Proof. auto. Qed.
Lemma io1 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> minv mo -> m_halted mo = None -> minv mo' /\ m_halted mo' = None.
Proof. intros n mo rsp mo' evs Hst _ Hmi Hh. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi']. auto. Qed.

Local Notation rsimeq := (rsimeq nstep step2 PhiP Phi2).

Lemma diag_pair : forall C X d, diag_short d -> rsimeq (RX C X) (io_diag io d) (io_diag (ioA A) d) (fun _ => RX C X).
Proof. intros C X d _. cbn [io ioA io_diag io_S]. apply (s_diag_sim nstep step2 PhiP Phi2 sub1 same1 (ok_sub2 K) (ok_same2 K)). Qed.

Lemma emit_pair : forall C X v, rsimeq (RX C X) (io_emit io v) (io_emit (ioA A) v) (fun _ => RX C X).
Proof.
  intros C X v. cbn [io ioA io_emit io_S].
  apply (s_emit_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX C X) (RX_get C X) (RX_set C X)).
Qed.

Lemma ioexit_pair : forall C X, rsimeq (RX C X) (io_exit io) (io_exit (ioA A)) (fun _ => RX C X).
Proof.
  intros C X. cbn [io ioA io_exit io_S].
  apply (stdout_exit_flush_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX C X) (RX_get C X) (RX_set C X)).
Qed.

Lemma exitnode_pair : forall C X c (Q : Empty_set -> Empty_set -> rel), rsim (RX C X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof. intros C X c Q. apply (exit_node_sim nstep step2 PhiP Phi2 sub1 (ok_sub2 K) minv MI2 (RX C X) (RX_models C X)). Qed.


Lemma open_pair : forall C X path, rsimeq (RX C X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => RX C X).
Proof. intros C X path. apply (open_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX C X) (RX_models C X) (RX_tables C X)). Qed.
Lemma close_pair : forall C X fd, rsimeq (RX C X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => RX C X).
Proof. intros C X fd. apply (close_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX C X) (RX_models C X) (RX_tables C X)). Qed.
Lemma read_pair : forall C X fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
  rsimeq (RX C X) (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
         (fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => RX C X s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => RX C X end).
Proof. intros C X fd buf1 buf2 cnt Hcnt. apply (read_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX C X) (RX_models C X) (RX_tables C X)). exact Hcnt. Qed.

Lemma CRUNX_nonneg : 0 <= CRUNX (ok_QOV K).
Proof. rewrite CRUNX_eq. pose proof (ok_QOV0 K). lia. Qed.

Lemma run_pair : forall C X cfg payload, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> C + zlength payload + ok_QOV K + CRUNX (ok_QOV K) <= ok_CMAX K ->
  rsimeq (RX C X) (run cfg payload) (runA A cfg payload) (fun _ => RX (C + zlength payload + ok_QOV K + CRUNX (ok_QOV K)) X).
Proof.
  intros C X cfg payload HL Hp HC. unfold run, runA, Prog.fuzz_one, fuzz_oneA.
  apply (target_run_sim nstep step2 PhiP Phi2 RX (ok_QOV K) (ok_CMAX K) raw_malloc (amalloc A) raw_free (afree A)
           (io_emit io) (io_emit (ioA A)) malloc_pair free_pair emit_pair RX_mono
           Client.script Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX Client.script_ok client_nreq client_rmax (ok_QOV0 K) C X cfg payload HL Hp HC).
Qed.

Local Notation crsim := (crsim nstep step2 nexit nexit PhiP Phi2).
Local Notation crsimeq := (crsimeq nstep step2 PhiP Phi2).
Local Notation gstotP := (gstot (St:=PState) nstep nexit PhiP).
Local Notation gstotA := (gstot (St:=ASt A) step2 nexit Phi2).

Lemma allocP_gstot : forall ns acc Xp s mo, Forall (fun n => 0 <= n <= REQMAX) ns -> OWN (acc ++ Xp) GT s mo ->
  gstotP (alloc_all raw_malloc ns acc) s mo
         (fun ps s' mo' => OWN (ps ++ Xp) GT s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  induction ns as [|n ns IH]; intros acc Xp s mo Hns HO; cbn [alloc_all].
  - apply gstot_ret. auto.
  - inversion Hns as [|n' ns' Hn Hns' E]; subst.
    eapply gstot_bind.
    + intros G. apply (raw_malloc_STOT (acc ++ Xp) GT n s mo frame_ok_GT HO ltac:(lia) (size_overflows_REQMAX n Hn) G).
    + intros r s' mo' (p & -> & HO' & _ & Hso & _ & Hfd & Hfs). cbn beta iota.
      eapply gstot_mono; [apply (IH (p :: acc) Xp s' mo' Hns' HO')|].
      intros ps s'' mo'' (HO'' & Hso' & Hfd' & Hfs'). split; [exact HO''|]. split; [congruence|]. split; congruence.
Qed.

Lemma freeP_gstot : forall ps Xp s mo, OWN (ps ++ Xp) GT s mo ->
  gstotP (free_all raw_free ps) s mo
         (fun _ s' mo' => OWN Xp GT s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  induction ps as [|p ps IH]; intros Xp s mo HO; cbn [free_all app] in *.
  - apply gstot_ret. auto.
  - eapply gstot_bind.
    + intros G. apply (raw_free_STOT (ps ++ Xp) GT p s mo frame_ok_GT HO G).
    + intros [] s' mo' (HO' & Hso & _ & Hfd & Hfs). cbn beta.
      eapply gstot_mono; [apply (IH Xp s' mo' HO')|].
      intros u s'' mo'' (HO'' & Hso' & Hfd' & Hfs'). split; [exact HO''|]. split; [congruence|]. split; congruence.
Qed.

Definition PostP (Xp : list bptr) (s : PState) (mo : Model) : Z -> PState -> Model -> Prop :=
  fun r s' mo' => r = 0 /\ OWN Xp GT s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo.

Lemma fuzz_withoutP_gstot : forall ps Xp s mo, OWN (ps ++ Xp) GT s mo -> gstotP (HarnessC.fuzz_without raw_free ps) s mo (PostP Xp s mo).
Proof.
  intros ps Xp s mo HO. unfold HarnessC.fuzz_without. eapply gstot_bind; [apply (freeP_gstot ps Xp s mo HO)|].
  intros [] s' mo' (HO' & Hso & Hfd & Hfs). apply gstot_ret. unfold PostP. auto.
Qed.

Lemma fuzz_withP_gstot : forall opt ps Xp s mo, Forall (fun n => 0 <= n <= REQMAX) opt -> OWN (ps ++ Xp) GT s mo ->
  gstotP (HarnessC.fuzz_with raw_malloc raw_free opt ps) s mo (PostP Xp s mo).
Proof.
  intros opt ps Xp s mo Hopt HO. unfold HarnessC.fuzz_with. eapply gstot_bind; [apply (allocP_gstot opt ps Xp s mo Hopt HO)|].
  intros ps' s' mo' (HO' & Hso & Hfd & Hfs). cbn beta.
  eapply gstot_bind; [apply (freeP_gstot ps' Xp s' mo' HO')|].
  intros [] s'' mo'' (HO'' & Hso' & Hfd' & Hfs'). apply gstot_ret. unfold PostP. split; [reflexivity|]. split; [exact HO''|]. split; [congruence|]. split; congruence.
Qed.

Lemma client_pre_req : Forall (fun n => 0 <= n <= REQMAX) Client.CLIENT_PRE.
Proof. unfold Client.CLIENT_PRE, Client.STATE_SIZE, REQMAX. repeat constructor; lia. Qed.
Lemma client_opt_req : Forall (fun n => 0 <= n <= REQMAX) Client.CLIENT_OPT.
Proof. unfold Client.CLIENT_OPT, Client.WINDOW_SIZE, REQMAX. repeat constructor; lia. Qed.

Lemma fuzz_oneC_cgstotP : forall Xp s mo data, OWN Xp GT s mo ->
  cgstot nstep nexit PhiP (ProgC.fuzz_oneC data) s mo (PostP Xp s mo).
Proof.
  intros Xp s mo data HO. unfold ProgC.fuzz_oneC, HarnessC.fuzz_one.
  eapply cgstot_bind; [apply cgstot_lift; apply (allocP_gstot Client.CLIENT_PRE [] Xp s mo client_pre_req HO)|].
  intros ps s' mo' (HO' & Hso & Hfd & Hfs). cbn beta.
  assert (W : gstotP (HarnessC.fuzz_without raw_free ps) s' mo' (PostP Xp s mo)).
  { eapply gstot_mono; [apply (fuzz_withoutP_gstot ps Xp s' mo' HO')|]. unfold PostP. intros r s'' mo'' (-> & H1 & H2 & H3 & H4).
    split; [reflexivity|]. split; [exact H1|]. split; [congruence|]. split; congruence. }
  destruct (length ps <? length Client.CLIENT_PRE)%nat.
  - apply cgstot_lift. exact W.
  - apply cgstot_choice; apply cgstot_lift; [| exact W].
    eapply gstot_mono; [apply (fuzz_withP_gstot Client.CLIENT_OPT ps Xp s' mo' client_opt_req HO')|]. unfold PostP.
    intros r s'' mo'' (-> & H1 & H2 & H3 & H4). split; [reflexivity|]. split; [exact H1|]. split; [congruence|]. split; congruence.
Qed.

Local Notation anames := (map (@fst (aptr A) Z)).

Lemma allocA_gstot : forall ns T Y s mo, Forall (fun n => 0 <= n <= Client.CLIENT_REQ_MAX) ns ->
  (length T + length Y + length ns <= 4)%nat -> AI K (T ++ Y) s mo ->
  ok_cost K s + Z.of_nat (length ns) * (Client.CLIENT_REQ_MAX + ok_QOV K) <= ok_CMAX K ->
  gstotA (alloc_all (amalloc A) ns (anames T)) s mo
         (fun ps s' mo' => exists T', ps = anames T' /\ (length T' <= length T + length ns)%nat /\ AI K (T' ++ Y) s' mo'
                           /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                           /\ ok_cost K s' <= ok_cost K s + Z.of_nat (length ns) * (Client.CLIENT_REQ_MAX + ok_QOV K)).
Proof.
  pose proof (ok_QOV0 K) as HQ0.
  induction ns as [|n ns IH]; intros T Y s mo Hns HL HA HCM; cbn [alloc_all].
  - apply gstot_ret. exists T. cbn [length]. split; [reflexivity|]. split; [lia|]. repeat (split; [reflexivity || exact HA|]). lia.
  - inversion Hns as [|n' ns' Hn Hns' E]; subst. cbn [length] in HL, HCM |- *.
    assert (HK : 0 <= Z.of_nat (length ns) * (Client.CLIENT_REQ_MAX + ok_QOV K)) by (unfold Client.CLIENT_REQ_MAX in *; nia).
    eapply gstot_bind.
    + intros G. apply (ok_malloc K (T ++ Y) n s mo HA); [unfold Client.CLIENT_REQ_MAX, REQMAX in *; lia| | unfold Client.CLIENT_REQ_MAX in *; nia| exact G].
      apply HISTOK_amb0. rewrite length_map, length_app. lia.
    + intros r s' mo' (q & -> & HA' & _ & Hso & Hfd & Hfs & Hc). cbn beta iota.
      eapply gstot_mono; [apply (IH ((q, n) :: T) Y s' mo' Hns'); [cbn [length]; lia| exact HA'| unfold Client.CLIENT_REQ_MAX in *; nia]|].
      intros ps s'' mo'' (T' & -> & HLT & HA'' & Hso' & Hfd' & Hfs' & Hc'). exists T'. split; [reflexivity|].
      split; [cbn [length] in HLT; lia|]. split; [exact HA''|].
      split; [congruence|]. split; [congruence|]. split; [congruence|]. unfold Client.CLIENT_REQ_MAX in *. nia.
Qed.

Lemma freeA_gstot : forall T Y s mo, AI K (T ++ Y) s mo -> ok_cost K s <= ok_CMAX K ->
  gstotA (free_all (afree A) (anames T)) s mo
         (fun _ s' mo' => AI K Y s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ ok_cost K s' <= ok_cost K s).
Proof.
  induction T as [|[q n] T IH]; intros Y s mo HA HC; cbn [free_all map fst app] in *.
  - apply gstot_ret. repeat (split; [reflexivity || exact HA|]). lia.
  - eapply gstot_bind.
    + intros G. apply (ok_free K (T ++ Y) q n s mo HA HC G).
    + intros [] s' mo' (HA' & Hso & Hfd & Hfs & Hc). cbn beta.
      eapply gstot_mono; [apply (IH Y s' mo' HA'); lia|].
      intros u s'' mo'' (HA'' & Hso' & Hfd' & Hfs' & Hc'). split; [exact HA''|]. split; [congruence|]. split; [congruence|]. split; [congruence| lia].
Qed.

Definition FCK : Z := FC (ok_QOV K) Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX.
Lemma FCK_eq : FCK = 2 * (32768 + ok_QOV K).
Proof. unfold FCK, FC, Client.CLIENT_MAX_REQS, Client.CLIENT_REQ_MAX. reflexivity. Qed.

Definition PostA (Y : list (aptr A * Z)) (s : ASt A) (mo : Model) : Z -> ASt A -> Model -> Prop :=
  fun r s' mo' => r = 0 /\ AI K Y s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                  /\ ok_cost K s' <= ok_cost K s + FCK.

Lemma fuzz_oneAC_cgstotA : forall Y s mo data, (length Y <= 2)%nat -> AI K Y s mo -> ok_cost K s + FCK <= ok_CMAX K ->
  cgstot step2 nexit Phi2 (ProgAC.fuzz_oneAC A data) s mo (PostA Y s mo).
Proof.
  intros Y s mo data HLY HA HC. unfold ProgAC.fuzz_oneAC, HarnessC.fuzz_one. pose proof (ok_QOV0 K) as HQ0. rewrite FCK_eq in *.
  pose proof Client.client_ok as [CL CS]. rewrite length_app in CL. apply Forall_app in CS. destruct CS as [CSp CSo].
  unfold Client.CLIENT_MAX_REQS in CL.
  assert (Lp : (length Client.CLIENT_PRE = 1)%nat) by reflexivity. assert (Lo : (length Client.CLIENT_OPT = 1)%nat) by reflexivity.
  eapply cgstot_bind; [apply cgstot_lift; apply (allocA_gstot Client.CLIENT_PRE [] Y s mo CSp); [cbn [length]; lia| exact HA| rewrite Lp; unfold Client.CLIENT_REQ_MAX in *; lia]|].
  intros ps s' mo' (T' & -> & LT' & HA' & Hso & Hfd & Hfs & Hc). cbn beta. rewrite Lp in Hc, LT'. cbn [length] in LT'. unfold Client.CLIENT_REQ_MAX in Hc.
  assert (W : forall s1 mo1 T1, AI K (T1 ++ Y) s1 mo1 -> a_so A s1 = a_so A s -> m_fds mo1 = m_fds mo -> m_fs mo1 = m_fs mo ->
               ok_cost K s1 <= ok_cost K s + 2 * (32768 + ok_QOV K) ->
               gstotA (HarnessC.fuzz_without (afree A) (anames T1)) s1 mo1 (PostA Y s mo)).
  { intros s1 mo1 T1 HA1 E1 E2 E3 Hc1. unfold HarnessC.fuzz_without. eapply gstot_bind; [apply (freeA_gstot T1 Y s1 mo1 HA1); lia|].
    intros [] s2 mo2 (HA2 & F1 & F2 & F3 & Hc2). apply gstot_ret. unfold PostA. rewrite FCK_eq.
    split; [reflexivity|]. split; [exact HA2|]. split; [congruence|]. split; [congruence|]. split; [congruence| lia]. }
  destruct (length (anames T') <? length Client.CLIENT_PRE)%nat eqn:EL.
  - apply cgstot_lift. apply (W s' mo' T' HA' Hso Hfd Hfs). lia.
  - apply Nat.ltb_ge in EL. rewrite length_map, Lp in EL.
    apply cgstot_choice; apply cgstot_lift; [| apply (W s' mo' T' HA' Hso Hfd Hfs); lia].
    unfold HarnessC.fuzz_with.
    eapply gstot_bind; [apply (allocA_gstot Client.CLIENT_OPT T' Y s' mo' CSo); [lia| exact HA'| rewrite Lo; unfold Client.CLIENT_REQ_MAX in *; lia]|].
    intros ps2 s2 mo2 (T2 & -> & _ & HA2 & G1 & G2 & G3 & Hc2). cbn beta. rewrite Lo in Hc2. unfold Client.CLIENT_REQ_MAX in Hc2.
    apply (W s2 mo2 T2 HA2); [congruence| congruence| congruence| lia].
Qed.

Lemma fuzz_pairC : forall C X data, (length X <= 2)%nat -> C + FCK <= ok_CMAX K ->
  crsimeq (RX C X) (ProgC.fuzz_oneC data) (ProgAC.fuzz_oneAC A data) (fun _ => RX (C + FCK) X).
Proof.
  intros C X data HLX HC. unfold RSimProg.crsimeq. apply crsim_silent.
  intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs & Hc & Hm).
  exists (PostP (pX X) s1 mo1), (PostA (aX X) s2 mo2).
  split; [apply fuzz_oneC_cgstotP; exact HO|].
  split; [apply fuzz_oneAC_cgstotA; [unfold aX; rewrite length_map; exact HLX| exact HA| lia]|].
  unfold PostP, PostA. intros a s1' mo1' b s2' mo2' (-> & HO' & Hso1 & Hfd1 & Hfs1) (-> & HA' & Hso2 & Hfd2 & Hfs2 & Hc2).
  split; [reflexivity|]. split; [exact HO'|]. split; [exact HA'|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; lia.
Qed.

Lemma run_pairC : forall C X cfg payload, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> C + zlength payload + ok_QOV K + CRUNX (ok_QOV K) <= ok_CMAX K ->
  crsimeq (RX C X) (ProgC.runC cfg payload) (ProgAC.runAC A cfg payload) (fun _ => RX (C + zlength payload + ok_QOV K + CRUNX (ok_QOV K)) X).
Proof.
  intros C X cfg payload HL Hp HC. unfold ProgC.runC, ProgAC.runAC.
  apply (target_runC_sim nstep step2 PhiP Phi2 RX (ok_QOV K) (ok_CMAX K) raw_malloc (amalloc A) raw_free (afree A)
           (io_emit io) (io_emit (ioA A)) malloc_pair free_pair emit_pair RX_mono
           Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX client_nreq client_rmax (ok_QOV0 K) ProgC.fuzz_oneC (ProgAC.fuzz_oneAC A) fuzz_pairC C X cfg payload HL Hp HC).
Qed.

Lemma main_exit_pairC : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  crsim (RX 0 []) (cmbind (DriverC.main_model io raw_malloc raw_free rsP alloc_init ProgC.runC alloc_count argv) (fun code => DriverC.exit_model io code))
                  (ProgAC.progA_mainC A rsA argv) Q.
Proof.
  intros argv Q Hargv. unfold ProgAC.progA_mainC.
  apply (main_exitC_sim nstep step2 PhiP Phi2 io (ioA A) raw_malloc (amalloc A) raw_free (afree A) rsP rsA
           alloc_init (alloc_initA A) alloc_count (alloc_countA A) RX (ok_QOV K) (ok_CMAX K) (CRUNX (ok_QOV K)));
    first [ exact CRUNX_nonneg | exact (ok_QOV0 K) | exact (ok_room K) | exact malloc_pair | exact free_pair | exact RX_perm | exact RX_mono
          | exact diag_pair | exact run_pairC | exact open_pair | exact close_pair | exact read_pair | exact ioexit_pair | exact exitnode_pair | exact Hargv
          | (intros C X bm; apply rsimeq_ret; intros ? ? ? ? H; exact H) | (intros C X; apply rsimeq_ret; intros ? ? ? ? H; exact H) ].
Qed.

Lemma main_exit_pair : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  rsim (RX 0 []) (code <- main_model io raw_malloc raw_free rsP alloc_init run alloc_count argv ;; exit_model io code)
                 (progA_main A rsA argv) Q.
Proof.
  intros argv Q Hargv. unfold progA_main.
  apply (main_exit_sim nstep step2 PhiP Phi2 io (ioA A) raw_malloc (amalloc A) raw_free (afree A) rsP rsA
           alloc_init (alloc_initA A) run (runA A) alloc_count (alloc_countA A) RX (ok_QOV K) (ok_CMAX K) (CRUNX (ok_QOV K)) CRUNX_nonneg (ok_QOV0 K) (ok_room K)
           malloc_pair free_pair RX_perm RX_mono diag_pair).
  - intros C X bm. apply rsimeq_ret. intros ? ? ? ? H; exact H.
  - intros C X. apply rsimeq_ret. intros ? ? ? ? H; exact H.
  - apply run_pair.
  - apply open_pair.
  - apply close_pair.
  - apply read_pair.
  - apply ioexit_pair.
  - apply exitnode_pair.
  - exact Hargv.
Qed.

Lemma OWN_vm X s mo mo' : OWN X GT s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> OWN X GT s mo'.
Proof.
  intros [(L & Hc & HK & Hi) [Hnd _]] Hvm Hmi Hh. split; [|split; [exact Hnd| exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| exact Hvm| exact Hmi| exact Hh].
Qed.

Section Pre.
Variable pre : Monad.M (ASt A) unit.
Hypothesis pre_pair : forall C X, rsim (RX C X) startup pre (fun _ _ => RX C X).

Lemma prog_pair : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  rsim (RX 0 []) (prog_with rsP argv) (pre ;;; progA_main A rsA argv) Q.
Proof.
  intros argv Q Hargv. unfold prog_with. eapply rsim_seq; [apply pre_pair|]. intros [] []. apply main_exit_pair. exact Hargv.
Qed.

Definition treeA (sA0 : ASt A) (argv : list (list Z)) : itree node (exc unit) :=
  ebind ((pre ;;; progA_main A rsA argv) sA0) (fun p => match fst p : Empty_set with end).


Lemma RX_init : forall en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  AI K [] sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp -> ok_cost K sA0 <= 0 ->
  RX 0 [] (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs lim en inp) sA0 moA0.
Proof.
  intros [sp brk0 mbase rnd] inp sA0 moA0 Hve Hvi HA Hso Hfd Hfs Hc0.
  (* the launch facts Spec/ModelInv GI_init takes. *)
  assert (Hrd : in_channel_reader inp = true)
    by (destruct Hvi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hvi) in Hve. destruct Hve as ((Hsp1 & Hsp2 & _) & Hbrk & (Hmb & _) & _).
  split; [| split; [exact HA| split; [cbn; symmetry; exact Hso| split; [rewrite m_fds_mo0; symmetry; exact Hfd| split; [rewrite m_fs_mo0; symmetry; exact Hfs|]]]]].
  2:{ split; [exact Hc0|]. pose proof (ok_room K) as HR. pose proof (ok_QOV0 K) as HQ. pose proof (CDONE_nonneg (ok_QOV K) HQ) as HD. pose proof CRUNX_nonneg as HX. unfold MAX_INPUT in HR. lia. }
  unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp].
  eapply OWN_weakG; [apply (GI_init psegs brk0 mbase sp lim inp _ _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain low_plain Hmb Hrd)|]. intros _; exact I.
Qed.

Lemma argv_Z_pieces' : forall argv, valid_argv argv -> Forall (fun a => zlength a <= PIECE_MAX) (argv_Z argv).
Proof.
  intros argv Hv. eapply Forall_impl; [|apply (argv_Z_short argv Hv)]. intros a Ha. unfold ARG_MAX_LEN, PIECE_MAX in *. lia.
Qed.

Lemma tglob_prog : forall en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tglob nstep PhiP (prog psegs rsP inp en) (mo0 psegs lim en inp).
Proof.
  intros en inp He Hi. apply tglob_PhiP_intro.
  - (* the launch's model is [with_vdso .. (init_model ..)] and its [minv] takes the channel
       reader: TopLevel's [mo0_minv] proves it from the entry, Sv48 and the reader. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    exact (mo0_minv _ _ _ _ en inp He (valid_input_either_va_size _ Hi) Hrd).
  - destruct en; reflexivity.
  - exact (proj2 (prog_model_ok_plain_L lim rsP en inp Hlim He Hi)).
  - exact (never_forced_pL lim rsP en inp Hlim He Hi).
Qed.


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

Theorem equiv_core_pre : forall en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  AI K [] sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp -> ok_cost K sA0 <= 0 ->
  tglob step2 Phi2 (treeA sA0 (argv_Z (in_argv inp))) moA0 ->
  (forall tr, ttrace nstep nexit (prog psegs rsP inp en) (mo0 psegs lim en inp) tr
              <-> ttrace step2 nexit (treeA sA0 (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (treeA sA0 (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros en inp sA0 moA0 He Hi HA Hso Hfd Hfs Hc0 GA. pose proof Hi as (Hargv & _).
  pose proof (prog_model_ok_plain_L lim rsP en inp Hlim He Hi) as [NL _].
  destruct (rsim_ttrace nstep step2 nexit nexit PhiP Phi2 (RX 0 []) (prog_with rsP (argv_Z (in_argv inp))) (pre ;;; progA_main A rsA (argv_Z (in_argv inp)))
              (fun _ _ _ _ _ _ => False) (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs lim en inp) sA0 moA0
              (prog_pair _ _ (argv_Z_pieces' _ Hargv)) (RX_init en inp sA0 moA0 He Hi HA Hso Hfd Hfs Hc0)) as [EQ NL2].
  - apply (tglob_after_empty nstep PhiP _ (fun p => match fst p : Empty_set with end)). exact (tglob_prog en inp He Hi).
  - apply (tglob_after_empty step2 Phi2 _ (fun p => match fst p : Empty_set with end)). exact GA.
  - intros tr r mo' Hp. destruct r as [|[[] ?]]. apply (NL tr Unr mo'). unfold prog, prog_itree. apply tpath_ebind. left. auto.
  - split.
    + intros tr. unfold prog, prog_itree, treeA. rewrite !ttrace_after_empty. apply EQ.
    + intros tr r mo' Hp. unfold treeA in Hp. apply tpath_after_empty in Hp as [r' Hp]. exact (NL2 tr r' mo' Hp).
Qed.
Definition treeAD (D : hist -> bool) (sA0 : ASt A) (argv : list (list Z)) : itree node (exc unit) :=
  ebind (RES D [] (cmbind (clift pre) (fun _ => ProgAC.progA_mainC A rsA argv)) sA0) (fun p => match fst p : Empty_set with end).

Lemma prog_pairC : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  crsim (RX 0 []) (prog_withC rsP argv) (cmbind (clift pre) (fun _ => ProgAC.progA_mainC A rsA argv)) Q.
Proof.
  intros argv Q Hargv. unfold prog_withC. eapply crsim_bind; [apply crsim_lift; apply pre_pair|]. intros [] []. apply main_exit_pairC. exact Hargv.
Qed.

Lemma tglob_progD : forall D en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tglob nstep PhiP (progD D psegs rsP inp en) (mo0 psegs lim en inp).
Proof.
  intros D en inp He Hi. apply tglob_PhiP_intro.
  - (* the launch's model is [with_vdso .. (init_model ..)] and its [minv] takes the channel
       reader: TopLevel's [mo0_minv] proves it from the entry, Sv48 and the reader. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    exact (mo0_minv _ _ _ _ en inp He (valid_input_either_va_size _ Hi) Hrd).
  - destruct en; reflexivity.
  - exact (proj2 (prog_model_ok_plain_DL lim D rsP en inp Hlim He Hi)).
  - exact (never_forced_p_DL lim D rsP en inp Hlim He Hi).
Qed.

Theorem equiv_core_preD : forall D1 D2 en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  AI K [] sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp -> ok_cost K sA0 <= 0 ->
  tglob step2 Phi2 (treeAD D2 sA0 (argv_Z (in_argv inp))) moA0 ->
  (forall tr, ttrace nstep nexit (progD D1 psegs rsP inp en) (mo0 psegs lim en inp) tr
              <-> ttrace step2 nexit (treeAD D2 sA0 (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (treeAD D2 sA0 (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros D1 D2 en inp sA0 moA0 He Hi HA Hso Hfd Hfs Hc0 GA. pose proof Hi as (Hargv & _).
  pose proof (prog_model_ok_plain_DL lim D1 rsP en inp Hlim He Hi) as [NL _].
  destruct (rsim_ttrace nstep step2 nexit nexit PhiP Phi2 (RX 0 [])
              (RES D1 [] (prog_withC rsP (argv_Z (in_argv inp))))
              (RES D2 [] (cmbind (clift pre) (fun _ => ProgAC.progA_mainC A rsA (argv_Z (in_argv inp)))))
              (fun _ _ _ _ _ _ => False) (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs lim en inp) sA0 moA0
              (crsim_RES nstep step2 nexit nexit PhiP Phi2 _ _ _ _ (prog_pairC _ _ (argv_Z_pieces' _ Hargv)) D1 [] D2 [])
              (RX_init en inp sA0 moA0 He Hi HA Hso Hfd Hfs Hc0)) as [EQ NL2].
  - apply (tglob_after_empty nstep PhiP _ (fun p => match fst p : Empty_set with end)). exact (tglob_progD D1 en inp He Hi).
  - apply (tglob_after_empty step2 Phi2 _ (fun p => match fst p : Empty_set with end)). exact GA.
  - intros tr r mo' Hp. destruct r as [|[[] ?]]. apply (NL tr Unr mo'). unfold progD, progD_itree, prog_withD. apply tpath_ebind. left. auto.
  - split.
    + intros tr. unfold progD, progD_itree, prog_withD, treeAD. rewrite !ttrace_after_empty. apply EQ.
    + intros tr r mo' Hp. unfold treeAD in Hp. apply tpath_after_empty in Hp as [r' Hp]. exact (NL2 tr r' mo' Hp).
Qed.
End Pre.

Lemma startup_pair : forall C X, rsim (RX C X) startup (mret tt) (fun _ _ => RX C X).
Proof.
  intros C X. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs & Hc) G1 G2.
  destruct (OWN_minv _ _ _ HO) as [Hmi Hh].
  eexists _, _. split; [apply (startup_STOT s1 mo1 Hmi Hh)| split; [apply STOT_ret|]].
  intros [] s1' mo1' [] s2' mo2' (-> & Hvm & Hfd1 & Hfs1 & Hmi' & Hh') (_ & -> & ->).
  split; [exact (OWN_vm _ _ _ _ HO Hvm Hmi' Hh')|]. split; [exact HA|]. split; [exact Hso|]. split; [congruence|]. split; [congruence| exact Hc].
Qed.

Theorem equiv_core : forall en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp -> AHAND inp sA0 moA0 ->
  (forall tr, ttrace nstep nexit (prog psegs rsP inp en) (mo0 psegs lim en inp) tr
              <-> ttrace step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros en inp sA0 moA0 He Hi (HA & Hso & Hfd & Hfs & Hc0 & GA).
  change (progA_tree A sA0 rsA (argv_Z (in_argv inp))) with (treeA (mret tt) sA0 (argv_Z (in_argv inp))) in GA |- *.
  exact (equiv_core_pre (mret tt) startup_pair en inp sA0 moA0 He Hi HA Hso Hfd Hfs Hc0 GA).
Qed.

Definition AHAND_D (D : hist -> bool) (inp : ProcInput) (sA0 : ASt A) (moA0 : Model) : Prop :=
  AI K [] sA0 moA0 /\ a_so A sA0 = stdout_init /\ m_fds moA0 = init_fds /\ m_fs moA0 = in_fs inp
  /\ ok_cost K sA0 <= 0
  /\ tglob step2 Phi2 (ProgAC.progA_treeD A D sA0 rsA (argv_Z (in_argv inp))) moA0.

Theorem equiv_coreD : forall D1 D2 en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp -> AHAND_D D2 inp sA0 moA0 ->
  (forall tr, ttrace nstep nexit (progD D1 psegs rsP inp en) (mo0 psegs lim en inp) tr
              <-> ttrace step2 nexit (ProgAC.progA_treeD A D2 sA0 rsA (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (ProgAC.progA_treeD A D2 sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros D1 D2 en inp sA0 moA0 He Hi (HA & Hso & Hfd & Hfs & Hc0 & GA).
  change (ProgAC.progA_treeD A D2 sA0 rsA (argv_Z (in_argv inp))) with (treeAD (mret tt) D2 sA0 (argv_Z (in_argv inp))) in GA |- *.
  exact (equiv_core_preD (mret tt) startup_pair D1 D2 en inp sA0 moA0 He Hi HA Hso Hfd Hfs Hc0 GA).
Qed.

End ASide.


Definition toP (en : ExecEntry) : ExecEntry :=
  mkEntry (en_sp en) (Z_to_bv 64 (reserved_top (segments_reserved psegs))) (en_mmap_base en) (en_draw en).

Lemma toP_valid : forall segsX pcX phX en inp,
  valid_entry (mkImage segsX pcX phX) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) (toP en) inp.
Proof.
  intros segsX pcX phX [sp brk0 mbase] inp H. cbn [valid_entry valid_entry_va toP en_sp en_mmap_base] in H |- *. destruct H as (Hsp & _ & Hmb & Hst).
  split; [exact Hsp|]. split; [| split; [exact Hmb| exact Hst]].
  unfold valid_brk. rewrite reserved_top_plain. rewrite unsigned_lit by lia. unfold brk_aslr_max, page_size. split; [lia|]. split; [lia| reflexivity].
Qed.

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require ITreeA.

Theorem equiv_PA (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
        (rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) :
  forall lim, 2^31 <= lim -> forall enP inp sA0 moA0,
    valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
    trace_equiv (tree_traces (prog psegs rsP inp enP) (mo0 psegs lim enP inp))
                (ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
    /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros lim Hlim enP inp sA0 moA0 HeP Hi HH.
  destruct (equiv_core A step2 Phi2 MI2 rsP rsA K lim Hlim enP inp sA0 moA0 HeP Hi HH) as [EQ NL2].
  split; [| exact NL2]. intros tr. unfold tree_traces, ITreeA.ptraces. split; intros (full & Hf & Hp); exists full; split; auto; apply EQ; exact Hf.
Qed.

Corollary equiv_PA_toP (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
        (rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) :
  forall lim, 2^31 <= lim -> forall segsX pcX phX enX inp sA0 moA0,
    valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
    trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs lim (toP enX) inp))
                (ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
    /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof. intros lim Hlim segsX pcX phX enX inp sA0 moA0 HeX Hi HH. exact (equiv_PA A step2 Phi2 MI2 rsP rsA K lim Hlim (toP enX) inp sA0 moA0 (toP_valid _ _ _ _ _ HeX) Hi HH). Qed.


Definition PasA : AAlloc := mkAAlloc PState bptr raw_malloc raw_free (fun _ _ _ _ => mret tt) ptr_addr ps_so set_so_ps.
Definition AIP (Y : list (bptr * Z)) (s : PState) (mo : Model) : Prop := OWN (map fst Y) GT s mo.

Lemma p_get_set : forall v s, ps_so (set_so_ps v s) = v. Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma p_set_set : forall v w s, set_so_ps v (set_so_ps w s) = set_so_ps v s. Proof. intros v w [? ? ? ?]; reflexivity. Qed.
Lemma p_set_get : forall s, set_so_ps (ps_so s) s = s. Proof. intros [? ? ? ?]; reflexivity. Qed.
Lemma p_addr_so : forall v s p, ptr_addr (set_so_ps v s) p = ptr_addr s p. Proof. intros v [? ? ? ?] p; reflexivity. Qed.

Lemma AIP_perm : forall Y Y' s mo, Permutation Y Y' -> AIP Y s mo -> AIP Y' s mo.
Proof. intros Y Y' s mo HP H. unfold AIP in *. eapply OWN_perm; [apply Permutation_map; exact HP| exact H]. Qed.
Lemma AIP_so : forall Y s mo v, AIP Y s mo -> AIP Y (set_so_ps v s) mo.
Proof. intros Y s mo v H. unfold AIP in *. eapply OWN_other; [exact H| reflexivity| reflexivity| exact I]. Qed.
Lemma AIP_model : forall Y s mo, AIP Y s mo -> minv mo /\ m_halted mo = None.
Proof. intros Y s mo H. exact (OWN_minv _ _ _ H). Qed.
Lemma AIP_fds : forall Y s mo f, AIP Y s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> AIP Y s (with_fds f mo).
Proof. intros Y s mo f H M Hh. exact (OWN_fds _ _ _ _ H M Hh). Qed.

Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Definition PCMAX : Z := CDONE 0 + MAX_INPUT + 0 + CRUNX 0.
Lemma PCMAX_room : CDONE 0 + MAX_INPUT + 0 + CRUNX 0 <= PCMAX. Proof. apply Z.le_refl. Qed.

Lemma P_malloc : forall Y n s mo, AIP Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  tglob nstep PhiP (raw_malloc n s) mo ->
  STOTP (raw_malloc n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AIP ((q, n) :: Y) s' mo' /\ n < 2^63
                         /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ 0 <= 0 + n + 0).
Proof.
  intros Y n s mo HA Hn _ G. eapply STOT_mono; [apply (raw_malloc_STOT (map fst Y) GT n s mo frame_ok_GT HA ltac:(lia) (size_overflows_REQMAX n Hn) G)|].
  intros r s' mo' (p & -> & HO & H63 & Hso & _ & Hfd & Hfs). exists p. unfold AIP. cbn [map fst]. splits; auto. lia.
Qed.

Lemma P_free : forall Y q n s mo, AIP ((q, n) :: Y) s mo -> 0 <= PCMAX -> tglob nstep PhiP (raw_free q s) mo ->
  STOTP (raw_free q s) mo (fun _ s' mo' => AIP Y s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ 0 <= 0).
Proof.
  intros Y q n s mo HA _ G. eapply STOT_mono; [apply (raw_free_STOT (map fst Y) GT q s mo frame_ok_GT HA G)|].
  intros [] s' mo' (HO & Hso & _ & Hfd & Hfs). unfold AIP. splits; auto. lia.
Qed.

Lemma P_annot : forall Y (q : bptr) (cap old new : Z) s mo, AIP Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
  (old = 0 \/ new = 0) ->
  tglob nstep PhiP (mret tt s) mo ->
  STOTP (mret tt s) mo (fun _ s' mo' => AIP Y s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ 0 <= 0).
Proof.
  intros Y q cap old new s mo HA _ _ _ _ _. eapply STOT_mono; [apply STOT_ret|]. intros [] s' mo' (_ & -> & ->). splits; auto. lia.
Qed.

Definition KP : AAllocOK PasA nstep PhiP minv :=
  mkAAllocOK PasA nstep PhiP minv sub1 same1 io1 MI1_pres p_get_set p_set_set p_set_get p_addr_so
             AIP AIP_perm AIP_so AIP_model AIP_fds
             0 PCMAX (Z.le_refl 0) PCMAX_room (fun _ => 0) (fun _ _ => eq_refl)
             (fun Y n s mo HA Hn HH _ => P_malloc Y n s mo HA Hn HH) P_free P_annot.

Local Notation RXP := (RX PasA nstep PhiP minv KP).

Lemma startup_startup : forall C X, rsim nstep nstep nexit nexit PhiP PhiP (RXP C X) startup startup (fun _ _ => RXP C X).
Proof.
  intros C X. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs & Hc) G1 G2.
  destruct (OWN_minv _ _ _ HO) as [Hmi1 Hh1]. destruct (OWN_minv _ _ _ HA) as [Hmi2 Hh2].
  eexists _, _. split; [apply (startup_STOT s1 mo1 Hmi1 Hh1)| split; [apply (startup_STOT s2 mo2 Hmi2 Hh2)|]].
  intros [] s1' mo1' [] s2' mo2' (-> & Hvm1 & Hfd1 & Hfs1 & Hmi1' & Hh1') (-> & Hvm2 & Hfd2 & Hfs2 & Hmi2' & Hh2').
  split; [exact (OWN_vm _ _ _ _ HO Hvm1 Hmi1' Hh1')|]. split; [exact (OWN_vm _ _ _ _ HA Hvm2 Hmi2' Hh2')|]. split; [exact Hso|]. split; [congruence|]. split; [congruence| exact Hc].
Qed.

Theorem equiv_PP : forall lim, 2^31 <= lim -> forall rs rs' en en' inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) en' inp -> valid_input_either inp ->
  trace_equiv (tree_traces (prog psegs rs inp en) (mo0 psegs lim en inp))
              (tree_traces (prog psegs rs' inp en') (mo0 psegs lim en' inp)).
Proof.
  intros lim Hlim rs rs' en en' inp He He' Hi. apply trees_equiv_of_ttrace.
  change (prog psegs rs' inp en') with (treeA PasA rs' startup (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))).
  apply (equiv_core_pre PasA nstep PhiP minv rs rs' KP lim Hlim startup startup_startup en inp _ _ He Hi).
  - (* the launch facts Spec/ModelInv GI_init takes. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    destruct en' as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He'. destruct He' as ((Hsp1 & Hsp2 & _) & Hbrk & (Hmb & _) & _). unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp AI KP]. unfold AIP. cbn [map].
    eapply OWN_weakG; [apply (GI_init psegs brk0 mbase sp lim inp _ _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain low_plain Hmb Hrd)|]. intros _; exact I.
  - reflexivity.
  - apply m_fds_mo0.
  - apply m_fs_mo0.
  - apply Z.le_refl.
  - change (treeA PasA rs' startup (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))) with (prog psegs rs' inp en'). apply (tglob_prog rs' lim Hlim); assumption.
Qed.


Theorem equiv_PA_D (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
        (rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) :
  forall lim, 2^31 <= lim -> forall D1 D2 enP inp sA0 moA0,
    valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp -> AHAND_D A step2 Phi2 MI2 rsA K D2 inp sA0 moA0 ->
    trace_equiv (tree_traces (progD D1 psegs rsP inp enP) (mo0 psegs lim enP inp))
                (ITreeA.ptraces step2 nexit (ProgAC.progA_treeD A D2 sA0 rsA (argv_Z (in_argv inp))) moA0)
    /\ (forall tr r mo', ~ tpath step2 (ProgAC.progA_treeD A D2 sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros lim Hlim D1 D2 enP inp sA0 moA0 HeP Hi HH.
  destruct (equiv_coreD A step2 Phi2 MI2 rsP rsA K lim Hlim D1 D2 enP inp sA0 moA0 HeP Hi HH) as [EQ NL2].
  split; [| exact NL2]. intros tr. unfold tree_traces, ITreeA.ptraces. split; intros (full & Hf & Hp); exists full; split; auto; apply EQ; exact Hf.
Qed.

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.PlainU0 Require Import UImg.
Lemma tglob_progD_u : forall D rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  tglob nstep PhiP (progD D usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof.
  intros D rs en inp He Hi. apply tglob_PhiP_intro.
  - (* the launch's model is [with_vdso .. (init_model ..)] and its [minv] takes the channel
       reader: TopLevel's [mo0_minv] proves it from the entry, Sv48 and the reader. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    exact (mo0_minv _ _ _ _ en inp He (valid_input_either_va_size _ Hi) Hrd).
  - destruct en; reflexivity.
  - exact (proj2 (prog_model_ok_ubsan_D D rs en inp He Hi)).
  - exact (never_forced_u_D D rs en inp He Hi).
Qed.

Theorem equiv_PP_D : forall lim, 2^31 <= lim -> forall D1 D2 rs rs' en en' inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) en' inp -> valid_input_either inp ->
  trace_equiv (tree_traces (progD D1 psegs rs inp en) (mo0 psegs lim en inp))
              (tree_traces (progD D2 psegs rs' inp en') (mo0 psegs lim en' inp)).
Proof.
  intros lim Hlim D1 D2 rs rs' en en' inp He He' Hi. apply trees_equiv_of_ttrace.
  change (progD D2 psegs rs' inp en') with (treeAD PasA rs' startup D2 (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))).
  apply (equiv_core_preD PasA nstep PhiP minv rs rs' KP lim Hlim startup startup_startup D1 D2 en inp _ _ He Hi).
  - (* the launch facts Spec/ModelInv GI_init takes. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    destruct en' as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He'. destruct He' as ((Hsp1 & Hsp2 & _) & Hbrk & (Hmb & _) & _). unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp AI KP]. unfold AIP. cbn [map].
    eapply OWN_weakG; [apply (GI_init psegs brk0 mbase sp lim inp _ _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain low_plain Hmb Hrd)|]. intros _; exact I.
  - reflexivity.
  - apply m_fds_mo0.
  - apply m_fs_mo0.
  - apply Z.le_refl.
  - change (treeAD PasA rs' startup D2 (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))) with (progD D2 psegs rs' inp en'). apply (tglob_progD rs' lim Hlim D2); assumption.
Qed.

Theorem equiv_PU_D : forall D1 D2 rs rs' en en' inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage usegs u_init_pc u_phdrs) en' inp -> valid_input_either inp ->
  trace_equiv (tree_traces (progD D1 psegs rs inp en) (mo0 psegs source_alloc_limit en inp))
              (tree_traces (progD D2 usegs rs' inp en') (mo0 usegs target_alloc_limit en' inp)).
Proof.
  intros D1 D2 rs rs' en en' inp He He' Hi. apply trees_equiv_of_ttrace.
  change (progD D2 usegs rs' inp en') with (treeAD PasA rs' startup D2 (ps_init (reservedZ usegs) (entry_atop en')) (argv_Z (in_argv inp))).
  apply (equiv_core_preD PasA nstep PhiP minv rs rs' KP source_alloc_limit ImgFacts.lim_p startup startup_startup D1 D2 en inp _ _ He Hi).
  - (* the launch facts Spec/ModelInv GI_init takes. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    destruct en' as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He'. destruct He' as ((Hsp1 & Hsp2 & _) & Hbrk & (Hmb & _) & _). unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp AI KP]. unfold AIP. cbn [map].
    eapply OWN_weakG; [apply (GI_init usegs brk0 mbase sp target_alloc_limit inp _ _ Hbrk ltac:(rewrite reserved_top_ubsan; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ImgFacts.ceil_ubsan ImgFacts.low_ubsan Hmb Hrd)|]. intros _; exact I.
  - reflexivity.
  - apply m_fds_mo0.
  - apply m_fs_mo0.
  - apply Z.le_refl.
  - change (treeAD PasA rs' startup D2 (ps_init (reservedZ usegs) (entry_atop en')) (argv_Z (in_argv inp))) with (progD D2 usegs rs' inp en'). apply tglob_progD_u; assumption.
Qed.
