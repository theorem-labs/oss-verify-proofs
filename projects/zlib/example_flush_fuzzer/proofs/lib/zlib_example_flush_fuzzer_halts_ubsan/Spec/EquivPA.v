(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim Monad MSafe MSafeP MPaths STree Malloc Stdio Adapter Driver
  PState Prog StepB KLink KEv KEvP ModelInv ImgFacts EquivShared EquivProg RSim RSimProg SizeHist PTotal ProgA LB_StmtA LB_Main FreshIface TargetSafeC ModelInvC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import CMonad CRSim ProgC ProgAC ModelOKC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require HarnessC AdapterC DriverC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import TopLevel ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PlainU0 Require UImg.
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


Definition CRUNX (q : Z) : Z := RUNX q.
Lemma CRUNX_eq q : CRUNX q = 4 * (2^21 + 766 + 2^20 + 308056 + 9 * q).   (* 1.4: RSimProg.FC's sizes 5968 / 7176 *)
Proof. reflexivity. Qed.

Section ASide.
Variable FM : flush_model.
Variable FK : fkit.
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
  AI : list (aptr A * Z) -> Z -> ASt A -> Model -> Prop;
  ok_AI_perm : forall Y Y' k s mo, Permutation Y Y' -> AI Y k s mo -> AI Y' k s mo;
  ok_AI_kle : forall Y k k' s mo, k <= k' -> AI Y k s mo -> AI Y k' s mo;
  ok_AI_so : forall Y k s mo v, AI Y k s mo -> AI Y k (a_set_so A v s) mo;
  ok_AI_model : forall Y k s mo, AI Y k s mo -> MI2 mo /\ m_halted mo = None;
  ok_AI_fds : forall Y k s mo f, AI Y k s mo -> MI2 (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI Y k s (with_fds f mo);
  ok_QOV : Z;
  ok_CMAX : Z;
  ok_QOV0 : 0 <= ok_QOV;
  ok_room : CDONE ok_QOV + MAX_INPUT + ok_QOV + CRUNX ok_QOV <= ok_CMAX;
  ok_cost : ASt A -> Z;
  ok_cost_so : forall v s, ok_cost (a_set_so A v s) = ok_cost s;
  ok_malloc : forall Y k n s mo, AI Y k s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) -> FPRE Y k n ->
      tglob step2 Phi2 (amalloc A n s) mo ->
      STOT2 (amalloc A n s) mo
            (fun r s' mo' => exists q, r = Some q /\ AI ((q, n) :: Y) (k + 1) s' mo' /\ n < 2^63 /\ (KREQ n -> afresh A s s' q = true)
                             /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                             /\ ok_cost s' <= ok_cost s + n + ok_QOV);
  ok_free : forall Y k q n s mo, AI ((q, n) :: Y) k s mo -> ok_cost s <= ok_CMAX ->
      tglob step2 Phi2 (afree A q s) mo ->
      STOT2 (afree A q s) mo
            (fun _ s' mo' => AI Y k s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                             /\ ok_cost s' <= ok_cost s)
}.

Variable K : AAllocOK.
Variable lim : Z.
Hypothesis Hlim : 2^31 <= lim.


Local Notation rel := (rel PState (ASt A)).
Local Notation rsim := (rsim nstep step2 nexit nexit PhiP Phi2).
Local Notation triple := (bptr * aptr A * Z)%type.

Definition pX (X : list triple) : list bptr := map (fun b => fst (fst b)) X.
Definition pXn (X : list triple) : list (bptr * Z) := map (fun b => (fst (fst b), snd b)) X.
Definition aX (X : list triple) : list (aptr A * Z) := map (fun b => (snd (fst b), snd b)) X.
Definition GT : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_GT : frame_ok GT. Proof. intros ? ? ? ? _ _ _ _; exact I. Qed.

Definition RX (C k : Z) (X : list triple) : rel := fun s1 mo1 s2 mo2 =>
  (OWN (pX X) GT s1 mo1 /\ fk_F FK (pXn X) k (ps_m s1)) /\ AI K (aX X) k s2 mo2 /\ ps_so s1 = a_so A s2 /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2
  /\ ok_cost K s2 <= C /\ ok_cost K s2 <= ok_CMAX K.

Lemma sizes_aX X : map snd (aX X) = map snd X. Proof. unfold aX. rewrite map_map. reflexivity. Qed.
Lemma pX_pXn X : map fst (pXn X) = pX X. Proof. unfold pX, pXn. rewrite map_map. reflexivity. Qed.
Lemma FPRE_pXn X k n : FPRE (xsz X) k n -> FPRE (pXn X) k n.
Proof. unfold xsz, pXn. intros H. apply (FPRE_map (fun b : triple => (fst (fst b), snd b))); [intros; reflexivity|]. apply (FPRE_map (fun t : triple => (tt, snd t))) in H; [exact H| intros; reflexivity]. Qed.
Lemma FPRE_aX X k n : FPRE (xsz X) k n -> FPRE (aX X) k n.
Proof. unfold xsz, aX. intros H. apply (FPRE_map (fun b : triple => (snd (fst b), snd b))); [intros; reflexivity|]. apply (FPRE_map (fun t : triple => (tt, snd t))) in H; [exact H| intros; reflexivity]. Qed.

Lemma OWN_minv X s mo : OWN X GT s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(L & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma OWN_fds X s mo f : OWN X GT s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> OWN X GT s (with_fds f mo).
Proof.
  intros [(L & Hc & HK & Hi) [Hnd _]] Hmi Hh. split; [|split; [exact Hnd| exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| apply m_vmmaps_with_fds| exact Hmi| exact Hh].
Qed.

Lemma RX_perm : forall C k X Y s1 mo1 s2 mo2, Permutation X Y -> RX C k X s1 mo1 s2 mo2 -> RX C k Y s1 mo1 s2 mo2.
Proof.
  intros C k X Y s1 mo1 s2 mo2 HP ([HO HF] & HA & Hso & Hfd & Hfs). split; [split|split; [| auto]].
  - eapply OWN_perm; [| exact HO]. unfold pX. apply Permutation_map. exact HP.
  - eapply (fk_perm FK); [| exact HF]. unfold pXn. apply Permutation_map. exact HP.
  - eapply (ok_AI_perm K); [| exact HA]. unfold aX. apply Permutation_map. exact HP.
Qed.

Lemma RX_mono : forall C C' k k' X s1 mo1 s2 mo2, C <= C' -> k <= k' -> RX C k X s1 mo1 s2 mo2 -> RX C' k' X s1 mo1 s2 mo2.
Proof.
  intros C C' k k' X s1 mo1 s2 mo2 HC Hk ([HO HF] & HA & Hso & Hfd & Hfs & Hc & Hm). unfold RX. splits; auto; [eapply (fk_kle FK); eauto| eapply (ok_AI_kle K); eauto| lia].
Qed.

Lemma RX_get : forall C k X s1 mo1 s2 mo2, RX C k X s1 mo1 s2 mo2 -> ps_so s1 = a_so A s2.
Proof. intros C k X s1 mo1 s2 mo2 (_ & _ & H & _). exact H. Qed.

Lemma RX_set : forall C k X s1 mo1 s2 mo2 v, RX C k X s1 mo1 s2 mo2 -> RX C k X (set_so_ps v s1) mo1 (a_set_so A v s2) mo2.
Proof.
  intros C k X s1 mo1 s2 mo2 v ([HO HF] & HA & Hso & Hfd & Hfs & Hc & Hm). split; [| split; [| split; [| split; [exact Hfd| split; [exact Hfs|]]]]].
  - split; [eapply OWN_other; [exact HO| reflexivity| reflexivity| exact I]| destruct s1; exact HF].
  - apply (ok_AI_so K). exact HA.
  - rewrite (ok_get_set K). destruct s1; reflexivity.
  - rewrite (ok_cost_so K). split; assumption.
Qed.

Lemma RX_models : forall C k X s1 mo1 s2 mo2, RX C k X s1 mo1 s2 mo2 ->
  minv mo1 /\ MI2 mo2 /\ m_halted mo1 = None /\ m_halted mo2 = None /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
Proof.
  intros C k X s1 mo1 s2 mo2 ([HO HF] & HA & Hso & Hfd & Hfs & _). destruct (OWN_minv _ _ _ HO) as [M1 H1]. destruct (ok_AI_model K _ _ _ _ HA) as [M2 H2]. splits; auto.
Qed.

Lemma RX_tables : forall C k X s1 mo1 s2 mo2 f, RX C k X s1 mo1 s2 mo2 ->
  minv (with_fds f mo1) -> MI2 (with_fds f mo2) -> m_halted (with_fds f mo1) = None -> m_halted (with_fds f mo2) = None ->
  RX C k X s1 (with_fds f mo1) s2 (with_fds f mo2).
Proof.
  intros C k X s1 mo1 s2 mo2 f ([HO HF] & HA & Hso & Hfd & Hfs & Hc) M1 M2 H1 H2. split; [| split; [| split; [exact Hso| split; [reflexivity| split; [| exact Hc]]]]].
  - split; [apply OWN_fds; auto| exact HF].
  - apply (ok_AI_fds K); auto.
  - rewrite !m_fs_with_fds. exact Hfs.
Qed.


Lemma size_overflows_REQMAX n : 0 <= n <= REQMAX -> size_overflows n = false.
Proof. intros Hn. unfold size_overflows, REQMAX in *. apply Z.leb_gt. lia. Qed.

Local Notation Qm := (Qm RX (ok_QOV K) fresh_topb (afresh A)).

Lemma malloc_pair : forall C k X n s10 s20, 0 <= n <= REQMAX -> HISTOK (n :: map snd X) -> FPRE (xsz X) k n -> C + n + ok_QOV K <= ok_CMAX K ->
  rsim (fun s1 mo1 s2 mo2 => s1 = s10 /\ s2 = s20 /\ RX C k X s1 mo1 s2 mo2) (raw_malloc n) (amalloc A n) (Qm C k X n s10 s20).
Proof.
  intros C k X n s10 s20 Hn HH HF HC. apply rsim_silent. intros s1 mo1 s2 mo2 (-> & -> & ([HO HF1] & HA & Hso & Hfd & Hfs & Hc & Hm)) G1 G2.
  eexists _, _. split; [| split].
  - apply (fk_stot_m FK GT (pXn X) k n s10 mo1 frame_ok_GT ltac:(rewrite pX_pXn; exact HO) HF1 ltac:(lia) (size_overflows_REQMAX n Hn) (FPRE_pXn _ _ _ HF) G1).
  - apply (ok_malloc K (aX X) k n s20 mo2 HA Hn ltac:(rewrite sizes_aX; exact HH) (FPRE_aX _ _ _ HF) G2).
  - intros a s1' mo1' b s2' mo2' (p & -> & HO' & HF' & Hn63 & HFr1 & Hso1 & Hfa1 & Hfd1 & Hfs1) (q & -> & HA' & _ & HFr2 & Hso2 & Hfd2 & Hfs2 & Hc2). cbn [RSimProg.Qm].
    split; [| split; [exact Hn63| intros HK; split; [exact (HFr1 HK)| exact (HFr2 HK)]]].
    split; [split; [rewrite pX_pXn in HO'; exact HO'| exact HF']|]. split; [exact HA'|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; lia.
Qed.

Lemma free_pair : forall C k X p q n, rsim (RX C k ((p, q, n) :: X)) (raw_free p) (afree A q) (fun _ _ => RX C k X).
Proof.
  intros C k X p q n. apply rsim_silent. intros s1 mo1 s2 mo2 ([HO HF1] & HA & Hso & Hfd & Hfs & Hc & Hm) G1 G2.
  eexists _, _. split; [| split].
  - apply (fk_stot_f FK GT (pXn X) k p n s1 mo1 frame_ok_GT ltac:(rewrite pX_pXn; exact HO) HF1 G1).
  - apply (ok_free K (aX X) k q n s2 mo2 HA Hm G2).
  - intros a s1' mo1' b s2' mo2' (HO' & HF' & Hso1 & Hfa1 & Hfd1 & Hfs1) (HA' & Hso2 & Hfd2 & Hfs2 & Hc2).
    split; [split; [rewrite pX_pXn in HO'; exact HO'| exact HF']|]. split; [exact HA'|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; lia.
Qed.


Lemma sub1 : forall n mo r mo' e, ~ nf_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma same1 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstep n mo r mo e. Proof. auto. Qed.
Lemma io1 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> minv mo -> m_halted mo = None -> minv mo' /\ m_halted mo' = None.
Proof. intros n mo rsp mo' evs Hst _ Hmi Hh. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi']. auto. Qed.

Local Notation rsimeq := (rsimeq nstep step2 PhiP Phi2).

Lemma diag_pair : forall C k X d, diag_short d -> rsimeq (RX C k X) (io_diag io d) (io_diag (ioA A) d) (fun _ => RX C k X).
Proof. intros C k X d _. cbn [io ioA io_diag io_S]. apply (s_diag_sim nstep step2 PhiP Phi2 sub1 same1 (ok_sub2 K) (ok_same2 K)). Qed.

Lemma emit_pair : forall C k X v, rsimeq (RX C k X) (io_emit io v) (io_emit (ioA A) v) (fun _ => RX C k X).
Proof.
  intros C k X v. cbn [io ioA io_emit io_S].
  apply (s_emit_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX C k X) (RX_get C k X) (RX_set C k X)).
Qed.

Lemma fpr_pair : forall C k X ps, Forall (fun p => zlength p <= TargetSafeC.PIECE_MAX) ps ->
  rsimeq (RX C k X) (stderr_fprintf (St:=PState) ps) (stderr_fprintf (St:=ASt A) ps) (fun _ => RX C k X).
Proof. intros C k X ps _. apply (stderr_fprintf_sim nstep step2 PhiP Phi2 sub1 same1 (ok_sub2 K) (ok_same2 K)). Qed.

Lemma fwr_pair : forall C k X bs, zlength bs <= TargetSafeC.PIECE_MAX ->
  rsimeq (RX C k X) (stderr_fwrite (St:=PState) bs) (stderr_fwrite (St:=ASt A) bs) (fun _ => RX C k X).
Proof. intros C k X bs _. apply (stderr_fwrite_sim nstep step2 PhiP Phi2 sub1 same1 (ok_sub2 K) (ok_same2 K)). Qed.

Lemma ioexit_pair : forall C k X, rsimeq (RX C k X) (io_exit io) (io_exit (ioA A)) (fun _ => RX C k X).
Proof.
  intros C k X. cbn [io ioA io_exit io_S].
  apply (stdout_exit_flush_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX C k X) (RX_get C k X) (RX_set C k X)).
Qed.

Lemma exitnode_pair : forall C k X c (Q : Empty_set -> Empty_set -> rel), rsim (RX C k X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof. intros C k X c Q. apply (exit_node_sim nstep step2 PhiP Phi2 sub1 (ok_sub2 K) minv MI2 (RX C k X) (RX_models C k X)). Qed.

Lemma open_pair : forall C k X path, rsimeq (RX C k X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => RX C k X).
Proof. intros C k X path. apply (open_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX C k X) (RX_models C k X) (RX_tables C k X)). Qed.
Lemma close_pair : forall C k X fd, rsimeq (RX C k X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => RX C k X).
Proof. intros C k X fd. apply (close_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX C k X) (RX_models C k X) (RX_tables C k X)). Qed.
Lemma read_pair : forall C k X fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
  rsimeq (RX C k X) (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
         (fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => RX C k X s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => RX C k X end).
Proof. intros C k X fd buf1 buf2 cnt Hcnt. apply (read_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX C k X) (RX_models C k X) (RX_tables C k X)). exact Hcnt. Qed.

Lemma CRUNX_nonneg : 0 <= CRUNX (ok_QOV K).
Proof. rewrite CRUNX_eq. pose proof (ok_QOV0 K). lia. Qed.

Local Notation crsim := (crsim nstep step2 nexit nexit PhiP Phi2).
Local Notation crsimeq := (crsimeq nstep step2 PhiP Phi2).

Lemma run_pairC : forall C k b1 b2 cap cfg payload, (exists j, (j <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat j) -> 0 <= k <= 12 ->
  zlength payload <= MAX_INPUT -> C + zlength payload + ok_QOV K + CRUNX (ok_QOV K) <= ok_CMAX K ->
  crsimeq (RX C k [(b1, b2, cap)]) (ProgC.runC FM cfg payload) (ProgAC.runAC A FM cfg payload)
          (fun _ s1 mo1 s2 mo2 => exists LK k', RX (C + zlength payload + ok_QOV K + CRUNX (ok_QOV K)) k' ((b1, b2, cap) :: LK) s1 mo1 s2 mo2).
Proof.
  intros C k b1 b2 cap cfg payload Hcap Hk Hp HC. unfold ProgC.runC, ProgAC.runAC, ProgC.fuzz_oneC, ProgAC.fuzz_oneAC, CRUNX.
  apply (target_runC_sim nstep step2 PhiP Phi2 FM RX (ok_QOV K) (ok_CMAX K) raw_malloc (amalloc A) raw_free (afree A) fresh_topb (afresh A)
           (io_emit io) (io_emit (ioA A)) malloc_pair free_pair emit_pair fpr_pair fwr_pair RX_mono RX_perm (ok_QOV0 K) C k b1 b2 cap cfg payload Hcap Hk Hp HC).
Qed.

Lemma main_exit_pairC : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  crsim (RX 0 0 []) (cmbind (DriverC.main_model io raw_malloc raw_free rsP alloc_init (ProgC.runC FM) alloc_count argv) (fun code => DriverC.exit_model io code))
                    (ProgAC.progA_mainC A FM rsA argv) Q.
Proof.
  intros argv Q Hargv. unfold ProgAC.progA_mainC.
  apply (main_exitC_sim nstep step2 PhiP Phi2 io (ioA A) raw_malloc (amalloc A) raw_free (afree A) fresh_topb (afresh A) rsP rsA
           alloc_init (alloc_initA A) alloc_count (alloc_countA A) RX (ok_QOV K) (ok_CMAX K) (CRUNX (ok_QOV K)));
    first [ exact CRUNX_nonneg | exact (ok_QOV0 K) | exact (ok_room K) | exact malloc_pair | exact free_pair | exact RX_perm | exact RX_mono
          | exact diag_pair | exact run_pairC | exact open_pair | exact close_pair | exact read_pair | exact ioexit_pair | exact exitnode_pair | exact Hargv
          | (intros C k X bm; apply rsimeq_ret; intros ? ? ? ? H; exact H) | (intros C k X; apply rsimeq_ret; intros ? ? ? ? H; exact H) ].
Qed.

Lemma OWN_vm X s mo mo' : OWN X GT s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> OWN X GT s mo'.
Proof.
  intros [(L & Hc & HK & Hi) [Hnd _]] Hvm Hmi Hh. split; [|split; [exact Hnd| exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| exact Hvm| exact Hmi| exact Hh].
Qed.

Section Pre.
Variable pre : Monad.M (ASt A) unit.
Hypothesis pre_pair : forall C k X, rsim (RX C k X) startup pre (fun _ _ => RX C k X).


Lemma RX_init : forall en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  AI K [] 0 sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp -> ok_cost K sA0 <= 0 ->
  RX 0 0 [] (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs lim en inp) sA0 moA0.
Proof.
  intros [sp brk0 mbase rnd] inp sA0 moA0 Hve Hvi HA Hso Hfd Hfs Hc0.
  (* the launch facts Spec/ModelInv GI_init takes: the channel reader (valid_input_either's 13th
     conjunct) and mmap_base_min <= mbase (valid_entry's third conjunct). *)
  assert (Hrd : in_channel_reader inp = true)
    by (destruct Hvi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hvi) in Hve. destruct Hve as ((Hsp1 & Hsp2 & _) & Hbrk & (Hmb & _) & _).
  split; [| split; [exact HA| split; [cbn; symmetry; exact Hso| split; [rewrite m_fds_mo0; symmetry; exact Hfd| split; [rewrite m_fs_mo0; symmetry; exact Hfs|]]]]].
  2:{ split; [exact Hc0|]. pose proof (ok_room K) as HR. pose proof (ok_QOV0 K) as HQ. pose proof (CDONE_nonneg (ok_QOV K) HQ) as HD. pose proof CRUNX_nonneg as HX. unfold MAX_INPUT in HR. lia. }
  unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. split.
  - eapply OWN_weakG; [apply (GI_init psegs brk0 mbase sp lim inp _ _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain low_plain Hmb Hrd)|]. intros _; exact I.
  - cbn [ps_m ps_init]. apply (fk_init FK). pose proof alloc_ceiling_lo_val. unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *. lia.
Qed.

Lemma argv_Z_pieces' : forall argv, valid_argv argv -> Forall (fun a => zlength a <= PIECE_MAX) (argv_Z argv).
Proof.
  intros argv Hv. eapply Forall_impl; [|apply (argv_Z_short argv Hv)]. intros a Ha. unfold ARG_MAX_LEN, PIECE_MAX in *. lia.
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

Definition treeAD (D : hist -> bool) (sA0 : ASt A) (argv : list (list Z)) : itree node (exc unit) :=
  ebind (RES D [] (cmbind (clift pre) (fun _ => ProgAC.progA_mainC A FM rsA argv)) sA0) (fun p => match fst p : Empty_set with end).

Lemma prog_pairC : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
  crsim (RX 0 0 []) (prog_withC FM rsP argv) (cmbind (clift pre) (fun _ => ProgAC.progA_mainC A FM rsA argv)) Q.
Proof.
  intros argv Q Hargv. unfold prog_withC. eapply crsim_bind; [apply crsim_lift; apply pre_pair|]. intros [] []. apply main_exit_pairC. exact Hargv.
Qed.

Lemma tglob_progD : forall D en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tglob nstep PhiP (progD FM D psegs rsP inp en) (mo0 psegs lim en inp).
Proof.
  intros D en inp He Hi. apply tglob_PhiP_intro.
  - (* the launch's model is [with_vdso .. (init_model ..)] and its [minv] takes the channel
       reader: TopLevel's [mo0_minv] proves it from the entry, Sv48 and the reader. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    exact (mo0_minv _ _ _ _ en inp He (valid_input_either_va_size _ Hi) Hrd).
  - destruct en; reflexivity.
  - exact (proj2 (prog_model_ok_plain_DL FM FK lim D rsP en inp Hlim He Hi)).
  - exact (never_forced_p_DL FM lim D rsP en inp Hlim He Hi).
Qed.

Theorem equiv_core_preD : forall D1 D2 en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  AI K [] 0 sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp -> ok_cost K sA0 <= 0 ->
  tglob step2 Phi2 (treeAD D2 sA0 (argv_Z (in_argv inp))) moA0 ->
  (forall tr, ttrace nstep nexit (progD FM D1 psegs rsP inp en) (mo0 psegs lim en inp) tr
              <-> ttrace step2 nexit (treeAD D2 sA0 (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (treeAD D2 sA0 (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros D1 D2 en inp sA0 moA0 He Hi HA Hso Hfd Hfs Hc0 GA. pose proof Hi as (Hargv & _).
  pose proof (prog_model_ok_plain_DL FM FK lim D1 rsP en inp Hlim He Hi) as [NL _].
  destruct (rsim_ttrace nstep step2 nexit nexit PhiP Phi2 (RX 0 0 [])
              (RES D1 [] (prog_withC FM rsP (argv_Z (in_argv inp))))
              (RES D2 [] (cmbind (clift pre) (fun _ => ProgAC.progA_mainC A FM rsA (argv_Z (in_argv inp)))))
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



End ASide.


Definition toP (en : ExecEntry) : ExecEntry :=
  mkEntry (en_sp en) (Z_to_bv 64 (reserved_top (segments_reserved psegs))) (en_mmap_base en) (en_draw en).


From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.LibA Require ITreeA.



Section PasA.
Variable FM : flush_model.
Variable FK : fkit.

Definition PasA : AAlloc := mkAAlloc PState bptr raw_malloc raw_free (fun _ _ _ _ => mret tt) ptr_addr fresh_topb ps_so set_so_ps.
Definition AIP (Y : list (bptr * Z)) (k : Z) (s : PState) (mo : Model) : Prop := OWN (map fst Y) GT s mo /\ fk_F FK Y k (ps_m s).

Lemma p_get_set : forall v s, ps_so (set_so_ps v s) = v. Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma p_set_set : forall v w s, set_so_ps v (set_so_ps w s) = set_so_ps v s. Proof. intros v w [? ? ? ?]; reflexivity. Qed.
Lemma p_set_get : forall s, set_so_ps (ps_so s) s = s. Proof. intros [? ? ? ?]; reflexivity. Qed.
Lemma p_addr_so : forall v s p, ptr_addr (set_so_ps v s) p = ptr_addr s p. Proof. intros v [? ? ? ?] p; reflexivity. Qed.

Lemma AIP_perm : forall Y Y' k s mo, Permutation Y Y' -> AIP Y k s mo -> AIP Y' k s mo.
Proof. intros Y Y' k s mo HP [H HF]. split; [eapply OWN_perm; [apply Permutation_map; exact HP| exact H]| eapply (fk_perm FK); [exact HP| exact HF]]. Qed.
Lemma AIP_kle : forall Y k k' s mo, k <= k' -> AIP Y k s mo -> AIP Y k' s mo.
Proof. intros Y k k' s mo Hk [H HF]. split; [exact H| eapply (fk_kle FK); [exact Hk| exact HF]]. Qed.
Lemma AIP_so : forall Y k s mo v, AIP Y k s mo -> AIP Y k (set_so_ps v s) mo.
Proof. intros Y k s mo v [H HF]. split; [eapply OWN_other; [exact H| reflexivity| reflexivity| exact I]| destruct s; exact HF]. Qed.
Lemma AIP_model : forall Y k s mo, AIP Y k s mo -> minv mo /\ m_halted mo = None.
Proof. intros Y k s mo [H _]. exact (OWN_minv _ _ _ H). Qed.
Lemma AIP_fds : forall Y k s mo f, AIP Y k s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> AIP Y k s (with_fds f mo).
Proof. intros Y k s mo f [H HF] M Hh. split; [exact (OWN_fds _ _ _ _ H M Hh)| exact HF]. Qed.

Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Definition PCMAX : Z := CDONE 0 + MAX_INPUT + 0 + CRUNX 0.
Lemma PCMAX_room : CDONE 0 + MAX_INPUT + 0 + CRUNX 0 <= PCMAX. Proof. apply Z.le_refl. Qed.

Lemma P_malloc : forall Y k n s mo, AIP Y k s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) -> FPRE Y k n ->
  tglob nstep PhiP (raw_malloc n s) mo ->
  STOTP (raw_malloc n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AIP ((q, n) :: Y) (k + 1) s' mo' /\ n < 2^63 /\ (KREQ n -> fresh_topb s s' q = true)
                         /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ 0 <= 0 + n + 0).
Proof.
  intros Y k n s mo [HA HF] Hn _ HFP G. eapply STOT_mono; [apply (fk_stot_m FK GT Y k n s mo frame_ok_GT HA HF ltac:(lia) (size_overflows_REQMAX n Hn) HFP G)|].
  intros r s' mo' (p & -> & HO & HF' & H63 & HFr & Hso & _ & Hfd & Hfs). exists p. unfold AIP. cbn [map fst]. splits; auto. lia.
Qed.

Lemma P_free : forall Y k q n s mo, AIP ((q, n) :: Y) k s mo -> 0 <= PCMAX -> tglob nstep PhiP (raw_free q s) mo ->
  STOTP (raw_free q s) mo (fun _ s' mo' => AIP Y k s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ 0 <= 0).
Proof.
  intros Y k q n s mo [HA HF] _ G. eapply STOT_mono; [apply (fk_stot_f FK GT Y k q n s mo frame_ok_GT HA HF G)|].
  intros [] s' mo' (HO & HF' & Hso & _ & Hfd & Hfs). unfold AIP. splits; auto. lia.
Qed.

Definition KP : AAllocOK PasA nstep PhiP minv :=
  mkAAllocOK PasA nstep PhiP minv sub1 same1 io1 MI1_pres p_get_set p_set_set p_set_get p_addr_so
             AIP AIP_perm AIP_kle AIP_so AIP_model AIP_fds
             0 PCMAX (Z.le_refl 0) PCMAX_room (fun _ => 0) (fun _ _ => eq_refl)
             P_malloc P_free.

Local Notation RXP := (RX FK PasA nstep PhiP minv KP).

Lemma startup_startup : forall C k X, rsim nstep nstep nexit nexit PhiP PhiP (RXP C k X) startup startup (fun _ _ => RXP C k X).
Proof.
  intros C k X. apply rsim_silent. intros s1 mo1 s2 mo2 ([HO HF] & [HA HF2] & Hso & Hfd & Hfs & Hc) G1 G2.
  destruct (OWN_minv _ _ _ HO) as [Hmi1 Hh1]. destruct (OWN_minv _ _ _ HA) as [Hmi2 Hh2].
  eexists _, _. split; [apply (startup_STOT s1 mo1 Hmi1 Hh1)| split; [apply (startup_STOT s2 mo2 Hmi2 Hh2)|]].
  intros [] s1' mo1' [] s2' mo2' (-> & Hvm1 & Hfd1 & Hfs1 & Hmi1' & Hh1') (-> & Hvm2 & Hfd2 & Hfs2 & Hmi2' & Hh2').
  split; [split; [exact (OWN_vm _ _ _ _ HO Hvm1 Hmi1' Hh1')| exact HF]|]. split; [split; [exact (OWN_vm _ _ _ _ HA Hvm2 Hmi2' Hh2')| exact HF2]|].
  split; [exact Hso|]. split; [congruence|]. split; [congruence| exact Hc].
Qed.

Import UImg.
Lemma tglob_progD_u : forall D rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  tglob nstep PhiP (progD FM D usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof.
  intros D rs en inp He Hi. apply tglob_PhiP_intro.
  - (* the launch's model is [with_vdso .. (init_model ..)] and its [minv] takes the channel
       reader: TopLevel's [mo0_minv] proves it from the entry, Sv48 and the reader. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    exact (mo0_minv _ _ _ _ en inp He (valid_input_either_va_size _ Hi) Hrd).
  - destruct en; reflexivity.
  - exact (proj2 (prog_model_ok_ubsan_D FM FK D rs en inp He Hi)).
  - exact (never_forced_u_D FM D rs en inp He Hi).
Qed.

(* the launch's model is
   [with_vdso v (init_model ..)]; the three launch premises of GI_init are APPENDED; equiv_PU_D discharges them. *)
Lemma AIP_init : forall segs brk0 mbase sp l inp v, valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi -> reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase ->
  in_channel_reader inp = true ->
  AIP [] 0 (ps_init (reservedZ segs) (bv_unsigned sp - stack_max_size)) (with_vdso v (init_model (segments_reserved segs) brk0 mbase sp l inp)).
Proof.
  intros segs brk0 mbase sp l inp v Hbrk Hpos Hsp Hceil Hlow Hmb Hrd. unfold AIP. cbn [map].
  split; [eapply OWN_weakG; [apply (GI_init segs brk0 mbase sp l inp _ v Hbrk Hpos Hsp eq_refl Hceil Hlow Hmb Hrd)| intros _; exact I]|].
  cbn [ps_m ps_init]. apply (fk_init FK). pose proof alloc_ceiling_lo_val. unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *. lia.
Qed.


Theorem equiv_PU_D : forall D1 D2 rs rs' en en' inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage usegs u_init_pc u_phdrs) en' inp -> valid_input_either inp ->
  trace_equiv (tree_traces (progD FM D1 psegs rs inp en) (mo0 psegs source_alloc_limit en inp))
              (tree_traces (progD FM D2 usegs rs' inp en') (mo0 usegs target_alloc_limit en' inp)).
Proof.
  intros D1 D2 rs rs' en en' inp He He' Hi. apply trees_equiv_of_ttrace.
  change (progD FM D2 usegs rs' inp en') with (treeAD FM PasA rs' startup D2 (ps_init (reservedZ usegs) (entry_atop en')) (argv_Z (in_argv inp))).
  apply (equiv_core_preD FM FK PasA nstep PhiP minv rs rs' KP source_alloc_limit ImgFacts.lim_p startup startup_startup D1 D2 en inp _ _ He Hi).
  - (* the launch facts AIP_init (so GI_init) takes. *)
    assert (Hrd : in_channel_reader inp = true)
      by (destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
    destruct en' as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He'. destruct He' as ((Hsp1 & Hsp2 & _) & Hbrk & (Hmb & _) & _). unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp AI KP].
    apply (AIP_init usegs brk0 mbase sp target_alloc_limit inp _ Hbrk ltac:(rewrite reserved_top_ubsan; lia) ltac:(split; [exact Hsp1| exact Hsp2]) ImgFacts.ceil_ubsan ImgFacts.low_ubsan Hmb Hrd).
  - reflexivity.
  - apply m_fds_mo0.
  - apply m_fs_mo0.
  - apply Z.le_refl.
  - change (treeAD FM PasA rs' startup D2 (ps_init (reservedZ usegs) (entry_atop en')) (argv_Z (in_argv inp))) with (progD FM D2 usegs rs' inp en'). apply tglob_progD_u; assumption.
Qed.
End PasA.
