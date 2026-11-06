(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe MPaths STree Malloc Stdio Harness Adapter Driver
PState Prog StepB KLink KEv ModelInv ImgFacts ModelOK EquivShared EquivProg RSim RSimProg SizeHist PTotal ProgA LB_StmtA LB_Main EquivK_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg.
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
AI : Z -> list (aptr A * Z) -> ASt A -> Model -> Prop;
ok_AI_perm : forall v Y Y' s mo, Permutation Y Y' -> AI v Y s mo -> AI v Y' s mo;
ok_AI_credit : forall v v' Y s mo, 0 <= v' <= v -> AI v Y s mo -> AI v' Y s mo;
ok_AI_so : forall v Y s mo w, AI v Y s mo -> AI v Y (a_set_so A w s) mo;
ok_AI_model : forall v Y s mo, AI v Y s mo -> MI2 mo /\ m_halted mo = None;
ok_AI_fds : forall v Y s mo f, AI v Y s mo -> MI2 (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI v Y s (with_fds f mo);
ok_malloc : forall v Y n s mo, AI v Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) -> FCOST n <= v ->
tglob step2 Phi2 (amalloc A n s) mo ->
STOT2 (amalloc A n s) mo
(fun r s' mo' => exists q, r = Some q /\ AI (v - FCOST n) ((q, n) :: Y) s' mo' /\ n < 2^63
/\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo);
ok_free : forall v Y q n s mo, AI v ((q, n) :: Y) s mo ->
tglob step2 Phi2 (afree A q s) mo ->
STOT2 (afree A q s) mo
(fun _ s' mo' => AI v Y s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo);
ok_annot : forall v Y q cap old new s mo, AI v Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
(old = 0 \/ new = 0) ->
tglob step2 Phi2 (aannot A q cap old new s) mo ->
STOT2 (aannot A q cap old new s) mo
(fun _ s' mo' => AI v Y s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo)
}.
Variable K : AAllocOK.
Variable LS : Z.
Hypothesis HLS : 2^31 <= LS.
Definition AHAND (inp : ProcInput) (sA0 : ASt A) (moA0 : Model) : Prop :=
AI K MAIN_QCOST [] sA0 moA0 /\ a_so A sA0 = stdout_init /\ m_fds moA0 = init_fds /\ m_fs moA0 = in_fs inp
/\ tglob step2 Phi2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0.
Local Notation rel := (rel PState (ASt A)).
Local Notation rsim := (rsim nstep step2 nexit nexit PhiP Phi2).
Local Notation triple := (bptr * aptr A * Z)%type.
Definition pX (X : list triple) : list bptr := map (fun b => fst (fst b)) X.
Definition aX (X : list triple) : list (aptr A * Z) := map (fun b => (snd (fst b), snd b)) X.
Definition GT : PState -> Model -> Prop := fun _ _ => True.
#[using="Type"] Lemma frame_ok_GT : frame_ok GT. Proof. intros ? ? ? ? _ _ _ _; exact I. Qed.
Definition RX (v : Z) (X : list triple) : rel := fun s1 mo1 s2 mo2 =>
OWN (pX X) GT s1 mo1 /\ AI K v (aX X) s2 mo2 /\ ps_so s1 = a_so A s2 /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
#[using="Type"] Lemma sizes_aX X : map snd (aX X) = map snd X. Proof. unfold aX. rewrite map_map. reflexivity. Qed.
#[using="Type"] Lemma OWN_minv X s mo : OWN X GT s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(L & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.
#[using="Type"] Lemma OWN_fds X s mo f : OWN X GT s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> OWN X GT s (with_fds f mo).
Proof.
intros [(L & Hc & HK & Hi) [Hnd _]] Hmi Hh. split; [|split; [exact Hnd| exact I]].
exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| apply m_vmmaps_with_fds| exact Hmi| exact Hh].
Qed.
#[using="Type"] Lemma RX_perm : forall v X Y s1 mo1 s2 mo2, Permutation X Y -> RX v X s1 mo1 s2 mo2 -> RX v Y s1 mo1 s2 mo2.
Proof.
intros v X Y s1 mo1 s2 mo2 HP (HO & HA & Hso & Hfd & Hfs). split; [| split; [| auto]].
- eapply OWN_perm; [| exact HO]. unfold pX. apply Permutation_map. exact HP.
- eapply (ok_AI_perm K); [| exact HA]. unfold aX. apply Permutation_map. exact HP.
Qed.
#[using="Type"] Lemma RX_credit : forall v v' X s1 mo1 s2 mo2, 0 <= v' <= v -> RX v X s1 mo1 s2 mo2 -> RX v' X s1 mo1 s2 mo2.
Proof.
intros v v' X s1 mo1 s2 mo2 Hv (HO & HA & Hrest). split; [exact HO|]. split; [| exact Hrest].
eapply (ok_AI_credit K); [exact Hv| exact HA].
Qed.
#[using="Type"] Lemma RX_get : forall v X s1 mo1 s2 mo2, RX v X s1 mo1 s2 mo2 -> ps_so s1 = a_so A s2.
Proof. intros v X s1 mo1 s2 mo2 (_ & _ & H & _). exact H. Qed.
#[using="Type"] Lemma RX_set : forall v0 X s1 mo1 s2 mo2 v, RX v0 X s1 mo1 s2 mo2 -> RX v0 X (set_so_ps v s1) mo1 (a_set_so A v s2) mo2.
Proof.
intros v0 X s1 mo1 s2 mo2 v (HO & HA & Hso & Hfd & Hfs). split; [| split; [| split; [| split; [exact Hfd| exact Hfs]]]].
- eapply OWN_other; [exact HO| reflexivity| reflexivity| exact I].
- apply (ok_AI_so K). exact HA.
- rewrite (ok_get_set K). destruct s1; reflexivity.
Qed.
#[using="Type"] Lemma RX_models : forall v X s1 mo1 s2 mo2, RX v X s1 mo1 s2 mo2 ->
minv mo1 /\ MI2 mo2 /\ m_halted mo1 = None /\ m_halted mo2 = None /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
Proof.
intros v X s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs). destruct (OWN_minv _ _ _ HO) as [M1 H1]. destruct (ok_AI_model K _ _ _ _ HA) as [M2 H2]. splits; auto.
Qed.
#[using="Type"] Lemma RX_tables : forall v X s1 mo1 s2 mo2 f, RX v X s1 mo1 s2 mo2 ->
minv (with_fds f mo1) -> MI2 (with_fds f mo2) -> m_halted (with_fds f mo1) = None -> m_halted (with_fds f mo2) = None ->
RX v X s1 (with_fds f mo1) s2 (with_fds f mo2).
Proof.
intros v X s1 mo1 s2 mo2 f (HO & HA & Hso & Hfd & Hfs) M1 M2 H1 H2. split; [| split; [| split; [exact Hso| split; [reflexivity|]]]].
- apply OWN_fds; auto.
- apply (ok_AI_fds K); auto.
- rewrite !m_fs_with_fds. exact Hfs.
Qed.
#[using="Type"] Lemma size_overflows_REQMAX n : 0 <= n <= REQMAX -> size_overflows n = false.
Proof. intros Hn. unfold size_overflows, REQMAX in *. apply Z.leb_gt. Local Ltac2 Set LiaHints.tbl := fun () => "0010>18539273086.11000004S2Hn".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma malloc_pair : forall v X n, 0 <= n <= REQMAX -> HISTOK (n :: map snd X) -> FCOST n <= v ->
rsim (RX v X) (raw_malloc n) (amalloc A n) (Qm RX v X n).
Proof.
intros v X n Hn HH Hv. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
eexists _, _. split; [| split].
- Local Ltac2 Set LiaHints.tbl := fun () => "0010=2424969826.26000004S2Hn".
apply (raw_malloc_STOT (pX X) GT n s1 mo1 frame_ok_GT HO ltac:(lia) (size_overflows_REQMAX n Hn) G1).
- apply (ok_malloc K v (aX X) n s2 mo2 HA Hn ltac:(rewrite sizes_aX; exact HH) Hv G2).
- intros a s1' mo1' b s2' mo2' (p & -> & HO' & Hn63 & Hso1 & Hfa1 & Hfd1 & Hfs1) (q & -> & HA' & _ & Hso2 & Hfd2 & Hfs2). cbn [Qm].
split; [| exact Hn63]. split; [exact HO'|]. split; [exact HA'|]. split; [congruence|]. split; congruence.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma free_pair : forall v X p q n, rsim (RX v ((p, q, n) :: X)) (raw_free p) (afree A q) (fun _ _ => RX v X).
Proof.
intros v X p q n. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
eexists _, _. split; [| split].
- apply (raw_free_STOT (pX X) GT p s1 mo1 frame_ok_GT HO G1).
- apply (ok_free K v (aX X) q n s2 mo2 HA G2).
- intros a s1' mo1' b s2' mo2' (HO' & Hso1 & Hfa1 & Hfd1 & Hfs1) (HA' & Hso2 & Hfd2 & Hfs2).
split; [exact HO'|]. split; [exact HA'|]. split; [congruence|]. split; congruence.
Qed.
#[using="Type"] Lemma sub1 : forall n mo r mo' e, ~ nf_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
#[using="Type"] Lemma same1 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstep n mo r mo e. Proof. auto. Qed.
#[using="Type"] Lemma io1 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
#[using="Type"] Lemma MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> minv mo -> m_halted mo = None -> minv mo' /\ m_halted mo' = None.
Proof. intros n mo rsp mo' evs Hst _ Hmi Hh. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi']. auto. Qed.
Local Notation rsimeq := (rsimeq nstep step2 PhiP Phi2).
#[using="Type"] Lemma diag_pair : forall v X d, diag_short d -> rsimeq (RX v X) (io_diag io d) (io_diag (ioA A) d) (fun _ => RX v X).
Proof. intros v X d _. cbn [io ioA io_diag io_S]. apply (s_diag_sim nstep step2 PhiP Phi2 sub1 same1 (ok_sub2 K) (ok_same2 K)). Qed.
#[using="Type"] Lemma emit_pair : forall v0 X v, rsimeq (RX v0 X) (io_emit io v) (io_emit (ioA A) v) (fun _ => RX v0 X).
Proof.
intros v0 X v. cbn [io ioA io_emit io_S].
apply (s_emit_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX v0 X) (RX_get v0 X) (RX_set v0 X)).
Qed.
#[using="Type"] Lemma ioexit_pair : forall v X, rsimeq (RX v X) (io_exit io) (io_exit (ioA A)) (fun _ => RX v X).
Proof.
intros v X. cbn [io ioA io_exit io_S].
apply (stdout_exit_flush_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX v X) (RX_get v X) (RX_set v X)).
Qed.
#[using="Type"] Lemma exitnode_pair : forall v X c (Q : Empty_set -> Empty_set -> rel), rsim (RX v X) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof. intros v X c Q. apply (exit_node_sim nstep step2 PhiP Phi2 sub1 (ok_sub2 K) minv MI2 (RX v X) (RX_models v X)). Qed.
#[using="Type"] Lemma nh_pair : forall v X (Q : Empty_set -> Empty_set -> rel), rsim (RX v X) new_handler (new_handlerA A) Q.
Proof. intros v X Q. unfold new_handler, new_handlerA. apply rsim_munr. Qed.
#[using="Type"] Lemma open_pair : forall v X path, rsimeq (RX v X) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => RX v X).
Proof. intros v X path. apply (open_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX v X) (RX_models v X) (RX_tables v X)). Qed.
#[using="Type"] Lemma close_pair : forall v X fd, rsimeq (RX v X) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => RX v X).
Proof. intros v X fd. apply (close_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX v X) (RX_models v X) (RX_tables v X)). Qed.
#[using="Type"] Lemma read_pair : forall v X fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
rsimeq (RX v X) (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
(fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => RX v X s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => RX v X end).
Proof. intros v X fd buf1 buf2 cnt Hcnt. apply (read_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX v X) (RX_models v X) (RX_tables v X)). exact Hcnt. Qed.
#[using="Type"] Lemma run_pair : forall v X cfg payload, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_QCOST <= v ->
rsimeq (RX v X) (run cfg payload) (runA A cfg payload) (fun _ => RX (v - RUN_QCOST) X).
Proof.
intros v X cfg payload HL Hp Hv. unfold run, runA, Prog.fuzz_one, fuzz_oneA.
apply (target_run_sim nstep step2 PhiP Phi2 RX raw_malloc (amalloc A) raw_free (afree A) new_handler (new_handlerA A)
(io_emit io) (io_emit (ioA A))
malloc_pair free_pair RX_perm RX_credit nh_pair emit_pair v X cfg payload HL Hp Hv).
Qed.
#[using="Type"] Lemma main_exit_pair : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
rsim (RX MAIN_QCOST []) (code <- main_model io raw_malloc raw_free rsP alloc_init run alloc_count argv ;; exit_model io code)
(progA_main A rsA argv) Q.
Proof.
intros argv Q Hargv. unfold progA_main.
apply (main_exit_sim nstep step2 PhiP Phi2 io (ioA A) raw_malloc (amalloc A) raw_free (afree A) rsP rsA
alloc_init (alloc_initA A) run (runA A) alloc_count (alloc_countA A) RX
malloc_pair free_pair RX_perm RX_credit diag_pair).
- intros v X bm. apply rsimeq_ret. intros ? ? ? ? H; exact H.
- intros v X. apply rsimeq_ret. intros ? ? ? ? H; exact H.
- apply run_pair.
- apply open_pair.
- apply close_pair.
- apply read_pair.
- apply ioexit_pair.
- apply exitnode_pair.
- exact Hargv.
- apply Z.le_refl.
Qed.
#[using="Type"] Lemma OWN_vm X s mo mo' : OWN X GT s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> OWN X GT s mo'.
Proof.
intros [(L & Hc & HK & Hi) [Hnd _]] Hvm Hmi Hh. split; [|split; [exact Hnd| exact I]].
exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| exact Hvm| exact Hmi| exact Hh].
Qed.
Section Pre.
Variable pre : Monad.M (ASt A) unit.
Hypothesis pre_pair : forall v X, rsim (RX v X) startup pre (fun _ _ => RX v X).
#[using="pre_pair"] Lemma prog_pair : forall argv (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv ->
rsim (RX MAIN_QCOST []) (prog_with rsP argv) (pre ;;; progA_main A rsA argv) Q.
Proof.
intros argv Q Hargv. unfold prog_with. eapply rsim_seq; [apply pre_pair|]. intros [] []. apply main_exit_pair. exact Hargv.
Qed.
Definition treeA (sA0 : ASt A) (argv : list (list Z)) : itree node (exc unit) :=
ebind ((pre ;;; progA_main A rsA argv) sA0) (fun p => match fst p : Empty_set with end).
#[using="Type"] Lemma RX_init : forall en inp sA0 moA0,
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
AI K MAIN_QCOST [] sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp ->
RX MAIN_QCOST [] (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs LS en inp) sA0 moA0.
Proof.
intros [sp brk0 mbase rnd] inp sA0 moA0 Hve Hvi HA Hso Hfd Hfs.
rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hvi) in Hve. destruct Hve as ((Hsp1 & Hsp2 & _) & Hbrk & _ & _).
split; [| split; [exact HA| split; [cbn; symmetry; exact Hso| split; [rewrite m_fds_mo0; symmetry; exact Hfd| rewrite m_fs_mo0; symmetry; exact Hfs]]]].
unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp].
Local Ltac2 Set LiaHints.tbl := fun () => "0010>18926758123.26000001S".
eapply OWN_weakG; [apply (GI_init psegs brk0 mbase sp LS inp _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain)|]. intros _; exact I.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma argv_Z_pieces' : forall argv, valid_argv argv -> Forall (fun a => zlength a <= PIECE_MAX) (argv_Z argv).
Proof.
intros argv Hv. eapply Forall_impl; [|apply (argv_Z_short argv Hv)]. intros a Ha. unfold ARG_MAX_LEN, PIECE_MAX in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>43170199003.15000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HLS"] Lemma tglob_prog : forall en inp,
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
tglob nstep PhiP (prog psegs rsP inp en) (mo0 psegs LS en inp).
Proof.
intros en inp He Hi. apply tglob_PhiP_intro.
- unfold mo0. apply minv_init. destruct en as [sp ? ? ?]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He.
destruct He as ((Hsp1 & Hsp2 & _) & _). cbn [en_sp]. split; [exact Hsp1| exact Hsp2].
- destruct en; reflexivity.
- exact (proj2 (prog_model_ok_plain_L LS rsP en inp HLS He Hi)).
- exact (never_forced_p_L LS rsP en inp HLS He Hi).
Qed.
#[using="Type"] Lemma ttrace_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop)
(t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo tr :
ttrace step nexit (ebind t f) mo tr <-> ttrace step nexit t mo tr.
Proof.
rewrite !ttrace_split, texit_ebind. split.
- intros [[Hx|(tr1 & [[] ?] & _)]|(r & mo' & Hp)]; [left; exact Hx|].
apply tpath_ebind in Hp as [[Hp ->]|(tr1 & [[] ?] & _)]. right. exists Unr, mo'. exact Hp.
- intros [Hx|(r & mo' & Hp)]; [left; left; exact Hx|]. right. destruct r as [|[[] ?]]. exists Unr, mo'. apply tpath_ebind. left. auto.
Qed.
#[using="Type"] Lemma tpath_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop)
(t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo tr r mo' :
tpath step (ebind t f) mo tr r mo' -> exists r', tpath step t mo tr r' mo'.
Proof. intros Hp. apply tpath_ebind in Hp as [[Hp ->]|(tr1 & [[] ?] & _)]. exists Unr. exact Hp. Qed.
#[using="Type"] Lemma tglob_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop) Phi
(t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo :
tglob step Phi (ebind t f) mo <-> tglob step Phi t mo.
Proof.
split; [apply tglob_ebind_l|]. intros H. apply tglob_ebind; [exact H|]. intros tr [[] ?] mo' _.
Qed.
#[using="HLS pre_pair"] Theorem equiv_core_pre : forall en inp sA0 moA0,
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
AI K MAIN_QCOST [] sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp ->
tglob step2 Phi2 (treeA sA0 (argv_Z (in_argv inp))) moA0 ->
(forall tr, ttrace nstep nexit (prog psegs rsP inp en) (mo0 psegs LS en inp) tr
<-> ttrace step2 nexit (treeA sA0 (argv_Z (in_argv inp))) moA0 tr)
/\ (forall tr r mo', ~ tpath step2 (treeA sA0 (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
intros en inp sA0 moA0 He Hi HA Hso Hfd Hfs GA. pose proof Hi as (Hargv & _).
pose proof (prog_model_ok_plain_L LS rsP en inp HLS He Hi) as [NL _].
destruct (rsim_ttrace nstep step2 nexit nexit PhiP Phi2 (RX MAIN_QCOST []) (prog_with rsP (argv_Z (in_argv inp))) (pre ;;; progA_main A rsA (argv_Z (in_argv inp)))
(fun _ _ _ _ _ _ => False) (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs LS en inp) sA0 moA0
(prog_pair _ _ (argv_Z_pieces' _ Hargv)) (RX_init en inp sA0 moA0 He Hi HA Hso Hfd Hfs)) as [EQ NL2].
- apply (tglob_after_empty nstep PhiP _ (fun p => match fst p : Empty_set with end)). exact (tglob_prog en inp He Hi).
- apply (tglob_after_empty step2 Phi2 _ (fun p => match fst p : Empty_set with end)). exact GA.
- intros tr r mo' Hp. destruct r as [|[[] ?]]. apply (NL tr Unr mo'). unfold prog, prog_itree. apply tpath_ebind. left. auto.
- split.
+ intros tr. unfold prog, prog_itree, treeA. rewrite !ttrace_after_empty. apply EQ.
+ intros tr r mo' Hp. unfold treeA in Hp. apply tpath_after_empty in Hp as [r' Hp]. exact (NL2 tr r' mo' Hp).
Qed.
End Pre.
#[using="Type"] Lemma startup_pair : forall v X, rsim (RX v X) startup (mret tt) (fun _ _ => RX v X).
Proof.
intros v X. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
destruct (OWN_minv _ _ _ HO) as [Hmi Hh].
eexists _, _. split; [apply (startup_STOT s1 mo1 Hmi Hh)| split; [apply STOT_ret|]].
intros [] s1' mo1' [] s2' mo2' (-> & Hvm & Hfd1 & Hfs1 & Hmi' & Hh') (_ & -> & ->).
split; [exact (OWN_vm _ _ _ _ HO Hvm Hmi' Hh')|]. split; [exact HA|]. split; [exact Hso|]. split; congruence.
Qed.
#[using="HLS"] Theorem equiv_core : forall en inp sA0 moA0,
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp -> AHAND inp sA0 moA0 ->
(forall tr, ttrace nstep nexit (prog psegs rsP inp en) (mo0 psegs LS en inp) tr
<-> ttrace step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr)
/\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
intros en inp sA0 moA0 He Hi (HA & Hso & Hfd & Hfs & GA).
change (progA_tree A sA0 rsA (argv_Z (in_argv inp))) with (treeA (mret tt) sA0 (argv_Z (in_argv inp))) in GA |- *.
exact (equiv_core_pre (mret tt) startup_pair en inp sA0 moA0 He Hi HA Hso Hfd Hfs GA).
Qed.
End ASide.
Definition toP (en : ExecEntry) : ExecEntry :=
mkEntry (en_sp en) (Z_to_bv 64 (reserved_top (segments_reserved psegs))) (en_mmap_base en) (en_draw en).
Lemma toP_valid : forall segsX pcX phX en inp,
valid_entry (mkImage segsX pcX phX) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) (toP en) inp.
Proof.
intros segsX pcX phX [sp brk0 mbase] inp H. cbn [valid_entry valid_entry_va toP en_sp en_mmap_base] in H |- *. destruct H as (Hsp & _ & Hmb & Hst).
split; [exact Hsp|]. split; [| split; [exact Hmb| exact Hst]].
unfold valid_brk. rewrite reserved_top_plain. Local Ltac2 Set LiaHints.tbl := fun () => "0030>51850865870.1159579069046.1161446899094.11000001002003SSS".
rewrite unsigned_lit by lia. unfold brk_aslr_max, page_size. split; [lia|]. split; [lia| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require ITreeA.
Theorem equiv_PA_L (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
(rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) (LS : Z) (HLS : 2^31 <= LS) :
forall enP inp sA0 moA0,
valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
trace_equiv (tree_traces (prog psegs rsP inp enP) (mo0 psegs LS enP inp))
(ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
/\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
intros enP inp sA0 moA0 HeP Hi HH.
destruct (equiv_core A step2 Phi2 MI2 rsP rsA K LS HLS enP inp sA0 moA0 HeP Hi HH) as [EQ NL2].
split; [| exact NL2]. intros tr. unfold tree_traces, ITreeA.ptraces. split; intros (full & Hf & Hp); exists full; split; auto; apply EQ; exact Hf.
Qed.
Corollary equiv_PA_toP_L (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
(rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) (LS : Z) (HLS : 2^31 <= LS) :
forall segsX pcX phX enX inp sA0 moA0,
valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
(ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
/\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof. intros segsX pcX phX enX inp sA0 moA0 HeX Hi HH. exact (equiv_PA_L A step2 Phi2 MI2 rsP rsA K LS HLS (toP enX) inp sA0 moA0 (toP_valid _ _ _ _ _ HeX) Hi HH). Qed.
Definition PasA : AAlloc := mkAAlloc PState bptr raw_malloc raw_free (fun _ _ _ _ => mret tt) ptr_addr ps_so set_so_ps.
Definition AIP (v : Z) (Y : list (bptr * Z)) (s : PState) (mo : Model) : Prop := OWN (map fst Y) GT s mo.
Lemma p_get_set : forall v s, ps_so (set_so_ps v s) = v. Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma p_set_set : forall v w s, set_so_ps v (set_so_ps w s) = set_so_ps v s. Proof. intros v w [? ? ? ?]; reflexivity. Qed.
Lemma p_set_get : forall s, set_so_ps (ps_so s) s = s. Proof. intros [? ? ? ?]; reflexivity. Qed.
Lemma p_addr_so : forall v s p, ptr_addr (set_so_ps v s) p = ptr_addr s p. Proof. intros v [? ? ? ?] p; reflexivity. Qed.
Lemma AIP_perm : forall v Y Y' s mo, Permutation Y Y' -> AIP v Y s mo -> AIP v Y' s mo.
Proof. intros v Y Y' s mo HP H. unfold AIP in *. eapply OWN_perm; [apply Permutation_map; exact HP| exact H]. Qed.
Lemma AIP_credit : forall v v' Y s mo, 0 <= v' <= v -> AIP v Y s mo -> AIP v' Y s mo.
Proof. intros v v' Y s mo _ H. exact H. Qed.
Lemma AIP_so : forall v0 Y s mo v, AIP v0 Y s mo -> AIP v0 Y (set_so_ps v s) mo.
Proof. intros v0 Y s mo v H. unfold AIP in *. eapply OWN_other; [exact H| reflexivity| reflexivity| exact I]. Qed.
Lemma AIP_model : forall v Y s mo, AIP v Y s mo -> minv mo /\ m_halted mo = None.
Proof. intros v Y s mo H. exact (OWN_minv _ _ _ H). Qed.
Lemma AIP_fds : forall v Y s mo f, AIP v Y s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> AIP v Y s (with_fds f mo).
Proof. intros v Y s mo f H M Hh. exact (OWN_fds _ _ _ _ H M Hh). Qed.
Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).
Lemma P_malloc : forall v Y n s mo, AIP v Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) -> FCOST n <= v ->
tglob nstep PhiP (raw_malloc n s) mo ->
STOTP (raw_malloc n s) mo
(fun r s' mo' => exists q, r = Some q /\ AIP (v - FCOST n) ((q, n) :: Y) s' mo' /\ n < 2^63
/\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
intros v Y n s mo HA Hn _ _ G. Local Ltac2 Set LiaHints.tbl := fun () => "0010<2431264729.8000004S2Hn".
eapply STOT_mono; [apply (raw_malloc_STOT (map fst Y) GT n s mo frame_ok_GT HA ltac:(lia) (size_overflows_REQMAX n Hn) G)|].
intros r s' mo' (p & -> & HO & H63 & Hso & _ & Hfd & Hfs). exists p. unfold AIP. cbn [map fst]. auto 10.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma P_free : forall v Y q n s mo, AIP v ((q, n) :: Y) s mo -> tglob nstep PhiP (raw_free q s) mo ->
STOTP (raw_free q s) mo (fun _ s' mo' => AIP v Y s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
intros v Y q n s mo HA G. eapply STOT_mono; [apply (raw_free_STOT (map fst Y) GT q s mo frame_ok_GT HA G)|].
intros [] s' mo' (HO & Hso & _ & Hfd & Hfs). unfold AIP. auto.
Qed.
Lemma P_annot : forall v Y (q : bptr) (cap old new : Z) s mo, AIP v Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
(old = 0 \/ new = 0) ->
tglob nstep PhiP (mret tt s) mo ->
STOTP (mret tt s) mo (fun _ s' mo' => AIP v Y s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
intros v Y q cap old new s mo HA _ _ _ _ _. eapply STOT_mono; [apply STOT_ret|]. intros [] s' mo' (_ & -> & ->). auto.
Qed.
Definition KP : AAllocOK PasA nstep PhiP minv :=
mkAAllocOK PasA nstep PhiP minv sub1 same1 io1 MI1_pres p_get_set p_set_set p_set_get p_addr_so
AIP AIP_perm AIP_credit AIP_so AIP_model AIP_fds P_malloc P_free P_annot.
Local Notation RXP := (RX PasA nstep PhiP minv KP).
Lemma startup_startup : forall v X, rsim nstep nstep nexit nexit PhiP PhiP (RXP v X) startup startup (fun _ _ => RXP v X).
Proof.
intros v X. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
destruct (OWN_minv _ _ _ HO) as [Hmi1 Hh1]. destruct (OWN_minv _ _ _ HA) as [Hmi2 Hh2].
eexists _, _. split; [apply (startup_STOT s1 mo1 Hmi1 Hh1)| split; [apply (startup_STOT s2 mo2 Hmi2 Hh2)|]].
intros [] s1' mo1' [] s2' mo2' (-> & Hvm1 & Hfd1 & Hfs1 & Hmi1' & Hh1') (-> & Hvm2 & Hfd2 & Hfs2 & Hmi2' & Hh2').
split; [exact (OWN_vm _ _ _ _ HO Hvm1 Hmi1' Hh1')|]. split; [exact (OWN_vm _ _ _ _ HA Hvm2 Hmi2' Hh2')|]. split; [exact Hso|]. split; congruence.
Qed.
Theorem equiv_PP_L : forall LS, 2^31 <= LS -> forall rs rs' en en' inp,
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) en' inp -> valid_input_either inp ->
trace_equiv (tree_traces (prog psegs rs inp en) (mo0 psegs LS en inp))
(tree_traces (prog psegs rs' inp en') (mo0 psegs LS en' inp)).
Proof.
intros LS HLS rs rs' en en' inp He He' Hi. apply trees_equiv_of_ttrace.
change (prog psegs rs' inp en') with (treeA PasA rs' startup (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))).
apply (equiv_core_pre PasA nstep PhiP minv rs rs' KP LS HLS startup startup_startup en inp _ _ He Hi).
- destruct en' as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He'. destruct He' as ((Hsp1 & Hsp2 & _) & Hbrk & _ & _). unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp AI KP]. unfold AIP. cbn [map].
Local Ltac2 Set LiaHints.tbl := fun () => "0010>18928856693.15000001S".
eapply OWN_weakG; [apply (GI_init psegs brk0 mbase sp LS inp _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain)|]. intros _; exact I.
- reflexivity.
- apply m_fds_mo0.
- apply m_fs_mo0.
- change (treeA PasA rs' startup (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))) with (prog psegs rs' inp en'). apply (tglob_prog rs' LS HLS); assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
