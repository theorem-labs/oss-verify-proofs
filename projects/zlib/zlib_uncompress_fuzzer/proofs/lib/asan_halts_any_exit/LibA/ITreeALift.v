(* NEW text
   LibA/ITreeALift, the ITreeA twin of TopLevel's impl_lift.  The run reads every step against
   segs ++ tail (tail = the vDSO pair, never executable), and its configurations carry that list's ROM; an ITreeA tree
   (implF / tree_atA over at_nodeA segs) is proved over the image's own list.  A tree over segs therefore gives the
   same tree over segs ++ tail, at the state whose ROM field is set to seg_rom (segs ++ tail):
     - a step over segs succeeds over segs ++ tail with the same access report (first match; a tail segment never
       yields code), and set_rom changes no step (no step reads the ROM field);
     - at_nodeA's memory facts lift by first match (TopLevel's bytes_at / at_node lifts), its ROM conjunct is the
       new ROM by construction;
     - nodesA_sound is already forall segs, so implF_srealizes instantiates at segs ++ tail.
   The final lemma implF_srealizes_run gives SpinAlg.srealizes (segs ++ tail) for the main body, over the same
   ptraces (which read no segment list).  Generic in the footprint step (fstepA, the Both proto's own) and in
   nstep / minv / nsafe / NMAX, which read no segment list either. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AS Require SpinAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit Require TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* ------------------------------------------------------------------------- *)
(* The machine level: one step with its access report, over segs ++ tail and  *)
(* with the ROM field replaced.                                               *)
(* ------------------------------------------------------------------------- *)

(* set_rom changes no access report but the state's own ROM field *)
Lemma itl_decacc_set_rom : forall sg r st w st' accs,
  decode_exec_accesses sg st w = MachineOk (@mkAccessReport machine_state st' accs) ->
  decode_exec_accesses sg (TopLevel.set_rom r st) w = MachineOk (@mkAccessReport machine_state (TopLevel.set_rom r st') accs).
Proof.
  intros sg r st w st' accs. unfold decode_exec_accesses.
  cbn [TopLevel.set_rom ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
  destruct (is_ecall w).
  - intro Hd. injection Hd as <- <-. reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); intro Hd; discriminate Hd].
    lazymatch goal with |- context [interp_eff_accesses sg ?t0 ?m0] =>
      destruct (interp_eff_accesses sg t0 m0) as [rep| |] end;
      [| intro Hd; discriminate Hd | intro Hd; discriminate Hd].
    destruct (access_value _ rep) as [c m']. intro Hd. injection Hd as <- <-. reflexivity.
Qed.

Lemma itl_stepacc_set_rom : forall sg r st st' accs,
  step_accesses sg st = MachineOk (@mkAccessReport machine_state st' accs) ->
  step_accesses sg (TopLevel.set_rom r st) = MachineOk (@mkAccessReport machine_state (TopLevel.set_rom r st') accs).
Proof.
  intros sg r st st' accs. unfold step_accesses.
  change (ms_pc (TopLevel.set_rom r st)) with (ms_pc st). change (ms_mem (TopLevel.set_rom r st)) with (ms_mem st).
  destruct (fetch_word sg (ms_pc st)) as [w|]; [apply itl_decacc_set_rom|].
  destruct (fetch_word_ov sg (ms_mem st) (ms_pc st)) as [w|]; [apply itl_decacc_set_rom|].
  destruct (fetch_tail_any sg (ms_mem st) (ms_pc st)) as [w|]; [apply itl_decacc_set_rom|].
  destruct (fetch_failure sg (ms_mem st) (ms_pc st)) eqn:FF; intro Hs; try discriminate Hs.
  exfalso. exact (TopLevel.fetch_failure_not_ok _ _ _ _ FF).
Qed.

Section RunTail.
Variables (segs tail : list Segment).
Hypothesis NX : Forall (fun s => seg_executable s = false) tail.

(* first match: a step over segs is the same step, with the same report, over segs ++ tail *)
Lemma itl_stepacc_app : forall st rep,
  step_accesses segs st = MachineOk rep -> step_accesses (segs ++ tail) st = MachineOk rep.
Proof.
  intros st rep. unfold step_accesses.
  rewrite (TopLevel.fetch_word_app segs tail NX), (TopLevel.fetch_word_ov_app segs tail NX),
          (TopLevel.fetch_tail_any_app segs tail NX).
  destruct (fetch_word segs (ms_pc st)) as [w|].
  { destruct (decode_exec_accesses segs st w) as [r| |] eqn:E; intro Hs; try discriminate Hs.
    rewrite (TopLevel.decode_app segs tail _ _ _ E). exact Hs. }
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|].
  { destruct (decode_exec_accesses segs st w) as [r| |] eqn:E; intro Hs; try discriminate Hs.
    rewrite (TopLevel.decode_app segs tail _ _ _ E). exact Hs. }
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|].
  { destruct (decode_exec_accesses segs st w) as [r| |] eqn:E; intro Hs; try discriminate Hs.
    rewrite (TopLevel.decode_app segs tail _ _ _ E). exact Hs. }
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:FF; intro Hs; try discriminate Hs.
  exfalso. exact (TopLevel.fetch_failure_not_ok _ _ _ _ FF).
Qed.

Lemma itl_mstepF_lift : forall r RNG ms ms',
  mstepF segs RNG ms ms' -> mstepF (segs ++ tail) RNG (TopLevel.set_rom r ms) (TopLevel.set_rom r ms').
Proof.
  intros r RNG ms ms' [Hsvc (accs & Ha & Hf)]. split; [exact Hsvc|].
  exists accs. split; [|exact Hf].
  apply itl_stepacc_set_rom. exact (itl_stepacc_app _ _ Ha).
Qed.

Lemma itl_mstepsF_lift : forall r RNG ms ms',
  mstepsF segs RNG ms ms' -> mstepsF (segs ++ tail) RNG (TopLevel.set_rom r ms) (TopLevel.set_rom r ms').
Proof.
  intros r RNG ms ms' Hm. induction Hm as [ms0|ms0 ms1 ms2 H1 H2 IH].
  - apply mstepsF_refl.
  - eapply mstepsF_cons; [exact (itl_mstepF_lift r RNG _ _ H1)| exact IH].
Qed.

Lemma itl_evtF_lift : forall r RNG (P : machine_state -> Prop) ms,
  evtF segs RNG P ms ->
  evtF (segs ++ tail) RNG (fun ms' => exists msp, ms' = TopLevel.set_rom r msp /\ P msp) (TopLevel.set_rom r ms).
Proof.
  intros r RNG P ms (ms1 & Hm & HP). exists (TopLevel.set_rom r ms1).
  split; [exact (itl_mstepsF_lift r RNG _ _ Hm)| exists ms1; split; [reflexivity| exact HP]].
Qed.

(* ------------------------------------------------------------------------- *)
(* The node level: at_nodeA over segs gives at_nodeA over segs ++ tail at the  *)
(* run's ROM (no hypothesis on the tail: reads lift by first match).           *)
(* ------------------------------------------------------------------------- *)

Lemma itl_at_nodeA_lift : forall n RNG ms,
  at_nodeA segs n RNG ms -> at_nodeA (segs ++ tail) n RNG (TopLevel.set_rom (seg_rom (segs ++ tail)) ms).
Proof.
  intros n RNG ms H.
  destruct n; cbn [at_nodeA] in H |- *.
  (* the ten nodes read through at_node / ncov *)
  all: try (destruct H as [Hat Hcov]; split; [exact (TopLevel.at_node_lift segs tail _ _ Hat)| exact Hcov]).
  (* NMmap: registers only *)
  all: try exact H.
  (* NWritev *)
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & H9 & iovs & H10 & H11).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [reflexivity|]. split; [exact H9|].
  exists iovs. split; [exact (TopLevel.bytes_at_app_tail segs tail _ _ _ H10)|].
  clear -H11. induction H11 as [|iov bs l1 l2 HP HF IH]; [constructor|].
  constructor; [|exact IH].
  destruct HP as (A & B & C & D). split; [exact A|]. split; [exact B|]. split; [|exact D].
  exact (TopLevel.bytes_at_app_tail segs tail _ _ _ C).
Qed.

(* ------------------------------------------------------------------------- *)
(* The tree level.                                                            *)
(* ------------------------------------------------------------------------- *)

Definition run_post {R} (Q : R -> footprint -> machine_state -> Prop) : R -> footprint -> machine_state -> Prop :=
  fun r RNG' ms' => exists msp, ms' = TopLevel.set_rom (seg_rom (segs ++ tail)) msp /\ Q r RNG' msp.

Variable fstep : node -> resp -> footprint -> footprint -> Prop.

Lemma implF_lift_run : forall {R} (t : itree node R) RNG Q ms,
  implF segs (at_nodeA segs) fstep RNG t Q ms ->
  implF (segs ++ tail) (at_nodeA (segs ++ tail)) fstep RNG t (run_post Q) (TopLevel.set_rom (seg_rom (segs ++ tail)) ms).
Proof.
  intros R t. induction t as [r|n k IH]; intros RNG Q ms H; cbn [implF] in H |- *.
  - exact (itl_evtF_lift (seg_rom (segs ++ tail)) RNG _ ms H).
  - eapply evtF_mono; [exact (itl_evtF_lift (seg_rom (segs ++ tail)) RNG _ ms H)|].
    intros ms' (msp & -> & Hat & Hk). split; [exact (itl_at_nodeA_lift n RNG msp Hat)|].
    intros rsp RNG' HF. rewrite TopLevel.nret_set_rom. apply IH. exact (Hk rsp RNG' HF).
Qed.

Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable NMAX : nat.

Lemma tree_atA_lift_run : forall {R} RNG A (t : itree node R) Q ms mo mo_,
  tree_atA segs (at_nodeA segs) nstep minv nsafe fstep NMAX RNG A t Q ms mo mo_ ->
  tree_atA (segs ++ tail) (at_nodeA (segs ++ tail)) nstep minv nsafe fstep NMAX RNG A t (run_post Q)
           (TopLevel.set_rom (seg_rom (segs ++ tail)) ms) mo mo_.
Proof.
  intros R RNG A t Q ms mo mo_ (Hi & Hl & Hh & Hm & Hs & Hr).
  split; [exact (implF_lift_run t RNG Q ms Hi)|].
  exact (conj Hl (conj Hh (conj Hm (conj Hs Hr)))).
Qed.

End RunTail.

(* The main body over the run's list: the ITreeA twin of TopLevel's run_of_tree step from impl to the run. *)
Theorem implF_srealizes_run : forall segs tail fstep NMAX {R} (t : itree node R) RNG A Q ms mo mo_,
  Forall (fun s => seg_executable s = false) tail ->
  tree_atA segs (at_nodeA segs) nstepA minvA (nsafeA NMAX) fstep NMAX RNG A t Q ms mo mo_ ->
  SpinAlg.srealizes (segs ++ tail) (mkCfg (TopLevel.set_rom (seg_rom (segs ++ tail)) ms) mo_) (ptraces nstepA nexitA t mo).
Proof.
  intros segs tail fstep NMAX R t RNG A Q ms mo mo_ NX HT.
  exact (implF_srealizes (segs ++ tail) (at_nodeA (segs ++ tail)) nstepA nexitA minvA (nsafeA NMAX) fstep NMAX
           (nodesA_sound (segs ++ tail) NMAX) t RNG A _ _ mo mo_
           (tree_atA_lift_run segs tail NX fstep nstepA minvA (nsafeA NMAX) NMAX RNG A t Q ms mo mo_ HT)).
Qed.
