(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe MPaths STree Malloc Stdio HarnessP Adapter Driver
  PState ProgP StepB KLink KEv ModelInv ImgFacts ModelOK EquivShared EquivProg RSim RSimProg SizeHist PTotal ProgA ProgZ EquivZA ModelZ ZSafe LB_Main Gap.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
Require OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common.Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PasA : AAlloc := mkAAlloc PState bptr raw_malloc raw_free (fun _ _ _ _ => mret tt) ptr_addr ps_so set_so_ps ps_fa set_fa_ps.

Definition GT : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_GT : frame_ok GT. Proof. intros ? ? ? ? _ _ _ _; exact I. Qed.

Definition AIP (Y : list (bptr * Z)) (s : PState) (mo : Model) : Prop := OWN (map fst Y) GT s mo.

Lemma OWN_minv X s mo : OWN X GT s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(L & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma OWN_vm X s mo mo' : OWN X GT s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> OWN X GT s mo'.
Proof.
  intros [(L & Hc & HK & Hi) [Hnd _]] Hvm Hmi Hh. split; [|split; [exact Hnd| exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| exact Hvm| exact Hmi| exact Hh].
Qed.

Lemma OWN_fds X s mo f : OWN X GT s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> OWN X GT s (with_fds f mo).
Proof. intros H Hmi Hh. eapply OWN_vm; [exact H| apply m_vmmaps_with_fds| exact Hmi| exact Hh]. Qed.

Lemma p_get_set : forall v s, ps_so (set_so_ps v s) = v. Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma p_set_set : forall v w s, set_so_ps v (set_so_ps w s) = set_so_ps v s. Proof. intros v w [? ? ? ?]; reflexivity. Qed.
Lemma p_set_get : forall s, set_so_ps (ps_so s) s = s. Proof. intros [? ? ? ?]; reflexivity. Qed.
Lemma p_addr_so : forall v s p, ptr_addr (set_so_ps v s) p = ptr_addr s p. Proof. intros v [? ? ? ?] p; reflexivity. Qed.
Lemma p_cl_get_set : forall v s, ps_fa (set_fa_ps v s) = v. Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma p_cl_so : forall v s, ps_fa (set_so_ps v s) = ps_fa s. Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma p_so_cl : forall v s, ps_so (set_fa_ps v s) = ps_so s. Proof. intros v [? ? ? ?]; reflexivity. Qed.

Lemma AIP_perm : forall Y Y' s mo, Permutation Y Y' -> AIP Y s mo -> AIP Y' s mo.
Proof. intros Y Y' s mo HP H. unfold AIP in *. eapply OWN_perm; [apply Permutation_map; exact HP| exact H]. Qed.
Lemma AIP_so : forall Y s mo v, AIP Y s mo -> AIP Y (set_so_ps v s) mo.
Proof. intros Y s mo v H. unfold AIP in *. eapply OWN_other; [exact H| reflexivity| reflexivity| exact I]. Qed.
Lemma AIP_cl : forall Y s mo v, AIP Y s mo -> AIP Y (set_fa_ps v s) mo.
Proof. intros Y s mo v H. unfold AIP in *. eapply OWN_other; [exact H| reflexivity| reflexivity| exact I]. Qed.
Lemma AIP_model : forall Y s mo, AIP Y s mo -> minv mo /\ m_halted mo = None.
Proof. intros Y s mo H. exact (OWN_minv _ _ _ H). Qed.
Lemma AIP_fds : forall Y s mo f, AIP Y s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> AIP Y s (with_fds f mo).
Proof. intros Y s mo f H Mi Hh. exact (OWN_fds _ _ _ _ H Mi Hh). Qed.

Lemma sub1 : forall n mo r mo' e, ~ nf_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma same1 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstep n mo r mo e. Proof. auto. Qed.
Lemma io1 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstep n mo r mo' e. Proof. auto. Qed.
Lemma MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> minv mo -> m_halted mo = None -> minv mo' /\ m_halted mo' = None.
Proof. intros n mo rsp mo' evs Hst _ Hmi Hh. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi']. auto. Qed.

Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Lemma size_overflows_REQMAX n : 0 <= n <= REQMAX -> size_overflows n = false.
Proof. intros Hn. unfold size_overflows, REQMAX in *. apply Z.leb_gt. lia. Qed.

Lemma P_malloc : forall Y n s mo, AIP Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  tglob nstep PhiP (raw_malloc n s) mo ->
  STOTP (raw_malloc n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AIP ((q, n) :: Y) s' mo' /\ n < 2^63
                         /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y n s mo HA Hn _ G. eapply STOT_mono; [apply (raw_malloc_STOT (map fst Y) GT n s mo frame_ok_GT HA ltac:(lia) (size_overflows_REQMAX n Hn) G)|].
  intros r s' mo' (p & -> & HO & H63 & Hso & Hfa & Hfd & Hfs). exists p. unfold AIP. cbn [map fst]. auto 10.
Qed.

Lemma P_free : forall Y q n s mo, AIP ((q, n) :: Y) s mo -> tglob nstep PhiP (raw_free q s) mo ->
  STOTP (raw_free q s) mo (fun _ s' mo' => AIP Y s' mo' /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y q n s mo HA G. eapply STOT_mono; [apply (raw_free_STOT (map fst Y) GT q s mo frame_ok_GT HA G)|].
  intros [] s' mo' (HO & Hso & Hfa & Hfd & Hfs). unfold AIP. auto.
Qed.

Lemma P_annot : forall Y (q : bptr) (cap old new : Z) s mo, AIP Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
  (old = 0 \/ new = 0) ->
  tglob nstep PhiP (mret tt s) mo ->
  STOTP (mret tt s) mo (fun _ s' mo' => AIP Y s' mo' /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y q cap old new s mo HA _ _ _ _ _. eapply STOT_mono; [apply STOT_ret|]. intros [] s' mo' (_ & -> & ->). auto.
Qed.

Definition KP : AAllocOK PasA nstep PhiP minv :=
  mkAAllocOK PasA nstep PhiP minv sub1 same1 io1 MI1_pres p_get_set p_set_set p_set_get p_addr_so p_cl_get_set p_cl_so p_so_cl
             AIP AIP_perm AIP_so AIP_cl AIP_model AIP_fds P_malloc P_free P_annot.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation RXP := (EquivZA.RX PasA nstep PhiP minv KP).
Local Notation rsimZP := (rsim nstep nstep nexit nexit PhiZ PhiP).

(* [comment removed for export] *)
Lemma main_exit_PasA : forall rs argv, ProgP.main_exit rs argv = progA_main PasA rs argv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma startup_pair : forall X, rsimZP (RXP X) (mret tt) startup (fun _ _ => RXP X).
Proof.
  intros X. apply rsim_silent. intros s1 mo1 s2 mo2 (M1 & H1 & HA & Hso & Hcl & Hfd & Hfs) G1 G2.
  destruct (AIP_model _ _ _ HA) as [Hmi2 Hh2].
  eexists _, _. split; [apply STOT_ret| split; [apply (startup_STOT s2 mo2 Hmi2 Hh2)|]].
  intros [] s1' mo1' [] s2' mo2' (_ & -> & ->) (-> & Hvm2 & Hfd2 & Hfs2 & Hmi2' & Hh2').
  unfold EquivZA.RX. split; [exact M1|]. split; [exact H1|]. split; [| split; [exact Hso| split; [exact Hcl| split; congruence]]].
  cbn [AI KP]. unfold AIP in *. exact (OWN_vm _ _ _ _ HA Hvm2 Hmi2' Hh2').
Qed.

Lemma prog_pair : forall rsZ rsP argv (Q : Empty_set -> Empty_set -> RSim.rel ZSt PState),
  Forall (fun a => zlength a <= PIECE_MAX) argv ->
  rsimZP (RXP []) (mret tt ;;; progA_main AAllocZ rsZ argv) (ProgP.prog_with rsP argv) Q.
Proof.
  intros rsZ rsP argv Q Hargv. unfold ProgP.prog_with. rewrite main_exit_PasA.
  eapply rsim_seq; [apply startup_pair|]. intros [] [].
  apply (EquivZA.main_exit_pair PasA nstep PhiP minv rsZ rsP KP argv Q Hargv).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_fds_mo0 : forall segs lim en inp, m_fds (mo0 segs lim en inp) = init_fds.
Proof. intros segs lim [? ? ?] inp. reflexivity. Qed.
Lemma m_fs_mo0 : forall segs lim en inp, m_fs (mo0 segs lim en inp) = in_fs inp.
Proof. intros segs lim [? ? ?] inp. reflexivity. Qed.

Section Image.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z).
Hypothesis Hpos : 0 < reserved_top (segments_reserved segs).
Hypothesis Hceil : reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo.
Hypothesis Hfloor : reserved_top (segments_reserved segs) + brk_aslr_max + 2^31 + 8 * PGSZ <= FLOOR.   (* [comment removed for export] *)
Hypothesis Hresv : live_bytes (segments_reserved segs) <= 2^30.
Hypothesis Hlim : 2^31 <= lim.

(* [comment removed for export] *)
Lemma tglob_prog : forall rs en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  tglob nstep PhiP (ProgP.prog segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros rs en inp He Hi. apply tglob_PhiP_intro.
  - eapply mo0_minv; [exact He| apply valid_input_either_va_size; exact Hi].
  - apply mo0_not_halted.
  - exact (proj2 (prog_model_ok segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim He Hi)).
  - exact (never_forced segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim He Hi).
Qed.

Theorem equiv_ZP_core : forall rsZ rsP en inp moZ,
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  minv moZ -> m_halted moZ = None -> m_fds moZ = init_fds -> m_fs moZ = in_fs inp ->
  forall tr, ttrace nstep nexit (progZ_tree rsZ (argv_Z (in_argv inp))) moZ tr
             <-> ttrace nstep nexit (ProgP.prog segs rsP inp en) (mo0 segs lim en inp) tr.
Proof.
  intros rsZ rsP en inp moZ He Hi MZ HZ FdZ FsZ.
  pose proof (progZ_no_leaf inp moZ rsZ Hi MZ HZ FdZ FsZ) as NLZ.
  pose proof (tglob_prog rsP en inp He Hi) as GP.
  pose proof Hi as (Hargv & _).
  unfold progZ_tree, progA_tree in *. unfold ProgP.prog, ProgP.prog_itree in *.
  set (sP0 := ps_init (reservedZ segs) (entry_atop en)) in *.
  destruct (rsim_ttrace nstep nstep nexit nexit PhiZ PhiP (EquivZA.RX PasA nstep PhiP minv KP [])
              (mret tt ;;; progA_main AAllocZ rsZ (argv_Z (in_argv inp))) (ProgP.prog_with rsP (argv_Z (in_argv inp)))
              (fun _ _ _ _ _ _ => False) sZ_init moZ sP0 (mo0 segs lim en inp)
              (prog_pair rsZ rsP _ _ (argv_Z_pieces _ Hargv))) as [EQ _].
  - (* [comment removed for export] *)
    unfold EquivZA.RX. split; [exact MZ|]. split; [exact HZ|]. split; [| split; [reflexivity| split; [split; reflexivity| split]]].
    + cbn [AI KP]. unfold AIP, clb. cbn [a_cl PasA ps_fa sP0 ps_init app aX map].
      destruct en as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He. destruct He as ((Hsp1 & Hsp2 & _) & Hbrk & _ & _).
      unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp].
      eapply OWN_weakG; [apply (GI_init segs brk0 mbase sp lim inp _ Hbrk Hpos ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl Hceil)|]. intros _; exact I.
    + rewrite FdZ. symmetry. apply m_fds_mo0.
    + rewrite FsZ. symmetry. apply m_fs_mo0.
  - apply tglob_trivial. intros; exact I.
  - apply (tglob_after_empty nstep PhiP _ (fun p => match fst p : Empty_set with end)). exact GP.
  - intros tr r mo' Hp. change ((mret tt ;;; progA_main AAllocZ rsZ (argv_Z (in_argv inp))) sZ_init) with (progA_main AAllocZ rsZ (argv_Z (in_argv inp)) sZ_init) in Hp.
    destruct r as [|[[] ?]]. apply (NLZ tr Unr mo'). apply tpath_ebind. left. auto.
  - intros tr. rewrite !ttrace_after_empty.
    change ((mret tt ;;; progA_main AAllocZ rsZ (argv_Z (in_argv inp))) sZ_init) with (progA_main AAllocZ rsZ (argv_Z (in_argv inp)) sZ_init) in EQ.
    apply EQ.
Qed.

(* [comment removed for export] *)
Theorem tfam_ZP : forall rsP en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  forall tr, tree_traces (ProgP.prog segs rsP inp en) (mo0 segs lim en inp) tr
             <-> Common.Spec.spec (in_argv inp) (in_fs inp) tr.
Proof.
  intros rsP en inp He Hi tr.
  destruct (moZ0_ok inp) as (Z1 & Z2 & Z3 & Z4).
  rewrite <- (bridgeU' inp (moZ0 inp) 0 Hi Z1 Z2 Z3 Z4 tr).
  unfold tree_traces. split; intros (full & Hf & Hp); exists full; (split; [| exact Hp]);
    apply (equiv_ZP_core 0 rsP en inp (moZ0 inp) He Hi Z1 Z2 Z3 Z4 full); exact Hf.
Qed.
End Image.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem tfam_plain : forall rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  forall tr, tree_traces (ProgP.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp) tr
             <-> Common.Spec.spec (in_argv inp) (in_fs inp) tr.
Proof. exact (tfam_ZP psegs p_init_pc p_phdrs source_alloc_limit top_pos_plain ceil_plain floor_plain resv_plain lim_p). Qed.

(* [comment removed for export] *)
Theorem tfam_plain_lim : forall lim, 2^31 <= lim -> forall rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  forall tr, tree_traces (ProgP.prog psegs rs inp en) (mo0 psegs lim en inp) tr
             <-> Common.Spec.spec (in_argv inp) (in_fs inp) tr.
Proof. intros lim Hlim. exact (tfam_ZP psegs p_init_pc p_phdrs lim top_pos_plain ceil_plain floor_plain resv_plain Hlim). Qed.

Theorem tfam_ubsan : forall rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  forall tr, tree_traces (ProgP.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp) tr
             <-> Common.Spec.spec (in_argv inp) (in_fs inp) tr.
Proof. exact (tfam_ZP usegs u_init_pc u_phdrs target_alloc_limit top_pos_ubsan ceil_ubsan floor_ubsan resv_ubsan lim_u). Qed.
