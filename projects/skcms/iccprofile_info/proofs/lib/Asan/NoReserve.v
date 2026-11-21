(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the nodes discharge the read-only-backing premise (RomBase.sys_rob), the mmap nodes take the decline test (place_declined_b), and grant_ok_nr_intro takes the call's hint; the ASan-init worked example (Section AsanInitReal) and the write, spin and straight-line nodes only it used are removed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SimInv PropExec CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac SpinAlg.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *) Import ListNotations.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import RomBase RomWritev.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.


(* ================================================================= *)
(* Materialization plumbing: the two wrappers every node below uses    *)
(* ================================================================= *)

(** A syscall effect with no writes and no copyins names no user-memory
    access: materializing it is the identity on ANY model (the
    [DivergeSim.materialize_model_accesses_nil] instance, stated at the
    effect so the node proofs can rewrite without normalizing
    [syscall_effect_accesses] first).  This covers every effect the mmap
    / munmap / exit nodes produce. *)
Lemma materialize_syscall_effect_nil :
  forall (m : Model) (r : word) (zs us : list (word * word)),
  materialize_model_accesses m
    (syscall_effect_accesses (mkEffectU r [] zs us [] []))
  = Some m.
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.

(** The munmap-effect spelling of the same fact ([munmap_eff] is a
    definition, so the [mkEffectU] pattern above does not match it
    syntactically). *)
Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
  materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
  = Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.

(* ================================================================= *)
(* Disjointness plumbing                                              *)
(* ================================================================= *)

(** Disjointness restricts along access-list inclusion. *)
Lemma accesses_outside_lazy_incl :
  forall (accs accs' : list (word * nat)) (lazy : list (word * word)),
  (forall x, In x accs' -> In x accs) ->
  accesses_outside_lazy accs lazy ->
  accesses_outside_lazy accs' lazy.
Proof.
  intros accs accs' lazy Hincl Hout a n lo sz Hin Hlz.
  exact (Hout a n lo sz (Hincl _ Hin) Hlz).
Qed.

Lemma accesses_outside_lazy_app_l :
  forall accs1 accs2 lazy,
  accesses_outside_lazy (accs1 ++ accs2) lazy ->
  accesses_outside_lazy accs1 lazy.
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. left. exact Hx.
Qed.

Lemma accesses_outside_lazy_app_r :
  forall accs1 accs2 lazy,
  accesses_outside_lazy (accs1 ++ accs2) lazy ->
  accesses_outside_lazy accs2 lazy.
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. right. exact Hx.
Qed.

(* ================================================================= *)
(* The NORESERVE model transformer and its frame                      *)
(* ================================================================= *)

(** State after a granted NORESERVE reservation: the ordinary grant
    ledger entry plus the lazy-backing record — exactly the
    [with_mmap_backing flags a n (with_vmmaps ... m)] the spec's grant
    branch applies when the NORESERVE bit is set
    ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mmap.v:2161-2166, 760-761]). *)
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m).

Lemma mmap_model_noreserve_halted : forall a n m,
  m_halted (mmap_model_noreserve a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fs : forall a n m,
  m_fs (mmap_model_noreserve a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fd1chan : forall a n m,
  fd1chan m -> fd1chan (mmap_model_noreserve a n m).
Proof. intros a n m H. exact H. Qed.
(** The whole point: the grant's page-aligned interior lands on the
    ledger.  For the modeled grant shape ([a] page-aligned, [n] the
    page-rounded nonzero length) [lazy_interior a n = [(a, n)]], so the
    ledger is non-empty from here on. *)
Lemma mmap_model_noreserve_lazy : forall a n m,
  m_vm_lazy (mmap_model_noreserve a n m) = lazy_interior a n ++ m_vm_lazy m.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* RESIDUAL 1 — the NORESERVE-shaped mmap call                        *)
(* ================================================================= *)

(** The register shape of the ASan shadow reservation: the ONE modeled
    anonymous rw shape ([Mmap.mmap_modeled_b], which masks the
    NORESERVE bit out via [mmap_flags_core]) with the bit SET:
    flags (a3) = MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE
               = 2 + 32 + 16384 = 16418. *)
Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(** Under [mmap_args_ok_noreserve] the fail-closed gates of
    [check_mmap] / [mmap_spec] are open: the masked shape matches. *)
Lemma mmap_args_ok_noreserve_gates : forall ms,
  mmap_args_ok_noreserve ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\
  mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
  = true.
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

(** The NORESERVE bit, read back where it changes answers. *)
Lemma mmap_noreserve_b_flags : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof. reflexivity. Qed.

(** May the kernel grant the NORESERVE reservation [a, a+n)?
    [MmapSim.grant_ok] minus the backed-budget conjunct: the reservation
    is granted UNCONDITIONALLY on budget ([mmap_noreserve_backed_ok] is
    [true] for a NORESERVE call); pages charge on first touch.

    Its first conjunct is [MmapSim.grant_ok]'s: the address is the ONE
    [Mmap.linux_place] gives, not merely a free one. *)
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

(** Building one: the placement test is all a caller has to show. *)
Lemma grant_ok_nr_intro : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  grant_ok_nr hint m a n = true.
Proof.
  intros hint m a n Hn Hnal Hpl.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok_nr. rewrite Hpl, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop).
  reflexivity.
Qed.

Lemma grant_ok_nr_place : forall hint m a n,
  grant_ok_nr hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok_nr in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

Lemma grant_ok_nr_unpack : forall hint m a n,
  grant_ok_nr hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_nr in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[_ H1] H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  auto 6.
Qed.

(** A budget-free grant is a fortiori not an errno encoding. *)
Lemma grant_nr_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_nr hint model a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg.
  destruct (grant_ok_nr_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

(** The errno resolutions of the NORESERVE call (failure-anytime is
    retained: this arm exists for every modeled mmap shape). *)
Lemma mmap_fail_ok_noreserve : forall segs ms x8 model e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok_noreserve ms -> In e mmap_errnos ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn Hdecl.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

(** The grant resolutions: any [grant_ok_nr] address, successor model
    [vm_add_lazy]-wrapped. *)
Lemma mmap_succ_ok_noreserve : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model a Hno Ha Hdecl Hg.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  rewrite (grant_nr_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  pose proof (grant_ok_nr_place _ _ _ _ Hg) as Hp.
  rewrite Hflags.
  unfold mmap_noreserve_backed_ok, with_mmap_backing.
  rewrite mmap_noreserve_b_flags.
  rewrite Hp. cbn [andb].
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

(** Inversion: the admissible outcomes of the NORESERVE call are
    EXACTLY the errnos plus the [grant_ok_nr] grants. *)
Lemma mmap_ok_inv_noreserve : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
      /\ model' = model) \/
   (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  destruct (place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
              (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hdecl;
    [discriminate|].
  rewrite Hflags in Hspec.
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite mmap_noreserve_b_flags in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
    cbv beta iota in Hspec.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. auto.
  - rewrite andb_true_r in Hspec.
    destruct (linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                (ms_gpr ms 0) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) r)
      eqn:Hcond; rewrite ?Hcond in Hspec.
    2:{ rewrite andb_false_l in Hspec. discriminate. }
    destruct (listNN_eqb zs
                [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
      rewrite ?Hzs in Hspec.
    2:{ rewrite andb_false_r in Hspec. discriminate. }
    cbn [andb] in Hspec.
    apply listNN_eqb_eq in Hzs. subst zs.
    inversion Hspec; subst.
    split; [reflexivity|]. right.
    exists r. split; [|split].
    + exact (grant_ok_nr_intro _ _ _ _ (proj1 (mmap_grant_len_ok _ Hl))
               (proj2 (mmap_grant_len_ok _ Hl)) Hcond).
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

Lemma mmap_no_unmodeled_noreserve : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hdecl Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hspec.
  unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hdecl in Hspec.
  cbv beta iota zeta in Hspec.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  rewrite E in Hspec. cbv beta iota in Hspec.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* ----------------------------------------------------------------- *)
(* One-step inversion for the NORESERVE mmap config — LAZY-TOLERANT   *)
(* by construction: both resolutions' effects name no access, so the  *)
(* materialization collapses on ANY ledger.                           *)
(* ----------------------------------------------------------------- *)

Lemma sstep_mmap_inv_noreserve : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hdecl Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model_noreserve a _ model) _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      right. exists a. auto.
  - (* sstep_syscall_materialization_fault: no access can fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst eff model';
      rewrite materialize_syscall_effect_nil in Hmat;
      discriminate
    end.
  - (* sstep_exit *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_noreserve_halted, Hh in H6; discriminate ]
    end.
  - (* sstep_killed: a killed post-model is halted, and no arm here halts *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | rewrite m_killed_of_m_halted_none in H6;
        [ discriminate | rewrite mmap_model_noreserve_halted; exact Hh ] ]
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled_noreserve segs ms x8 model Hno Hargs Hdecl H3)
    end.
Qed.

(** The NORESERVE node's interface.  NO ledger hypothesis at all: the
    reservation itself is usable both before (ASan's shadow, empty
    ledger) and after (a second reservation) the ledger fills. *)
Lemma node_mmap_noreserve : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  node_ok segs (mkCfg ms model)
    ({e : Z | In e mmap_errnos}
     + {a : word | grant_ok_nr (ms_gpr ms 0) model a
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
    (fun _ => [])
    (fun i => match i with
       | inl (exist _ e _) =>
           mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
       | inr (exist _ a _) =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs Hdecl.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [[e He] | [a Ha]]; cbn.
    + rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
               model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok_noreserve; assumption.
      * exact Hh.
      * apply materialize_syscall_effect_nil.
    + apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
               (mmap_model_noreserve a n model) (mmap_model_noreserve a n model) []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_succ_ok_noreserve; assumption.
      * rewrite mmap_model_noreserve_halted; exact Hh.
      * apply materialize_syscall_effect_nil.
  - intros e st Hss.
    destruct (sstep_mmap_inv_noreserve ms model x8 e st Hh Hsvc Hno Hargs Hdecl Hss)
      as [-> [(er & Her & ->) | (a & Ha & ->)]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr (exist _ a Ha)). split; reflexivity.
Qed.

(** The plain two-branch NORESERVE node (both arms continue). *)
Lemma srz_mmap_noreserve : forall ms model x8 A B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes segs (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hsvc Hno Hargs Hdecl HA HB Hex.
  destruct Hex as [a0 Ha0].
  eapply (srz_alt2 segs (mkCfg ms model)
            {e : Z | In e mmap_errnos}
            {a : word | grant_ok_nr (ms_gpr ms 0) model a
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ A B
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  2: rob_auto.
  - apply (node_mmap_noreserve ms model x8); assumption.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

(* ================================================================= *)
(* RESIDUAL 2 — lazy-tolerant re-derivations of the mmap and munmap  *)
(* nodes (exit needs nothing: [SpinAlg.srz_exit] has no ledger       *)
(* premise)                                                          *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* mmap (plain rw shape), through a non-empty ledger                  *)
(* ----------------------------------------------------------------- *)

Lemma sstep_mmap_inv_lazy : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hdecl Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      right. exists a. auto.
  - (* sstep_syscall_materialization_fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst eff model';
      rewrite materialize_syscall_effect_nil in Hmat;
      discriminate
    end.
  - (* sstep_exit *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_halted, Hh in H6; discriminate ]
    end.
  - (* sstep_killed: a killed post-model is halted, and no arm here halts *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | rewrite m_killed_of_m_halted_none in H6;
        [ discriminate | rewrite mmap_model_halted; exact Hh ] ]
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs Hdecl H3)
    end.
Qed.

(** [SpinAlg.node_mmap] with the [m_vm_lazy model = []] premise
    DROPPED: both resolutions' effects name no access. *)
Lemma node_mmap_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  node_ok segs (mkCfg ms model)
    ({e : Z | In e mmap_errnos}
     + {a : word | grant_ok (ms_gpr ms 0) model a
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
    (fun _ => [])
    (fun i => match i with
       | inl (exist _ e _) =>
           mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
       | inr (exist _ a _) =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs Hdecl.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [[e He] | [a Ha]]; cbn.
    + rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
               model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok; assumption.
      * exact Hh.
      * apply materialize_syscall_effect_nil.
    + apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
               (mmap_model a n model) (mmap_model a n model) []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_succ_ok; assumption.
      * rewrite mmap_model_halted; exact Hh.
      * apply materialize_syscall_effect_nil.
  - intros e st Hss.
    destruct (sstep_mmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hdecl Hss)
      as [-> [(er & Her & ->) | (a & Ha & ->)]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr (exist _ a Ha)). split; reflexivity.
Qed.

(** The plain two-branch mmap node, ledger-free. *)
Lemma srz_mmap_lazy : forall ms model x8 A B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes segs (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hsvc Hno Hargs Hdecl HA HB Hex.
  destruct Hex as [a0 Ha0].
  eapply (srz_alt2 segs (mkCfg ms model)
            {e : Z | In e mmap_errnos}
            {a : word | grant_ok (ms_gpr ms 0) model a
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ A B
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  2: rob_auto.
  - apply (node_mmap_lazy ms model x8); assumption.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

(* ----------------------------------------------------------------- *)
(* munmap, through a non-empty ledger                                 *)
(* ----------------------------------------------------------------- *)

Lemma sstep_munmap_inv_lazy : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + right.
      match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite materialize_munmap_eff_nil in Hmat;
        inversion Hmat; subst
      end.
      reflexivity.
  - (* sstep_syscall_materialization_fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite materialize_syscall_effect_nil in Hmat
      | rewrite materialize_munmap_eff_nil in Hmat ];
      discriminate
    end.
  - (* sstep_exit *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6 | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - (* sstep_killed *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6
      | rewrite m_killed_of_m_halted_none in H6;
        [| rewrite munmap_model_halted; exact Hh] ];
      discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

Lemma node_munmap_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
    (fun _ => [])
    (fun i => match i with
       | inl (exist _ e _) =>
           mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
       | inr _ =>
           mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                 (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                               model)
       end).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs. split.
  - intros [[e He] | []]; cbn.
    + rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
               model model []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_fail_ok; assumption.
      * exact Hh.
      * apply materialize_syscall_effect_nil.
    + apply (sstep_syscall segs ms model x8 (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_ok; assumption.
      * rewrite munmap_model_halted; exact Hh.
      * apply materialize_munmap_eff_nil.
  - intros e st Hss.
    destruct (sstep_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
      as [-> [(er & Her & ->) | ->]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr tt). split; reflexivity.
Qed.

Lemma srz_munmap_lazy : forall ms model x8 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  (forall e, In e munmap_errnos ->
     srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) T) ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hsvc Hno Hargs Hfail Hc.
  apply (srz_silent_all segs (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
           (fun i => match i with
              | inl (exist _ e _) =>
                  mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
              | inr _ =>
                  mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                      model)
              end) T (inr tt));
    [apply (node_munmap_lazy ms model x8); assumption | rob_auto |].
  intros [[e He] | []]; cbn; [exact (Hfail e He) | exact Hc].
Qed.

(* ================================================================= *)
(* RESIDUAL 3 — the chained disjoint straight line                    *)
(* ================================================================= *)

(** [CatSim.msteps] with the access reports CARRIED: a run of ordinary
    (non-syscall) instruction steps, accumulating every reported
    range.  Chain per-instruction [stepacc_*] facts (below) into one
    [msteps_acc], show the accumulated list disjoint from the ledger
    ONCE, and the whole line walks any obligation through it. *)
Inductive msteps_acc
    : machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step_accesses segs ms
      = MachineOk (@mkAccessReport machine_state ms1 ranges) ->
    msteps_acc ms1 ms2 accs ->
    msteps_acc ms ms2 (ranges ++ accs).

Lemma msteps_acc_one : forall ms ms' ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  msteps_acc ms ms' ranges.
Proof.
  intros ms ms' ranges Hsvc Hstep.
  rewrite <- (app_nil_r ranges).
  eapply msta_step; [exact Hsvc | exact Hstep | apply msta_refl].
Qed.

Lemma msteps_acc_trans : forall ms ms' ms'' accs1 accs2,
  msteps_acc ms ms' accs1 -> msteps_acc ms' ms'' accs2 ->
  msteps_acc ms ms'' (accs1 ++ accs2).
Proof.
  intros ms ms' ms'' accs1 accs2 H; revert accs2 ms''.
  induction H as [ms | ms ms1 ms2 ranges accs Hsvc Hstep H IH];
    intros accs2 ms'' H2; [exact H2|].
  rewrite <- app_assoc. eapply msta_step; eauto.
Qed.

Lemma rz_msteps_disjoint : forall ms ms' model accs T,
  m_halted model = None ->
  msteps_acc ms ms' accs ->
  accesses_outside_lazy accs (m_vm_lazy model) ->
  realizes segs (mkCfg ms' model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms ms' model accs T Hh Hms; revert T;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros T Hout Hc; [exact Hc|].
  eapply rz_step_disjoint;
    [ exact Hh | exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.

(** ...and the straight line INTO a spin ([LazyFrame.ts_step_disjoint],
    chained). *)
Lemma ts_msteps_disjoint : forall ms ms' model accs,
  msteps_acc ms ms' accs ->
  accesses_outside_lazy accs (m_vm_lazy model) ->
  to_spin segs ms' model ->
  to_spin segs ms model.
Proof.
  intros ms ms' model accs Hms;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros Hout Hspin; [exact Hspin|].
  eapply ts_step_disjoint;
    [ exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hspin] ].
Qed.

End WithSegs.

(* ================================================================= *)
(* RESIDUAL 3, per-instruction layer: [PropExec]'s step inventory     *)
(* mirrored at the [step_accesses] level.  Same hypotheses, same      *)
(* successor state, conclusion CARRIES the access report: [] for the  *)
(* ALU / branch / jump / ecall forms, the single read range for the   *)
(* seven load forms.  PropExec has no store lemmas, so none appear    *)
(* here (mirror the coverage, one level down).  These are what an     *)
(* [msteps_acc] chain is built from.                                  *)
(* ================================================================= *)

End WithFP1.
Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.
Section WithFP2.
Context {fx : FPState}.


(* ----------------------------------------------------------------- *)
(* ALU forms: empty report                                            *)
(* ----------------------------------------------------------------- *)

Lemma stepacc_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* Branches / jumps / lui / auipc / ecall: empty report               *)
(* ----------------------------------------------------------------- *)

Lemma stepacc_branch_tk_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst regs (btgt pc (bv_signed imm)) mem rom) []).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma stepacc_branch_ft_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst regs (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma stepacc_lui : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma stepacc_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma stepacc_jal_x0 : forall segs regs pc mem rom w (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst regs (btgt pc (bv_signed imm)) mem rom) []).
Proof.
  intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  rewrite is_x0_0; cbv beta iota.
  rewrite b_addsext. reflexivity.
Qed.

Lemma stepacc_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
          (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.

Lemma stepacc_ecall : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
       ms_svc_pending := Some (getr regs 17);
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    []).
Proof.
  intros segs regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* Loads: the report is the single read range                         *)
(* ----------------------------------------------------------------- *)

Lemma stepacc_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
  { rewrite le_word_1, b_extract8_id. apply bv_eq.
    unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite b_lb_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 16 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 16) with 65536%Z.
    change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 32 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 32) with 4294967296%Z.
    change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 8%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

End WithFP2.
