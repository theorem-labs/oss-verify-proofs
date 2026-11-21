(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the place_declined_b premise on successful mmap answers; munmap can be refused; the model's error returns; the grant_ok changes; the mapping ledger's reserved ranges and mmap base; write's access_ok range; walks over the binary's segments lifted to the run's segment list). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SimInv ExitSim PropExec CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac SpinAlg.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RomBase RomWrite RomWritev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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

(** The write effect's single copyin range, materialized through a
    disjoint ledger: the identity ([LazyFrame] instance at the effect). *)
Lemma materialize_syscall_effect_copyin_disjoint :
  forall (m : Model) (r : word) (a : word) (n : nat),
  accesses_outside_lazy [(a, n)] (m_vm_lazy m) ->
  materialize_model_accesses m
    (syscall_effect_accesses (with_copyins [(a, n)] (mkEffect r [] [])))
  = Some m.
Proof.
  intros m r a n Hout.
  exact (materialize_model_accesses_disjoint m [(a, n)] Hout).
Qed.

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

(** [access_outside_range] is monotone in the access length. *)
Lemma access_outside_range_mono : forall (a : word) (n n' : nat) (lo sz : word),
  (n' <= n)%nat ->
  access_outside_range a n lo sz ->
  access_outside_range a n' lo sz.
Proof.
  intros a n n' lo sz Hle [Hnw Hd].
  split; [lia | destruct Hd as [Hd | Hd]; [left; lia | right; exact Hd]].
Qed.

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

(** A shorter access at the same base stays outside (the write node's
    per-delivery instance: disjointness of the FULL buffer covers every
    delivered prefix). *)
Lemma accesses_outside_lazy_shrink :
  forall (a : word) (len n : nat) (lazy : list (word * word)),
  (n <= len)%nat ->
  accesses_outside_lazy [(a, len)] lazy ->
  accesses_outside_lazy [(a, n)] lazy.
Proof.
  intros a len n lazy Hle Hout a' n' lo sz Hin Hlz.
  destruct Hin as [Hin | []]. injection Hin as Ha Hn. subst a' n'.
  apply (access_outside_range_mono a len n lo sz Hle).
  apply (Hout a len lo sz); [left; reflexivity | exact Hlz].
Qed.

(* ================================================================= *)
(* The NORESERVE model transformer and its frame                      *)
(* ================================================================= *)

(** State after a granted NORESERVE reservation: the ordinary grant
    ledger entry plus the lazy-backing record — exactly the
    [with_mmap_backing flags a n (with_vmmaps ... m)] the spec's grant
    branch applies when the NORESERVE bit is set (Mmap.v:941-948,
    341-342). *)
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
  unfold check_mmap. cbv beta.
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
  unfold check_mmap. cbv beta.
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
  unfold check_mmap in Hspec. cbv beta in Hspec.
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
  unfold check_mmap in Hspec. cbv beta in Hspec.
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

(** THE SPIN-ARMED NORESERVE NODE: the shadow-reservation shape ASan
    init actually has.  Every refusal spins ([to_spin], model
    unchanged — on the FIRST reservation the ledger is still empty
    there, so the no-lazy spellings feed this hypothesis
    as-is); every grant continues as [B] with the ledger non-empty.
    The refusal arm contributes only [[]], so the node realizes [B]
    alone. *)
Lemma srz_mmap_spin_noreserve : forall ms model x8 B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model) ->
  (forall a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes segs (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes segs (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hsvc Hno Hargs Hdecl Hspin HB Hex.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB a0 Ha0)).
  eapply srz_conseq.
  { apply (srz_node segs (mkCfg ms model)
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
                end)
             (fun i => match i with inl _ => t_nil | inr _ => B end)
             (inr (exist _ a0 Ha0))).
    - apply (node_mmap_noreserve ms model x8); assumption.
    - eapply sys_rob_memfree; [exact Hsvc | rewrite Hno; exact memfree_222].
    - intros [[e He] | [a Ha]]; cbn.
      + apply srz_spin; cbn; [apply Hspin; exact He | exact Hh].
      + apply HB; exact Ha. }
  intro tr. split.
  - intros [[[e He] | [a Ha]] Hi]; cbn in Hi.
    + apply (t_emit_nil_eq t_nil eq_refl tr) in Hi.
      unfold t_nil in Hi. subst tr. exact HB0.
    + exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro HBtr. exists (inr (exist _ a0 Ha0)).
    exact (proj2 (t_emit_nil_eq B HB0 tr) HBtr).
Qed.

(* ================================================================= *)
(* RESIDUAL 2 — lazy-tolerant re-derivations of the syscall nodes     *)
(* the ASan skeleton needs (mmap, munmap, write(1); exit needs        *)
(* nothing: [SpinAlg.srz_exit] never had a ledger premise)            *)
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

(** The spin-armed mmap node, ledger-free: [SpinAlg.srz_mmap_spin]
    usable AFTER the NORESERVE grant (the ASan skeleton's second
    allocation, standing on a non-empty ledger). *)
Lemma srz_mmap_spin_lazy : forall ms model x8 B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes segs (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes segs (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hsvc Hno Hargs Hdecl Hspin HB Hex.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB a0 Ha0)).
  eapply srz_conseq.
  { apply (srz_node segs (mkCfg ms model)
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
                end)
             (fun i => match i with inl _ => t_nil | inr _ => B end)
             (inr (exist _ a0 Ha0))).
    - apply (node_mmap_lazy ms model x8); assumption.
    - eapply sys_rob_memfree; [exact Hsvc | rewrite Hno; exact memfree_222].
    - intros [[e He] | [a Ha]]; cbn.
      + apply srz_spin; cbn; [apply Hspin; exact He | exact Hh].
      + apply HB; exact Ha. }
  intro tr. split.
  - intros [[[e He] | [a Ha]] Hi]; cbn in Hi.
    + apply (t_emit_nil_eq t_nil eq_refl tr) in Hi.
      unfold t_nil in Hi. subst tr. exact HB0.
    + exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro HBtr. exists (inr (exist _ a0 Ha0)).
    exact (proj2 (t_emit_nil_eq B HB0 tr) HBtr).
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
    (* #38 gave srz_silent_all a SECOND premise, `sys_rob segs c`, between node_ok and
       the per-successor obligation (SpinAlg.v:377-380, and the twin at
       AsanNodesLibE.v:167-170 states it identically).  This bracket supplied two slots
       for three goals, which is the whole of "Incorrect number of goals (expected 3
       tactics)" -- the apply never changed, the lemma did.  rob_auto is the discharge
       the in-tree caller that COMPILES already uses for this exact goal
       (AsanNodesLibE.v:343, `2: rob_auto.`), and RomBase.v:196 defines it; NoReserve
       requires RomBase directly.
       The ordinal here is safe where an inversion's would not be: it indexes this
       LEMMA'S OWN premise order, which its statement fixes, not an inductive's arm
       numbering, which a revision renumbers. *)
    [apply (node_munmap_lazy ms model x8); assumption | rob_auto |].
  intros [[e He] | []]; cbn; [exact (Hfail e He) | exact Hc].
Qed.

(* ----------------------------------------------------------------- *)
(* write(1, buf, len), through a non-empty ledger — the ONE node       *)
(* whose effect names an access (the copyin of the buffer), so the     *)
(* lazy-tolerant form takes the DISJOINTNESS hypothesis: the whole     *)
(* buffer lies outside every lazy range.                               *)
(* ----------------------------------------------------------------- *)

Lemma sstep_write_next_inv_disjoint : forall ms model x8 buf evs c',
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs (SNext c') ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
  intros ms model x8 buf evs c' Hh Hout Hfd Hsvc Hno Hg Hr Hok Hnb Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
                   (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - (* sstep_exit : write leaves the model unchanged, so it cannot halt *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed: same — an unchanged model is not killed *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
    end.
Qed.

Lemma sstep_write_inv_disjoint : forall ms model x8 buf evs st,
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hout Hfd Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  destruct st as [c'|].
  - destruct (sstep_write_next_inv_disjoint ms model x8 buf evs c'
                Hh Hout Hfd Hsvc Hno Hg Hr Hok Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
    exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
  - (* SError: the write is modeled, and its one access is disjoint,
       so neither error transition applies *)
    exfalso. inversion Hss; subst; try congruence.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
        Hmat : materialize_model_accesses ?model' _ = None |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
                    Hfd Hno Hg Hr Hok Hnb H3)
          as (n & _ & Hn2 & Heff & Hm & _);
        subst eff model';
        rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
                   (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
        discriminate
      end.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
      end.
Qed.

Lemma node_write1_disjoint : forall ms model x8 buf,
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok segs (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb. split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + apply materialize_syscall_effect_copyin_disjoint.
      exact (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout).
  - intros e st Hss.
    destruct (sstep_write_inv_disjoint ms model x8 buf e st
                Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma srz_write1_disjoint : forall ms model x8 buf T,
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes segs (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes segs (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node segs (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1_disjoint ms model x8 buf); assumption.
  - apply (write1_rob segs ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
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

(** The chained node: a disjoint straight line is silent and preserves
    the model exactly, whatever the ledger holds. *)
Lemma srz_msteps_disjoint : forall ms ms' model accs T,
  m_halted model = None ->
  msteps_acc ms ms' accs ->
  accesses_outside_lazy accs (m_vm_lazy model) ->
  srealizes segs (mkCfg ms' model) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms ms' model accs T Hh Hms; revert T;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros T Hout Hc; [exact Hc|].
  eapply srz_step_disjoint;
    [ exact Hh | exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
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

(* ================================================================= *)
(* Worked example: the FULL ASan-init shape in miniature.             *)
(*                                                                    *)
(* A NORESERVE shadow reservation (every refusal spins; a grant       *)
(* leaves a NON-EMPTY lazy ledger), a disjoint straight line to a     *)
(* plain rw mmap (every refusal spins — THROUGH the non-empty ledger; *)
(* every grant continues), a disjoint line to a write(1) of a         *)
(* ledger-disjoint buffer, a disjoint line to an exit.  The           *)
(* conclusion is the standard obs_iff / no_error pair, and the proof  *)
(* is node applications and leaves only: this is the skeleton an      *)
(* proof instantiates on the real binary (the hypotheses below are    *)
(* exactly what its symbolic execution produces — [stepacc_*] chains  *)
(* for the walks, [prove_to_spin]/[ts_*] for the refusal arms,        *)
(* register/decode facts for the ecall shapes).                       *)
(* ================================================================= *)

Section AsanInitReal.
Variable segs : list Segment.

(** The reservation ecall configuration. *)
Variables (ms1 : machine_state) (model : Model) (x8a : word).
Hypothesis Hh : m_halted model = None.
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc1 : ms_svc_pending ms1 = Some x8a.
Hypothesis Hno1 : bv_unsigned x8a = 222%Z.
Hypothesis Hargs1 : mmap_args_ok_noreserve ms1.
Hypothesis Hdecl1 :
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms1 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms1 1))) = false.

Let nZ1 : Z := page_round_up_Z (bv_unsigned (ms_gpr ms1 1)).
Let n1 : word := page_round_up (ms_gpr ms1 1).
Let model1 (a1 : word) : Model := mmap_model_noreserve a1 n1 model.
Let post1 (a1 : word) : machine_state :=
  advance_past_svc (apply_effect ms1 (mkEffect a1 [] [(a1, n1)])).

(** Refusal arm of the reservation: the ledger is still empty here, so
    a per-binary proof feeds this from the no-lazy spellings
    as-is. *)
Hypothesis Hrefuse1 : forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 ms1 (errno_ret e))) model.
Hypothesis Hex1 : exists a, grant_ok_nr (ms_gpr ms1 0) model a nZ1 = true.

(** Post-grant straight line to the rw mmap ecall — the ledger is
    non-empty now ([lazy_interior a1 n1 ++ []]), so the walk carries
    its access report and shows it disjoint. *)
Variable ms2 : word -> machine_state.
Variable accs1 : word -> list (word * nat).
Hypothesis Hwalk1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  msteps_acc segs (post1 a1) (ms2 a1) (accs1 a1).
Hypothesis Hout1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  accesses_outside_lazy (accs1 a1) (m_vm_lazy (model1 a1)).

(** The rw mmap ecall, standing on the non-empty ledger. *)
Variable x8b : word.
Hypothesis Hno2 : bv_unsigned x8b = 222%Z.
Hypothesis Hsvc2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  ms_svc_pending (ms2 a1) = Some x8b.
Hypothesis Hargs2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  mmap_args_ok (ms2 a1).
Hypothesis Hdecl2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  place_declined_b (m_kernel (model1 a1)) (m_vmmaps (model1 a1))
    (ms_gpr (ms2 a1) 0)
    (page_round_up_Z (bv_unsigned (ms_gpr (ms2 a1) 1))) = false.

Let nZ2 (a1 : word) : Z := page_round_up_Z (bv_unsigned (ms_gpr (ms2 a1) 1)).
Let n2 (a1 : word) : word := page_round_up (ms_gpr (ms2 a1) 1).
Let model2 (a1 a2 : word) : Model := mmap_model a2 (n2 a1) (model1 a1).
Let post2 (a1 a2 : word) : machine_state :=
  advance_past_svc (apply_effect (ms2 a1) (mkEffect a2 [] [(a2, n2 a1)])).

(** Refusal arm of the rw mmap: spins THROUGH the non-empty ledger
    (fed by [ts_msteps_disjoint]/[ts_spin_no_access] on the real
    binary). *)
Hypothesis Hrefuse2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 (ms2 a1) (errno_ret e))) (model1 a1).
Hypothesis Hex2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  exists a2, grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true.

(** Post-grant straight line to the write ecall. *)
Variable ms3 : word -> word -> machine_state.
Variable accs2 : word -> word -> list (word * nat).
Hypothesis Hwalk2 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  msteps_acc segs (post2 a1 a2) (ms3 a1 a2) (accs2 a1 a2).
Hypothesis Hout2 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  accesses_outside_lazy (accs2 a1 a2) (m_vm_lazy (model2 a1 a2)).

(** The write(1) ecall: the buffer is disjoint from the lazy ledger
    (on the real binary: it lives in the image's data/stack, and
    [region_free] keeps the reservation away from the image). *)
Variable buf : list byte.
Hypothesis Hbufnb : (1 <= length buf)%nat.
Hypothesis Hbufmod : buf_modeled buf.
Variable x8c : word.
Hypothesis Hno3 : bv_unsigned x8c = 64%Z.
Hypothesis Hw_svc : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_svc_pending (ms3 a1 a2) = Some x8c.
Hypothesis Hw_fd1 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_gpr (ms3 a1 a2) 0 = Z_to_bv 64 1.
Hypothesis Hw_read : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_read_bytes (ms3 a1 a2) (ms_gpr (ms3 a1 a2) 1) (ms_gpr (ms3 a1 a2) 2) = Some buf.
(** ...on a range [vfs_write]'s [access_ok] accepts, which the channel
    arm asks before it reads the source; see [CatSim.write1_check_n]. *)
Hypothesis Hw_acc : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  access_okb (ms_gpr (ms3 a1 a2) 1) (bv_unsigned (ms_gpr (ms3 a1 a2) 2)) = true.
Hypothesis Hw_out : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  accesses_outside_lazy [(ms_gpr (ms3 a1 a2) 1, length buf)]
    (m_vm_lazy (model2 a1 a2)).

(** Post-write straight line (per delivered length) to the exit ecall. *)
Variable msE : word -> word -> nat -> machine_state.
Variable accs3 : word -> word -> nat -> list (word * nat).
Hypothesis Hwalk3 : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  msteps_acc segs
    (advance_past_svc (set_gpr0 (ms3 a1 a2) (len_word (firstn n buf))))
    (msE a1 a2 n) (accs3 a1 a2 n).
Hypothesis Hout3 : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  accesses_outside_lazy (accs3 a1 a2 n) (m_vm_lazy (model2 a1 a2)).

(** The exit ecall. *)
Variables (x8d : word) (cs : word).
Hypothesis HE_no : is_exit_no x8d.
Hypothesis HE_svc : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  ms_svc_pending (msE a1 a2 n) = Some x8d.
Hypothesis HE_code : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  bv_and (ms_gpr (msE a1 a2 n) 0) (Z_to_bv 64 255) = cs.

(** The derivation: four node applications, three disjoint walks, one
    exit leaf. *)
Theorem asan_init_srealizes :
  srealizes segs (mkCfg ms1 model)
    (t_write_ch (Z_to_bv 64 1) buf (t_exit cs (m_fs model))).
Proof.
  eapply srz_mmap_spin_noreserve;
    [ exact Hh | exact Hsvc1 | exact Hno1 | exact Hargs1 | exact Hdecl1 | exact Hrefuse1 |
    | exact Hex1 ].
  intros a1 Hg1.
  eapply srz_msteps_disjoint;
    [ exact Hh | exact (Hwalk1 a1 Hg1) | exact (Hout1 a1 Hg1) | ].
  eapply srz_mmap_spin_lazy;
    [ exact Hh | exact (Hsvc2 a1 Hg1) | exact Hno2 | exact (Hargs2 a1 Hg1)
    | exact (Hdecl2 a1 Hg1) | exact (Hrefuse2 a1 Hg1) | | exact (Hex2 a1 Hg1) ].
  intros a2 Hg2.
  eapply srz_msteps_disjoint;
    [ exact Hh | exact (Hwalk2 a1 a2 Hg1 Hg2) | exact (Hout2 a1 a2 Hg1 Hg2) | ].
  eapply srz_write1_disjoint;
    [ exact Hh | exact (Hw_out a1 a2 Hg1 Hg2) | exact Hfd
    | exact (Hw_svc a1 a2 Hg1 Hg2) | exact Hno3 | exact (Hw_fd1 a1 a2 Hg1 Hg2)
    | exact (Hw_read a1 a2 Hg1 Hg2) | exact (Hw_acc a1 a2 Hg1 Hg2)
    | exact Hbufmod | exact Hbufnb | ].
  intros n Hn1 Hn2.
  eapply srz_msteps_disjoint;
    [ exact Hh | exact (Hwalk3 a1 a2 n Hg1 Hg2 Hn1 Hn2)
    | exact (Hout3 a1 a2 n Hg1 Hg2 Hn1 Hn2) | ].
  rewrite <- (HE_code a1 a2 n Hg1 Hg2 Hn1 Hn2).
  apply (srz_exit segs (msE a1 a2 n) (model2 a1 a2) x8d);
    [ exact Hh | exact (HE_svc a1 a2 n Hg1 Hg2 Hn1 Hn2) | exact HE_no ].
Qed.

(** The standard pair.  The observation set is exactly the per-delivery
    write shape followed by the exit — neither spinning refusal arm is
    visible in it. *)
Theorem asan_init_obs_iff : forall tr,
  obs_trace segs (mkCfg ms1 model) tr
  <-> (exists full, wpick (Z_to_bv 64 1) [buf] full
        /\ is_prefix tr (full ++ [ExitEv cs (m_fs model)])).
Proof.
  intro tr.
  rewrite (srealizes_obs_iff segs _ _ asan_init_srealizes tr).
  assert (Hall : Forall (fun b : list byte => (1 <= length b)%nat) [buf])
    by (constructor; [exact Hbufnb | constructor]).
  exact (t_writes_ch_pick_exit_iff (Z_to_bv 64 1) [buf] cs (m_fs model) tr Hall).
Qed.

Theorem asan_init_no_error : ~ reaches_error segs (mkCfg ms1 model).
Proof.
  exact (srealizes_no_error segs _ _ asan_init_srealizes).
Qed.

End AsanInitReal.
End WithFP2.
