(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common.AllocSim — union-of-resolutions glue for brk-allocating binaries.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Outcomes are [(list (list byte) * word)] pairs (buffers of [bv 8]
    bytes, exit code a [word = bv 64]); break values, requests and
    growth amounts are [word]s; all no-wrap bookkeeping (allocation
    ceiling, wraparound detection, interval bounds) is in [Z] over
    [bv_unsigned].  Following the CatSim conventions the brk syscall
    number is Z-characterized: the [tou_brk] node (and every brk
    decoding lemma) carries a pending number [x8] with
    [bv_unsigned x8 = 214%Z].

    A binary that allocates its output buffer with [brk] does not have a
    single deterministic trace: the environment resolves each brk call
    (Mmap.brk_spec), so the observable behavior is a UNION over
    resolutions of (write buffers, exit code) outcomes.  This file
    provides:

    - [to_outcomes segs ms model U]: from machine state [ms] and model
      [model], the reachable set of (bufs, code) outcomes is EXACTLY [U].
      Leaves are [WallSim.to_wallexit] retry loops, which re-offer what a
      short write left behind until the whole buffer is out, so a leaf
      still pins one [(bufs, code)] outcome; interior nodes are brk
      syscalls branching over every admissible resolution.
    - the trace characterization ([alloc_obs_iff]): [obs_trace] is
      exactly the prefixes of [wevents bufs ++ [ExitEv code (in_fs inp)]] for
      outcomes in [U]; plus no-error ([alloc_no_error_run]).  The retry
      loop puts the whole buffer out, so this file quantifies over
      outcomes alone — the per-delivery choices ([CatSim.wpick]) are
      already discharged inside [to_wallexit] and appear nowhere here.
    - the [Equivalence.equiv]-level glue ([alloc_strong_equiv]): two
      binaries with the SAME outcome set are observably equivalent.
    - brk-spec decoding helpers ([brk_ok_iff], [tou_brk_r]) so per-binary
      proofs work with the resolved break value [r] directly, and the
      [apply_zeros]/[zmem] memory theory for the zero-backed grant. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit Require Import SimInv ExitSim PropExec CatSim CatExec WallSim.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ========================================================================= *)
(* Local word-algebra helpers (candidates to lift into BvBase/PropExec if a  *)
(* second Common file needs them).                                           *)
(* ========================================================================= *)

(** Unsigned value of a non-wrapping [bv] sum. *)
Lemma u_add_small : forall a b : word,
  (bv_unsigned a + bv_unsigned b < 2 ^ 64)%Z ->
  bv_unsigned (a + b) = (bv_unsigned a + bv_unsigned b)%Z.
Proof.
  intros a b H. rewrite bv_add_unsigned, bv_wrap64_mod. apply Z.mod_small.
  pose proof (u64_range a). pose proof (u64_range b). lia.
Qed.

Lemma word_add_0_r : forall a : word, a + Z_to_bv 64 0 = a.
Proof.
  intro a. apply bv_eq.
  rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r, bv_wrap64_mod. apply Z.mod_small. apply u64_range.
Qed.

(** [r + t - r = t] in the additive group of [bv 64] (no side conditions). *)
Lemma word_add_sub_cancel : forall r t : word, r + t - r = t.
Proof.
  intros r t. apply bv_eq.
  rewrite bv_sub_unsigned, bv_add_unsigned, !bv_wrap64_mod.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned r + bv_unsigned t - bv_unsigned r)%Z
    with (bv_unsigned t) by lia.
  apply Z.mod_small. apply u64_range.
Qed.

Lemma word_neq0_unsigned : forall r : word,
  r <> Z_to_bv 64 0 -> (bv_unsigned r <> 0)%Z.
Proof.
  intros r Hne Hu. apply Hne. apply bv_eq. rewrite Hu. reflexivity.
Qed.

(** Address-walk step for [wbytes_app] ([nat_to_word] offset form). *)
Lemma word_add_nat_S : forall (a : word) k,
  (a + 1) + nat_to_word k = a + nat_to_word (S k).
Proof.
  intros a k. apply bv_eq. unfold nat_to_word.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite Zplus_mod_idemp_l, !Zplus_mod_idemp_r.
  f_equal. lia.
Qed.

(* ========================================================================= *)
(* apply_zeros / zmem: the zero-backed grant as a functional overlay.        *)
(* ========================================================================= *)

(** The zero-fill of a single granted range [b, b+l).  Coverage is checked
    in [Z] over unsigned values, mirroring [Run.zeros_cover] (grant ranges
    never wrap). *)
Definition zmem (mem : word -> option byte) (b l : word) : word -> option byte :=
  fun a => if Z.leb (bv_unsigned b) (bv_unsigned a)
              && Z.ltb (bv_unsigned a) (bv_unsigned b + bv_unsigned l)
           then Some (Z_to_bv 8 0) else mem a.

Lemma apply_zeros_nil : forall mem, apply_zeros mem [] = mem.
Proof. reflexivity. Qed.

Lemma apply_zeros_one : forall mem b l,
  apply_zeros mem [(b, l)] = zmem mem b l.
Proof.
  intros mem b l. apply functional_extensionality. intro a.
  unfold apply_zeros, zeros_cover, zmem. cbn [existsb fst snd].
  rewrite orb_false_r. reflexivity.
Qed.

Lemma zmem_out : forall mem b l a,
  (bv_unsigned a < bv_unsigned b \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  zmem mem b l a = mem a.
Proof.
  intros mem b l a Hd. unfold zmem.
  destruct Hd as [Hd | Hd].
  - assert (E : (bv_unsigned b <=? bv_unsigned a)%Z = false) by (apply Z.leb_gt; lia).
    rewrite E. reflexivity.
  - assert (E : (bv_unsigned a <? bv_unsigned b + bv_unsigned l)%Z = false)
      by (apply Z.ltb_ge; lia).
    rewrite E, andb_false_r. reflexivity.
Qed.

(** No-overflow hypothesis (inherited from [rdn_ext]); trivial at
    call sites — the read window sits far below 2^64. *)
Lemma rdn_zmem_out : forall segs mem b l (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  rdn segs (zmem mem b l) a n = rdn segs mem a n.
Proof.
  intros segs mem b l a n Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply zmem_out. lia.
Qed.

Lemma rdn_zmem_in1 : forall segs mem b l (a : word),
  (bv_unsigned b <= bv_unsigned a < bv_unsigned b + bv_unsigned l)%Z ->
  rdn segs (zmem mem b l) a 1 = Some [Z_to_bv 8 0].
Proof.
  intros segs mem b l a [Hlo Hhi]. cbn [rdn]. unfold zmem.
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  reflexivity.
Qed.

(** wbytes over a split list — lets a store loop accumulate one flat
    [wbytes] over the granted region. *)
Lemma wbytes_app : forall {bs1 bs2 : list byte} m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word (length bs1)) bs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 m a.
  - cbn [app wbytes length].
    replace (a + nat_to_word 0) with a; [reflexivity|].
    symmetry. exact (word_add_0_r a).
  - cbn [app wbytes length].
    rewrite IH, word_add_nat_S. reflexivity.
Qed.

(* ========================================================================= *)
(* Model plumbing for a brk transition.                                      *)
(* ========================================================================= *)

Lemma with_vmmaps_fds : forall h m, m_fds (with_vmmaps h m) = m_fds m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_fs : forall h m, m_fs (with_vmmaps h m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_halted : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_vm : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.
Lemma with_vmmaps_lazy : forall h m,
  m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma fd1chan_with_vmmaps : forall h m, fd1chan m -> fd1chan (with_vmmaps h m).
Proof. intros h m H. unfold fd1chan in *. exact H. Qed.

(** VM lifecycle cleanup rewrites only the sparse-backing ledgers, so it
    carries the fd table across unchanged. *)
Lemma fd1chan_forget_vm_ranges : forall ranges m,
  fd1chan m -> fd1chan (forget_vm_ranges ranges m).
Proof.
  induction ranges as [|[a n] ranges IH]; intros m H; cbn [forget_vm_ranges].
  - exact H.
  - apply IH. unfold fd1chan, vm_forget_range, with_vm_backing in *.
    cbn [m_fds m_fd] in *. exact H.
Qed.

(** advance-past-svc of a brk effect applied at the raw ecall record. *)
Lemma adv_brk : forall regs pc x8 mem rom r zs,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} (mkEffect r [] zs))
  = mkst (regupd regs 10 r) (v_addi pc 4) (apply_zeros mem zs) rom.
Proof.
  intros regs pc x8 mem rom r zs.
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* ========================================================================= *)
(* brk syscall-spec decoding, through the verified checker.                  *)
(* ========================================================================= *)

Lemma in_sysno_sys_input214 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Lemma in_arg0_sys_input214 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(** Which arm answers this number, on the SPEC side.  [syscall_spec] is
    [dispatch spec_table], so fixing the number settles the table lookup by
    conversion and the dispatcher disappears -- the same one-line argument
    [Checks.Sys.DispatchCompute] makes for [check_syscall], made here
    instead so that this file needs only the brk checker rather than the
    module that re-exports every arm's. *)
Lemma syscall_spec_brk : forall segs ms x8 model o,
  bv_unsigned x8 = 214%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input214, Hno. reflexivity.
Qed.

(** The allocator examples have no lazy mappings or materialized sparse
    pages.  Package a VM ledger with that empty backing state for the pure
    outcome algebra below. *)
Definition vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] None None None.

Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
  Mmap.brk_grow_ok (vm_model h) req r.

(** The admissibility condition used by the pure allocator outcome algebra. *)
Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  Mmap.brk_r_ok (vm_model h) req r = true.

(** The corresponding condition at a live syscall state, whose backing
    ledger is part of the decision. *)
Definition brk_resolution_ok (m : Model) (req r : word) : Prop :=
  Mmap.brk_r_ok m req r = true.

(** The model after adopting resolution [r]. *)
Definition brk_model (req r : word) (m : Model) : Model :=
  with_brk_next m req r.

(** ... and so [brk] as a whole does: it retags the break, rewrites the
    VM ledger and forgets the backing of what it unmapped.  Stated at
    [brk_model] rather than at its [with_vmmaps] core so that a proof
    stepping over a brk node does not have to know how [with_brk_next] is
    layered. *)
Lemma fd1chan_brk_model : forall req r m,
  fd1chan m -> fd1chan (brk_model req r m).
Proof.
  intros req r m H. unfold brk_model, with_brk_next. cbv zeta.
  apply fd1chan_forget_vm_ranges, fd1chan_with_vmmaps, H.
Qed.

Lemma check_brk_ok_inv : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  eff = mkEffectU (eff_ret eff) []
          (brk_zeros req (eff_ret eff) (vm_brk (m_vmmaps m)))
          (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps m))) [] []
  /\ evs = []
  /\ brk_resolution_ok m req (eff_ret eff)
  /\ m' = brk_model req (eff_ret eff) m.
Proof.
  intros req [r ws zs us cs copyins] m m' evs H.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (Mmap.brk_r_ok m req r) eqn:HR; [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))) eqn:HZ;
    [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))) eqn:HU;
    [|cbn [andb] in H; discriminate].
  cbn [andb] in H.
  apply listNN_eqb_eq in HZ. subst zs.
  apply listNN_eqb_eq in HU. subst us.
  inversion H; clear H; subst.
  cbn [eff_ret]. unfold brk_resolution_ok, brk_model.
  repeat split; try reflexivity. exact HR.
Qed.

Lemma check_brk_ok_intro : forall req r m,
  brk_resolution_ok m req r ->
  check_brk req (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
                              (brk_unmaps r (vm_brk (m_vmmaps m))) [] []) m
  = CheckOk (brk_model req r m) [].
Proof.
  intros req r m HR. unfold brk_resolution_ok in HR.
  unfold check_brk. rewrite HR.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  unfold brk_model. reflexivity.
Qed.

(** Admissible outcomes of a brk syscall, in terms of the resolved [r]. *)
Lemma brk_ok_iff : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 214%Z ->
  (syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) <->
   (eff = mkEffectU (eff_ret eff) []
            (brk_zeros (ms_gpr ms 0) (eff_ret eff) (vm_brk (m_vmmaps model)))
            (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model))) [] []
    /\ evs = []
    /\ brk_resolution_ok model (ms_gpr ms 0) (eff_ret eff)
    /\ model' = brk_model (ms_gpr ms 0) (eff_ret eff) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno. split.
  - intro H. apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
    apply check_brk_complete_ok in H.
    apply check_brk_ok_inv in H. exact H.
  - intros (Heff & -> & Hok & ->).
    apply (proj2 (syscall_spec_brk _ _ _ _ _ Hno)). apply check_brk_sound_ok.
    rewrite Heff at 1. cbn [eff_ret].
    apply check_brk_ok_intro. exact Hok.
Qed.

Lemma brk_ok_intro : forall segs ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  brk_resolution_ok model (ms_gpr ms 0) r ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                        (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
        (brk_model (ms_gpr ms 0) r model) []).
Proof.
  intros segs ms x8 model r Hno Hok.
  apply (brk_ok_iff segs ms x8 model _ _ _ Hno). cbn [eff_ret]. auto.
Qed.

(** brk never takes the error transition. *)
Lemma brk_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 214%Z ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno H.
  apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
  apply (check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in H.
  unfold check_brk in H.
  destruct (Mmap.brk_r_ok model (ms_gpr ms 0) (Z_to_bv 64 0)
            && listNN_eqb []
                 (brk_zeros (ms_gpr ms 0) (Z_to_bv 64 0) (vm_brk (m_vmmaps model)))
            && listNN_eqb []
                 (brk_unmaps (Z_to_bv 64 0) (vm_brk (m_vmmaps model))));
    discriminate.
Qed.

(** brk is receptive: some resolution is always admissible.
    KEEPING the current break ([r = vm_brk h]) is admitted by every path
    (query/invalid returns it; shrink and grow both have the failure
    branch that keeps it). *)
Lemma brk_receptive : forall segs ms x8 model,
  bv_unsigned x8 = 214%Z ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []).
Proof.
  intros segs ms x8 model Hno.
  pose (r := vm_brk (m_vmmaps model)).
  exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                        (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
         (brk_model (ms_gpr ms 0) r model).
  apply brk_ok_intro; [exact Hno|].
  unfold brk_resolution_ok, Mmap.brk_r_ok, r. cbv zeta.
  destruct (w_is0 (ms_gpr ms 0)
            || Z.ltb (bv_unsigned (ms_gpr ms 0))
                     (bv_unsigned (min_brk (m_vmmaps model)))).
  - apply bv_eqb_refl.
  - destruct (Z.ltb (bv_unsigned (ms_gpr ms 0))
                    (bv_unsigned (vm_brk (m_vmmaps model)))).
    + rewrite bv_eqb_refl, orb_true_r. reflexivity.
    + rewrite bv_eqb_refl, orb_true_r, andb_true_l.
      unfold brk_grow_ok, Mmap.brk_grow_ok.
      now rewrite Z.ltb_irrefl, andb_false_r.
Qed.

(** brk grow of req<>0 from an established nonzero break to r > old:
    the visible zero-fill is exactly the shared page-rounded range helper. *)
Lemma brk_zeros_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_zeros req r old =
    brk_page_range (page_round_up_Z (bv_unsigned old))
                   (page_round_up_Z (bv_unsigned r)).
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_zeros, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

(** The ledger records the SAME page-rounded range the zero-fill names:
    [Mmap.brk_grants] and [Mmap.brk_zeros] are one term, so a grow adds
    exactly the pages it installs and a grow inside one page adds
    nothing. *)
Lemma brk_grants_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_grants req r old =
    brk_page_range (page_round_up_Z (bv_unsigned old))
                   (page_round_up_Z (bv_unsigned r)).
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_grants, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

(** …and that is the same term as the zero-fill, with no hypotheses. *)
Lemma brk_grants_is_brk_zeros : forall req r old,
  brk_grants req r old = brk_zeros req r old.
Proof. reflexivity. Qed.

Lemma brk_zeros_query : forall r old, brk_zeros (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_zeros, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma brk_grants_query : forall r old, brk_grants (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_grants, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma brk_zeros_keep : forall req old, brk_zeros req old old = [].
Proof.
  intros req old. unfold brk_zeros, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

Lemma brk_grants_keep : forall req old, brk_grants req old old = [].
Proof.
  intros req old. unfold brk_grants, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

(** brk KEEPS the break: nothing is freed. *)
Lemma brk_unmaps_keep : forall old, brk_unmaps old old = [].
Proof.
  intros old. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
  unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.

(** The QUERY resolution frees nothing — the same [r = vm_brk h] premise
    [brk_model_query] takes, so a query node discharges both from it. *)
Lemma brk_unmaps_query : forall h r,
  r = vm_brk h -> brk_unmaps r (vm_brk h) = [].
Proof. intros h r ->. apply brk_unmaps_keep. Qed.

(** Any resolution that does not LOWER the break frees nothing: page
    rounding is monotone, so the freed interval is empty.  This covers
    the query/invalid path ([r = old]) and both grow resolutions. *)
Lemma brk_unmaps_grow : forall r old,
  (bv_unsigned old <= bv_unsigned r)%Z -> brk_unmaps r old = [].
Proof.
  intros r old H. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E0; [|reflexivity].
  assert (E : (page_round_up_Z (bv_unsigned r)
               <? page_round_up_Z (bv_unsigned old))%Z = false)
    by (apply Z.ltb_ge, page_round_up_Z_mono, H).
  unfold brk_page_range. rewrite E. reflexivity.
Qed.

(** Unfolding [brk_grow_ok] on an actual grow. *)
Lemma brk_grow_ok_grow : forall h req r,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
  brk_grow_ok h req r
  = ((if (page_round_up_Z (bv_unsigned (vm_brk h))
          <? page_round_up_Z (bv_unsigned r))%Z
      then (page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
           && region_free (vm_reserved h ++ vm_maps h)
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (vm_brk h))))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                             - page_round_up_Z (bv_unsigned (vm_brk h))))
      else true)
     && (vm_backed_bytes h + brk_grow_bytes h r <=? vm_limit h)%Z)%bool.
Proof.
  intros h req r Hreq H0 Hlt.
  assert (Hmaps : m_vmmaps (vm_model h) = h) by reflexivity.
  assert (Hbacked : vm_backing_used (vm_model h) = vm_backed_bytes h).
  { unfold vm_backing_used, vm_model.
    cbv [mkModel m_vmmaps m_vm m_vm_lazy m_vm_materialized
         vmst_lazy vmst_materialized].
    change ((live_bytes (vm_backed_maps h) + 0)%Z =
            live_bytes (vm_backed_maps h)).
    apply Z.add_0_r. }
  unfold brk_grow_ok, Mmap.brk_grow_ok, Mmap.brk_budget_ok.
  rewrite Hmaps, Hbacked.
  assert (E2 : (0 <? bv_unsigned (vm_brk h))%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned (vm_brk h) <? bv_unsigned r)%Z = true)
    by (apply Z.ltb_lt; lia).
  rewrite E2, E3. reflexivity.
Qed.

Lemma brk_grow_ok_keep : forall h req,
  brk_grow_ok h req (vm_brk h) = true.
Proof.
  intros h req. unfold brk_grow_ok, Mmap.brk_grow_ok.
  cbv [vm_model mkModel m_vmmaps m_vm vm_backing_used m_vm_lazy
       m_vm_materialized vmst_lazy vmst_materialized].
  cbn [vmst_maps vm_backed_bytes maps_subtract_all].
  rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(** Elementary page-rounding facts used by the allocator examples. *)
Lemma page_round_up_Z_aligned : forall z,
  (0 <= z)%Z -> (z mod page_size = 0)%Z -> page_round_up_Z z = z.
Proof.
  intros z Hz Hmod. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdiv.
  replace (z + 4096 - 1)%Z with
    (4095 + (z / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

Lemma page_round_up_Z_bounds : forall z,
  (0 <= z)%Z ->
  (z <= page_round_up_Z z <= z + page_size - 1)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hmod.
  lia.
Qed.

(** Eight-byte chunk rounding is contained in page rounding. *)
Lemma round8_le_page_round : forall z,
  (0 <= z)%Z ->
  ((((z + 7) / 8) * 8) <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z.
  pose proof (Z.div_mod (z + 7) 8 ltac:(lia)) as H8.
  pose proof (Z.mod_pos_bound (z + 7) 8 ltac:(lia)) as H8mod.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hp.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hpmod.
  assert (H8ceil :
    (z <= ((z + 7) / 8) * 8 <= z + 7)%Z) by lia.
  assert (Hpceil :
    (z <= ((z + 4096 - 1) / 4096) * 4096)%Z) by lia.
  set (q8 := ((z + 7) / 8)%Z) in *.
  set (qp := ((z + 4096 - 1) / 4096)%Z) in *.
  assert (Hq : (q8 <= 512 * qp)%Z) by lia.
  change (q8 * 8 <= qp * 4096)%Z.
  lia.
Qed.

Lemma round8_le_page_grant : forall old n,
  (0 <= old)%Z -> (0 <= n)%Z ->
  (old mod page_size = 0)%Z ->
  ((((n + 7) / 8) * 8) <= page_round_up_Z (old + n) - old)%Z.
Proof.
  intros old n Hold Hn Hmod.
  unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod old 4096 ltac:(lia)) as Holddiv.
  replace (old + n + 4096 - 1)%Z with
    ((n + 4096 - 1) + (old / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  pose proof (round8_le_page_round n Hn).
  unfold page_round_up_Z in *. lia.
Qed.

(** A prefix of a free interval with the same base is free. *)
Lemma region_free_prefix : forall maps b small big,
  (bv_unsigned small <= bv_unsigned big)%Z ->
  region_free maps b big = true -> region_free maps b small = true.
Proof.
  induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree;
    [reflexivity|].
  cbn [region_free] in Hfree |- *.
  apply andb_true_iff in Hfree as [Hhead Htail].
  apply andb_true_iff. split; [|eapply IH; eassumption].
  apply negb_true_iff in Hhead. apply negb_true_iff.
  unfold iv_overlap in Hhead |- *.
  apply andb_false_iff in Hhead. apply andb_false_iff.
  destruct Hhead as [Hhead|Hhead]; [left|right];
    apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.

(** On a page-aligned established break, every genuine grow crosses into a
    nonempty physical page interval.  This is the convenient proof-facing
    spelling of [brk_grow_ok]: physical ceiling/disjointness, logical budget. *)
Lemma brk_grow_ok_aligned_grow : forall h req r,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
  (bv_unsigned (vm_brk h) mod page_size = 0)%Z ->
  brk_grow_ok h req r
  = (((page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
      && region_free (vm_reserved h ++ vm_maps h) (vm_brk h)
           (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                        - bv_unsigned (vm_brk h))))
     && (vm_backed_bytes h + brk_grow_bytes h r <=? vm_limit h)%Z)%bool.
Proof.
  intros h req r Hreq Hpos Hlt Halign.
  rewrite brk_grow_ok_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk h))) by lia.
  assert (Hround : (bv_unsigned (vm_brk h)
                    < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  replace (Z_to_bv 64 (bv_unsigned (vm_brk h))) with (vm_brk h).
  - reflexivity.
  - symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma brk_zeros_aligned_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  (bv_unsigned old mod page_size = 0)%Z ->
  brk_zeros req r old =
    [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - bv_unsigned old))].
Proof.
  intros req r old Hreq Hpos Hlt Halign.
  rewrite brk_zeros_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned old)) by lia.
  unfold brk_page_range.
  assert (Hround : (bv_unsigned old < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(** Everything a caller needs about the page-rounded grant a successful grow
    from [r] to [r + w] hands back, given only the two facts the brk spec
    leaves on the table: that the new break fits under the run's grant top,
    and that the granted pages and the one page above them are free (the
    range [Mmap.brk_grow_ok] tests).  [g] is the grant the caller has
    already named; the results say it holds the requested [w] bytes, that both
    the grant and the request stay under the ceiling, and that the requested
    prefix and the grant itself are free — the two prefixes of the gate's
    range a run lemma asks for.

    [top] exists because each caller spells the new break differently (a word
    sum, or a nat length plus one).  Passing the caller's own spelling through
    means the ceiling bound comes back already in the form the caller's
    success lemma asks for, with no rewrite in between.

    [ceil] is the run's [State.alloc_top], passed in with its own
    bound ([State.alloc_top_page_lt]: a page above it is still below
    2^64, which is what the gate's one-page lookahead needs) so this
    file need not know which ledger it came from. *)
Lemma brk_aligned_grant_ok :
  forall (res : list (word * word)) (r w g : word) (top ceil : Z),
  bv_unsigned (r + w) = (bv_unsigned r + bv_unsigned w)%Z ->
  bv_unsigned (r + w) = top ->
  g = Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r) ->
  (ceil + page_size < 2 ^ 64)%Z ->
  (page_round_up_Z (bv_unsigned (r + w)) <= ceil)%Z ->
  region_free res r
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                 - bv_unsigned r)) = true ->
     bv_unsigned g = (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z
  /\ (bv_unsigned w <= bv_unsigned g)%Z
  /\ (bv_unsigned r + bv_unsigned g <= ceil)%Z
  /\ (top <= ceil)%Z
  /\ region_free res r w = true
  /\ region_free res r g = true.
Proof.
  intros res r w g top ceil Hnowrap Htop Hg Hacp Hceil Hfree.
  pose proof (u64_range r). pose proof (u64_range w).
  pose proof (page_round_up_Z_bounds (bv_unsigned (r + w))
                (proj1 (u64_range (r + w)))).
  assert (Hps : (0 < page_size)%Z) by (vm_compute; reflexivity).
  (* [StepTac.u_Z2bv] is downstream of this file, so reprove it here. *)
  assert (Hu : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
                 bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. apply Z.mod_small.
    split; [exact Hlo | exact Hhi]. }
  assert (HgU : bv_unsigned g
                = (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z)
    by (subst g; apply Hu; lia).
  repeat split; rewrite ?HgU; try lia.
  (* the gate tests one page more than the grant, so both the request and
     the grant are prefixes of the range [Hfree] covers *)
  - apply (region_free_prefix res r w
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite Hu by lia; lia | exact Hfree].
  - apply (region_free_prefix res r g
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite HgU, Hu by lia; lia | exact Hfree].
Qed.

(* ========================================================================= *)
(* Two-node brk resolution-set algebra: a binary that queries the break      *)
(* (req = 0), then grows it by [t] bytes (req = brk + t), taking the         *)
(* failure exit ([([], 4)]) on either an unusable query resolution or a      *)
(* refused/wrapping grow, and the success buffers [bufs] otherwise.  This    *)
(* is the shared shape behind brk_rev_ns/alloc_join_ns/oob_read_bug_ns:      *)
(* only the growth amount [t] and success buffers [bufs] differ per binary   *)
(* (all three write [(list (list byte) * word)] outcomes, so no further      *)
(* type parameter is needed).  [t = 0] is handled explicitly                 *)
(* ([oob_read_bug_ns]'s n = 0 case: re-requesting the current break can      *)
(* never fail) so every binary can use this algebra whether or not its       *)
(* growth amount is provably positive.                                       *)
(*                                                                           *)
(* [t] is a [word]; the "wrap" arm of [T1] and the no-wrap bound of          *)
(* [growable] are stated in [Z] over [bv_unsigned r + bv_unsigned t].        *)
(* ========================================================================= *)

(** Can the break grow from [r] by [t] bytes, against reservation list
    [reserved], grant top [top] (the run's [State.alloc_top]) and
    allocation budget [lim] ([State.vm_limit] of a fresh ledger: no live
    grants yet, so the [t] added bytes must fit the whole budget)?  The
    free region is the installed pages plus the one above them, as in
    [Mmap.brk_grow_ok].  [t = 0] (re-requesting the current break) is
    trivially growable regardless of the top/free-region/budget check. *)
Definition growable (reserved : list (word * word)) (lim top : Z) (t r : word)
    : Prop :=
  r <> Z_to_bv 64 0 /\ (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z /\
  (t = Z_to_bv 64 0 \/
   (((if (page_round_up_Z (bv_unsigned r)
          <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
      then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            <=? top)%Z
           && region_free reserved
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                (Z_to_bv 64 (page_round_up_Z
                               (bv_unsigned r + bv_unsigned t)
                              + page_size - page_round_up_Z (bv_unsigned r)))
      else true)
     && (Z.max 0 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                  - page_round_up_Z (bv_unsigned r)) <=? lim)%Z)%bool = true)).

(** Branch outcome set after the FIRST brk resolved to [r].  The exit-4
    element is present iff a failing continuation exists: [r = 0],
    address wraparound, or ([t <> 0] and the kernel may keep the old
    break at the second brk). *)
Definition T1 (reserved : list (word * word)) (lim top : Z) (t : word)
    (bufs : list (list byte))
    (r : word) : (list (list byte) * word) -> Prop :=
  fun o => (o = ([], Z_to_bv 64 4)
            /\ (r = Z_to_bv 64 0
                \/ (2 ^ 64 <= bv_unsigned r + bv_unsigned t)%Z
                \/ t <> Z_to_bv 64 0))
        \/ (growable reserved lim top t r /\ o = (bufs, Z_to_bv 64 0)).

(** Branch outcome set after the SECOND brk resolved to [r2]. *)
Definition T2 (want : word) (bufs : list (list byte)) (r2 : word)
    : (list (list byte) * word) -> Prop :=
  fun o => (r2 = want /\ o = (bufs, Z_to_bv 64 0))
        \/ (r2 <> want /\ o = ([], Z_to_bv 64 4)).

(** [brk_r_ok] at the FIRST query (req = 0) on an UNESTABLISHED break
    with [brk(0)] (musl/glibc [sbrk(0)]) — which is DETERMINISTIC: the
    kernel reports the break, established at [execve] (the quantified
    ASLR base [Run.mi_init_brk]). *)
Lemma brk_r_ok_query_iff : forall h r,
  brk_r_ok h (Z_to_bv 64 0) r <-> r = vm_brk h.
Proof.
  intros h r. unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  unfold w_is0. rewrite bv_eqb_refl. cbn [orb].
  apply bv_eqb_eq.
Qed.

(** [reserved_top] bounds every reservation from above — the shape the
    ASLR-base bound [Run.valid_brk] hands a [region_free_above]-style
    argument. *)
Lemma reserved_top_above : forall reserved (r : Z),
  (reserved_top reserved <= r)%Z ->
  Forall (fun p : word * word =>
            (bv_unsigned (fst p) + bv_unsigned (snd p) <= r)%Z) reserved.
Proof.
  induction reserved as [|[a sz] l IH]; intros r Hr; cbn [reserved_top] in *.
  - constructor.
  - constructor; [cbn [fst snd]; lia | apply IH; lia].
Qed.

(** A region at or above the image top is free of every reservation. *)
Lemma region_free_above_top : forall reserved (lo n : word),
  (reserved_top reserved <= bv_unsigned lo)%Z ->
  region_free reserved lo n = true.
Proof.
  induction reserved as [|[a sz] l IH]; intros lo n Hr;
    cbn [reserved_top] in *; [reflexivity|].
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. lia.
Qed.

(** A region entirely above every reservation is free. *)
Lemma region_free_above : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned (fst p) + bv_unsigned (snd p)
                    <= bv_unsigned lo)%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.

(** A region entirely below every reservation is free. *)
Lemma region_free_below : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned lo + bv_unsigned n
                    <= bv_unsigned (fst p))%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned a <? bv_unsigned lo + bv_unsigned n)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E, andb_false_r. cbn [negb andb]. apply IH. exact Hl.
Qed.

(** The ceiling and free-region test of [growable]'s second disjunct,
    beside a budget test on the RAW growth [t <= lim], for the shape every
    example grow site has: a page-aligned established break [r] sitting
    above every reservation, grown by a positive [t] that fits under both
    the physical ceiling and the budget.  The budget conjunct here is not
    [growable]'s: [growable] tests the page-rounded growth
    [Z.max 0 (page_round_up_Z (r + t) - page_round_up_Z r) <= lim], so
    this lemma does not discharge [growable]; [growable_aligned_grow_rounded]
    below does.  On a page-aligned [r] the rounded interval starts at [r]
    itself, so the whole free-region check reduces to
    [region_free_above_top].  All five hypotheses are what a grow site
    already holds — alignment and the reservation-top bound from its
    initial-state facts, the rest from its own arithmetic on [t].  The
    ceiling bound is stated on [r + t + page_size - 1], the largest value
    the rounding can reach, so a site never has to reason about
    [page_round_up_Z] itself. *)
Lemma growable_aligned_grow : forall reserved lim top (t r : word),
  (bv_unsigned r mod page_size = 0)%Z ->
  (reserved_top reserved <= bv_unsigned r)%Z ->
  (0 < bv_unsigned t)%Z ->
  (bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
  (bv_unsigned t <= lim)%Z ->
  ((if (page_round_up_Z (bv_unsigned r)
        <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
    then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
          <=? top)%Z
         && region_free reserved
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
              (Z_to_bv 64 (page_round_up_Z
                             (bv_unsigned r + bv_unsigned t)
                            + page_size - page_round_up_Z (bv_unsigned r)))
    else true)
   && (bv_unsigned t <=? lim)%Z)%bool = true.
Proof.
  intros reserved lim top t r Halign Htop Hpos Hceil Hlim.
  pose proof (proj1 (u64_range r)) as Hr0.
  rewrite (page_round_up_Z_aligned (bv_unsigned r)); [|lia|exact Halign].
  assert (Hru := page_round_up_Z_bounds
    (bv_unsigned r + bv_unsigned t) ltac:(lia)).
  assert (Hltpage :
    (bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z)
    by lia.
  rewrite (proj2 (Z.ltb_lt _ _) Hltpage).
  apply andb_true_iff. split; [apply andb_true_iff; split|].
  - apply Z.leb_le. lia.
  - rewrite Z_to_bv_bv_unsigned. apply region_free_above_top. exact Htop.
  - apply Z.leb_le. exact Hlim.
Qed.

(** The page-rounded disjunct of [growable], exactly as [growable] states
    it, for the same grow-site shape as [growable_aligned_grow]: the
    budget hypothesis is [growable]'s own page-rounded test. *)
Lemma growable_aligned_grow_rounded : forall reserved lim top (t r : word),
  (bv_unsigned r mod page_size = 0)%Z ->
  (reserved_top reserved <= bv_unsigned r)%Z ->
  (0 < bv_unsigned t)%Z ->
  (bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
  (Z.max 0 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            - page_round_up_Z (bv_unsigned r)) <= lim)%Z ->
  ((if (page_round_up_Z (bv_unsigned r)
        <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
    then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
          <=? top)%Z
         && region_free reserved
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
              (Z_to_bv 64 (page_round_up_Z
                             (bv_unsigned r + bv_unsigned t)
                            + page_size - page_round_up_Z (bv_unsigned r)))
    else true)
   && (Z.max 0 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                - page_round_up_Z (bv_unsigned r)) <=? lim)%Z)%bool = true.
Proof.
  intros reserved lim top t r Halign Htop Hpos Hceil Hlim.
  apply andb_true_iff. split.
  - pose proof (growable_aligned_grow reserved
                  (bv_unsigned t) top t r Halign Htop Hpos Hceil
                  (Z.le_refl _)) as Hg.
    apply andb_true_iff in Hg as [Hg _]. exact Hg.
  - apply Z.leb_le. exact Hlim.
Qed.

Lemma brk_aslr_max_val : brk_aslr_max = 1073741824%Z.
Proof. reflexivity. Qed.

(** The model after a brk(0) QUERY is unchanged modulo re-tagging the
    break: the resolution is the current break, nothing is granted or
    freed.  (Normalizes the stuck [brk_maps_next] guard once the
    resolution is known to BE the break.) *)
Lemma brk_model_next_query : forall h r,
  r = vm_brk h ->
  brk_model_next h (Z_to_bv 64 0) r
  = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h)
      (vm_start_brk h) r (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros h r ->. unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r.
  rewrite brk_grants_query, brk_unmaps_keep. reflexivity.
Qed.

Lemma brk_model_query : forall r m,
  r = vm_brk (m_vmmaps m) ->
  brk_model (Z_to_bv 64 0) r m
  = with_vmmaps
      (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
        (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) r
        (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
        (vm_init_sp (m_vmmaps m))) m.
Proof.
  intros r m ->. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  rewrite brk_model_next_query by reflexivity. reflexivity.
Qed.

(** The GROW-node decode: on an established break [r] with heap base
    ([vm_start_brk]) [s], [brk(req)] with [req >= s] (not below Linux's
    [min_brk] = [start_brk]), [req >= r], and [req > 0] resolves to [req]
    (grow) or [r] (kept), gated by [brk_grow_ok] — the query/invalid and
    shrink guards are all excluded. *)
Lemma brk_r_ok_grow_iff : forall reserved lim s r maps noaccess mb sp req r2,
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned s <= bv_unsigned req)%Z ->
  (bv_unsigned r <= bv_unsigned req)%Z ->
  (brk_r_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 <->
   (r2 = req \/ r2 = r)
   /\ brk_grow_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 = true).
Proof.
  intros reserved lim s r maps noaccess mb sp req r2 Hpos Hs Hreq.
  unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    apply Z.eqb_neq. lia. }
  rewrite E0.
  assert (Hmin : (bv_unsigned req <?
                   bv_unsigned (min_brk (mkVmMapsFull reserved maps noaccess s r lim mb sp)))%Z
                 = false).
  { apply Z.ltb_ge. unfold min_brk. cbn [vm_start_brk]. lia. }
  cbn [vmst_maps]. rewrite Hmin. cbn [orb vm_brk].
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned r)) ltac:(lia)).
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. tauto.
Qed.

(** The ledger is spelled with a free [sp] (and a base nothing reads)
    because [brk_grow_ok] compares against [State.alloc_top] of the
    ledger it is handed: the [top] the set algebra was stated at has to
    be THAT ledger's, [bv_unsigned sp - stack_max_size]. *)
Lemma T1_iff_T2 : forall reserved lim s (mb sp : word) t bufs r,
  r <> Z_to_bv 64 0 -> (bv_unsigned s <= bv_unsigned r)%Z ->
  (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z ->
  forall o, T1 reserved lim (bv_unsigned sp - stack_max_size) t bufs r o <->
    (exists r2, brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
                /\ T2 (r + t) bufs r2 o).
Proof.
  intros reserved lim s mb sp t bufs r Hr0 Hs Hnw o.
  pose proof (u64_range r) as Hur. pose proof (u64_range t) as Hut.
  pose proof (word_neq0_unsigned r Hr0) as Hur0.
  assert (Huadd : bv_unsigned (r + t) = (bv_unsigned r + bv_unsigned t)%Z)
    by (apply u_add_small; exact Hnw).
  assert (Hwant0 : r + t <> Z_to_bv 64 0).
  { intro He. apply (f_equal bv_unsigned) in He.
    rewrite Huadd in He.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
  assert (Bridge : forall r2,
             brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 <->
             (r2 = r + t \/ r2 = r)
             /\ brk_grow_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
                = true)
    by (intro r2; apply brk_r_ok_grow_iff with (maps := []) (noaccess := []); lia).
  split.
  - intros [[-> Hcase] | [Hg ->]].
    + (* exit 4: failure resolution r2 = r, which exists iff t <> 0 *)
      assert (Ht0 : t <> Z_to_bv 64 0)
        by (destruct Hcase as [Hc | [Hc | Hc]]; [congruence | lia | exact Hc]).
      pose proof (word_neq0_unsigned t Ht0) as Hut0.
      exists r. split.
      * apply Bridge. split; [right; reflexivity|].
        exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)).
      * right. split; [| reflexivity].
        intro He. apply (f_equal bv_unsigned) in He.
        rewrite Huadd in He. lia.
    + (* success: r2 = want *)
      destruct Hg as (_ & _ & Hb).
      exists (r + t). split.
      * apply Bridge. split; [left; reflexivity|].
        destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz].
        { assert (Ht0 : t = Z_to_bv 64 0)
            by (apply bv_eq; rewrite Hz; reflexivity).
          rewrite Ht0, word_add_0_r.
          exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) r). }
        destruct Hb as [Hb | Hb];
          [exfalso; apply Hz; rewrite Hb; reflexivity |].
        rewrite brk_grow_ok_grow;
          cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes];
          [| exact Hwant0 | lia | lia].
        unfold brk_grow_bytes. cbn [vm_brk].
        rewrite app_nil_r, Huadd, Z.add_0_l.
        exact Hb.
      * left. split; reflexivity.
  - intros (r2 & Hrok & Hb).
    apply Bridge in Hrok. destruct Hrok as (Hcase & Hgrow).
    destruct Hb as [[-> ->] | [Hne ->]].
    + (* success resolution *)
      right. split; [| reflexivity].
      split; [exact Hr0 | split; [exact Hnw |]].
      destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz];
        [left; apply bv_eq; rewrite Hz; reflexivity | right].
      rewrite brk_grow_ok_grow in Hgrow;
        cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes] in *;
        [| exact Hwant0 | lia | lia].
      unfold brk_grow_bytes in Hgrow. cbn [vm_brk] in Hgrow.
      rewrite app_nil_r, Huadd, Z.add_0_l in Hgrow.
      exact Hgrow.
    + (* failure resolution: r2 = r, and t <> 0 or r2 = want *)
      left. split; [reflexivity |].
      right. right.
      intro Ht0. subst t.
      rewrite word_add_0_r in Hne, Hcase.
      destruct Hcase as [Hc | Hc]; exact (Hne Hc).
Qed.

Lemma T2_fail_iff : forall want bufs r2,
  r2 <> want -> forall o, T2 want bufs r2 o <-> o = ([], Z_to_bv 64 4).
Proof.
  intros want bufs r2 Hne o. unfold T2. tauto.
Qed.

Lemma T2_succ_iff : forall want bufs o,
  T2 want bufs want o <-> o = (bufs, Z_to_bv 64 0).
Proof.
  intros want bufs o. unfold T2. tauto.
Qed.

(* ========================================================================= *)
(* to_outcomes: the exact outcome set of a brk-branching run.                *)
(* ========================================================================= *)

Section WithSegs.
Variable segs : list Segment.

Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
    fd1chan model ->
    to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
    bufs_modeled bufs ->
    (forall o, U o <-> o = (bufs, code)) ->
    to_outcomes ms model U
| tou_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes ms' model U ->
    to_outcomes ms model U
| tou_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes ms model U.

(** Prepend a deterministic instruction run. *)
Lemma tou_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_outcomes ms' model U -> to_outcomes ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tou_step; eauto.
Qed.

(** Forgetting VM ranges preserves the non-VM state and cannot introduce
    sparse mappings. *)
Lemma forget_vm_ranges_frame : forall ranges model,
  m_halted (forget_vm_ranges ranges model) = m_halted model /\
  m_fs (forget_vm_ranges ranges model) = m_fs model /\
  m_fds (forget_vm_ranges ranges model) = m_fds model /\
  (m_vm_lazy model = [] -> m_vm_lazy (forget_vm_ranges ranges model) = []).
Proof.
  induction ranges as [|[a n] ranges IH]; intros model; cbn [forget_vm_ranges].
  - auto.
  - specialize (IH (vm_forget_range (bv_unsigned a)
      (bv_unsigned a + bv_unsigned n) model)).
    destruct IH as (Hhalt & Hfs & Hfds & Hlazy).
    unfold vm_forget_range, with_vm_backing in Hhalt, Hfs, Hfds, Hlazy.
    cbn [m_halted m_fs m_fds m_vm_lazy] in Hhalt, Hfs, Hfds, Hlazy.
    repeat split; try assumption.
    intro Hempty. apply Hlazy. rewrite Hempty. reflexivity.
Qed.

(** brk transitions keep the model running and the fs/fds untouched.  Starting
    from an eager-only model, lifecycle cleanup also leaves no lazy mappings. *)
Lemma brk_step_shape : forall ms x8 model eff model' evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  bv_unsigned x8 = 214%Z ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\ m_halted model' = None /\ m_fs model' = m_fs model
  /\ m_fds model' = m_fds model
  /\ m_vm_lazy model' = m_vm_lazy model.
Proof.
  intros ms x8 model eff model' evs Hh Hlazy Hno Hs.
  apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hs.
  destruct Hs as (_ & -> & _ & ->).
  unfold brk_model, with_brk_next. cbv zeta.
  destruct (forget_vm_ranges_frame
    (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model)))
    (with_vmmaps
      (brk_model_next (m_vmmaps model) (ms_gpr ms 0) (eff_ret eff)) model))
    as (Hhalt & Hfs & Hfds & Hlazy').
  repeat split.
  - rewrite Hhalt. unfold with_vmmaps. cbn [m_halted]. exact Hh.
  - rewrite Hfs. unfold with_vmmaps. reflexivity.
  - rewrite Hfds. unfold with_vmmaps. reflexivity.
  - rewrite Hlazy. apply Hlazy'.
    unfold with_vmmaps. cbn [m_vm_lazy]. exact Hlazy.
Qed.

(** One-step inversion at a brk ecall. *)
Lemma sstep_brk_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  sstep segs (mkCfg ms model) evs st ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
    evs = [] /\
    st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    assert (Hx : x0 = x8) by congruence; subst x0.
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno H3)
      as (He & _ & _ & _ & Hlazy').
    subst evs.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)) in H7.
    inversion H7; subst model''.
    exists eff, model'; auto.
  - (* sstep_syscall_materialization_fault: no lazy range can fault *)
    exfalso.
    match goal with
    | Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
        as (He & _ & _ & _ & Hlazy'); subst evs0;
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
      discriminate
    end.
  - (* sstep_exit: brk cannot halt the model *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hhalt : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      congruence
    end.
  - (* sstep_killed: brk cannot kill it either *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hkill : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      assert (Hhn : m_halted model' = None) by congruence;
      rewrite (m_killed_of_m_halted_none _ Hhn) in Hkill; discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (brk_no_unmodeled segs ms x8 model Hno Hspec)
    end.
Qed.

(* ------------------------------------------------------------------------- *)
(* Trace characterization.                                                    *)
(* ------------------------------------------------------------------------- *)

Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
  wevents (fst o) ++ [ExitEv (snd o) fs].

(** The omni reading of a brk-branching run: every execution ends by
    halting with one of the outcomes, having emitted exactly that
    outcome's trace.  One induction over [to_outcomes]; the leaves are
    [WallSim.to_wallexit_exec], the brk node's successors are exactly the
    admissible resolutions ([sstep_brk_inv]). *)
Definition outcomes_post (fs : Fs.Fs) (U : (list (list byte) * word) -> Prop) : post :=
  fun tr o => exists out, U out /\ tr = outcome_trace fs out /\ exits_with (snd out) tr o.

Lemma to_outcomes_exec : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  OmniRun.exec segs (mkCfg ms model) (outcomes_post (m_fs model) U).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy.
  - (* tou_wexit *)
    eapply exec_conseq;
      [exact (to_wallexit_exec segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
                Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte) |].
    intros tr o (Heq & Hx). exists (bufs, code).
    split; [apply HU; reflexivity |].
    split; [unfold outcome_trace; cbn [fst snd]; rewrite <- wevents_ch_fd1; exact Heq |].
    cbn [snd]. exact Hx.
  - (* tou_step *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
  - (* tou_brk: every admissible resolution is a successor *)
    apply exec_step; [exact Hh | | |].
    + destruct (brk_receptive segs ms x8 model Hno) as (eff & model' & Hspec).
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & _ & _ & Hlazy').
      eexists; eexists.
      apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)). reflexivity.
    + intros evs Hss.
      destruct (sstep_brk_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & _ & _ & Habs). discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_brk_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & Hfs & _ & Hlazy').
      eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy)) |].
      intros tr o (out & Hout & Heq & Hx). exists out.
      split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
      split; [| exact Hx].
      cbn [app]. unfold outcome_trace in Heq |- *. rewrite Hfs in Heq. exact Heq.
Qed.

(** Bites: the judgment names the outcome, so a different reading of the
    same run is refuted — no exit code outside the outcome set, and no
    silence. *)
Lemma to_outcomes_no_other_exit : forall ms model U,
  to_outcomes ms model U -> m_halted model = None -> m_vm_lazy model = [] ->
  forall code', (forall o, U o -> snd o <> code') ->
  ~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof.
  intros ms model U Hto Hh Hlazy code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & Hout & _ & Hx)); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne out Hout Hx').
Qed.

Lemma to_outcomes_not_silent : forall ms model U,
  to_outcomes ms model U -> m_halted model = None -> m_vm_lazy model = [] ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
  intros ms model U Hto Hh Hlazy Hc.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & _ & Heq & Hx)); [| destruct Hx].
  destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  subst tr. unfold outcome_trace in Hnil.
  destruct (wevents (fst out)); discriminate Hnil.
Qed.

Lemma to_outcomes_star_only : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists o, U o /\ is_prefix tr (outcome_trace (m_fs model) o).
Proof.
  intros ms model U Hto Hh Hlazy tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy) Hstar))
    as (tr' & o & _ & (out & Hout & Heq & _)).
  exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.

Lemma to_outcomes_star_admits : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall o, U o ->
    exists c, star segs (mkCfg ms model) (outcome_trace (m_fs model) o) c.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - (* tou_wexit *)
    apply HU in Ho. subst o.
    unfold outcome_trace; cbn [fst snd].
    rewrite <- wevents_ch_fd1.
    eapply (to_wallexit_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1);
      [exact Hh | exact Hlazy | exact (fd1chan_fdchan model Hfd)
      | exact Hbm | exact Hte].
  - (* tou_step *)
    destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model) o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - (* tou_brk *)
    apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno Hspec)
      as (Hevs & Hh' & Hfs & _ & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy) o Ht)
      as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model') o)
      by (unfold outcome_trace; rewrite Hfs; reflexivity).
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []);
      try assumption.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)).
    reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* No-error characterization.                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma to_outcomes_no_error : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model U Hto Hh Hlazy. apply exec_no_error.
  eapply exec_conseq; [exact (to_outcomes_exec ms model U Hto Hh Hlazy) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* ------------------------------------------------------------------------- *)
(* Ergonomic brk node: everything in terms of the resolved break value r.     *)
(* ------------------------------------------------------------------------- *)

(** [tou_brk] specialized to a continuation family indexed by the
    resolved break [r].  Per-binary proofs use this: they receive the
    admissibility facts on [r], the post state written with
    [apply_zeros], and the updated model, and must return the branch
    outcome set [T' r]. *)
Lemma tou_brk_r : forall ms model x8 (T' : word -> (list (list byte) * word) -> Prop) U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  (forall r,
     brk_resolution_ok model (ms_gpr ms 0) r ->
     to_outcomes
       (advance_past_svc (apply_effect ms
          (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                          (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])))
       (brk_model (ms_gpr ms 0) r model)
       (T' r)) ->
  (forall o, U o <->
     (exists r, brk_resolution_ok model (ms_gpr ms 0) r /\ T' r o)) ->
  to_outcomes ms model U.
Proof.
  intros ms model x8 T' U Hsvc Hno Hcont HU.
  apply (tou_brk ms model x8 (fun eff _ => T' (eff_ret eff)) U);
    [exact Hsvc | exact Hno | |].
  - intros eff model' evs Hspec.
    apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    pose proof (Hcont (eff_ret eff) Hok) as H.
    rewrite <- Heff in H. exact H.
  - intro o. rewrite HU. split.
    + intros (r & Hok & Ht).
      exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                            (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
             (brk_model (ms_gpr ms 0) r model), [].
      split; [apply brk_ok_intro; [exact Hno | exact Hok] | exact Ht].
    + intros (eff & model' & evs & Hspec & Ht).
      apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
      destruct Hspec as (_ & _ & Hok & _).
      exists (eff_ret eff). auto.
Qed.

(** Singleton leaf, ergonomic form. *)
Lemma tou_wexit_eq : forall ms model bufs code,
  fd1chan model ->
  to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
  bufs_modeled bufs ->
  to_outcomes ms model (fun o => o = (bufs, code)).
Proof.
  intros ms model bufs code Hfd Hte Hbm.
  apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm | tauto].
Qed.

(** Rewire the outcome set along an extensional equivalence. *)
Lemma tou_equiv : forall ms model U V,
  to_outcomes ms model U ->
  (forall o, V o <-> U o) ->
  to_outcomes ms model V.
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros V HV.
  - apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm |].
    intro o. rewrite (HV o). apply HU.
  - eapply tou_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tou_brk ms model x8 T V); [exact Hsvc | exact Hno | |].
    + intros eff model' evs Hspec. exact (Hcont eff model' evs Hspec).
    + intro o. rewrite (HV o). apply HU.
Qed.

End WithSegs.

(* ========================================================================= *)
(* Run-level packaging and the equivalence glue.                             *)
(* ========================================================================= *)

(** The run-level omni judgment of a brk-branching run. *)
Lemma alloc_omni_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes (run_segments segs inp sp mb)
              (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
              (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (outcomes_post (in_fs inp) U).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto.
  cbn [omni_run]. unfold init_config.
  exact (to_outcomes_exec (run_segments segs inp sp mb) _ _ U Hto eq_refl eq_refl).
Qed.

Lemma alloc_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes (run_segments segs inp sp mb)
              (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
              (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
    <-> exists o, U o /\ is_prefix tr (outcome_trace (in_fs inp) o).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
  unfold init_config.
  set (ms := init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) in *.
  set (m0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
               (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) in *.
  assert (Hh : m_halted m0 = None) by reflexivity.
  assert (Hlazy : m_vm_lazy m0 = []) by reflexivity.
  assert (Hfs : m_fs m0 = in_fs inp) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_outcomes_star_only (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy tr' c Hstar)
      as (o & Ho & Hp').
    exists o. split; [exact Ho|].
    rewrite Hfs in Hp'. eapply is_prefix_trans; eauto.
  - intros (o & Ho & Hp).
    destruct (to_outcomes_star_admits (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
    rewrite Hfs in Hstar.
    exists (outcome_trace (in_fs inp) o), c. split; assumption.
Qed.

Lemma alloc_no_error_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes (run_segments segs inp sp mb)
              (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
              (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
  eapply exec_conseq; [exact (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(** The omni equivalence for two brk-allocating binaries with the SAME
    outcome set [U], at the two role budgets. *)
Lemma alloc_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp source_alloc_limit inp)) U ->
  to_outcomes (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp target_alloc_limit inp)) U ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
    intros tr o (out & _ & _ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.

(** The [Equivalence]-level equivalence for two brk-allocating binaries
    with the SAME outcome set [U] (each run at ITS quantified break
    base — [U] must be base-independent, which [Run.valid_brk]'s bounds
    give the examples). *)
Lemma alloc_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         U inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp rlim inp)) U ->
  to_outcomes (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp alim inp)) U ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    U inp Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
    reflexivity.
  - cbn. apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.
End WithFP1.
