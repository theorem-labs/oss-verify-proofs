(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import MmapComplete.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.FO.P04 Require Import Mmap Mprotect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* port727 (2026-11-15, TRIAL): 's own mmap placement, beside FO/P04's local Mmap. *)
Module LMm := LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Module LPl := LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.

(* port727: FO/P04's
   first-fit base is a Linux placement (Checks/Placement.v l.867 linux_place_exists) once the top-down window
   reaches [task_unmapped_base + nZ]: a base below task_unmapped_base then ends below mmap_top, and any other base
   lies in the fallback window [task_unmapped_base, alloc_top). Every reachable state meets the premise
   (mmap_top >= min (mmap_base_min, alloc_top), both far above task_unmapped_base = 0x2aaaaab000). *)
Lemma p04_gap_linux_place : forall h thp hint nZ,
  0 < nZ -> nZ mod page_size = 0 ->
  LMm.task_unmapped_base + nZ <= mmap_top h ->
  Mmap.vm_gap_available h nZ = true ->
  exists a, LMm.linux_place h thp hint nZ a.
Proof.
  intros h thp hint nZ Hn Hal Htop Hg.
  destruct (Mmap.vm_gap_available_find _ _ Hg) as [a Ha].
  destruct (Mmap.vm_find_base_sound _ _ _ Ha) as (A1 & A2 & A3 & A4).
  apply LPl.linux_place_exists; [exact Hn | exact Hal |].
  exists (bv_unsigned a).
  assert (Ea : Z_to_bv 64 (bv_unsigned a) = a) by apply Z_to_bv_bv_unsigned.
  assert (Hps : page_size <= bv_unsigned a).
  { change page_size with 4096 in *. pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096). lia. }
  destruct (Z_lt_ge_dec (bv_unsigned a) LMm.task_unmapped_base) as [Hlt|Hge].
  - left. unfold LMm.gap_fits. rewrite Ea. split; [exact A1|]. split; [exact Hps|]. split; [lia| exact A4].
  - right. unfold LMm.gap_fits. rewrite Ea. split; [exact A1|]. split; [lia|]. split; [exact A3| exact A4].
Qed.


Lemma errno_of_None_not_errno : forall r es, errno_of r = None -> errno_ret_in es r = true ->
  errnos_ok es = true -> False.
Proof.
  intros r es Hn Hin Hok. apply errno_ret_in_true in Hin as (e & HIn & ->).
  pose proof (errnos_ok_range es e Hok HIn) as [H1 H2].
  rewrite errno_of_errno_ret in Hn by lia. discriminate.
Qed.

Lemma errno_ret_in_nil : forall r, errno_ret_in [] r = false.
Proof. reflexivity. Qed.

Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof. reflexivity. Qed.

Lemma mmap_destructive_errnos_nil : mmap_destructive_errnos = [].
Proof. reflexivity. Qed.

Lemma errno_ret_in_when : forall b r, errno_ret_in (mmap_errnos_when b) r = true -> b = true /\ r = errno_ret ENOMEM.
Proof.
  intros [|] r H; [|rewrite mmap_errnos_when_false, errno_ret_in_nil in H; discriminate].
  split; [reflexivity|]. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity.
Qed.

Lemma errno_ret_in_mprotect_when : forall b r,
  errno_ret_in (mprotect_errnos_when b) r = true -> b = true /\ r = errno_ret ENOMEM.
Proof.
  intros [|] r H; [|cbn in H; discriminate].
  split; [reflexivity|]. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity.
Qed.

Lemma errno_of_below_top : forall r h nZ, 0 <= nZ -> bv_unsigned r + nZ <= alloc_top h -> errno_of r = None.
Proof.
  intros r h nZ Hn Hb. pose proof (alloc_top_room h) as R. unfold two_pow_64, stack_max_size in R.
  apply errno_of_small. lia.
Qed.

Lemma bv_eqb_errno_small : forall e (aw : word), errno_of aw = None -> 1 <= e <= 4095 ->
  bv_eqb (errno_ret e) aw = false.
Proof.
  intros e aw Hn He. destruct (bv_eqb (errno_ret e) aw) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. rewrite <- E, errno_of_errno_ret in Hn by lia. discriminate.
Qed.

Lemma page_round_up_Z_nonneg' : forall z, 0 <= z -> 0 <= page_round_up_Z z.
Proof. intros z Hz. unfold page_round_up_Z, page_size. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]. Qed.

Lemma page_size_4096 : page_size = 4096.
Proof. reflexivity. Qed.


Lemma gap_available_of_free_base : forall h nZ g,
  0 <= nZ -> g mod 4096 = 0 -> 0 < g -> g + nZ <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  Mmap.vm_gap_available h nZ = true.
Proof.
  intros h nZ g Hn Hal Hpos Htop Hfree. pose proof (alloc_top_lt h) as T. unfold two_pow_64 in T.
  assert (Hg : bv_unsigned (Z_to_bv 64 g) = g) by (apply unsigned_lit; lia).
  apply (MmapComplete.vm_gap_available_complete h nZ (Z_to_bv 64 g)); rewrite ?Hg; assumption.
Qed.

Lemma grant_refusable_false_intro : forall flags m nZ,
  mmap_noreserve_b flags = false ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m) ->
  Mmap.vm_gap_available (m_vmmaps m) nZ = true ->
  Mmap.mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ Hnr Hb Hg. unfold Mmap.mmap_grant_refusable, mmap_noreserve_backed_ok.
  rewrite Hnr, Hg. rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.

Lemma reserve_refusable_false_intro : forall m nZ,
  Mmap.vm_gap_available (m_vmmaps m) nZ = true -> Mmap.mmap_reserve_refusable m nZ = false.
Proof. intros m nZ Hg. unfold Mmap.mmap_reserve_refusable. rewrite Hg. reflexivity. Qed.


(** Forced-only port: a refusal outcome of an allocation node, beside a non-refusal outcome of the same
    input, is not a node step — the node relation removes it as a spurious refusal.  This is the one fact
    the patch-04 proofs read off the patched errno lists ([mmap_errnos_when] of a [*_refusable] test); each
    arm below supplies the non-refusal outcome (the GRANT) when its [*_refusable] test is false. *)
Lemma listNN_eqb_refl_fo : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

Lemma nstep_refusal_no_grant : forall n i mo eff mo' evs eff2 mo2 evs2,
  node_input n = Some i -> nstep n mo eff mo' evs ->
  injected_family_off alloc_forced_cfg i = true ->
  refusal_b i mo (eff_ret eff) = true ->
  syscall_spec i mo (LinuxProcessSemantics.LinuxProcessSem.Monad.Ok eff2 mo2 evs2) -> refusal_b i mo (eff_ret eff2) = false -> False.
Proof.
  intros n i mo eff mo' evs eff2 mo2 evs2 Hi Hst Hoff Hr Hs2 Hnr2.
  destruct n; cbn [node_input] in Hi; try discriminate; injection Hi as <-; cbn [nstep node_input] in Hst;
    first [ destruct Hst as (_ & _ & _ & Hns) | destruct Hst as (_ & _ & Hns) ];
    apply Hns; (split; [exact Hoff|]); (split; [exact Hr|]); exists eff2, mo2, evs2; split; assumption.
Qed.

Section AnonMmap.
Variables (addr len prot flags : Z).
Hypothesis Hlen : 0 < len < 2^64.

Let lenw := Z_to_bv 64 len.
Let nZ := mmap_len len.
Let ia := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                          Z_to_bv 64 (-1); Z_to_bv 64 0].

Lemma anon_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ.
Proof.
  split.
  - subst lenw. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - subst lenw nZ. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma anon_off_ok : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false.
Proof. reflexivity. Qed.

Lemma anon_of_modeled :
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  negb (mmap_anon_b (Z_to_bv 64 flags)) = false.
Proof.
  intros Hshape.
  unfold mmap_modeled_b in Hshape. apply andb_prop in Hshape as [Hs _]. apply andb_prop in Hs as [_ Hs].
  unfold mmap_anon_b. apply Z.eqb_eq in Hs. unfold mmap_flags_core in Hs.
  apply negb_false_iff. apply negb_true_iff. apply Z.eqb_neq. intros Z0.
  assert (T : Z.testbit (Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE) 5 = true) by (rewrite Hs; reflexivity).
  rewrite Z.ldiff_spec in T. apply andb_prop in T as [T _].
  assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
  rewrite Z0 in T'. discriminate.
Qed.

Lemma anon_of_noaccess :
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  negb (mmap_anon_b (Z_to_bv 64 flags)) = false
  /\ mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false.
Proof.
  intros Hshape.
  assert (Hs0 := Hshape). unfold mmap_noaccess_b in Hs0. apply andb_prop in Hs0 as [Hs0 _]. apply andb_prop in Hs0 as [Hp Hf].
  split.
  - unfold mmap_anon_b. apply Z.eqb_eq in Hf. unfold mmap_flags_core in Hf.
    apply negb_false_iff. apply negb_true_iff. apply Z.eqb_neq. intros Z0.
    assert (T : Z.testbit (Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE) 5 = true) by (rewrite Hf; reflexivity).
    rewrite Z.ldiff_spec in T. apply andb_prop in T as [T _].
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
    rewrite Z0 in T'. discriminate.
  - unfold mmap_modeled_b. apply Z.eqb_eq in Hp. rewrite Hp. reflexivity.
Qed.

Lemma ia_off : injected_family_off alloc_forced_cfg ia = true.
Proof. reflexivity. Qed.

Lemma ia_refusal_enomem : forall mo, refusal_b ia mo (errno_ret ENOMEM) = true.
Proof. intros mo. reflexivity. Qed.

Lemma ia_refusal_errno_in : forall mo r, refusal_b ia mo r = errno_ret_in mmap_errnos r.
Proof. intros mo r. reflexivity. Qed.

Lemma mmap_errnos_not_small : forall r h, bv_unsigned r + nZ <= alloc_top h -> errno_ret_in mmap_errnos r = false.
Proof.
  intros r h Hb. pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
  assert (NOERR : errno_of r = None) by (apply (errno_of_below_top r h nZ); [lia | exact Hb]).
  unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite bv_eqb_sym.
  rewrite (bv_eqb_errno_small ENOMEM r NOERR) by (unfold ENOMEM; lia). reflexivity.
Qed.

(* port727: at the anonymous grant is Linux's placement ([linux_place_is], Checks/Sys/Mm/
   Mmap.v l.111) behind the hinted decline ([place_declined_b], #146). Two premises are ADDED (statement change):
   the decline premise (the ruled hint = 0 / no-decline form; a NULL hint discharges it by place_declined_b_null)
   and OPTION 4's window premise. The P04 refusability premise stays and gives the base. *)
Lemma anon_grant_place : forall mo,
  Mmap.vm_gap_available (m_vmmaps mo) nZ = true ->
  LMm.task_unmapped_base + nZ <= mmap_top (m_vmmaps mo) ->
  exists a, LPl.linux_place_is (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 addr) nZ a = true
            /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps mo).
Proof.
  intros mo Rg Htop.
  pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
  assert (HnAl : nZ mod page_size = 0) by (subst nZ; unfold mmap_len; apply LPl.page_round_up_Z_aligned).
  assert (HnPos : 0 < nZ) by lia.
  destruct (p04_gap_linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 addr) nZ HnPos HnAl Htop Rg)
    as [p Hp].
  destruct (LPl.linux_place_admissible _ _ _ _ _ HnPos HnAl Hp) as (B1 & B2 & B3 & B4).
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom.
  assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; unfold stack_max_size, two_pow_64 in *; lia).
  exists (Z_to_bv 64 p). split.
  - apply LPl.linux_place_is_iff; [exact HnPos| exact HnAl| rewrite Up; exact Hp].
  - rewrite Up. exact B3.
Qed.

(** GRANT, anonymous rw arm: with budget and a free range, the spec admits a grant. *)
Lemma mmap_anon_rw_grant : forall mo,
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  Mmap.mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = false ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr) nZ = false ->
  LMm.task_unmapped_base + nZ <= mmap_top (m_vmmaps mo) ->
  exists eff2 mo2, syscall_spec ia mo (LinuxProcessSemantics.LinuxProcessSem.Monad.Ok eff2 mo2 []) /\ refusal_b ia mo (eff_ret eff2) = false.
Proof.
  intros mo Hshape R Hdecl Htop. destruct anon_len_facts as [L0 L1].
  unfold Mmap.mmap_grant_refusable in R. apply orb_false_iff in R as [Rb Rg].
  apply negb_false_iff in Rb. apply negb_false_iff in Rg.
  destruct (anon_grant_place mo Rg Htop) as (a & A4 & A3).
  pose proof (mmap_errnos_not_small a (m_vmmaps mo) A3) as HE.
  exists (mkEffectU a [] [(a, Z_to_bv 64 nZ)] [] [] []). eexists. split.
  - apply check_syscall_ok_iff. subst ia. dispatch_pure_fo 222.
    unfold check_mmap. fold lenw. rewrite anon_off_ok, (anon_of_modeled Hshape), L0, Hshape. cbv iota beta zeta.
    rewrite L1, Hdecl. cbv iota beta zeta.
    rewrite HE, A4, Rb, listNN_eqb_refl_fo.
    reflexivity.
  - rewrite ia_refusal_errno_in. exact HE.
Qed.

(** GRANT, anonymous PROT_NONE reservation: with a free range, the spec admits a reservation. *)
Lemma mmap_anon_none_grant : forall mo,
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  Mmap.mmap_reserve_refusable mo nZ = false ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr) nZ = false ->
  LMm.task_unmapped_base + nZ <= mmap_top (m_vmmaps mo) ->
  exists eff2 mo2, syscall_spec ia mo (LinuxProcessSemantics.LinuxProcessSem.Monad.Ok eff2 mo2 []) /\ refusal_b ia mo (eff_ret eff2) = false.
Proof.
  intros mo Hshape R Hdecl Htop. destruct anon_len_facts as [L0 L1].
  destruct (anon_of_noaccess Hshape) as [G2 G3].
  unfold Mmap.mmap_reserve_refusable in R. apply negb_false_iff in R.
  destruct (anon_grant_place mo R Htop) as (a & A4 & A3).
  pose proof (mmap_errnos_not_small a (m_vmmaps mo) A3) as HE.
  exists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []). eexists. split.
  - apply check_syscall_ok_iff. subst ia. dispatch_pure_fo 222.
    unfold check_mmap. fold lenw. rewrite anon_off_ok, G2, L0, G3, Hshape. cbv iota beta zeta.
    rewrite L1, Hdecl. cbv iota beta zeta.
    rewrite HE, A4, listNN_eqb_refl_fo.
    reflexivity.
  - rewrite ia_refusal_errno_in. exact HE.
Qed.

(* port727: + OPTION 4's window premise (the grant needs it). The decline is read off the step
   itself: an Ok answer of the modeled arm is past [place_declined_b]. The success guard is linux_place_is. *)
Lemma nstep_mmap_rw_err_refusable : forall mo rsp mo' evs e,
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  LMm.task_unmapped_base + nZ <= mmap_top (m_vmmaps mo) ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ Mmap.mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape Htop H He. destruct anon_len_facts as [L0 L1].
  pose proof H as Hst0.
  apply -> nstep_mmap_iff in H. destruct H as [[_ H] _]. unfold check_mmap in H. fold lenw in H.
  rewrite anon_off_ok, (anon_of_modeled Hshape), L0, Hshape in H. cbv iota beta in H.
  rewrite L1 in H.
  destruct (place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr) nZ) eqn:Hdecl; [discriminate|].
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  fold nZ in H.
  case_errno_in_eqn H Herr.
  - apply errno_ret_in_true in Herr as (e0 & He0 & ->). destruct He0 as [<- | []].
    destruct zs; [|discriminate]. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
    split; [reflexivity|]. split; [| auto].
    destruct (Mmap.mmap_grant_refusable (Z_to_bv 64 flags) mo nZ) eqn:R; [reflexivity|]. exfalso.
    destruct (mmap_anon_rw_grant mo Hshape R Hdecl Htop) as (eff2 & mo2 & Hs2 & Hnr2).
    exact (nstep_refusal_no_grant (NMmap addr len prot flags) ia mo _ _ _ eff2 mo2 [] eq_refl Hst0 ia_off (ia_refusal_enomem mo) Hs2 Hnr2).
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _].
    pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
    assert (HnAl : nZ mod page_size = 0) by (subst nZ; unfold mmap_len; apply LPl.page_round_up_Z_aligned).
    assert (HnPos : 0 < nZ) by lia.
    destruct (LPl.linux_place_is_admissible _ _ _ _ _ HnPos HnAl E) as (_ & _ & Etop & _).
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) Etop) in He. discriminate.
Qed.

Lemma nstep_mmap_none_err_refusable : forall mo rsp mo' evs e,
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  LMm.task_unmapped_base + nZ <= mmap_top (m_vmmaps mo) ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ Mmap.mmap_reserve_refusable mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape Htop H He. destruct anon_len_facts as [L0 L1].
  destruct (anon_of_noaccess Hshape) as [G2 G3].
  pose proof H as Hst0.
  apply -> nstep_mmap_iff in H. destruct H as [[_ H] _]. unfold check_mmap in H. fold lenw in H.
  rewrite anon_off_ok, G2, L0, G3, Hshape in H. cbv iota beta in H.
  rewrite L1 in H.
  destruct (place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr) nZ) eqn:Hdecl; [discriminate|].
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct ws; [|discriminate]. destruct zs; [|discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  fold nZ in H.
  case_errno_in_eqn H Herr.
  - apply errno_ret_in_true in Herr as (e0 & He0 & ->). destruct He0 as [<- | []].
    destruct us; [|discriminate]. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
    split; [reflexivity|]. split; [| auto].
    destruct (Mmap.mmap_reserve_refusable mo nZ) eqn:R; [reflexivity|]. exfalso.
    destruct (mmap_anon_none_grant mo Hshape R Hdecl Htop) as (eff2 & mo2 & Hs2 & Hnr2).
    exact (nstep_refusal_no_grant (NMmap addr len prot flags) ia mo _ _ _ eff2 mo2 [] eq_refl Hst0 ia_off (ia_refusal_enomem mo) Hs2 Hnr2).
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _].
    pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
    assert (HnAl : nZ mod page_size = 0) by (subst nZ; unfold mmap_len; apply LPl.page_round_up_Z_aligned).
    assert (HnPos : 0 < nZ) by lia.
    destruct (LPl.linux_place_is_admissible _ _ _ _ _ HnPos HnAl E) as (_ & _ & Etop & _).
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) Etop) in He. discriminate.
Qed.
End AnonMmap.

Section FixedMmap.
Variables (a len prot flags : Z).
Hypothesis Hlen : 0 < len < 2^64.
Hypothesis Ha : 0 <= a.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hwrap : a + mmap_len len < 2^64.

Let aw := Z_to_bv 64 a.
Let lenw := Z_to_bv 64 len.
Let nZ := mmap_len len.
Let nw := Z_to_bv 64 nZ.
Let ifx := pure_input 222 [Z_to_bv 64 a; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                           Z_to_bv 64 (-1); Z_to_bv 64 0].

Lemma fixed_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ /\ bv_unsigned aw = a.
Proof.
  pose proof (mmap_len_bound len ltac:(lia)).
  repeat split.
  - subst lenw. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - subst lenw nZ. rewrite unsigned_lit by lia. reflexivity.
  - subst aw. apply unsigned_lit. lia.
Qed.

Lemma fixed_gate_wrap : (two_pow_64 <=? bv_unsigned aw + page_round_up_Z (bv_unsigned lenw)) = false.
Proof.
  destruct fixed_len_facts as (_ & -> & ->). apply Z.leb_gt. unfold two_pow_64. subst nZ. lia.
Qed.
Lemma fixed_gate_align : negb (Z.eqb (bv_unsigned aw mod page_size) 0) = false.
Proof. destruct fixed_len_facts as (_ & _ & ->). rewrite page_size_4096, Hal. reflexivity. Qed.

Lemma fixed_shape_pre :
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false
  /\ negb (mmap_anon_b (Z_to_bv 64 flags)) = false
  /\ mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false.
Proof.
  intros Hs.
  assert (CORE : mmap_flags_core (Z_to_bv 64 flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED
                 \/ mmap_flags_core (Z_to_bv 64 flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED_NOREPLACE
                 \/ mmap_flags_core (Z_to_bv 64 flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED + MAP_FIXED_NOREPLACE).
  { destruct (mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S1.
    { unfold mmap_fixed_noaccess_b in S1. apply andb_prop in S1 as [S1 _]. apply andb_prop in S1 as [_ Hc].
      apply Z.eqb_eq in Hc. auto. }
    destruct (mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S2.
    { unfold mmap_fixed_rw_b in S2. apply andb_prop in S2 as [S2 _]. apply andb_prop in S2 as [_ Hc].
      apply Z.eqb_eq in Hc. auto. }
    destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S3.
    { unfold mmap_noreplace_noaccess_b in S3. apply andb_prop in S3 as [S3 _]. apply andb_prop in S3 as [_ Hc].
      unfold mmap_noreplace_flags_b in Hc. apply orb_prop in Hc as [Hc|Hc]; apply Z.eqb_eq in Hc; auto. }
    destruct (mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S4.
    { unfold mmap_noreplace_rw_b in S4. apply andb_prop in S4 as [S4 _]. apply andb_prop in S4 as [_ Hc].
      unfold mmap_noreplace_flags_b in Hc. apply orb_prop in Hc as [Hc|Hc]; apply Z.eqb_eq in Hc; auto. }
    discriminate Hs. }
  assert (BIT : Z.testbit (mmap_flags_core (Z_to_bv 64 flags)) 5 = true)
    by (destruct CORE as [-> |[-> | ->]]; reflexivity).
  unfold mmap_flags_core in BIT. rewrite Z.ldiff_spec in BIT. apply andb_prop in BIT as [BIT _].
  split; [reflexivity|]. split.
  { unfold mmap_anon_b. apply negb_false_iff, negb_true_iff, Z.eqb_neq. intros Z0.
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, BIT; reflexivity).
    rewrite Z0 in T'. discriminate. }
  assert (NE : Z.eqb (mmap_flags_core (Z_to_bv 64 flags)) (MAP_PRIVATE + MAP_ANONYMOUS) = false)
    by (destruct CORE as [-> |[-> | ->]]; reflexivity).
  unfold mmap_modeled_b, mmap_noaccess_b. rewrite NE, !andb_false_r. auto.
Qed.

Lemma ifx_off : injected_family_off alloc_forced_cfg ifx = true.
Proof. reflexivity. Qed.

Lemma ifx_refusal_enomem : forall mo, refusal_b ifx mo (errno_ret ENOMEM) = true.
Proof. intros mo. reflexivity. Qed.

Lemma ifx_refusal_errno_in : forall mo r, refusal_b ifx mo r = errno_ret_in mmap_errnos r.
Proof. intros mo r. reflexivity. Qed.

(** GRANT, MAP_FIXED PROT_NONE: in each of the arm's three ledger cases the replacement at [aw] is
    admitted (never charged, range given). *)
Lemma fixed_none_grant : forall mo,
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  a + nZ <= alloc_top (m_vmmaps mo) -> 0 < a ->
  (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw = true
   \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw = true
   \/ region_free (vm_reserved (m_vmmaps mo)) aw nw = true) ->
  errno_ret_in mmap_errnos aw = false ->
  exists mo2, check_mmap aw lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                (mkEffectU aw [] [] [(aw, nw)] [] []) mo = CheckOk mo2 [].
Proof.
  intros mo Hshape Htop Hpos Hreg HEaw. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape; reflexivity)) as (G1 & G2 & G3 & G4).
  unfold check_mmap. rewrite G1, G2, L0, G3, G4, Hshape. cbv iota beta zeta.
  rewrite fixed_gate_wrap, fixed_gate_align, L1.
  replace (bv_unsigned aw + nZ <=? alloc_top (m_vmmaps mo)) with true by (symmetry; apply Z.leb_le; lia).
  replace (0 <? bv_unsigned aw) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota. fold nw.
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  - rewrite HEaw, bv_eqb_refl, listNN_eqb_refl_fo. cbn [andb]. eexists. reflexivity.
  - destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
    + rewrite HEaw, bv_eqb_refl, listNN_eqb_refl_fo. cbn [andb]. eexists. reflexivity.
    + destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:S3.
      * rewrite HEaw, bv_eqb_refl, listNN_eqb_refl_fo. cbn [andb]. eexists. reflexivity.
      * exfalso. destruct Hreg as [R|[R|R]]; congruence.
Qed.

(** Under patch 04 this arm offered no errno at all; on the unpatched spec its two -ENOMEM resolutions
    are refusals beside the always-admitted replacement, so the filtered node relation has none. *)
Lemma nstep_mmap_fixed_none_no_err : forall mo rsp mo' evs,
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap a len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = None /\ eff_ret rsp = aw /\ evs = [].
Proof.
  intros mo rsp mo' evs Hshape H. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape; reflexivity)) as (G1 & G2 & G3 & G4).
  pose proof H as Hst0.
  apply -> nstep_mmap_iff in H. destruct H as [[_ H] _]. unfold check_mmap in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, Hshape in H. cbv iota beta in H. cbv zeta in H.
  rewrite fixed_gate_wrap in H.
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:Gt; [discriminate|].
  rewrite fixed_gate_align in H.
  destruct (negb (0 <? bv_unsigned aw)) eqn:Gp; [discriminate|].
  apply negb_false_iff, Z.leb_le in Gt. rewrite L1, La in Gt.
  apply negb_false_iff, Z.ltb_lt in Gp. rewrite La in Gp.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Gt]).
  assert (HEaw : errno_ret_in mmap_errnos aw = false).
  { unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite bv_eqb_sym.
    rewrite (bv_eqb_errno_small ENOMEM aw NOERR) by (unfold ENOMEM; lia). reflexivity. }
  rewrite L1 in H. fold nw in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret].
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  2: destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  3: destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:S3; [|discriminate].
  all: assert (Hreg : region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw = true
                      \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw = true
                      \/ region_free (vm_reserved (m_vmmaps mo)) aw nw = true)
         by first [left; assumption | right; left; assumption | right; right; assumption].
  all: destruct ws; [|discriminate]; destruct zs; [|discriminate];
       destruct cs; [|destruct us; discriminate]; destruct ci; [|destruct us; discriminate].
  all: case_errno_in_eqn H Herr;
    [ exfalso; apply errno_ret_in_true in Herr as (e0 & He0 & ->); destruct He0 as [<- | []];
      destruct (fixed_none_grant mo Hshape Gt Gp Hreg HEaw) as [mo2 Hc2];
      apply (nstep_refusal_no_grant (NMmap a len prot flags) ifx mo _ _ _ (mkEffectU aw [] [] [(aw, nw)] [] []) mo2 [] eq_refl Hst0
               ifx_off (ifx_refusal_enomem mo));
      [ apply check_syscall_ok_iff; dispatch_pure_fo 222; exact Hc2
      | rewrite ifx_refusal_errno_in; exact HEaw ]
    | ].
  all: cbn [andb] in H; cbv iota in H.
  all: destruct (bv_eqb r aw && _) eqn:E; [|discriminate]; apply andb_prop in E as [E _]; apply bv_eqb_eq in E; subst r.
  all: injection H as _ <-; auto.
Qed.
End FixedMmap.

Section Mprotect.
Variables (a len : Z).
Hypothesis Hlen : 0 < len < 2^64.
Hypothesis Ha : 0 <= a.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hwrap : a + mmap_len len < 2^64.

Let aw := Z_to_bv 64 a.
Let nZ := mmap_len len.
Let nw := Z_to_bv 64 nZ.
Let ipx := pure_input 226 [Z_to_bv 64 a; Z_to_bv 64 len; Z_to_bv 64 (PROT_READ + PROT_WRITE)].

Lemma ipx_off : injected_family_off alloc_forced_cfg ipx = true.
Proof. reflexivity. Qed.

Lemma ipx_refusal_enomem : forall mo, refusal_b ipx mo (errno_ret ENOMEM) = true.
Proof. intros mo. reflexivity. Qed.

Lemma ipx_refusal_zero : forall mo, refusal_b ipx mo (Z_to_bv 64 0) = false.
Proof. intros mo. reflexivity. Qed.

(* port727: 's check_mprotect answers unmodeled for a range meeting the vDSO pair
   (Checks/Sys/Mm/Mprotect.v l.32-37), ahead of the arms below. An Ok answer is past that test. *)
Lemma mprotect_rw_vdso : forall eff mo mo' evs,
  check_mprotect aw (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE)) eff mo = CheckOk mo' evs ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true.
Proof.
  intros eff mo mo' evs H. pose proof (mmap_len_bound len ltac:(lia)) as LB.
  unfold check_mprotect in H.
  assert (La : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Ll : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
  rewrite La, page_size_4096, Hal in H. cbn [Z.eqb negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  rewrite Ll in H. fold (mmap_len len) in H. fold nZ in H.
  replace (two_pow_64 <=? a + nZ) with false in H by (symmetry; apply Z.leb_gt; unfold two_pow_64; subst nZ; lia).
  change (negb (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)))) with false in H. cbv iota zeta in H. fold nw in H.
  destruct (region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw); [reflexivity| discriminate H].
Qed.

(** The guard of the exposing arm, read off the checker the same way the step lemma reads it. *)
(* port727: + the vDSO premise (statement change, the CHANGE-LIST row 15 mprotect pattern). *)
Lemma mprotect_rw_unfold : forall eff mo,
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true ->
  check_mprotect aw (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE)) eff mo =
  if map_contains (vm_noaccess (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw then
    match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r
        then match zs with [] => CheckOk mo [] | _ => CheckReject end
        else if mprotect_budget_ok mo aw nw && w_is0 r && listNN_eqb zs [(aw, nw)]
        then CheckOk (mprotect_model_next mo aw nw) []
        else CheckReject
    | _ => CheckReject
    end
  else if map_contains (vm_maps (m_vmmaps mo)) aw nw && region_free (vm_noaccess (m_vmmaps mo)) aw nw then
    match eff with
    | mkEffectU r [] [] [] [] [] => if w_is0 r then CheckOk mo [] else CheckReject
    | _ => CheckReject
    end
  else CheckUnmodeled.
Proof.
  intros eff mo Hv. pose proof (mmap_len_bound len ltac:(lia)) as LB.
  unfold check_mprotect.
  assert (La : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Ll : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false.
  rewrite La, page_size_4096, Hal. cbn [Z.eqb negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Ll. fold (mmap_len len). fold nZ.
  replace (two_pow_64 <=? a + nZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; subst nZ; lia).
  change (negb (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)))) with false. cbv iota zeta. fold nw.
  rewrite Hv. reflexivity.
Qed.

(** GRANT, mprotect exposing a reserved range: with the commit charge fitting, the exposure is admitted. *)
Lemma mprotect_rw_grant : forall mo,
  map_contains (vm_noaccess (m_vmmaps mo)) aw nw = true ->
  map_contains (vm_maps (m_vmmaps mo)) aw nw = true ->
  Mprotect.mprotect_refusable mo aw nw = false ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true ->
  exists mo2, check_mprotect aw (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE))
                (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] []) mo = CheckOk mo2 [].
Proof.
  intros mo C1 C2 R Hv. unfold Mprotect.mprotect_refusable in R. apply negb_false_iff in R.
  rewrite (mprotect_rw_unfold _ _ Hv), C1, C2. cbn [andb]. cbv iota.
  replace (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false by reflexivity.
  rewrite R, listNN_eqb_refl_fo. replace (w_is0 (Z_to_bv 64 0)) with true by reflexivity. cbn [andb].
  eexists. reflexivity.
Qed.

Lemma nstep_mprotect_err_refusable : forall mo rsp mo' evs e,
  nstep (NMprotect a len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  let h := m_vmmaps mo in
  e = ENOMEM /\ mo' = mo /\ evs = []
  /\ map_contains (vm_noaccess h) aw nw = true /\ map_contains (vm_maps h) aw nw = true
  /\ Mprotect.mprotect_refusable mo aw nw = true.
Proof.
  intros mo rsp mo' evs e H He. pose proof (mmap_len_bound len ltac:(lia)) as LB.
  pose proof H as Hst0.
  apply -> nstep_mprotect_iff in H. destruct H as [H _]. fold aw in H.
  pose proof (mprotect_rw_vdso _ _ _ _ H) as Hv. rewrite (mprotect_rw_unfold _ _ Hv) in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct (map_contains (vm_noaccess (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  - apply andb_prop in S1 as [C1 C2].
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    case_errno_in_eqn H Herr.
    + apply errno_ret_in_true in Herr as (e0 & He0 & ->).
      assert (Ee0 : e0 = ENOMEM) by (destruct He0 as [<- | []]; reflexivity). subst e0.
      rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
      destruct zs; [|discriminate]. injection H as <- <-.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact C1|]. split; [exact C2|].
      destruct (Mprotect.mprotect_refusable mo aw nw) eqn:R; [reflexivity|]. exfalso.
      destruct (mprotect_rw_grant mo C1 C2 R Hv) as [mo2 Hc2].
      apply (nstep_refusal_no_grant (NMprotect a len (PROT_READ + PROT_WRITE)) ipx mo _ _ _ (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] []) mo2 [] eq_refl
               Hst0 ipx_off (ipx_refusal_enomem mo)).
      * apply check_syscall_ok_iff. dispatch_pure_fo 226. exact Hc2.
      * exact (ipx_refusal_zero mo).
    + exfalso. destruct (mprotect_budget_ok mo aw nw && w_is0 r && _) eqn:E; [|discriminate].
      apply andb_prop in E as [E _]. apply andb_prop in E as [_ E]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
      rewrite errno_of_lit in He by lia. discriminate.
  - exfalso. destruct (map_contains (vm_maps (m_vmmaps mo)) aw nw && region_free (vm_noaccess (m_vmmaps mo)) aw nw); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    rewrite errno_of_lit in He by lia. discriminate.
Qed.

Lemma mprotect_refusable_false_intro : forall mo,
  vm_backing_used (mprotect_model_next mo aw nw) <= vm_limit (m_vmmaps mo) ->
  Mprotect.mprotect_refusable mo aw nw = false.
Proof.
  intros mo Hb. unfold Mprotect.mprotect_refusable, mprotect_budget_ok, vm_backing_within_limit.
  unfold mprotect_model_next in *. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit].
  rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.
End Mprotect.

