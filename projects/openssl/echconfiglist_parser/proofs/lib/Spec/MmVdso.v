(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the [Inv_node] obligation of [SReachTreeInv] for the
   unit's mm nodes ([MmNodes.mmsafe]: brk, the three mmap shapes, munmap, mprotect), for the
   invariant "the overlay holds no byte of the window [vlo, vhi), and the window sits inside an
   entry of the launch's vDSO/vvar pair, which is in the reserved ledger" ([vc_cfg]).
     - Memory: each node's effect has no writes and no copies, and every range it zero-fills
       misses the window ([VdsoClean.nret_clean]; [Run.apply_effect], Run.v:176-189, writes
       exactly the declared ranges, [Run.zeros_cover], Run.v:105-108).  The zero-fills are
       the PROT_RW NULL-hint grant, tested by [region_free] over [vm_reserved ++ vm_maps]
       ([MmNodes.mmap_grant_conds]); the brk grow [[PAGE_ALIGN old, PAGE_ALIGN r)]
       ([Mmap.brk_zeros], Sys/Mm/Mmap.v:211-215, [Mmap.brk_page_range] :167-170), whose gate
       [Mmap.brk_grow_ok] (:380-392) tests the same range and one page more against
       [vm_reserved ++ vm_maps]; and the mprotect RW range, which [mmsafe] asks to be
       [region_free] against [vdso_reserved] itself.  [region_free] (State.v:6346-6350, through
       [iv_overlap] :6341-6343) puts such a range apart from every entry of its ledger, so apart
       from the entry holding the window.
     - Model: no mm node writes [m_kernel], [vm_reserved] or [vm_mmap_base], and
       [nstep_mm_post] keeps [alloc_top] (State.v:3393-3394); [vdso_top] (State.v:3483) reads
       only [vm_mmap_base] and [alloc_top] ([mmap_top], :3466-3467), so the pair
       [vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))] (State.v:6559-6564) is the same
       list after the step.
   [vdso_reserved] takes the kernel build and a [Z] top, as [mm_vinv] uses it.  The section
   context also takes [AllocForced], because [MmNodes]' shape lemmas ([nstep_brk_iff] and the
   rest) are stated under it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require VmMapsDisjoint.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require KLink.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MmVdso.
Context {SC : StepCfg} {AF : AllocForced SC}.
Variables vlo vhi : Z.

(** The window lies inside one entry of [l]. *)
Definition win_in (l : list (word * word)) : Prop :=
  exists r, In r l /\ bv_unsigned (fst r) <= vlo /\ vhi <= bv_unsigned (fst r) + bv_unsigned (snd r).

(** The window lies inside an entry of the launch's vDSO/vvar pair, and the pair is reserved. *)
Definition mm_vinv (mo : Model) : Prop :=
  win_in (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo)))
  /\ incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo)).

Definition vc_cfg (c : config) : Prop :=
  vclean vlo vhi (ms_mem (cfg_ms c)) /\ mm_vinv (cfg_model c).

(** What one mm node does that the invariant reads. *)
Definition mm_shape (mo : Model) (rsp : SyscallEffect) (mo' : Model) : Prop :=
  eff_writes rsp = [] /\ eff_copies rsp = [] /\ Forall (range_off vlo vhi) (eff_zeros rsp)
  /\ m_kernel mo' = m_kernel mo
  /\ vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo)
  /\ vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo).

Lemma mm_shape_intro : forall mo rsp mo',
  eff_writes rsp = [] -> eff_copies rsp = [] -> Forall (range_off vlo vhi) (eff_zeros rsp) ->
  m_kernel mo' = m_kernel mo ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  mm_shape mo rsp mo'.
Proof.
  intros mo rsp mo' H1 H2 H3 H4 H5 H6. unfold mm_shape.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

Lemma zeros_nil_off : forall rsp : SyscallEffect,
  eff_zeros rsp = [] -> Forall (range_off vlo vhi) (eff_zeros rsp).
Proof. intros rsp E. rewrite E. constructor. Qed.

(** A range [region_free] against a ledger misses an entry of it that holds the window. *)
Lemma off_of_free : forall l (a n : word) (r : word * word),
  region_free l a n = true -> In r l ->
  bv_unsigned (fst r) <= vlo -> vhi <= bv_unsigned (fst r) + bv_unsigned (snd r) ->
  range_off vlo vhi (a, n).
Proof.
  intros l a n [rb rs] Hf Hin Hlo Hhi. cbn [fst snd] in Hlo, Hhi.
  pose proof (KLink.region_free_InZ l a n rb rs Hf Hin) as D.
  unfold range_off. cbn [fst snd]. lia.
Qed.

Lemma off_shrink : forall (a n n' : word), bv_unsigned n <= bv_unsigned n' ->
  range_off vlo vhi (a, n') -> range_off vlo vhi (a, n).
Proof.
  intros a n n' Hle H. unfold range_off in H |- *. cbn [fst snd] in H |- *. lia.
Qed.

(** Free against [vm_reserved ++ vm_maps]: the pair is in [vm_reserved]. *)
Lemma vinv_off_res : forall mo (a n : word), mm_vinv mo ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
  range_off vlo vhi (a, n).
Proof.
  intros mo a n VI Hf. unfold mm_vinv, win_in in VI.
  destruct VI as [(r & Hin & Hlo & Hhi) Hinc].
  assert (Hin' : In r (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))).
  { apply in_or_app. left. exact (Hinc r Hin). }
  exact (off_of_free _ a n r Hf Hin' Hlo Hhi).
Qed.

(** Free against the pair itself. *)
Lemma vinv_off_vdso : forall mo (a n : word), mm_vinv mo ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) a n = true ->
  range_off vlo vhi (a, n).
Proof.
  intros mo a n VI Hf. unfold mm_vinv, win_in in VI.
  destruct VI as [(r & Hin & Hlo & Hhi) _].
  exact (off_of_free _ a n r Hf Hin Hlo Hhi).
Qed.

(** The brk zero-fill: empty unless the break grows, and then the grow gate tested
    [[lo, hi + page_size)] free against [vm_reserved ++ vm_maps], a superset of the
    zero-filled [[lo, hi)]. *)
Lemma grow_zeros_off : forall mo (rq r : word), mm_vinv mo -> brk_r_ok mo rq r = true ->
  Forall (range_off vlo vhi) (brk_zeros rq r (vm_brk (m_vmmaps mo))).
Proof.
  intros mo rq r VI Hok. unfold brk_zeros.
  destruct (brk_is_grow rq r (vm_brk (m_vmmaps mo))) eqn:Eg; [|constructor].
  pose proof (VmMapsDisjoint.brk_r_ok_grow mo rq r Hok Eg) as Hg.
  unfold brk_is_grow in Eg. apply andb_prop in Eg as [Eg1 Eg3]. apply andb_prop in Eg1 as [_ Eg2].
  apply Z.ltb_lt in Eg2. apply Z.ltb_lt in Eg3.
  unfold brk_grow_ok in Hg. cbv zeta in Hg.
  assert (Gc : (Z.ltb 0 (bv_unsigned (vm_brk (m_vmmaps mo)))
                && Z.ltb (bv_unsigned (vm_brk (m_vmmaps mo))) (bv_unsigned r)) = true).
  { rewrite (proj2 (Z.ltb_lt _ _) Eg2), (proj2 (Z.ltb_lt _ _) Eg3). reflexivity. }
  rewrite Gc in Hg. cbv beta iota in Hg.
  unfold brk_page_range.
  destruct (Z.ltb (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps mo))))
                  (page_round_up_Z (bv_unsigned r))) eqn:Elh; [|constructor].
  rewrite ?Elh in Hg. cbv beta iota in Hg.
  apply andb_prop in Hg as [Hg1 _]. apply andb_prop in Hg1 as [Htop Hrf].
  apply Z.leb_le in Htop. apply Z.ltb_lt in Elh.
  pose proof (vinv_off_res mo _ _ VI Hrf) as Hoff.
  constructor; [|constructor].
  refine (off_shrink _ _ _ _ Hoff).
  assert (Hps : page_size = 4096) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps mo))) as R0.
  pose proof (alloc_top_room (m_vmmaps mo)) as Room. unfold two_pow_64, stack_max_size in Room.
  assert (Hlo0 : 0 <= page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps mo)))).
  { unfold page_round_up_Z. rewrite Hps. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
  rewrite !unsigned_wz by lia. lia.
Qed.

Lemma mm_brk_shape : forall req mo rsp mo' evs, mminv mo -> mmsafe (NBrk req) mo ->
  Nodes.nstep (NBrk req) mo rsp mo' evs -> mm_vinv mo -> mm_shape mo rsp mo'.
Proof.
  intros req mo rsp mo' evs MI SF NS VI. cbn [mmsafe] in SF.
  pose proof (nstep_brk_iff mo req rsp mo' evs SF) as E. cbv zeta in E.
  apply (proj1 E) in NS. clear E.
  destruct NS as (_ & Er & Em). subst rsp mo'.
  rewrite (with_brk_next_eq mo (wz req) (brk_result mo (wz req)) MI).
  apply mm_shape_intro; [reflexivity | reflexivity | | reflexivity | reflexivity | reflexivity].
  cbn [eff_zeros].
  exact (grow_zeros_off mo (wz req) (brk_result mo (wz req)) VI (brk_result_ok mo (wz req))).
Qed.

Lemma mm_mmap_shape : forall addr len prot flags mo rsp mo' evs, mminv mo ->
  mmsafe (NMmap addr len prot flags) mo ->
  Nodes.nstep (NMmap addr len prot flags) mo rsp mo' evs -> mm_vinv mo -> mm_shape mo rsp mo'.
Proof.
  intros addr len prot flags mo rsp mo' evs MI SF NS VI.
  pose proof SF as SF0. cbn [mmsafe] in SF.
  destruct SF as [(Ea & Ef & [Ep | Ep] & Hl) | (Ef & Ep & Hl & _)].
  - (* PROT_RW, NULL hint: the grant is zero-filled and [region_free] over the ledger *)
    subst addr flags prot.
    pose proof (nstep_mmap_rw_iff mo len rsp mo' evs Hl) as E. cbv zeta in E.
    apply (proj1 E) in NS. clear E.
    destruct NS as [_ [(Er & Em & _) | (a & G & _ & Er & Em)]]; subst rsp mo'.
    + apply mm_shape_intro;
        [reflexivity | reflexivity | apply zeros_nil_off; reflexivity | reflexivity | reflexivity | reflexivity].
    + unfold mmap_grant_conds in G. cbv beta zeta in G.
      destruct G as (G1 & G2 & G3 & Grf & G5).
      apply mm_shape_intro; [reflexivity | reflexivity | | reflexivity | reflexivity | reflexivity].
      cbn [eff_zeros]. constructor; [| constructor].
      exact (vinv_off_res mo a _ VI Grf).
  - (* PROT_NONE, NULL hint: no zero-fill *)
    subst addr flags prot.
    pose proof (nstep_mmap_na_iff mo len rsp mo' evs Hl) as E. cbv zeta in E.
    apply (proj1 E) in NS. clear E.
    destruct NS as [_ [(Er & Em & _) | (a & _ & Er & Em)]]; subst rsp mo';
      (apply mm_shape_intro;
         [reflexivity | reflexivity | apply zeros_nil_off; reflexivity | reflexivity | reflexivity | reflexivity]).
  - (* MAP_FIXED PROT_NONE: no zero-fill *)
    subst flags prot.
    pose proof (nstep_mmap_fixed_iff mo addr len rsp mo' evs MI SF0) as E. cbv zeta in E.
    apply (proj1 E) in NS. clear E.
    destruct NS as (_ & Er & Em). subst rsp mo'.
    apply mm_shape_intro;
      [reflexivity | reflexivity | apply zeros_nil_off; reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

Lemma mm_munmap_shape : forall addr len mo rsp mo' evs, mminv mo -> mmsafe (NMunmap addr len) mo ->
  Nodes.nstep (NMunmap addr len) mo rsp mo' evs -> mm_shape mo rsp mo'.
Proof.
  intros addr len mo rsp mo' evs MI SF NS.
  pose proof (nstep_munmap_iff mo addr len rsp mo' evs MI SF) as E. cbv zeta in E.
  apply (proj1 E) in NS. clear E.
  destruct NS as (_ & Er & Em). subst rsp mo'.
  apply mm_shape_intro;
    [reflexivity | reflexivity | apply zeros_nil_off; reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

Lemma mm_mprotect_shape : forall addr len prot mo rsp mo' evs, mmsafe (NMprotect addr len prot) mo ->
  Nodes.nstep (NMprotect addr len prot) mo rsp mo' evs -> mm_vinv mo -> mm_shape mo rsp mo'.
Proof.
  intros addr len prot mo rsp mo' evs SF NS VI.
  pose proof SF as SF0. cbn [mmsafe] in SF.
  destruct SF as (Ep & _ & _ & _ & _ & _ & _ & VD). subst prot.
  pose proof (nstep_mprotect_iff mo addr len rsp mo' evs SF0) as E. cbv zeta in E.
  apply (proj1 E) in NS. clear E.
  destruct NS as [_ [(_ & Er & Em) | (_ & Er & Em)]]; subst rsp mo'.
  - apply mm_shape_intro;
      [reflexivity | reflexivity | apply zeros_nil_off; reflexivity | reflexivity | reflexivity | reflexivity].
  - (* the exposed noaccess pages are zero-filled; [mmsafe] put them apart from the pair *)
    apply mm_shape_intro; [reflexivity | reflexivity | | reflexivity | reflexivity | reflexivity].
    cbn [eff_zeros]. constructor; [| constructor].
    exact (vinv_off_vdso mo _ _ VI VD).
Qed.

Lemma mm_node_shape : forall n mo rsp mo' evs, mminv mo -> mmsafe n mo ->
  Nodes.nstep n mo rsp mo' evs -> mm_vinv mo -> mm_shape mo rsp mo'.
Proof.
  intros n mo rsp mo' evs MI SF NS VI.
  destruct n as [fd bs|fd bufs|path|fd buf count|fd|fd rq| |code|req|addr len prot flags|addr len|addr len prot];
    try (exfalso; exact SF).
  - exact (mm_brk_shape req mo rsp mo' evs MI SF NS VI).
  - exact (mm_mmap_shape addr len prot flags mo rsp mo' evs MI SF NS VI).
  - exact (mm_munmap_shape addr len mo rsp mo' evs MI SF NS).
  - exact (mm_mprotect_shape addr len prot mo rsp mo' evs SF NS VI).
Qed.

(** [mm_vinv] reads [m_kernel], [vm_reserved], [vm_mmap_base] and [alloc_top] only. *)
Lemma mm_vinv_frame : forall mo mo',
  m_kernel mo' = m_kernel mo ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) ->
  mm_vinv mo -> mm_vinv mo'.
Proof.
  intros mo mo' Ek Er Eb Et VI. unfold mm_vinv in VI |- *. destruct VI as [W Hinc].
  split.
  - rewrite Ek, (KLink.kb_vdso_top_eq (m_vmmaps mo) (m_vmmaps mo') Eb Et). exact W.
  - exact (KLink.kb_vdso_in_eq mo mo' Ek Er Eb Et Hinc).
Qed.

Theorem mm_node_vc : forall (segs : list Segment) n ms mo rsp mo' evs,
  at_node segs n ms -> m_halted mo = None -> mminv mo -> mmsafe n mo -> Nodes.nstep n mo rsp mo' evs ->
  vc_cfg (mkCfg ms mo) -> vc_cfg (mkCfg (ITree.nret ms rsp) mo').
Proof.
  intros segs n ms mo rsp mo' evs _ Hh MI SF NS VC.
  unfold vc_cfg in VC |- *. cbn [cfg_ms cfg_model] in VC |- *.
  destruct VC as [Hcl VI].
  pose proof (mm_node_shape n mo rsp mo' evs MI SF NS VI) as SH. unfold mm_shape in SH.
  destruct SH as (Hw & Hc & Hz & Ek & Er & Eb).
  pose proof (nstep_mm_post n mo rsp mo' evs MI SF Hh (m_killed_of_m_halted_none mo Hh) NS) as PO.
  destruct PO as (_ & _ & _ & _ & Et).
  split.
  - exact (nret_clean vlo vhi ms rsp Hw Hc Hz Hcl).
  - exact (mm_vinv_frame mo mo' Ek Er Eb Et VI).
Qed.

End MmVdso.
