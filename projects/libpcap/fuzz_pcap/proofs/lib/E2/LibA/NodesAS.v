(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec ITree RelSpec Nodes PlacementSearch.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ModelX MmXfer SpecXfer.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA NodesA NodesSil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesMmSh.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude Dispatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition setvm (v : VmState) (m : Model) : Model :=
  mkModelOf (m_fd m) v (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).

Lemma setvm_id : forall m, setvm (m_vm m) m = m.
Proof. intros [fd vm io fs pr lm tm]. reflexivity. Qed.
Lemma setvm_setvm : forall v w m, setvm v (setvm w m) = setvm v m.
Proof. reflexivity. Qed.
Lemma m_vm_setvm : forall v m, m_vm (setvm v m) = v.
Proof. reflexivity. Qed.

Definition fsnode (n : node) : Prop :=
  match n with
  | NWrite _ _ | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _
  | NOpenW _ _ | NWritevF _ _ | NReadv _ _ | NUnlink _ _ | NLseek _ _ _ => True
  | _ => False
  end.

Ltac solve_side :=
  first [ reflexivity | eassumption | exact I
        | split; solve_side
        | eexists; solve_side
        | left; solve [solve_side]
        | right; solve [solve_side] ].

Ltac nstep_destr :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  | H : False |- _ => destruct H
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  | H : context [if ?x then _ else _] |- _ => destruct x eqn:?
  end; subst.

Lemma nstep_setvm : forall n v mo rsp mo' evs,
  fsnode n -> nstep n mo rsp mo' evs -> nstep n (setvm v mo) rsp (setvm v mo') evs.
Proof.
  intros n v mo rsp mo' evs Hn H. destruct n; try contradiction; clear Hn; cbn [nstep] in *.
  all: unfold write_result, open_result, openw_result, lseek_result in *.
  all: change (m_fds (setvm v mo)) with (m_fds mo); change (m_fs (setvm v mo)) with (m_fs mo);
       try change (write_dirref ?p (setvm v mo)) with (write_dirref p mo).
  all: nstep_destr; solve [solve_side].
Qed.

Lemma nstep_vm_same : forall n mo rsp mo' evs,
  fsnode n -> nstep n mo rsp mo' evs -> m_vm mo' = m_vm mo.
Proof.
  intros n mo rsp mo' evs Hn H. destruct n; try contradiction; clear Hn; cbn [nstep] in *.
  all: unfold write_result, open_result, openw_result, lseek_result in *.
  all: nstep_destr; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_of_setvm : forall n v mo rsp m' evs,
  fsnode n -> nstep n (setvm v mo) rsp m' evs ->
  nstep n mo rsp (setvm (m_vm mo) m') evs /\ m' = setvm v (setvm (m_vm mo) m').
Proof.
  intros n v mo rsp m' evs Hn H. split.
  - apply (nstep_setvm n (m_vm mo)) in H; [|exact Hn]. rewrite setvm_setvm, setvm_id in H. exact H.
  - rewrite setvm_setvm. pose proof (nstep_vm_same _ _ _ _ _ Hn H) as E. rewrite m_vm_setvm in E.
    rewrite <- E. symmetry. apply setvm_id.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lf_setvm : forall mo, lf mo = setvm (mkVmState (m_vmmaps mo) [] []) mo.
Proof. reflexivity. Qed.

Lemma WB_lf : forall lz mat mo, WB lz mat (lf mo) = with_vm_backing lz mat mo.
Proof. reflexivity. Qed.

Lemma fs_nsafe_lf : forall n mo, fsnode n -> nsafe n mo -> nsafe n (lf mo).
Proof. intros n mo Hn H. destruct n; try contradiction; exact H. Qed.

Lemma fs_at_sysno : forall segs n ms, fsnode n -> at_node segs n ms ->
  forall x8, ms_svc_pending ms = Some x8 -> fs_sysno (bv_unsigned x8) = true /\ alloc_no (bv_unsigned x8) = false.
Proof.
  intros segs n ms Hn Hat x8 Hx. destruct n; try contradiction; cbn [at_node] in Hat;
    rewrite (proj1 Hat) in Hx; injection Hx as <-; split; reflexivity.
Qed.

Section FS.
Variable segs : list Segment.
Variable NMAX : nat.
Variable SHM : list (Z * Z).

(* [comment removed for export] *)
Definition fs_cov : Prop := forall n RNG ms mo x8 eff mo' evs,
  fsnode n -> at_nodeA segs n RNG ms -> ms_svc_pending ms = Some x8 ->
  minv mo -> m_halted mo = None -> nsafe n mo ->
  syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
  Forall (acc_in RNG) (syscall_effect_accesses eff).

Hypothesis COV : fs_cov.

Section Common.
  Variables (A : alw) (RNG : footprint) (n : node) (ms : machine_state) (mo mo_ : Model).
  Hypothesis Hfs : fsnode n.
  Hypothesis Hat : at_nodeA segs n RNG ms.
  Hypothesis Hh : m_halted mo = None.
  Hypothesis Hminv : minvA SHM mo.
  Hypothesis Hsafe : nsafeA NMAX SHM n mo.
  Hypothesis FOK : footprint_ok (m_vm_lazy mo) A RNG.
  Hypothesis MR : mrel A mo mo_.
  Hypothesis INV : ainv (m_vm_lazy mo) A NMAX mo_.

  Let TW := lf mo.
  Let mat := m_vm_materialized mo_.
  Let lz := m_vm_lazy mo.

  #[using="A MR"] Lemma fs_mo_ : mo_ = WB lz mat TW.
  Proof. unfold TW. rewrite WB_lf. exact (proj1 MR). Qed.

  #[using="segs NMAX SHM RNG ms mo Hfs Hat Hsafe"] Lemma fs_notexit : match n with NExit _ => False | _ => True end.
  Proof. destruct n; try exact I; contradiction. Qed.

  #[using="NMAX SHM RNG Hfs Hat Hh Hminv Hsafe"] Lemma fs_facts : node_facts_cfg segs (nstep n) ms TW.
  Proof.
    apply all_facts; [exact fs_notexit | apply at_nodeA_at_node with (RNG := RNG); exact Hat | exact (proj1 Hminv)
                     | exact Hh | apply fs_nsafe_lf; [exact Hfs| exact (proj1 Hsafe)]].
  Qed.

  (* [comment removed for export] *)
  Definition canon_of (m0' : Model) : Model := setvm (m_vm mo) m0'.

  #[using="Hfs"] Lemma fs_canon_nstep : forall rsp m0' evs, nstep n TW rsp m0' evs ->
    nstep n mo rsp (canon_of m0') evs /\ m0' = lf (canon_of m0') /\ m_vm (canon_of m0') = m_vm mo.
  Proof.
    intros rsp m0' evs H. unfold TW in H. rewrite lf_setvm in H.
    destruct (nstep_of_setvm _ _ _ _ _ _ Hfs H) as [H1 H2]. split; [exact H1|]. split; [| reflexivity].
    rewrite H2 at 1. unfold canon_of. rewrite setvm_setvm. reflexivity.
  Qed.

  #[using="Type"] Lemma fs_WB_canon : forall m0', m0' = lf (canon_of m0') -> WB lz mat m0' = MX (canon_of m0') mat.
  Proof.
    intros m0' E. rewrite E, WB_lf. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="RNG n Hfs Hat"] Lemma fs_nospur : forall x8 M eff, ms_svc_pending ms = Some x8 -> ~ spurious_refusal_cfg CFG (sys_input segs ms x8) M eff.
  Proof.
    intros x8 M eff Hx. apply spurious_refusal_family_on. rewrite injected_family_off_CFG, in_sysno_si.
    exact (proj2 (fs_at_sysno segs n ms Hfs (at_nodeA_at_node _ _ _ _ Hat) x8 Hx)).
  Qed.

  #[using="RNG n Hfs Hat"] Lemma fs_fssys : forall x8, ms_svc_pending ms = Some x8 -> fs_sysno (bv_unsigned (in_sysno (sys_input segs ms x8))) = true.
  Proof. intros x8 Hx. rewrite in_sysno_si. exact (proj1 (fs_at_sysno segs n ms Hfs (at_nodeA_at_node _ _ _ _ Hat) x8 Hx)). Qed.

  (* [comment removed for export] *)
  #[using="MR INV"] Lemma fs_ainv_succ : forall m0', m_vm (canon_of m0') = m_vm mo -> ainv lz A NMAX (MX (canon_of m0') mat).
  Proof.
    intros m0' VM. destruct INV as [LZ ND AW FIN ROOM].
    pose proof (same_but_mat_frame _ _ (proj1 MR)) as (_ & VMM & _).
    pose proof (same_but_mat_nonlazy _ _ (proj1 MR)) as NL.
    constructor.
    - rewrite m_vm_lazy_MX. unfold m_vm_lazy, lz. rewrite VM. reflexivity.
    - rewrite m_vm_materialized_MX. exact ND.
    - rewrite m_vm_materialized_MX. exact AW.
    - exact FIN.
    - rewrite nonlazy_bytes_MX, m_vmmaps_MX. rewrite NL, VMM in ROOM.
      unfold nonlazy_bytes, m_vmmaps, m_vm_lazy in *. rewrite VM. exact ROOM.
  Qed.

  (* [comment removed for export] *)
  #[using="NMAX SHM COV RNG n Hfs Hat Hh Hminv Hsafe FOK MR INV"] Lemma fs_mat : forall x8 eff m0' evs,
    ms_svc_pending ms = Some x8 -> syscall_spec (sys_input segs ms x8) TW (Ok eff m0' evs) ->
    m0' = lf (canon_of m0') -> m_vm (canon_of m0') = m_vm mo ->
    exists mo'', materialize_model_accesses (WB lz mat m0') (syscall_effect_accesses eff) = Some mo'' /\ mrel A (canon_of m0') mo''.
  Proof.
    intros x8 eff m0' evs Hx Hsp E VM. rewrite (fs_WB_canon m0' E).
    pose proof (COV n RNG ms TW x8 eff m0' evs Hfs Hat Hx (proj1 Hminv) Hh
                  (fs_nsafe_lf _ _ Hfs (proj1 Hsafe)) Hsp) as FA.
    destruct (account_ok lz A NMAX _ _ (fs_ainv_succ m0' VM) (accesses_ok_of_footprint _ _ _ _ FOK FA))
      as (mo'' & Hm & INV'' & SB).
    exists mo''. split; [exact Hm|].
    split; [eapply same_but_mat_trans; [apply same_but_mat_MX| exact SB]|].
    split; [unfold m_vm_materialized; rewrite VM; exact (proj1 (proj2 MR))|].
    destruct INV'' as [_ ND'' AW'' _ _]. auto.
  Qed.

  (* [comment removed for export] *)

  #[using="NMAX SHM COV RNG Hfs Hat Hh Hminv Hsafe FOK MR INV TW mat lz"] Lemma fs_complete : forall evs X,
    sstep_cfg segs CFG (mkCfg ms mo_) evs X ->
    exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstep n mo rsp mo' evs /\ mrel A mo' mo_'.
  Proof.
    intros evs X Hss. destruct fs_facts as (x8 & Hx & Hc & Hs & Hnu & Hnh & Hpres & Hprog).
    pose proof (fs_fssys x8 Hx) as FS.
    destruct (sstep_svc_inv segs _ _ _ _ _ Hx Hss)
      as [(eff & moX & mo'' & Hsp & Hns & Hh' & Hmat & ->)
         | [(eff & moX & evs0 & Hsp & Hns & Hh' & Hmat & -> & ->)
         | [(eff & moX & evs0 & code & Hsp & Hh' & -> & ->)
         | [(eff & moX & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
    - rewrite fs_mo_ in Hsp. apply (proj1 (spec_WB_ok lz mat _ _ _ _ _ FS)) in Hsp as (m0' & Hsp0 & ->).
      destruct (Hc _ _ _ Hsp0 (fs_nospur x8 _ _ Hx)) as (rsp & Heq & HP).
      destruct (fs_canon_nstep _ _ _ HP) as (HN & E & VM).
      destruct (fs_mat x8 eff m0' evs Hx Hsp0 E VM) as (mo2 & Hm2 & MR2).
      rewrite Hm2 in Hmat. injection Hmat as <-.
      exists rsp, (canon_of m0'), mo2. rewrite Heq. auto.
    - exfalso. rewrite fs_mo_ in Hsp. apply (proj1 (spec_WB_ok lz mat _ _ _ _ _ FS)) in Hsp as (m0' & Hsp0 & ->).
      destruct (Hc _ _ _ Hsp0 (fs_nospur x8 _ _ Hx)) as (rsp & Heq & HP).
      destruct (fs_canon_nstep _ _ _ HP) as (HN & E & VM).
      destruct (fs_mat x8 eff m0' evs0 Hx Hsp0 E VM) as (mo2 & Hm2 & MR2). congruence.
    - exfalso. rewrite fs_mo_ in Hsp. apply (proj1 (spec_WB_ok lz mat _ _ _ _ _ FS)) in Hsp as (m0' & Hsp0 & ->).
      pose proof (Hnh _ _ _ Hsp0) as E0. change (m_halted (WB lz mat m0')) with (m_halted m0') in Hh'. congruence.
    - exfalso. rewrite fs_mo_ in Hsp. apply (proj1 (spec_WB_ok lz mat _ _ _ _ _ FS)) in Hsp as (m0' & Hsp0 & ->).
      pose proof (m_killed_of_m_halted_none _ (Hnh _ _ _ Hsp0)) as E0.
      change (m_killed (WB lz mat m0')) with (m_killed m0') in Hk. congruence.
    - exfalso. rewrite fs_mo_ in Hsp. apply (proj1 (spec_WB_unmodeled lz mat _ _ FS)) in Hsp. exact (Hnu Hsp).
  Qed.

  #[using="NMAX COV RNG Hfs Hat Hh Hminv Hsafe FOK MR INV TW mat lz"] Lemma fs_sound : forall rsp mo' evs, nstep n mo rsp mo' evs ->
    m_halted mo' = None /\ minvA SHM mo' /\
    exists mo_', sstep_cfg segs CFG (mkCfg ms mo_) evs (SNext (mkCfg (nret ms rsp) mo_')) /\ mrel A mo' mo_'.
  Proof.
    intros rsp mo' evs HN. destruct fs_facts as (x8 & Hx & Hc & Hs & Hnu & Hnh & Hpres & Hprog).
    pose proof (fs_fssys x8 Hx) as FS.
    pose proof (nstep_vm_same _ _ _ _ _ Hfs HN) as VM.
    assert (HT : nstep n TW rsp (lf mo') evs).
    { unfold TW. rewrite !lf_setvm. unfold m_vmmaps. rewrite VM. apply nstep_setvm; [exact Hfs| exact HN]. }
    destruct (Hpres _ _ _ HT) as [Hh0 Hminv0].
    split; [exact Hh0|]. split.
    { split; [exact Hminv0|]. split.
      - unfold m_vm_materialized. rewrite VM. exact (proj1 (proj2 Hminv)).
      - unfold shinv, m_vmmaps. rewrite VM. exact (proj2 (proj2 Hminv)). }
    destruct (Hs _ _ _ HT) as (eff & Heq & Hsp0 & _).
    assert (EC : canon_of (lf mo') = mo').
    { unfold canon_of. rewrite lf_setvm, setvm_setvm, <- VM. apply setvm_id. }
    assert (E : lf mo' = lf (canon_of (lf mo'))) by (rewrite EC; reflexivity).
    assert (VMc : m_vm (canon_of (lf mo')) = m_vm mo) by reflexivity.
    destruct (fs_mat x8 eff (lf mo') evs Hx Hsp0 E VMc) as (mo2 & Hm2 & MR2). rewrite EC in MR2.
    exists mo2. split; [|exact MR2].
    rewrite <- Heq. unfold nret.
    eapply sstep_cfg_syscall with (model' := WB lz mat (lf mo')).
    - rewrite (mrel_halted _ _ _ MR). exact Hh.
    - exact Hx.
    - rewrite fs_mo_. apply (proj2 (spec_WB_ok lz mat _ _ _ _ _ FS)). exists (lf mo'). split; [exact Hsp0| reflexivity].
    - apply fs_nospur. exact Hx.
    - exact Hh0.
    - exact Hm2.
  Qed.

  #[using="segs NMAX SHM RNG ms Hfs Hat Hh Hminv Hsafe TW"] Lemma fs_progress : exists rsp mo' evs, nstep n mo rsp mo' evs.
  Proof.
    destruct fs_facts as (x8 & Hx & Hc & Hs & Hnu & Hnh & Hpres & (rsp & m0' & evs & HP)).
    exists rsp, (canon_of m0'), evs. exact (proj1 (fs_canon_nstep _ _ _ HP)).
  Qed.

End Common.
End FS.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_b_model : forall i m m' ret, bv_unsigned (in_sysno i) <> 214 -> refusal_b i m ret = refusal_b i m' ret.
Proof. intros i m m' ret H. unfold refusal_b. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma spec_of_check_eq : forall i1 i2 m,
  (forall e, check_syscall i1 e m = check_syscall i2 e m) -> forall o, syscall_spec i1 m o <-> syscall_spec i2 m o.
Proof.
  intros i1 i2 m H [eff m' evs|].
  - rewrite <- !check_syscall_ok_iff, H. reflexivity.
  - rewrite <- !(check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])), H. reflexivity.
Qed.

Definition eff_quiet (eff : resp) (evs : list event) : Prop :=
  syscall_effect_accesses eff = [] /\ evs = [].

Section MM.
Variable segs : list Segment.
Variable NMAX : nat.
Variable SHM : list (Z * Z).
Variables (A : alw) (RNG : footprint) (n : node) (ms : machine_state) (mo mo_ : Model).
Hypothesis Hh : m_halted mo = None.
Hypothesis Hminv : minvA SHM mo.
Hypothesis MR : mrel A mo mo_.
Hypothesis INV : ainv (m_vm_lazy mo) A NMAX mo_.

Let mat := m_vm_materialized mo_.
#[using="A MR"] Lemma mm_mo_ : mo_ = MX mo mat. Proof. exact (proj1 MR). Qed.
#[using="A mo_ MR"] Lemma mm_CAN : m_vm_materialized mo = []. Proof. exact (proj1 (proj2 MR)). Qed.
#[using="A mo INV"] Lemma mm_LEN : (length mat <= NMAX)%nat. Proof. exact (ainv_len _ _ _ _ INV). Qed.

(* [comment removed for export] *)
Variables (i : SyscallInput) (x8 : word) (chk : resp -> Model -> check_result).
Hypothesis Hin : node_input n = Some i.
Hypothesis Hnstep : forall eff m' evs, nstep n mo eff m' evs <->
  (evs = [] /\ syscall_spec i mo (Ok eff m' evs) /\ ~ spurious_refusal_cfg CFG i mo eff).
Hypothesis Hsvc : ms_svc_pending ms = Some x8.
Hypothesis Hno : in_sysno i = x8.
Hypothesis Hnb : bv_unsigned x8 <> 214.
Hypothesis Ha0 : in_arg i 0 = areg ms 10.
Hypothesis Hchk_ms : forall e M, check_syscall (sys_input segs ms x8) e M = chk e M.
Hypothesis Hchk_i : forall e M, check_syscall i e M = chk e M.
Hypothesis Hx : forall e, relX mo mat (chk e (MX mo mat)) (chk e mo).
Hypothesis Hq : forall e M M' evs, chk e M = CheckOk M' evs -> eff_quiet e evs.
Hypothesis Hshape : forall e m' evs, chk e mo = CheckOk m' evs -> vm_only mo m' /\ shinv SHM m'.
Hypothesis Hlive : spec_live i mo.
Hypothesis Hdec : refusal_decided CFG i mo.

#[using="A MR mat chk Hno Hnb Ha0 Hchk_ms Hchk_i Hx"] Lemma mm_spur : forall eff,
  spurious_refusal_cfg CFG (sys_input segs ms x8) mo_ eff <-> spurious_refusal_cfg CFG i mo eff.
Proof.
  intros eff. rewrite (spurious_ext (sys_input segs ms x8) i mo_ eff).
  2:{ rewrite in_sysno_si. symmetry. exact Hno. }
  2:{ rewrite in_a0_si. symmetry. exact Ha0. }
  2:{ apply spec_of_check_eq. intros e. rewrite Hchk_ms, Hchk_i. reflexivity. }
  assert (NB : bv_unsigned (in_sysno i) <> 214) by (rewrite Hno; exact Hnb).
  rewrite mm_mo_. unfold spurious_refusal_cfg.
  split; intros (Hoff & Href & eff' & m' & evs' & Hsp & Hnr); (split; [exact Hoff|]); split.
  - rewrite (refusal_b_model i mo (MX mo mat)); [exact Href| exact NB].
  - apply check_syscall_ok_iff in Hsp. rewrite Hchk_i in Hsp. pose proof (Hx eff') as R. rewrite Hsp in R.
    apply relX_ok_l in R as (m0 & f & Hc & _). exists eff', m0, evs'.
    split; [apply check_syscall_ok_iff; rewrite Hchk_i; exact Hc|]. rewrite (refusal_b_model i mo (MX mo mat)); [exact Hnr| exact NB].
  - rewrite (refusal_b_model i (MX mo mat) mo); [exact Href| exact NB].
  - apply check_syscall_ok_iff in Hsp. rewrite Hchk_i in Hsp. pose proof (Hx eff') as R. rewrite Hsp in R.
    apply relX_ok_r in R as (_ & f & Hc & _). exists eff', (MX m' (List.filter f mat)), evs'.
    split; [apply check_syscall_ok_iff; rewrite Hchk_i; exact Hc|]. rewrite (refusal_b_model i (MX mo mat) mo); [exact Hnr| exact NB].
Qed.

#[using="NMAX MR INV"] Lemma mm_mrel_succ : forall m f, m_vm_materialized m = List.filter f (m_vm_materialized mo) -> mrel A m (MX m (List.filter f mat)).
Proof.
  intros m f Hm. split; [apply same_but_mat_MX|]. split; [rewrite Hm, mm_CAN; reflexivity|].
  rewrite m_vm_materialized_MX. destruct INV as [_ ND AL _ _]. split; [apply NoDup_filter; exact ND|].
  intros p Hp. apply AL. apply (incl_filter f mat p Hp).
Qed.

#[using="NMAX SHM Hh MR INV mat i x8 chk Hnstep Hsvc Hno Hnb Ha0 Hchk_ms Hchk_i Hx Hq Hshape Hlive"] Lemma mm_complete : forall evs X,
  sstep_cfg segs CFG (mkCfg ms mo_) evs X ->
  exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstep n mo rsp mo' evs /\ mrel A mo' mo_'.
Proof.
  intros evs X Hss.
  destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hss)
    as [(eff & moX & mo'' & Hsp & Hns & Hh' & Hmat & ->)
       | [(eff & moX & evs0 & Hsp & Hns & Hh' & Hmat & -> & ->)
       | [(eff & moX & evs0 & code & Hsp & Hh' & -> & ->)
       | [(eff & moX & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
  all: try (apply check_syscall_ok_iff in Hsp; rewrite Hchk_ms, mm_mo_ in Hsp;
            pose proof (Hx eff) as R; rewrite Hsp in R; apply relX_ok_l in R as (m & f & Hc & S & -> & Hm);
            pose proof (Hq _ _ _ _ Hc) as (Hacc & Eevs); pose proof (Hshape _ _ _ Hc) as (VO & SH)).
  - subst evs. rewrite Hacc, materialize_nil in Hmat. injection Hmat as <-.
    exists eff, m, (MX m (List.filter f mat)). split; [reflexivity|]. split; [| apply mm_mrel_succ; exact Hm].
    apply Hnstep. split; [reflexivity|]. split; [apply check_syscall_ok_iff; rewrite Hchk_i; exact Hc|].
    intros Hs. apply Hns. apply mm_spur. exact Hs.
  - exfalso. rewrite Hacc, materialize_nil in Hmat. discriminate.
  - exfalso. rewrite m_halted_MX in Hh'. destruct VO as (_ & _ & E & _). congruence.
  - exfalso. destruct VO as (_ & _ & E & _). rewrite Hh in E.
    pose proof (m_killed_of_m_halted_none _ E) as K. change (m_killed (MX m (List.filter f mat))) with (m_killed m) in Hk. congruence.
  - exfalso. apply (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])) in Hsp. rewrite Hchk_ms, mm_mo_ in Hsp.
    pose proof (Hx (mkEffect (Z_to_bv 64 0) [] [])) as R. apply relX_unmodeled in R. apply R in Hsp.
    apply (proj1 Hlive). apply (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])). rewrite Hchk_i. exact Hsp.
Qed.

#[using="NMAX Hh Hminv MR INV mat i x8 chk Hnstep Hsvc Hno Hnb Ha0 Hchk_ms Hchk_i Hx Hq Hshape"] Lemma mm_sound : forall rsp mo' evs, nstep n mo rsp mo' evs ->
  m_halted mo' = None /\ minvA SHM mo' /\
  exists mo_', sstep_cfg segs CFG (mkCfg ms mo_) evs (SNext (mkCfg (nret ms rsp) mo_')) /\ mrel A mo' mo_'.
Proof.
  intros rsp mo' evs HN. apply Hnstep in HN as (-> & Hsp & Hns).
  apply check_syscall_ok_iff in Hsp. rewrite Hchk_i in Hsp.
  pose proof (Hx rsp) as R. rewrite Hsp in R. apply relX_ok_r in R as (S & f & Hc & Hm).
  pose proof (Hq _ _ _ _ Hsp) as (Hacc & _). pose proof (Hshape _ _ _ Hsp) as (VO & SH).
  assert (Hh' : m_halted mo' = None) by (destruct VO as (_ & _ & E & _); congruence).
  split; [exact Hh'|]. split.
  { split; [| split; [rewrite Hm, mm_CAN; reflexivity| exact SH]].
    eapply (minv_vm_only (lf mo) (lf mo')); [| split; reflexivity | exact (proj1 Hminv)].
    destruct VO as (V1 & V2 & V3 & V4 & V5). repeat split; assumption. }
  exists (MX mo' (List.filter f mat)). split; [| apply mm_mrel_succ; exact Hm].
  unfold nret.
  eapply (sstep_cfg_syscall segs CFG ms mo_ x8 rsp (MX mo' (List.filter f mat)) (MX mo' (List.filter f mat)) []).
  - rewrite (mrel_halted _ _ _ MR). exact Hh.
  - exact Hsvc.
  - apply check_syscall_ok_iff. rewrite Hchk_ms, mm_mo_. exact Hc.
  - intros Hs. apply Hns. apply mm_spur. exact Hs.
  - rewrite m_halted_MX. exact Hh'.
  - rewrite Hacc. apply materialize_nil.
Qed.

#[using="i chk Hnstep Hchk_i Hq Hlive Hdec"] Lemma mm_progress : exists rsp mo' evs, nstep n mo rsp mo' evs.
Proof.
  destruct Hlive as [Hnu [[eff m' evs|] Ho]]; [| exfalso; exact (Hnu Ho)].
  destruct (admissible_exists i mo eff m' evs Hdec Ho) as (eff1 & m1 & evs1 & Hsp1 & Hns1).
  pose proof Hsp1 as Hc. apply check_syscall_ok_iff in Hc. rewrite Hchk_i in Hc.
  pose proof (Hq _ _ _ _ Hc) as (_ & ->).
  exists eff1, m1, []. apply Hnstep. auto.
Qed.

End MM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_syscall_mmap : forall i e M, bv_unsigned (in_sysno i) = 222 ->
  check_syscall i e M = Mmap.check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) e M.
Proof.
  intros i e M H. unfold check_syscall. rewrite H.
  change (lookup_ca checked_table 222) with (Some arm_mmap). cbv beta iota. apply ca_check_arm_mmap.
Qed.

Lemma check_syscall_munmap : forall i e M, bv_unsigned (in_sysno i) = 215 ->
  check_syscall i e M = Mmap.check_munmap (in_arg i 0) (in_arg i 1) e M.
Proof.
  intros i e M H. unfold check_syscall. rewrite H.
  change (lookup_ca checked_table 215) with (Some arm_munmap). cbv beta iota. apply ca_check_arm_munmap.
Qed.

Lemma check_mmap_quiet : forall a l p f d off e M M' evs,
  Mmap.check_mmap a l p f d off e M = CheckOk M' evs -> eff_quiet e evs.
Proof.
  intros a l p f d off e M M' evs H. unfold Mmap.check_mmap in H.
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = CheckOk _ _ => discriminate H
          | CheckUnmodeled = CheckOk _ _ => discriminate H
          | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (-> & _ & ->)
          | (if ?x then _ else _) = _ => destruct x
          | (match ?x with _ => _ end) = _ => destruct x
          end).
  all: try (injection H as _ <-). all: split; reflexivity.
Qed.

Lemma check_munmap_quiet : forall a l e M M' evs,
  Mmap.check_munmap a l e M = CheckOk M' evs -> eff_quiet e evs.
Proof.
  intros a l e M M' evs H. unfold Mmap.check_munmap in H.
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = CheckOk _ _ => discriminate H
          | CheckUnmodeled = CheckOk _ _ => discriminate H
          | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (-> & _ & ->)
          | (if ?x then _ else _) = _ => destruct x
          | (match ?x with _ => _ end) = _ => destruct x
          end).
  all: try (injection H as _ <-). all: split; reflexivity.
Qed.

Section MMInst.
Variable segs : list Segment.
Variable NMAX : nat.
Variable SHM : list (Z * Z).
Variables (A : alw) (RNG : footprint) (ms : machine_state) (mo mo_ : Model).
Hypothesis Hh : m_halted mo = None.
Hypothesis Hminv : minvA SHM mo.
Hypothesis MR : mrel A mo mo_.
Hypothesis INV : ainv (m_vm_lazy mo) A NMAX mo_.

Definition three (n : node) : Prop :=
  (forall evs X, sstep_cfg segs CFG (mkCfg ms mo_) evs X ->
     exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstep n mo rsp mo' evs /\ mrel A mo' mo_')
  /\ (forall rsp mo' evs, nstep n mo rsp mo' evs ->
        m_halted mo' = None /\ minvA SHM mo' /\
        exists mo_', sstep_cfg segs CFG (mkCfg ms mo_) evs (SNext (mkCfg (nret ms rsp) mo_')) /\ mrel A mo' mo_')
  /\ (exists rsp mo' evs, nstep n mo rsp mo' evs).

#[using="Hh Hminv MR INV"] Lemma mmapA_three : forall addr len prot flags,
  at_node segs (NMmap addr len prot flags) ms -> nsafeA NMAX SHM (NMmap addr len prot flags) mo ->
  three (NMmap addr len prot flags).
Proof.
  intros addr len prot flags (Hsvc & Hnr & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) (Hsafe & Hslack & Hap).
  cbn [nsafe node_input] in Hsafe. destruct Hsafe as [Hlive Hdec].
  set (n := NMmap addr len prot flags).
  set (i := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]).
  set (chk := fun e M => Mmap.check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                           (Z_to_bv 64 (-1)) (Z_to_bv 64 0) e M).
  assert (Hchk_ms : forall e M, check_syscall (sys_input segs ms (Z_to_bv 64 222)) e M = chk e M).
  { intros e M. rewrite check_syscall_mmap by (rewrite in_sysno_si; reflexivity).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }
  assert (Hchk_i : forall e M, check_syscall i e M = chk e M).
  { intros e M. rewrite check_syscall_mmap by reflexivity. reflexivity. }
  assert (Hx : forall e, relX mo (m_vm_materialized mo_) (chk e (MX mo (m_vm_materialized mo_))) (chk e mo)).
  { intros e. unfold chk. cbn [nslack] in Hslack. destruct Hslack as (S1 & S2 & S3).
    apply (check_mmap_X NMAX); [exact (proj1 (proj2 MR)) | exact (ainv_len _ _ _ _ INV) | exact S1 | exact S2 | exact S3]. }
  assert (Hshape : forall e m' evs, chk e mo = CheckOk m' evs -> vm_only mo m' /\ shinv SHM m').
  { intros e m' evs Hc. split.
    - assert (Hsp : syscall_spec i mo (Ok e m' evs)) by (apply check_syscall_ok_iff; rewrite Hchk_i; exact Hc).
      rewrite syscall_spec_222 in Hsp by reflexivity.
      exact (proj1 (mmap_shape _ _ _ _ _ _ _ _ _ _ _ (noreserve_clear flags Hnr) Hsp)).
    - eapply (check_mmap_shinv SHM); [exact Hc| exact (proj2 (proj2 Hminv))| exact Hap]. }
  split; [| split].
  - eapply (mm_complete segs NMAX) with (i := i) (chk := chk) (x8 := Z_to_bv 64 222) (SHM := SHM); try eassumption;
      first [ reflexivity | (intros; unfold n, i; cbn [nstep node_input]; tauto) | discriminate
            | (symmetry; exact Ha0) | (intros e M M' evs Hc; eapply check_mmap_quiet; exact Hc) ].
  - eapply (mm_sound segs NMAX) with (i := i) (chk := chk) (x8 := Z_to_bv 64 222); try eassumption;
      first [ reflexivity | (intros; unfold n, i; cbn [nstep node_input]; tauto) | discriminate
            | (symmetry; exact Ha0) | (intros e M M' evs Hc; eapply check_mmap_quiet; exact Hc) ].
  - eapply mm_progress with (i := i) (chk := chk); try eassumption;
      first [ (intros; unfold n, i; cbn [nstep node_input]; tauto) | (intros e M M' evs Hc; eapply check_mmap_quiet; exact Hc) ].
Qed.

#[using="Hh Hminv MR INV"] Lemma munmapA_three : forall addr len,
  at_node segs (NMunmap addr len) ms -> nsafeA NMAX SHM (NMunmap addr len) mo ->
  three (NMunmap addr len).
Proof.
  intros addr len (Hsvc & Ha0 & Ha1) (Hsafe & Hslack & Hap).
  cbn [nsafe node_input] in Hsafe. destruct Hsafe as [Hlive Hdec].
  set (n := NMunmap addr len).
  set (i := pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]).
  set (chk := fun e M => Mmap.check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) e M).
  assert (Hchk_ms : forall e M, check_syscall (sys_input segs ms (Z_to_bv 64 215)) e M = chk e M).
  { intros e M. rewrite check_syscall_munmap by (rewrite in_sysno_si; reflexivity).
    rewrite in_a0_si, in_a1_si, Ha0, Ha1. reflexivity. }
  assert (Hchk_i : forall e M, check_syscall i e M = chk e M).
  { intros e M. rewrite check_syscall_munmap by reflexivity. reflexivity. }
  assert (Hx : forall e, relX mo (m_vm_materialized mo_) (chk e (MX mo (m_vm_materialized mo_))) (chk e mo)).
  { intros e. unfold chk. apply check_munmap_X. }
  assert (Hshape : forall e m' evs, chk e mo = CheckOk m' evs -> vm_only mo m' /\ shinv SHM m').
  { intros e m' evs Hc. split.
    - assert (Hsp : syscall_spec i mo (Ok e m' evs)) by (apply check_syscall_ok_iff; rewrite Hchk_i; exact Hc).
      rewrite syscall_spec_215 in Hsp by reflexivity.
      exact (proj1 (munmap_shape _ _ _ _ _ _ _ Hsp)).
    - eapply (check_munmap_shinv SHM); [exact Hc| exact (proj2 (proj2 Hminv))| exact Hap]. }
  split; [| split].
  - eapply (mm_complete segs NMAX) with (i := i) (chk := chk) (x8 := Z_to_bv 64 215) (SHM := SHM); try eassumption;
      first [ reflexivity | (intros; unfold n, i; cbn [nstep node_input]; tauto) | discriminate
            | (symmetry; exact Ha0) | (intros e M M' evs Hc; eapply check_munmap_quiet; exact Hc) ].
  - eapply (mm_sound segs NMAX) with (i := i) (chk := chk) (x8 := Z_to_bv 64 215); try eassumption;
      first [ reflexivity | (intros; unfold n, i; cbn [nstep node_input]; tauto) | discriminate
            | (symmetry; exact Ha0) | (intros e M M' evs Hc; eapply check_munmap_quiet; exact Hc) ].
  - eapply mm_progress with (i := i) (chk := chk); try eassumption;
      first [ (intros; unfold n, i; cbn [nstep node_input]; tauto) | (intros e M M' evs Hc; eapply check_munmap_quiet; exact Hc) ].
Qed.

End MMInst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_cases : forall n,
  fsnode n \/ (exists a l p f, n = NMmap a l p f) \/ (exists a l, n = NMunmap a l) \/ (exists c, n = NExit c)
  \/ (forall segs RNG ms, ~ at_nodeA segs n RNG ms).
Proof.
  intros n. destruct n; try (left; exact I).
  all: try (right; right; right; right; intros segs RNG ms H; exact H).
  - right; right; right; left. eexists; reflexivity.
  - right; left. do 4 eexists; reflexivity.
  - right; right; left. do 2 eexists; reflexivity.
Qed.

Theorem nodesA_sound : forall segs NMAX SHM, fs_cov segs ->
  node_soundA node segs (at_nodeA segs) (npeekA segs) nstepA nexitA (minvA SHM) (nsafeA NMAX SHM) NMAX.
Proof.
  intros segs NMAX SHM COV. constructor.
  - intros n RNG ms H. exact (at_nodeA_pending segs n RNG ms H).
  - (* [comment removed for export] *)
    intros n RNG A ms mo mo_ evs X Hat Hh Hminv Hsafe FOK MR INV Hss. change OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG with CFG in Hss.
    destruct (node_cases n) as [Hfs | [(a & l & p & f & ->) | [(a & l & ->) | [(c & ->) | Hno]]]].
    + left. exact (fs_complete segs NMAX SHM COV A RNG n ms mo mo_ Hfs Hat Hh Hminv Hsafe FOK MR INV evs X Hss).
    + left. exact (proj1 (mmapA_three segs NMAX SHM A ms mo mo_ Hh Hminv MR INV a l p f (at_nodeA_at_node _ _ _ _ Hat) Hsafe) evs X Hss).
    + left. exact (proj1 (munmapA_three segs NMAX SHM A ms mo mo_ Hh Hminv MR INV a l (at_nodeA_at_node _ _ _ _ Hat) Hsafe) evs X Hss).
    + right. pose proof (at_nodeA_at_node _ _ _ _ Hat) as Hat0.
      assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
      destruct (exit_node_facts segs ms mo_ c Hat0 Hh_) as [Hc _]. destruct (Hc _ _ Hss) as [-> ->].
      exists (exit_code c), (with_halted (exit_code c) mo), (with_halted (exit_code c) mo_).
      split; [reflexivity|]. split; [split; reflexivity|]. split; [| reflexivity].
      change (m_fs (with_halted (exit_code c) mo)) with (m_fs mo). rewrite (mrel_fs _ _ _ MR). reflexivity.
    + exfalso. exact (Hno _ _ _ Hat).
  - (* [comment removed for export] *)
    intros n RNG A ms mo mo_ rsp mo' evs Hat Hh Hminv Hsafe FOK MR INV HN. change OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG with CFG.
    destruct (node_cases n) as [Hfs | [(a & l & p & f & ->) | [(a & l & ->) | [(c & ->) | Hno]]]].
    + exact (fs_sound segs NMAX SHM COV A RNG n ms mo mo_ Hfs Hat Hh Hminv Hsafe FOK MR INV rsp mo' evs HN).
    + exact (proj1 (proj2 (mmapA_three segs NMAX SHM A ms mo mo_ Hh Hminv MR INV a l p f (at_nodeA_at_node _ _ _ _ Hat) Hsafe)) rsp mo' evs HN).
    + exact (proj1 (proj2 (munmapA_three segs NMAX SHM A ms mo mo_ Hh Hminv MR INV a l (at_nodeA_at_node _ _ _ _ Hat) Hsafe)) rsp mo' evs HN).
    + destruct HN.
    + exfalso. exact (Hno _ _ _ Hat).
  - (* [comment removed for export] *)
    intros n RNG A ms mo mo_ cw mo' Hat Hh Hminv Hsafe MR HX. change OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG with CFG.
    assert (Hc : exists c, n = NExit c) by (destruct n; try contradiction; eexists; reflexivity).
    destruct Hc as [c ->]. cbn [nexitA nexit] in HX. destruct HX as [-> ->].
    split; [reflexivity|].
    pose proof (at_nodeA_at_node _ _ _ _ Hat) as Hat0.
    assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
    exists (with_halted (exit_code c) mo_). split; [| reflexivity].
    change (m_fs (with_halted (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) mo)) with (m_fs mo).
    rewrite <- (mrel_fs _ _ _ MR). exact (proj2 (exit_node_facts segs ms mo_ c Hat0 Hh_)).
  - (* [comment removed for export] *)
    intros n RNG A ms mo mo_ Hat Hh Hminv Hsafe FOK MR INV.
    destruct (node_cases n) as [Hfs | [(a & l & p & f & ->) | [(a & l & ->) | [(c & ->) | Hno]]]].
    + left. eapply (fs_progress segs NMAX SHM); eassumption.
    + left. exact (proj2 (proj2 (mmapA_three segs NMAX SHM A ms mo mo_ Hh Hminv MR INV a l p f (at_nodeA_at_node _ _ _ _ Hat) Hsafe))).
    + left. exact (proj2 (proj2 (munmapA_three segs NMAX SHM A ms mo mo_ Hh Hminv MR INV a l (at_nodeA_at_node _ _ _ _ Hat) Hsafe))).
    + right. eexists _, _. split; reflexivity.
    + exfalso. exact (Hno _ _ _ Hat).
  - (* [comment removed for export] *)
    intros n f ms mo Hn. destruct n; try discriminate Hn. cbn [npeekA] in Hn. injection Hn as <-.
    cbn [nstepA nstep]. split; [reflexivity|]. split; [reflexivity|].
    exists (peekA_val segs ms addr). split; [apply peekA_val_range| reflexivity].
  - (* [comment removed for export] *)
    intros n f RNG ms Hn Hat. destruct n; try discriminate Hn. exact Hat.
Qed.
