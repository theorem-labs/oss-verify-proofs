(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RelSpec RelSpecMremap NodesM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From Stdlib Require Import Classical_Prop.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache.

Lemma spur_transfer : forall i i' m eff,
  bv_unsigned (in_sysno i) = bv_unsigned (in_sysno i') -> in_arg i 0 = in_arg i' 0 ->
  (forall o, syscall_spec i m o <-> syscall_spec i' m o) ->
  spurious_refusal_cfg fcfg i m eff -> spurious_refusal_cfg fcfg i' m eff.
Proof.
  intros i i' m eff Hn Ha Hs (Hoff & Hr & (eff' & m' & evs' & Hs' & Hr')).
  assert (Ef : injected_family_off fcfg i = injected_family_off fcfg i') by (unfold injected_family_off; rewrite Hn; reflexivity).
  assert (Er : forall r, refusal_b i m r = refusal_b i' m r) by (intros r; unfold refusal_b; rewrite Hn, Ha; reflexivity).
  split; [rewrite <- Ef; exact Hoff|]. split; [rewrite <- Er; exact Hr|].
  exists eff', m', evs'. split; [apply Hs; exact Hs' | rewrite <- Er; exact Hr'].
Qed.

Section OneNode.
Variable segs : list Segment.
Variable mo : Model.
Variable OUT : outcome SyscallEffect -> Prop.

Variable iP : SyscallInput -> Prop.
Hypothesis Hchar : forall i o, iP i -> (syscall_spec i mo o <-> OUT o).
Hypothesis HOUT : forall o, OUT o ->
  exists eff mo', o = Ok eff mo' [] /\ mo_ok mo' /\ vm_agree mo mo'.
Hypothesis Hmo : mo_ok mo.

Lemma one_model : forall i eff mo' evs, iP i ->
  syscall_spec i mo (Ok eff mo' evs) -> evs = [] /\ mo_ok mo' /\ vm_agree mo mo'.
Proof.
  intros i eff mo' evs Hi Hs. apply (Hchar i _ Hi) in Hs. destruct (HOUT _ Hs) as (eff1 & mo1 & E & Hok & Hva).
  apply Ok_inj in E as (_ & <- & ->). auto.
Qed.

Lemma one_progress : forall i, iP i -> (exists o, OUT o) ->
  exists eff mo' evs, evs = [] /\ syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg fcfg i mo eff.
Proof.
  intros i Hi [o Ho]. destruct (HOUT o Ho) as (eff & mo' & -> & _ & _).
  apply (Hchar i _ Hi) in Ho.
  destruct (classic (spurious_refusal_cfg fcfg i mo eff)) as [Hsp | Hns].
  - destruct Hsp as (_ & _ & (eff' & m' & evs' & Hs' & Hr')).
    destruct (one_model i eff' m' evs' Hi Hs') as (-> & _ & _).
    exists eff', m', []. split; [reflexivity|]. split; [exact Hs'|]. apply fcfg_nonref_nonspur. exact Hr'.
  - exists eff, mo', []. split; [reflexivity|]. split; [exact Ho | exact Hns].
Qed.

Variable ms : machine_state.
Variable x8 : word.
Hypothesis Hsvc : ms_svc_pending ms = Some x8.
Hypothesis Hsys : iP (sys_input segs ms x8).
Variable ipure : SyscallInput.
Hypothesis Hpure : iP ipure.
Hypothesis Hid : forall i i', iP i -> iP i' ->
  bv_unsigned (in_sysno i) = bv_unsigned (in_sysno i') /\ in_arg i 0 = in_arg i' 0.

Lemma one_transfer : forall o, syscall_spec ipure mo o <-> syscall_spec (sys_input segs ms x8) mo o.
Proof. intros o. rewrite (Hchar ipure o Hpure), (Hchar _ o Hsys). reflexivity. Qed.

Lemma one_nonspur_transfer : forall eff,
  ~ spurious_refusal_cfg fcfg ipure mo eff <-> ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo eff.
Proof.
  intros eff. destruct (Hid _ _ Hpure Hsys) as [Hn Ha]. split; intros H Hsp; apply H.
  - apply (spur_transfer _ _ mo eff (eq_sym Hn) (eq_sym Ha)); [intros o; symmetry; apply one_transfer | exact Hsp].
  - apply (spur_transfer _ _ mo eff Hn Ha); [apply one_transfer | exact Hsp].
Qed.

Lemma one_sound : forall eff mo' evs,
  evs = [] /\ syscall_spec ipure mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg fcfg ipure mo eff ->
  sstep_cfg segs fcfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')).
Proof.
  intros eff mo' evs (-> & Hs & Hns).
  destruct (one_model ipure eff mo' [] Hpure Hs) as (_ & Hok' & _).
  apply one_transfer in Hs. apply one_nonspur_transfer in Hns.
  apply (sstep_cfg_syscall segs fcfg ms mo x8 eff mo' mo' []).
  - apply (mo_ok_halted _ Hmo).
  - exact Hsvc.
  - exact Hs.
  - exact Hns.
  - apply (mo_ok_halted _ Hok').
  - apply materialize_model_accesses_no_lazy. apply (mo_ok_lazy _ Hok').
Qed.

Lemma one_complete : forall evs X,
  sstep_cfg segs fcfg (mkCfg ms mo) evs X ->
  exists eff mo', X = SNext (mkCfg (nret ms eff) mo')
    /\ (evs = [] /\ syscall_spec ipure mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg fcfg ipure mo eff).
Proof.
  intros evs X Hst. inversion Hst; subst; try congruence.
  -
    match goal with Hx : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in Hx; injection Hx as <- end.
    match goal with Hs : syscall_spec _ mo (Ok ?e ?m1 ?ev), Hn : ~ spurious_refusal_cfg fcfg _ mo ?e |- _ =>
      pose proof (one_model _ _ _ _ Hsys Hs) as (-> & Hok1 & _);
      apply one_transfer in Hs; apply one_nonspur_transfer in Hn;
      exists e, m1; split; [| split; [reflexivity | split; [exact Hs | exact Hn]]] end.
    match goal with Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
      rewrite (materialize_model_accesses_no_lazy m1 _ (mo_ok_lazy _ Hok1)) in Hm; injection Hm as <- end.
    reflexivity.
  -
    match goal with Hx : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in Hx; injection Hx as <- end.
    match goal with Hs : syscall_spec _ mo (Ok ?e ?m1 ?ev) |- _ =>
      pose proof (one_model _ _ _ _ Hsys Hs) as (_ & Hok1 & _) end.
    match goal with Hm : materialize_model_accesses ?m1 _ = None |- _ =>
      rewrite (materialize_model_accesses_no_lazy m1 _ (mo_ok_lazy _ Hok1)) in Hm; discriminate Hm end.
  -
    match goal with Hx : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in Hx; injection Hx as <- end.
    match goal with Hs : syscall_spec _ mo (Ok ?e ?m1 ?ev) |- _ =>
      pose proof (one_model _ _ _ _ Hsys Hs) as (_ & Hok1 & _) end.
    exfalso. pose proof (mo_ok_halted _ Hok1). congruence.
  -
    match goal with Hx : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in Hx; injection Hx as <- end.
    match goal with Hs : syscall_spec _ mo (Ok ?e ?m1 ?ev) |- _ =>
      pose proof (one_model _ _ _ _ Hsys Hs) as (_ & Hok1 & _) end.
    exfalso. match goal with Hk : m_killed ?m1 = Some _ |- _ =>
      rewrite (m_killed_of_m_halted_none _ (mo_ok_halted _ Hok1)) in Hk; discriminate Hk end.
  -
    match goal with Hx : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in Hx; injection Hx as <- end.
    match goal with Hs : syscall_spec _ mo Unmodeled |- _ =>
      apply (Hchar _ _ Hsys) in Hs; destruct (HOUT _ Hs) as (? & ? & E & _); discriminate E end.
Qed.

End OneNode.

Section PerNode.
Variable segs : list Segment.

Definition iP1 (no : Z) (a0 : word) (i : SyscallInput) : Prop :=
  bv_unsigned (in_sysno i) = no /\ in_arg i 0 = a0.
Definition iP2 (no : Z) (a0 a1 : word) (i : SyscallInput) : Prop :=
  bv_unsigned (in_sysno i) = no /\ in_arg i 0 = a0 /\ in_arg i 1 = a1.
Definition iP3 (no : Z) (a0 a1 a2 : word) (i : SyscallInput) : Prop :=
  bv_unsigned (in_sysno i) = no /\ in_arg i 0 = a0 /\ in_arg i 1 = a1 /\ in_arg i 2 = a2.
Definition iP4 (no : Z) (a0 a1 a2 a3 : word) (i : SyscallInput) : Prop :=
  bv_unsigned (in_sysno i) = no /\ in_arg i 0 = a0 /\ in_arg i 1 = a1 /\ in_arg i 2 = a2 /\ in_arg i 3 = a3.
Definition iP6 (no : Z) (a0 a1 a2 a3 a4 a5 : word) (i : SyscallInput) : Prop :=
  bv_unsigned (in_sysno i) = no /\ in_arg i 0 = a0 /\ in_arg i 1 = a1 /\ in_arg i 2 = a2
  /\ in_arg i 3 = a3 /\ in_arg i 4 = a4 /\ in_arg i 5 = a5.

Lemma iP1_id : forall no a0 i i', iP1 no a0 i -> iP1 no a0 i' ->
  bv_unsigned (in_sysno i) = bv_unsigned (in_sysno i') /\ in_arg i 0 = in_arg i' 0.
Proof. intros no a0 i i' [A B] [A' B']. split; congruence. Qed.
Lemma iP2_id : forall no a0 a1 i i', iP2 no a0 a1 i -> iP2 no a0 a1 i' ->
  bv_unsigned (in_sysno i) = bv_unsigned (in_sysno i') /\ in_arg i 0 = in_arg i' 0.
Proof. intros no a0 a1 i i' [A [B _]] [A' [B' _]]. split; congruence. Qed.
Lemma iP3_id : forall no a0 a1 a2 i i', iP3 no a0 a1 a2 i -> iP3 no a0 a1 a2 i' ->
  bv_unsigned (in_sysno i) = bv_unsigned (in_sysno i') /\ in_arg i 0 = in_arg i' 0.
Proof. intros no a0 a1 a2 i i' [A [B _]] [A' [B' _]]. split; congruence. Qed.
Lemma iP4_id : forall no a0 a1 a2 a3 i i', iP4 no a0 a1 a2 a3 i -> iP4 no a0 a1 a2 a3 i' ->
  bv_unsigned (in_sysno i) = bv_unsigned (in_sysno i') /\ in_arg i 0 = in_arg i' 0.
Proof. intros no a0 a1 a2 a3 i i' [A [B _]] [A' [B' _]]. split; congruence. Qed.
Lemma iP6_id : forall no a0 a1 a2 a3 a4 a5 i i', iP6 no a0 a1 a2 a3 a4 a5 i -> iP6 no a0 a1 a2 a3 a4 a5 i' ->
  bv_unsigned (in_sysno i) = bv_unsigned (in_sysno i') /\ in_arg i 0 = in_arg i' 0.
Proof. intros no a0 a1 a2 a3 a4 a5 i i' [A [B _]] [A' [B' _]]. split; congruence. Qed.

Local Ltac ok_out Hmo :=
  eexists _, _; split; [reflexivity|];
  match goal with |- mo_ok ?m' /\ vm_agree ?m ?m' =>
    assert (VA : vm_only m m') by vm_only_done;
    split; [exact (vm_agree_mo_ok _ _ VA Hmo) | exact VA] end.

Definition OUT_brk (req : word) (mo : Model) (o : outcome SyscallEffect) : Prop :=
  exists r, brk_r_ok mo req r = true
       /\ o = Ok (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
                 (with_brk_next mo req r) [].

Lemma char_brk : forall req mo i o, iP1 214 req i -> (syscall_spec i mo o <-> OUT_brk req mo o).
Proof.
  intros req mo i o [Hno Ha0]. rewrite (syscall_spec_214 i mo o Hno), Ha0. apply brk_outcome.
Qed.

Lemma OUT_brk_ok : forall req mo o, mo_ok mo -> OUT_brk req mo o ->
  exists eff mo', o = Ok eff mo' [] /\ mo_ok mo' /\ vm_agree mo mo'.
Proof. intros req mo o Hmo (r & _ & ->). ok_out Hmo. Qed.

Lemma brk_r_ok_same : forall mo req, brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  intros mo req. unfold brk_r_ok. rewrite bv_eqb_refl.
  destruct (w_is0 req || _)%bool; [reflexivity|].
  destruct (bv_unsigned req <? _)%Z; [rewrite orb_true_r; reflexivity|].
  rewrite orb_true_r. cbn [andb]. unfold brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma OUT_brk_inh : forall req mo, exists o, OUT_brk req mo o.
Proof. intros req mo. eexists. exists (vm_brk (m_vmmaps mo)). split; [apply brk_r_ok_same | reflexivity]. Qed.

Definition OUT_munmap (addr len : word) (mo : Model) (o : outcome SyscallEffect) : Prop :=
  let h := m_vmmaps mo in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
         (with_mmap_destroyed addr n
            (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) addr)
               (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) [].

Lemma char_munmap : forall addr len mo i o,
  iP2 215 addr len i ->
  bv_unsigned addr mod page_size = 0 -> w_is0 len = false ->
  bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= TASK_SIZE ->
  map_has (vm_maps (m_vmmaps mo)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (syscall_spec i mo o <-> OUT_munmap addr len mo o).
Proof.
  intros addr len mo i o (Hno & Ha0 & Ha1) H1 H2 H3 H4.
  rewrite (syscall_spec_215 i mo o Hno), Ha0, Ha1. apply munmap_exact_outcome; assumption.
Qed.

Lemma OUT_munmap_ok : forall addr len mo o, mo_ok mo -> OUT_munmap addr len mo o ->
  exists eff mo', o = Ok eff mo' [] /\ mo_ok mo' /\ vm_agree mo mo'.
Proof. intros addr len mo o Hmo ->. ok_out Hmo. Qed.

Definition OUT_mmap (addr len prot flags : word) (mo : Model) (o : outcome SyscallEffect) : Prop :=
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (mmap_rw_shape prot flags /\
     (mmap_err_out mo o
      \/ exists a, ((bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                    /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                    /\ mmap_noreserve_backed_ok flags mo nZ = true)
                   /\ o = Ok (mkEffect a [] [(a, n)])
                            (with_mmap_backing flags a n
                              (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
                                              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) []))
  \/ (mmap_none_shape prot flags /\
     (mmap_err_out mo o
      \/ exists a, ((bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                    /\ region_free (vm_reserved h ++ vm_maps h) a n = true)
                   /\ o = Ok (mkEffectU a [] [] [(a, n)] [] [])
                            (with_mmap_backing flags a n
                              (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                                              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) []))
  \/ (mmap_fixed_shape addr len prot flags h /\
     (mmap_err_out mo o
      \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
                (with_mmap_replacement flags addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                      ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) []
      \/ exists e, In e mmap_errnos /\
           o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                  (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) mo) [])).

Lemma shapes_exclusive_1 : forall prot flags, mmap_rw_shape prot flags -> ~ mmap_none_shape prot flags.
Proof. intros prot flags H [H1 _]. unfold mmap_rw_shape in H. congruence. Qed.
Lemma shapes_exclusive_2 : forall addr len prot flags h, mmap_rw_shape prot flags -> ~ mmap_fixed_shape addr len prot flags h.
Proof. intros addr len prot flags h H (H1 & _). unfold mmap_rw_shape in H. congruence. Qed.
Lemma shapes_exclusive_3 : forall addr len prot flags h, mmap_none_shape prot flags -> ~ mmap_fixed_shape addr len prot flags h.
Proof. intros addr len prot flags h [_ H] (_ & H1 & _). congruence. Qed.

Lemma char_mmap : forall addr len prot flags mo i o,
  iP6 222 addr len prot flags (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i ->
  w_is0 len = false -> mmap_anon_b flags = true ->
  (mmap_rw_shape prot flags \/ mmap_none_shape prot flags \/ mmap_fixed_shape addr len prot flags (m_vmmaps mo)) ->
  (syscall_spec i mo o <-> OUT_mmap addr len prot flags mo o).
Proof.
  intros addr len prot flags mo i o (Hno & H0 & H1 & H2 & H3 & H4 & H5) Hlen Han Hsh.
  rewrite (syscall_spec_222 i mo o Hno), H0, H1, H2, H3, H4, H5. unfold OUT_mmap.
  destruct Hsh as [Hrw | [Hnone | Hfx]].
  - rewrite (mmap_rw_outcome addr len prot flags (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o eq_refl Han Hlen Hrw). split.
    + intros H. left. split; [exact Hrw | exact H].
    + intros [[_ H] | [[Hn _] | [Hf _]]]; [exact H | |].
      * exfalso. exact (shapes_exclusive_1 _ _ Hrw Hn).
      * exfalso. exact (shapes_exclusive_2 _ _ _ _ _ Hrw Hf).
  - pose proof Hnone as [Hm Hn]. rewrite (mmap_noaccess_outcome addr len prot flags (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o eq_refl Han Hlen Hm Hn). split.
    + intros H. right; left. split; [exact Hnone | exact H].
    + intros [[Hr _] | [[_ H] | [Hf _]]]; [| exact H |].
      * exfalso. exact (shapes_exclusive_1 _ _ Hr Hnone).
      * exfalso. exact (shapes_exclusive_3 _ _ _ _ _ Hnone Hf).
  - pose proof Hfx as (Hm & Hn & Hf & Hc & Hal & Hpos & Hrf & Hmc).
    rewrite (mmap_fixed_noaccess_outcome addr len prot flags (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o eq_refl Han Hlen Hm Hn Hf Hc Hal Hpos Hrf Hmc). split.
    + intros H. right; right. split; [exact Hfx | exact H].
    + intros [[Hr _] | [[Hnn _] | [_ H]]]; [| | exact H].
      * exfalso. exact (shapes_exclusive_2 _ _ _ _ _ Hr Hfx).
      * exfalso. exact (shapes_exclusive_3 _ _ _ _ _ Hnn Hfx).
Qed.

Lemma OUT_mmap_ok : forall addr len prot flags mo o,
  mmap_noreserve_b flags = false -> mo_ok mo -> OUT_mmap addr len prot flags mo o ->
  exists eff mo', o = Ok eff mo' [] /\ mo_ok mo' /\ vm_agree mo mo'.
Proof.
  intros addr len prot flags mo o Hnr Hmo H. unfold OUT_mmap in H.
  destruct H as [[_ [(e & _ & ->) | (a & _ & ->)]] | [[_ [(e & _ & ->) | (a & _ & ->)]] | [_ [(e & _ & ->) | [-> | (e & _ & ->)]]]]];
    ok_out Hmo.
Qed.

Lemma OUT_mmap_inh : forall addr len prot flags mo,
  (mmap_rw_shape prot flags \/ mmap_none_shape prot flags \/ mmap_fixed_shape addr len prot flags (m_vmmaps mo)) ->
  exists o, OUT_mmap addr len prot flags mo o.
Proof.
  intros addr len prot flags mo [H | [H | H]]; unfold OUT_mmap; cbv zeta.
  - eexists. left. split; [exact H|]. left. exists ENOMEM. split; [left; reflexivity | reflexivity].
  - eexists. right; left. split; [exact H|]. left. exists ENOMEM. split; [left; reflexivity | reflexivity].
  - eexists. right; right. split; [exact H|]. right; left. reflexivity.
Qed.

Definition OUT_mprotect (addr len prot : word) (mo : Model) (o : outcome SyscallEffect) : Prop :=
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  (exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) mo [])
  \/ (mprotect_budget_ok mo addr n = true
      /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next mo addr n) []).

Lemma char_mprotect : forall addr len prot mo i o,
  iP3 226 addr len prot i ->
  mprotect_grows_conflict_b prot = false -> bv_unsigned addr mod page_size = 0 -> w_is0 len = false ->
  bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64 -> mprotect_modeled_b prot = true ->
  map_contains (vm_noaccess (m_vmmaps mo)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  map_contains (vm_maps (m_vmmaps mo)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  (syscall_spec i mo o <-> OUT_mprotect addr len prot mo o).
Proof.
  intros addr len prot mo i o (Hno & H0 & H1 & H2) G1 G2 G3 G4 G5 G6 G7.
  rewrite (syscall_spec_226 i mo o Hno), H0, H1, H2. apply mprotect_expose_outcome; assumption.
Qed.

Lemma OUT_mprotect_ok : forall addr len prot mo o, mo_ok mo -> OUT_mprotect addr len prot mo o ->
  exists eff mo', o = Ok eff mo' [] /\ mo_ok mo' /\ vm_agree mo mo'.
Proof. intros addr len prot mo o Hmo [(e & _ & ->) | (_ & ->)]; ok_out Hmo. Qed.

Lemma OUT_mprotect_inh : forall addr len prot mo, exists o, OUT_mprotect addr len prot mo o.
Proof.
  intros addr len prot mo. unfold OUT_mprotect. cbv zeta.
  eexists. left. exists ENOMEM. split; [left; reflexivity | reflexivity].
Qed.

Definition OUT_mremap (old osz nsz : word) (mo : Model) (o : outcome SyscallEffect) : Prop := mremap_out old osz nsz mo o.

Lemma char_mremap : forall old osz nsz mo i o,
  iP4 216 old osz nsz (Z_to_bv 64 1) i ->
  bv_unsigned old mod page_size = 0 -> page_align_is0_b nsz = false -> page_align_is0_b osz = false ->
  mremap_source_b (m_vmmaps mo) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned osz))) (page_round_up_Z (bv_unsigned osz)) = true ->
  mremap_backing_uniform_b mo old (Z_to_bv 64 (page_round_up_Z (bv_unsigned osz))) = true ->
  (syscall_spec i mo o <-> OUT_mremap old osz nsz mo o).
Proof.
  intros old osz nsz mo i o (Hno & H0 & H1 & H2 & H3) G1 G2 G3 G4 G5.
  rewrite (syscall_spec_216 i mo o Hno), H0, H1, H2, H3. unfold OUT_mremap.
  apply mremap_maymove_outcome; try assumption. reflexivity.
Qed.

Lemma OUT_mremap_ok : forall old osz nsz mo o, mo_ok mo -> OUT_mremap old osz nsz mo o ->
  exists eff mo', o = Ok eff mo' [] /\ mo_ok mo' /\ vm_agree mo mo'.
Proof.
  intros old osz nsz mo o Hmo H. unfold OUT_mremap, mremap_out in H. cbv zeta in H.
  destruct H as [[_ ->] | [_ [(e & _ & ->) | [[_ ->] | [(_ & _ & ->) | (_ & dst & _ & ->)]]]]]; ok_out Hmo.
Qed.

Lemma OUT_mremap_inh : forall old osz nsz mo, exists o, OUT_mremap old osz nsz mo o.
Proof.
  intros old osz nsz mo. unfold OUT_mremap, mremap_out. cbv zeta.
  destruct (Z.eq_dec (page_round_up_Z (bv_unsigned osz)) (page_round_up_Z (bv_unsigned nsz))) as [E|NE].
  - eexists. left. split; [exact E | reflexivity].
  - eexists. right. split; [exact NE|]. left. exists ENOMEM. split; [left; reflexivity | reflexivity].
Qed.

Lemma iP_pure_brk : forall req, iP1 214 (Z_to_bv 64 req) (pure_input 214 [Z_to_bv 64 req]).
Proof. intros. split; reflexivity. Qed.
Lemma iP_pure_munmap : forall a l, iP2 215 (Z_to_bv 64 a) (Z_to_bv 64 l) (pure_input 215 [Z_to_bv 64 a; Z_to_bv 64 l]).
Proof. intros. repeat split; reflexivity. Qed.
Lemma iP_pure_mprotect : forall a l p,
  iP3 226 (Z_to_bv 64 a) (Z_to_bv 64 l) (Z_to_bv 64 p) (pure_input 226 [Z_to_bv 64 a; Z_to_bv 64 l; Z_to_bv 64 p]).
Proof. intros. repeat split; reflexivity. Qed.
Lemma iP_pure_mmap : forall a l p f,
  iP6 222 (Z_to_bv 64 a) (Z_to_bv 64 l) (Z_to_bv 64 p) (Z_to_bv 64 f) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
      (pure_input 222 [Z_to_bv 64 a; Z_to_bv 64 l; Z_to_bv 64 p; Z_to_bv 64 f; Z_to_bv 64 (-1); Z_to_bv 64 0]).
Proof. intros. repeat split; reflexivity. Qed.
Lemma iP_pure_mremap : forall o l n,
  iP4 216 (Z_to_bv 64 o) (Z_to_bv 64 l) (Z_to_bv 64 n) (Z_to_bv 64 1)
      (pure_input 216 [Z_to_bv 64 o; Z_to_bv 64 l; Z_to_bv 64 n; Z_to_bv 64 1; Z_to_bv 64 0]).
Proof. intros. repeat split; reflexivity. Qed.

Local Ltac sys_iP :=
  unfold iP1, iP2, iP3, iP4, iP6; rewrite ?in_sysno_si, ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si;
  repeat split; try assumption; try reflexivity.

Theorem mm_model : forall n mo eff mo' evs,
  nsafe n mo -> mo_ok mo -> nstep n mo eff mo' evs -> evs = [] /\ mo_ok mo' /\ vm_agree mo mo'.
Proof.
  intros n mo eff mo' evs Hs Hmo Hst. destruct (nstep_nsafe_vm_only n mo eff mo' evs Hs Hst) as [VA ->].
  split; [reflexivity|]. split; [exact (vm_agree_mo_ok _ _ VA Hmo) | exact VA].
Qed.

Theorem mm_progress : forall n mo, nsafe n mo -> mo_ok mo -> exists eff mo' evs, nstep n mo eff mo' evs.
Proof.
  intros n mo Hs Hmo; destruct n; cbn [nsafe] in Hs; try contradiction; unfold nstep; cbn [node_input].
  - eapply (one_progress mo (OUT_brk (Z_to_bv 64 req) mo) (iP1 214 (Z_to_bv 64 req))).
    + intros; apply char_brk; assumption.
    + intros; eapply OUT_brk_ok; eassumption.
    + apply iP_pure_brk.
    + apply OUT_brk_inh.
  - destruct Hs as (Hlen & Hnr & Han & Hsh).
    eapply (one_progress mo (OUT_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) mo)
              (iP6 222 (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0))).
    + intros; apply char_mmap; assumption.
    + intros; eapply OUT_mmap_ok; eassumption.
    + apply iP_pure_mmap.
    + apply OUT_mmap_inh. exact Hsh.
  - destruct Hs as (H1 & H2 & H3 & H4).
    eapply (one_progress mo (OUT_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) mo) (iP2 215 (Z_to_bv 64 addr) (Z_to_bv 64 len))).
    + intros; apply char_munmap; assumption.
    + intros; eapply OUT_munmap_ok; eassumption.
    + apply iP_pure_munmap.
    + eexists. reflexivity.
  - destruct Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    eapply (one_progress mo (OUT_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) mo)
              (iP3 226 (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot))).
    + intros; apply char_mprotect; assumption.
    + intros; eapply OUT_mprotect_ok; eassumption.
    + apply iP_pure_mprotect.
    + apply OUT_mprotect_inh.
  - destruct Hs as (H1 & H2 & H3 & H4 & H5).
    eapply (one_progress mo (OUT_mremap (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) mo)
              (iP4 216 (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) (Z_to_bv 64 1))).
    + intros; apply char_mremap; assumption.
    + intros; eapply OUT_mremap_ok; eassumption.
    + apply iP_pure_mremap.
    + apply OUT_mremap_inh.
Qed.

Theorem mm_sound : forall n ms mo eff mo' evs,
  at_node segs n ms -> nsafe n mo -> mo_ok mo -> nstep n mo eff mo' evs ->
  sstep_cfg segs fcfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')).
Proof.
  intros n ms mo eff mo' evs Hat Hs Hmo Hst; destruct n; cbn [nsafe] in Hs; try contradiction;
    unfold nstep in Hst; cbn [node_input] in Hst; cbn [at_node] in Hat.
  - destruct Hat as [Hsvc Ha0].
    eapply (one_sound segs mo (OUT_brk (Z_to_bv 64 req) mo) (iP1 214 (Z_to_bv 64 req))); try exact Hst.
    + intros; apply char_brk; assumption.
    + intros; eapply OUT_brk_ok; eassumption.
    + exact Hmo.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_brk.
    + apply iP1_id.
  - destruct Hat as (Hsvc & A0 & A1 & A2 & A3 & A4 & A5). destruct Hs as (Hlen & Hnr & Han & Hsh).
    eapply (one_sound segs mo (OUT_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) mo)
              (iP6 222 (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)));
      try exact Hst.
    + intros; apply char_mmap; assumption.
    + intros; eapply OUT_mmap_ok; eassumption.
    + exact Hmo.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_mmap.
    + apply iP6_id.
  - destruct Hat as (Hsvc & A0 & A1). destruct Hs as (H1 & H2 & H3 & H4).
    eapply (one_sound segs mo (OUT_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) mo) (iP2 215 (Z_to_bv 64 addr) (Z_to_bv 64 len)));
      try exact Hst.
    + intros; apply char_munmap; assumption.
    + intros; eapply OUT_munmap_ok; eassumption.
    + exact Hmo.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_munmap.
    + apply iP2_id.
  - destruct Hat as (Hsvc & A0 & A1 & A2). destruct Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    eapply (one_sound segs mo (OUT_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) mo)
              (iP3 226 (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot))); try exact Hst.
    + intros; apply char_mprotect; assumption.
    + intros; eapply OUT_mprotect_ok; eassumption.
    + exact Hmo.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_mprotect.
    + apply iP3_id.
  - destruct Hat as (Hsvc & A0 & A1 & A2 & A3). destruct Hs as (H1 & H2 & H3 & H4 & H5).
    eapply (one_sound segs mo (OUT_mremap (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) mo)
              (iP4 216 (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) (Z_to_bv 64 1))); try exact Hst.
    + intros; apply char_mremap; assumption.
    + intros; eapply OUT_mremap_ok; eassumption.
    + exact Hmo.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_mremap.
    + apply iP4_id.
Qed.

Theorem mm_complete : forall n ms mo evs X,
  at_node segs n ms -> nsafe n mo -> mo_ok mo -> sstep_cfg segs fcfg (mkCfg ms mo) evs X ->
  exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs.
Proof.
  intros n ms mo evs X Hat Hs Hmo Hst; destruct n; cbn [nsafe] in Hs; try contradiction;
    unfold nstep; cbn [node_input]; cbn [at_node] in Hat.
  - destruct Hat as [Hsvc Ha0].
    eapply (one_complete segs mo (OUT_brk (Z_to_bv 64 req) mo) (iP1 214 (Z_to_bv 64 req))); try exact Hst.
    + intros; apply char_brk; assumption.
    + intros; eapply OUT_brk_ok; eassumption.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_brk.
    + apply iP1_id.
  - destruct Hat as (Hsvc & A0 & A1 & A2 & A3 & A4 & A5). destruct Hs as (Hlen & Hnr & Han & Hsh).
    eapply (one_complete segs mo (OUT_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) mo)
              (iP6 222 (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)));
      try exact Hst.
    + intros; apply char_mmap; assumption.
    + intros; eapply OUT_mmap_ok; eassumption.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_mmap.
    + apply iP6_id.
  - destruct Hat as (Hsvc & A0 & A1). destruct Hs as (H1 & H2 & H3 & H4).
    eapply (one_complete segs mo (OUT_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) mo) (iP2 215 (Z_to_bv 64 addr) (Z_to_bv 64 len)));
      try exact Hst.
    + intros; apply char_munmap; assumption.
    + intros; eapply OUT_munmap_ok; eassumption.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_munmap.
    + apply iP2_id.
  - destruct Hat as (Hsvc & A0 & A1 & A2). destruct Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    eapply (one_complete segs mo (OUT_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) mo)
              (iP3 226 (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot))); try exact Hst.
    + intros; apply char_mprotect; assumption.
    + intros; eapply OUT_mprotect_ok; eassumption.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_mprotect.
    + apply iP3_id.
  - destruct Hat as (Hsvc & A0 & A1 & A2 & A3). destruct Hs as (H1 & H2 & H3 & H4 & H5).
    eapply (one_complete segs mo (OUT_mremap (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) mo)
              (iP4 216 (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) (Z_to_bv 64 1))); try exact Hst.
    + intros; apply char_mremap; assumption.
    + intros; eapply OUT_mremap_ok; eassumption.
    + exact Hsvc.
    + sys_iP.
    + apply iP_pure_mremap.
    + apply iP4_id.
Qed.

End PerNode.
