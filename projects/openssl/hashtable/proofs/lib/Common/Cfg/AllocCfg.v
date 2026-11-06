(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sysret (ms : machine_state) (ret : word) (mem' : word -> option byte)
    : machine_state :=
  {| ms_regs := Riscv.Prelude.bvmap_set (10%bv : bv 5) ret (ms_regs ms);
     ms_fregs := ms_fregs ms;
     ms_pc_val := (ms_pc ms + Z_to_bv 64 4)%bv;
     ms_svc_pending := None;
     ms_resv := ms_resv ms;
     ms_fcsr := ms_fcsr ms;
     ms_mem := mem';
     ms_rom := ms_rom ms |}.

(* [comment removed for export] *)
Lemma advance_apply_effect_eq : forall ms ret zs us cis,
  advance_past_svc (apply_effect ms (mkEffectU ret [] zs us [] cis))
  = sysret ms ret (apply_zeros (apply_unmaps (ms_mem ms) us) zs).
Proof. intros. reflexivity. Qed.

Lemma advance_apply_effect_zeros : forall ms a zs,
  advance_past_svc (apply_effect ms (mkEffect a [] zs))
  = sysret ms a (apply_zeros (ms_mem ms) zs).
Proof. intros. reflexivity. Qed.

Lemma advance_apply_effect_unmaps : forall ms r us,
  advance_past_svc (apply_effect ms (mkEffectU r [] [] us [] []))
  = sysret ms r (apply_unmaps (ms_mem ms) us).
Proof. intros. reflexivity. Qed.

Lemma advance_apply_effect_ret : forall ms r,
  advance_past_svc (apply_effect ms (mkEffect r [] [])) = sysret ms r (ms_mem ms).
Proof. intros. reflexivity. Qed.

Lemma sysret_gpr0 : forall ms ret mem', ms_gpr (sysret ms ret mem') 0 = ret.
Proof.
  intros. unfold ms_gpr, sysret. cbn [ms_regs]. rewrite gpr0_reg_eq.
  unfold Riscv.Sem.reg_get. rewrite Riscv.Prelude.bvmap_get_set_same. reflexivity.
Qed.

Lemma sysret_reg_other : forall ms ret mem' (r : bv 5),
  r <> (10%bv : bv 5) ->
  Riscv.Sem.reg_get (ms_regs (sysret ms ret mem')) r = Riscv.Sem.reg_get (ms_regs ms) r.
Proof.
  intros ms ret mem' r Hr. unfold sysret. cbn [ms_regs]. unfold Riscv.Sem.reg_get.
  rewrite Riscv.Prelude.bvmap_get_set_other; [reflexivity | congruence].
Qed.

Lemma sysret_mem : forall ms ret mem', ms_mem (sysret ms ret mem') = mem'.
Proof. reflexivity. Qed.
Lemma sysret_pc : forall ms ret mem', ms_pc (sysret ms ret mem') = (ms_pc ms + Z_to_bv 64 4)%bv.
Proof. reflexivity. Qed.
Lemma sysret_svc : forall ms ret mem', ms_svc_pending (sysret ms ret mem') = None.
Proof. reflexivity. Qed.
Lemma sysret_rom : forall ms ret mem', ms_rom (sysret ms ret mem') = ms_rom ms.
Proof. reflexivity. Qed.
Lemma sysret_fregs : forall ms ret mem', ms_fregs (sysret ms ret mem') = ms_fregs ms.
Proof. reflexivity. Qed.
Lemma sysret_resv : forall ms ret mem', ms_resv (sysret ms ret mem') = ms_resv ms.
Proof. reflexivity. Qed.
Lemma sysret_fcsr : forall ms ret mem', ms_fcsr (sysret ms ret mem') = ms_fcsr ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma apply_zeros_one : forall mem a n x,
  apply_zeros mem [(a, n)] x
  = if (bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)
    then Some (Z_to_bv 8 0) else mem x.
Proof.
  intros. unfold apply_zeros, zeros_cover. cbn [existsb fst snd]. rewrite orb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma apply_unmaps_one : forall mem a n x,
  apply_unmaps mem [(a, n)] x
  = if (bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)
    then None else mem x.
Proof.
  intros. unfold apply_unmaps, zeros_cover. cbn [existsb fst snd]. rewrite orb_false_r. reflexivity.
Qed.

Lemma apply_zeros_nil : forall mem, apply_zeros mem [] = mem.
Proof. reflexivity. Qed.
Lemma apply_unmaps_nil : forall mem, apply_unmaps mem [] = mem.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma w_is0_iff : forall w : word, w_is0 w = true <-> bv_unsigned w = 0.
Proof.
  intros w. unfold w_is0. rewrite bv_eqb_eq. split.
  - intros ->. reflexivity.
  - intros H. apply bv_eq. rewrite H. reflexivity.
Qed.

Lemma syscall_spec_mmap : forall segs ms x8 m o,
  bv_unsigned x8 = 222 ->
  (syscall_spec (sys_input segs ms x8) m o
   <-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
         (ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) m o).
Proof.
  intros segs ms x8 m o Hno. unfold syscall_spec, Sys.Dispatch.dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

Lemma syscall_spec_munmap : forall segs ms x8 m o,
  bv_unsigned x8 = 215 ->
  (syscall_spec (sys_input segs ms x8) m o
   <-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) m o).
Proof.
  intros segs ms x8 m o Hno. unfold syscall_spec, Sys.Dispatch.dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

Lemma syscall_spec_brk : forall segs ms x8 m o,
  bv_unsigned x8 = 214 ->
  (syscall_spec (sys_input segs ms x8) m o
   <-> brk_spec (ms_gpr ms 0) (sys_input segs ms x8) m o).
Proof.
  intros segs ms x8 m o Hno. unfold syscall_spec, Sys.Dispatch.dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

Lemma syscall_spec_mprotect : forall segs ms x8 m o,
  bv_unsigned x8 = 226 ->
  (syscall_spec (sys_input segs ms x8) m o
   <-> mprotect_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) m o).
Proof.
  intros segs ms x8 m o Hno. unfold syscall_spec, Sys.Dispatch.dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

Lemma bind_get_vmmaps {A} (k : VmMaps -> Sys A) : forall i m o,
  bind get_vmmaps k i m o <-> k (m_vmmaps m) i m o.
Proof.
  intros i m o. unfold bind, get_vmmaps. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
    injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists (m_vmmaps m), m, [], evs. split; [reflexivity|].
    split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
    injection H1 as -> -> ->. exact H2.
  - intros H. right. exists (m_vmmaps m), m, []. split; [reflexivity | exact H].
Qed.

(* [comment removed for export] *)
Lemma alloc_family_off : forall cfg segs ms x8,
  sc_alloc cfg = false ->
  (bv_unsigned x8 = 214 \/ bv_unsigned x8 = 216 \/ bv_unsigned x8 = 222 \/ bv_unsigned x8 = 226) ->
  injected_family_off cfg (sys_input segs ms x8) = true.
Proof.
  intros cfg segs ms x8 Hc Hno. rewrite injected_family_off_sysno. unfold sysno_family_off.
  destruct Hno as [H | [H | [H | H]]]; rewrite H; cbn; rewrite Hc; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma munmap_family_on : forall cfg segs ms x8,
  bv_unsigned x8 = 215 -> injected_family_off cfg (sys_input segs ms x8) = false.
Proof.
  intros cfg segs ms x8 H. rewrite injected_family_off_sysno. unfold sysno_family_off.
  rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_cfg_svc_iff : forall ms m x8,
  m_halted m = None ->
  ms_svc_pending ms = Some x8 ->
  ~ syscall_spec (sys_input segs ms x8) m Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) m (Ok eff m' evs) ->
     m_halted m' = None /\ m_vm_lazy m' = []) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    exists eff m',
      syscall_spec (sys_input segs ms x8) m (Ok eff m' e)
      /\ ~ spurious_refusal_cfg cfg (sys_input segs ms x8) m eff
      /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m').
Proof.
  intros ms m x8 Hh Hsvc Hnu Hout e st. split.
  - intros Hss.
    inversion Hss; subst; try congruence;
      try (exfalso; apply Hnu; assumption);
      match goal with H : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H; inversion H; subst end.
    + match goal with Hs : syscall_spec _ _ (Ok ?eff ?m' _) |- _ =>
        destruct (Hout _ _ _ Hs) as [_ Hl]; exists eff, m' end.
      split; [assumption |]. split; [assumption |].
      match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hl) in Hm; inversion Hm; subst end.
      reflexivity.
    + exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hm : materialize_model_accesses _ _ = None |- _ =>
        destruct (Hout _ _ _ Hs) as [_ Hl];
        rewrite (materialize_model_accesses_no_lazy _ _ Hl) in Hm; discriminate Hm end.
    + exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hc : m_halted _ = Some _ |- _ =>
        destruct (Hout _ _ _ Hs) as [Hn _]; rewrite Hn in Hc; discriminate Hc end.
    + exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hk : m_killed _ = Some _ |- _ =>
        destruct (Hout _ _ _ Hs) as [Hn _];
        rewrite (m_killed_of_m_halted_none _ Hn) in Hk; discriminate Hk end.
  - intros (eff & m' & Hs & Hns & ->).
    destruct (Hout _ _ _ Hs) as [Hn Hl].
    eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact Hs | exact Hns | exact Hn |].
    apply materialize_model_accesses_no_lazy. exact Hl.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_of_step_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  (forall e st, sstep_cfg segs cfg c e st <-> exists i, e = evs i /\ st = SNext (nx i)) ->
  node_ok_cfg cfg segs c I evs nx.
Proof.
  intros c I evs nx H. split.
  - intros i. apply H. exists i. split; reflexivity.
  - intros e st Hss. apply H. exact Hss.
Qed.

Lemma node_ok_cfg_of_step_iff_det : forall c e0 c0,
  (forall e st, sstep_cfg segs cfg c e st <-> e = e0 /\ st = SNext c0) ->
  node_ok_cfg cfg segs c unit (fun _ => e0) (fun _ => c0).
Proof.
  intros c e0 c0 H. apply node_ok_cfg_of_step_iff. intros e st. rewrite H. split.
  - intros [-> ->]. exists tt. split; reflexivity.
  - intros (_ & -> & ->). split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_anon_args (ms : machine_state) (len : Z) : Prop :=
  bv_unsigned (ms_gpr ms 1) = len /\ 0 < len
  /\ bv_unsigned (ms_gpr ms 2) = 3          (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 3) = 34         (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 5) = 0.

(* [comment removed for export] *)
Definition mmap_grant_model (a : word) (nZ : Z) (m : Model) : Model :=
  with_vmmaps (ledger_grant a (Z_to_bv 64 nZ) (m_vmmaps m)) m.

Lemma mmap_anon_spec_iff : forall ms x8 m len,
  bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  let nZ := page_round_up_Z len in
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
    \/ exists a, mmap_grant_b m a nZ = true
                 /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 nZ)]) (mmap_grant_model a nZ m) [].
Proof.
  intros ms x8 m len Hno (Hlen & Hpos & Hprot & Hflags & Hoff) nZ o.
  rewrite (syscall_spec_mmap segs ms x8 m o Hno).
  set (flags := ms_gpr ms 3) in *. set (off := ms_gpr ms 5) in *. set (prot := ms_gpr ms 2) in *.
  assert (G1 : mmap_off_aligned_b off = true)
    by (unfold mmap_off_aligned_b; rewrite Hoff; reflexivity).
  assert (G2 : mmap_anon_b flags = true) by (unfold mmap_anon_b; rewrite Hflags; reflexivity).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : mmap_modeled_b prot flags off = true).
  { unfold mmap_modeled_b, mmap_flags_core.
    rewrite Hprot, Hflags, (proj2 (w_is0_iff off) Hoff). reflexivity. }
  assert (G5 : mmap_noreserve_b flags = false)
    by (unfold mmap_noreserve_b; rewrite Hflags; reflexivity).
  unfold mmap_spec. rewrite G1, G2, G3, G4. cbn [negb].
  unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite G5, Hlen. fold nZ.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify.
  split.
  - destruct o as [eff m' evs |].
    + intros [H | H]; sys_destruct.
      * left. match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end.
        reflexivity.
      * right. match goal with Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb end.
        eexists. split; [apply mmap_grant_b_iff; repeat split; eassumption |].
        reflexivity.
    + intros [H | H]; sys_destruct.
  - intros [-> | (a & Ha & ->)].
    + left. exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
      split; reflexivity.
    + right. apply mmap_grant_b_iff in Ha as (A1 & A2 & A3 & A4 & A5).
      exists m, m, [], []. split; [reflexivity |]. split; [| reflexivity].
      exists a, m, [], []. split.
      { exists a. split; [| reflexivity]. repeat split; try assumption. apply Z.leb_le. exact A5. }
      split; [| reflexivity].
      exists tt, (mmap_grant_model a nZ m), [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Lemma mmap_grant_model_facts : forall a nZ m,
  m_halted (mmap_grant_model a nZ m) = m_halted m
  /\ m_vm_lazy (mmap_grant_model a nZ m) = m_vm_lazy m
  /\ m_vm_materialized (mmap_grant_model a nZ m) = m_vm_materialized m
  /\ m_vmmaps (mmap_grant_model a nZ m) = ledger_grant a (Z_to_bv 64 nZ) (m_vmmaps m).
Proof. intros. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_refusal_enomem : forall ms x8 m,
  bv_unsigned x8 = 222 ->
  refusal_b (sys_input segs ms x8) m (errno_ret ENOMEM) = true.
Proof.
  intros ms x8 m Hno. rewrite refusal_b_enomem_arm by (right; left; exact Hno).
  apply bv_eqb_eq. reflexivity.
Qed.

Lemma mmap_refusal_grant : forall ms x8 m a,
  bv_unsigned x8 = 222 ->
  bv_unsigned a mod page_size = 0 ->
  refusal_b (sys_input segs ms x8) m a = false.
Proof.
  intros ms x8 m a Hno Hal. rewrite refusal_b_enomem_arm by (right; left; exact Hno).
  apply not_enomem_page_aligned. exact Hal.
Qed.

(* [comment removed for export] *)
Theorem mmap_anon_step_iff : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_b m a nZ = true) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    exists a, mmap_grant_b m a nZ = true /\ e = [] /\
      st = SNext (mkCfg (sysret ms a (apply_zeros (ms_mem ms) [(a, Z_to_bv 64 nZ)]))
                        (mmap_grant_model a nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hlazy Hsvc Hno Hargs nZ (a0 & Ha0) e st.
  pose proof (mmap_anon_spec_iff ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec. fold nZ in Hspec.
  assert (Hoff : injected_family_off cfg (sys_input segs ms x8) = true)
    by (apply alloc_family_off; [exact Hc | right; right; left; exact Hno]).
  rewrite (sstep_cfg_svc_iff ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & Hns & ->). apply Hspec in Hs as [Hs | (a & Ha & Hs)].
      * exfalso. inversion Hs; subst. apply Hns. split; [exact Hoff |]. split.
        { cbn [eff_ret]. apply mmap_refusal_enomem. exact Hno. }
        exists (mkEffect a0 [] [(a0, Z_to_bv 64 nZ)]), (mmap_grant_model a0 nZ m), [].
        split; [apply Hspec; right; exists a0; split; [exact Ha0 | reflexivity] |].
        cbn [eff_ret]. apply mmap_refusal_grant; [exact Hno |].
        apply mmap_grant_b_iff in Ha0. tauto.
      * inversion Hs; subst. exists a. split; [exact Ha |]. split; reflexivity.
    + intros (a & Ha & -> & ->).
      exists (mkEffect a [] [(a, Z_to_bv 64 nZ)]), (mmap_grant_model a nZ m).
      split; [apply Hspec; right; exists a; split; [exact Ha | reflexivity] |].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. cbn [eff_ret].
      apply mmap_refusal_grant; [exact Hno |]. apply mmap_grant_b_iff in Ha. tauto.
  - intros Hun. apply Hspec in Hun as [Hun | (a & _ & Hun)]; discriminate Hun.
  - intros eff m' evs Hs. apply Hspec in Hs as [Hs | (a & _ & Hs)]; inversion Hs; subst.
    + split; assumption.
    + split; [exact Hh | exact Hlazy].
Qed.

(* [comment removed for export] *)
Theorem mmap_anon_step_iff_forced : forall ms x8 m len,
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  (forall a, mmap_grant_b m a (page_round_up_Z len) = false) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\ st = SNext (mkCfg (sysret ms (errno_ret ENOMEM) (ms_mem ms)) m).
Proof.
  intros ms x8 m len Hh Hlazy Hsvc Hno Hargs Hnone e st.
  pose proof (mmap_anon_spec_iff ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec.
  assert (Honly : forall o, syscall_spec (sys_input segs ms x8) m o <->
                            o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []).
  { intros o. rewrite Hspec. split; [| intros ->; left; reflexivity].
    intros [-> | (a & Ha & _)]; [reflexivity | rewrite Hnone in Ha; discriminate Ha]. }
  rewrite (sstep_cfg_svc_iff ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & _ & ->). apply Honly in Hs. inversion Hs; subst.
      split; reflexivity.
    + intros (-> & ->). exists (mkEffect (errno_ret ENOMEM) [] []), m.
      split; [apply Honly; reflexivity |]. split; [| reflexivity].
      intros (_ & _ & (eff' & m' & evs' & Hs' & Hnr)).
      apply Honly in Hs'. inversion Hs'; subst. cbn [eff_ret] in Hnr.
      rewrite (mmap_refusal_enomem ms x8 m Hno) in Hnr. discriminate Hnr.
  - intros Hun. apply Honly in Hun. discriminate Hun.
  - intros eff m' evs Hs. apply Honly in Hs. inversion Hs; subst. split; assumption.
Qed.

(* [comment removed for export] *)
Definition mmap_grant_index (m : Model) (nZ : Z) : Type :=
  {a : word | mmap_grant_b m a nZ = true}.

Theorem node_mmap_anon_cfg : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_b m a nZ = true) ->
  node_ok_cfg cfg segs (mkCfg ms m) (mmap_grant_index m nZ) (fun _ => [])
    (fun i => mkCfg (sysret ms (proj1_sig i)
                       (apply_zeros (ms_mem ms) [(proj1_sig i, Z_to_bv 64 nZ)]))
                    (mmap_grant_model (proj1_sig i) nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hlazy Hsvc Hno Hargs nZ Hex.
  apply node_ok_cfg_of_step_iff. intros e st.
  rewrite (mmap_anon_step_iff ms x8 m len Hc Hh Hlazy Hsvc Hno Hargs Hex e st). fold nZ. split.
  - intros (a & Ha & -> & ->). exists (exist _ a Ha). split; reflexivity.
  - intros ([a Ha] & -> & ->). exists a. cbn [proj1_sig]. repeat split. exact Ha.
Qed.

Theorem rzc_mmap_anon : forall ms x8 m len T,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_b m a nZ = true) ->
  (forall a, mmap_grant_b m a nZ = true ->
     realizes_cfg cfg segs
       (mkCfg (sysret ms a (apply_zeros (ms_mem ms) [(a, Z_to_bv 64 nZ)]))
              (mmap_grant_model a nZ m)) T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m len T Hc Hh Hlazy Hsvc Hno Hargs nZ Hex HT.
  destruct Hex as (a0 & Ha0).
  eapply (rzc_cases_same cfg segs (mkCfg ms m) (mmap_grant_index m nZ) _ T (exist _ a0 Ha0)).
  - apply (node_mmap_anon_cfg ms x8 m len Hc Hh Hlazy Hsvc Hno Hargs). exists a0. exact Ha0.
  - intros [a Ha]. cbn [proj1_sig]. apply HT. exact Ha.
Qed.

(* [comment removed for export] *)
Theorem mmap_anon_inv : forall R L c S m a len,
  ledger_inv R L c S (m_vmmaps m) ->
  0 < len ->
  mmap_grant_b m a (page_round_up_Z len) = true ->
  ledger_inv R L (c + 1) (S + page_round_up_Z len)
    (m_vmmaps (mmap_grant_model a (page_round_up_Z len) m)).
Proof.
  intros R L c S m a len Hinv Hlen Ha.
  apply mmap_grant_b_iff in Ha as (A1 & A2 & A3 & A4 & _).
  rewrite (li_reserved _ _ _ _ _ Hinv) in A4.
  change (m_vmmaps (mmap_grant_model a (page_round_up_Z len) m))
    with (ledger_grant a (Z_to_bv 64 (page_round_up_Z len)) (m_vmmaps m)).
  apply ledger_inv_grant; try assumption.
  - apply page_round_up_Z_pos. exact Hlen.
  - apply page_round_up_Z_mod.
Qed.

End WithCfg.

(* [comment removed for export] *)

Section WithCfg2.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_cfg_det_iff : forall ms m x8 eff0 m0 e0,
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) m o <-> o = Ok eff0 m0 e0) ->
  m_halted m0 = None -> m_vm_lazy m0 = [] ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = e0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms m x8 eff0 m0 e0 Hh Hsvc Hspec Hh0 Hl0 e st.
  rewrite (sstep_cfg_svc_iff cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & _ & ->). apply Hspec in Hs. inversion Hs; subst. split; reflexivity.
    + intros (-> & ->). exists eff0, m0. split; [apply Hspec; reflexivity |]. split; [| reflexivity].
      intros (_ & Hr & (eff' & m' & evs' & Hs' & Hnr)).
      apply Hspec in Hs'. inversion Hs'; subst. rewrite Hr in Hnr. discriminate Hnr.
  - intros Hun. apply Hspec in Hun. discriminate Hun.
  - intros eff m' evs Hs. apply Hspec in Hs. inversion Hs; subst. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_filter_det_iff : forall ms m x8 eff0 m0 e0,
  injected_family_off cfg (sys_input segs ms x8) = true ->
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) m (Ok eff0 m0 e0) ->
  refusal_b (sys_input segs ms x8) m (eff_ret eff0) = false ->
  m_halted m0 = None -> m_vm_lazy m0 = [] ->
  (forall o, syscall_spec (sys_input segs ms x8) m o ->
     o = Ok eff0 m0 e0
     \/ exists eff m' evs, o = Ok eff m' evs
          /\ refusal_b (sys_input segs ms x8) m (eff_ret eff) = true
          /\ m_halted m' = None /\ m_vm_lazy m' = []) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = e0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms m x8 eff0 m0 e0 Hoff Hh Hsvc Hs0 Hnr0 Hh0 Hl0 Hall e st.
  rewrite (sstep_cfg_svc_iff cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & Hns & ->).
      destruct (Hall _ Hs) as [Heq | (eff1 & m1 & evs1 & Heq & Hr & _)]; inversion Heq; subst.
      * split; reflexivity.
      * exfalso. apply Hns. split; [exact Hoff |]. split; [exact Hr |].
        exists eff0, m0, e0. split; assumption.
    + intros (-> & ->). exists eff0, m0. split; [exact Hs0 |]. split; [| reflexivity].
      apply spurious_refusal_not_refusal. exact Hnr0.
  - intros Hun. destruct (Hall _ Hun) as [Heq | (? & ? & ? & Heq & _)]; discriminate Heq.
  - intros eff m' evs Hs.
    destruct (Hall _ Hs) as [Heq | (eff1 & m1 & evs1 & Heq & _ & Hn & Hl)]; inversion Heq; subst;
      split; assumption.
Qed.

(* [comment removed for export] *)

Definition munmap_model (a n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
    (with_vmmaps (ledger_unmap a n (m_vmmaps m)) m).

Lemma munmap_model_nolazy : forall a n m,
  model_nolazy m -> munmap_model a n m = with_vmmaps (ledger_unmap a n (m_vmmaps m)) m.
Proof.
  intros a n m Hnl. unfold munmap_model. apply vm_forget_range_nolazy.
  apply model_nolazy_with_vmmaps. exact Hnl.
Qed.

(* [comment removed for export] *)
Definition munmap_entry_args (ms : machine_state) (m : Model) (len : Z) (n : word) : Prop :=
  bv_unsigned (ms_gpr ms 1) = len /\ 0 < len
  /\ bv_unsigned n = page_round_up_Z len
  /\ bv_unsigned (ms_gpr ms 0) mod page_size = 0
  /\ bv_unsigned (ms_gpr ms 0) + bv_unsigned n <= TASK_SIZE
  /\ In (ms_gpr ms 0, n) (vm_maps (m_vmmaps m)).

Lemma munmap_entry_spec_iff : forall ms x8 m len n,
  bv_unsigned x8 = 215 ->
  munmap_entry_args ms m len n ->
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, n)] [] [])
           (munmap_model (ms_gpr ms 0) n m) [].
Proof.
  intros ms x8 m len n Hno (Hlen & Hpos & Hn & Hal & Htask & Hin) o.
  rewrite (syscall_spec_munmap segs ms x8 m o Hno).
  set (a := ms_gpr ms 0) in *.
  assert (Hnn : Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = n).
  { rewrite Hlen, <- Hn. apply u64_id. }
  assert (Ht : (TASK_SIZE <? bv_unsigned a + page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false).
  { apply Z.ltb_ge. rewrite Hlen, <- Hn. exact Htask. }
  assert (Hhas : map_has (vm_maps (m_vmmaps m)) a n = true) by (apply map_has_In; exact Hin).
  unfold munmap_spec.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (w_is0_pos (ms_gpr ms 1)) by lia. cbn [negb orb].
  rewrite bind_get_vmmaps. rewrite Ht, Hnn, Hhas.
  fold (ledger_unmap a n (m_vmmaps m)).
  unfold bind, set_vmmaps, forget_vm_range, modify, pure.
  split.
  - destruct o as [eff m' evs |]; intros H; sys_destruct. reflexivity.
  - intros ->.
    eexists tt, _, [], []. split; [reflexivity |]. split; [| reflexivity].
    eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Theorem munmap_entry_step_iff : forall ms x8 m len n,
  m_halted m = None -> model_nolazy m ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_entry_args ms m len n ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms (Z_to_bv 64 0) (apply_unmaps (ms_mem ms) [(ms_gpr ms 0, n)]))
                      (with_vmmaps (ledger_unmap (ms_gpr ms 0) n (m_vmmaps m)) m)).
Proof.
  intros ms x8 m len n Hh Hnl Hsvc Hno Hargs e st.
  pose proof (munmap_entry_spec_iff ms x8 m len n Hno Hargs) as Hspec.
  rewrite (munmap_model_nolazy _ _ _ Hnl) in Hspec.
  rewrite (sstep_cfg_det_iff ms m x8 _ _ _ Hh Hsvc Hspec); [reflexivity | exact Hh | exact (proj1 Hnl)].
Qed.

Theorem node_munmap_entry_cfg : forall ms x8 m len n,
  m_halted m = None -> model_nolazy m ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_entry_args ms m len n ->
  node_ok_cfg cfg segs (mkCfg ms m) unit (fun _ => [])
    (fun _ => mkCfg (sysret ms (Z_to_bv 64 0) (apply_unmaps (ms_mem ms) [(ms_gpr ms 0, n)]))
                    (with_vmmaps (ledger_unmap (ms_gpr ms 0) n (m_vmmaps m)) m)).
Proof.
  intros ms x8 m len n Hh Hnl Hsvc Hno Hargs. apply node_ok_cfg_of_step_iff_det.
  apply (munmap_entry_step_iff ms x8 m len n); assumption.
Qed.

Theorem rzc_munmap_entry : forall ms x8 m len n T,
  m_halted m = None -> model_nolazy m ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_entry_args ms m len n ->
  realizes_cfg cfg segs
    (mkCfg (sysret ms (Z_to_bv 64 0) (apply_unmaps (ms_mem ms) [(ms_gpr ms 0, n)]))
           (with_vmmaps (ledger_unmap (ms_gpr ms 0) n (m_vmmaps m)) m)) T ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m len n T Hh Hnl Hsvc Hno Hargs HT.
  eapply rzc_silent1; [apply (node_munmap_entry_cfg ms x8 m len n); assumption | exact HT].
Qed.

(* [comment removed for export] *)
Lemma munmap_entry_args_of_inv : forall R L c S ms m len n,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned (ms_gpr ms 1) = len -> 0 < len ->
  bv_unsigned n = page_round_up_Z len ->
  In (ms_gpr ms 0, n) (vm_maps (m_vmmaps m)) ->
  munmap_entry_args ms m len n.
Proof.
  intros R L c S ms m len n Hinv Hlen Hpos Hn Hin.
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hinv) as [_ Htop].
  pose proof (li_aligned _ _ _ _ _ Hinv) as Hali. pose proof (li_top _ _ _ _ _ Hinv) as Htp.
  rewrite Forall_forall in Hali, Htp.
  destruct (Hali _ Hin) as [Hal _]. destruct (Htp _ Hin) as [_ Hhi].
  unfold e_lo, e_hi, e_lo, e_sz in *. cbn [fst snd] in *.
  repeat split; try assumption. clear - Hhi Htop. lia.
Qed.

Theorem munmap_entry_inv : forall R L c S (m : Model) a n,
  ledger_inv R L c S (m_vmmaps m) ->
  In (a, n) (vm_maps (m_vmmaps m)) ->
  ledger_inv R L (c - 1) (S - bv_unsigned n)
    (m_vmmaps (with_vmmaps (ledger_unmap a n (m_vmmaps m)) m)).
Proof. intros R L c S m a n Hinv Hin. exact (ledger_inv_unmap R L c S _ a n Hinv Hin). Qed.

(* [comment removed for export] *)

Lemma brk_spec_iff : forall ms x8 m,
  bv_unsigned x8 = 214 ->
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    exists r, brk_r_ok m (ms_gpr ms 0) r = true
      /\ o = Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps m)))
                          (brk_unmaps r (vm_brk (m_vmmaps m))) [] [])
                (with_brk_next m (ms_gpr ms 0) r) [].
Proof.
  intros ms x8 m Hno o. rewrite (syscall_spec_brk segs ms x8 m o Hno).
  unfold brk_spec, bind, get_model, choose, modify, pure. split.
  - destruct o as [eff m' evs |]; intros H; sys_destruct.
    eexists. split; [eassumption | reflexivity].
  - intros (r & Hr & ->).
    exists m, m, [], []. split; [reflexivity |]. split; [| reflexivity].
    exists r, m, [], []. split; [exists r; split; [exact Hr | reflexivity] |]. split; [| reflexivity].
    eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_query_spec_iff : forall ms x8 m,
  bv_unsigned x8 = 214 ->
  (bv_unsigned (ms_gpr ms 0) = 0
   \/ bv_unsigned (ms_gpr ms 0) < bv_unsigned (vm_start_brk (m_vmmaps m))) ->
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (vm_brk (m_vmmaps m)) [] []) m [].
Proof.
  intros ms x8 m Hno Hq o. rewrite (brk_spec_iff ms x8 m Hno o).
  set (req := ms_gpr ms 0) in *. set (b := vm_brk (m_vmmaps m)).
  assert (Hok : forall r, brk_r_ok m req r = bv_eqb r b).
  { intros r. unfold brk_r_ok. cbv zeta. fold b.
    destruct Hq as [Hq | Hq].
    - rewrite (proj2 (w_is0_iff req) Hq). reflexivity.
    - unfold min_brk. rewrite (proj2 (Z.ltb_lt _ _) Hq), orb_true_r. reflexivity. }
  assert (Hpost : with_brk_next m req b = m).
  { unfold with_brk_next. cbv zeta. fold b. rewrite brk_unmaps_same. cbn [forget_vm_ranges].
    unfold b. rewrite brk_model_next_same. apply with_vmmaps_self. }
  split.
  - intros (r & Hr & ->). rewrite Hok in Hr. apply bv_eqb_eq in Hr. subst r.
    rewrite brk_zeros_same, brk_unmaps_same, Hpost. reflexivity.
  - intros ->. exists b. split; [rewrite Hok; apply bv_eqb_eq; reflexivity |].
    rewrite brk_zeros_same, brk_unmaps_same, Hpost. reflexivity.
Qed.

Theorem brk_query_step_iff : forall ms x8 m,
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  (bv_unsigned (ms_gpr ms 0) = 0
   \/ bv_unsigned (ms_gpr ms 0) < bv_unsigned (vm_start_brk (m_vmmaps m))) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\ st = SNext (mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m Hh Hl Hsvc Hno Hq e st.
  rewrite (sstep_cfg_det_iff ms m x8 _ _ _ Hh Hsvc (brk_query_spec_iff ms x8 m Hno Hq) Hh Hl).
  reflexivity.
Qed.

Theorem node_brk_query_cfg : forall ms x8 m,
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  (bv_unsigned (ms_gpr ms 0) = 0
   \/ bv_unsigned (ms_gpr ms 0) < bv_unsigned (vm_start_brk (m_vmmaps m))) ->
  node_ok_cfg cfg segs (mkCfg ms m) unit (fun _ => [])
    (fun _ => mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m Hh Hl Hsvc Hno Hq. apply node_ok_cfg_of_step_iff_det.
  apply (brk_query_step_iff ms x8 m); assumption.
Qed.

Theorem rzc_brk_query : forall ms x8 m T,
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  (bv_unsigned (ms_gpr ms 0) = 0
   \/ bv_unsigned (ms_gpr ms 0) < bv_unsigned (vm_start_brk (m_vmmaps m))) ->
  realizes_cfg cfg segs (mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m) T ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m T Hh Hl Hsvc Hno Hq HT.
  eapply rzc_silent1; [apply (node_brk_query_cfg ms x8 m); assumption | exact HT].
Qed.

(* [comment removed for export] *)
Definition brk_grow_args (ms : machine_state) (m : Model) : Prop :=
  let h := m_vmmaps m in
  0 < bv_unsigned (vm_brk h)
  /\ bv_unsigned (vm_brk h) mod page_size = 0
  /\ bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)
  /\ bv_unsigned (vm_brk h) < bv_unsigned (ms_gpr ms 0)
  /\ bv_unsigned (ms_gpr ms 0) mod page_size = 0.

Lemma brk_grow_args_of_inv : forall R L c S ms m,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned (ms_gpr ms 0) ->
  bv_unsigned (ms_gpr ms 0) mod page_size = 0 ->
  brk_grow_args ms m.
Proof.
  intros R L c S ms m Hinv H1 H2. unfold brk_grow_args. cbv zeta.
  split; [exact (li_brk_pos _ _ _ _ _ Hinv) |].
  split; [exact (li_brk_al _ _ _ _ _ Hinv) |].
  split; [exact (li_brk_min _ _ _ _ _ Hinv) |].
  split; assumption.
Qed.

Definition brk_grow_model (req : word) (m : Model) : Model :=
  with_vmmaps (ledger_brk_grow req (m_vmmaps m)) m.

(* [comment removed for export] *)
Definition brk_grow_zeros (req : word) (m : Model) : list (word * word) :=
  [(vm_brk (m_vmmaps m),
    Z_to_bv 64 (bv_unsigned req - bv_unsigned (vm_brk (m_vmmaps m))))].

Lemma brk_grow_spec_iff : forall ms x8 m,
  bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (vm_brk (m_vmmaps m)) [] []) m []
    \/ (brk_grow_b m (ms_gpr ms 0) = true
        /\ o = Ok (mkEffect (ms_gpr ms 0) [] (brk_grow_zeros (ms_gpr ms 0) m))
                  (brk_grow_model (ms_gpr ms 0) m) []).
Proof.
  intros ms x8 m Hno (Hb0 & Hbal & Hmin & Hlt & Hral) o.
  rewrite (brk_spec_iff ms x8 m Hno o).
  set (req := ms_gpr ms 0) in *. set (h := m_vmmaps m) in *. set (b := vm_brk h) in *.
  assert (Hreq0 : w_is0 req = false) by (apply w_is0_pos; lia).
  assert (Hneq : bv_eqb req b = false) by (apply bv_eqb_false_unsigned; lia).
  assert (Hok : forall r, brk_r_ok m req r = (bv_eqb r req || bv_eqb r b) && brk_grow_ok m req r).
  { intros r. unfold brk_r_ok. cbv zeta. fold h b. unfold min_brk.
    rewrite Hreq0. cbn [orb].
    rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned (vm_start_brk h)))) by lia.
    rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. reflexivity. }
  assert (Hpost_b : with_brk_next m req b = m).
  { unfold with_brk_next. cbv zeta. fold h b. rewrite brk_unmaps_same. cbn [forget_vm_ranges].
    unfold b. rewrite brk_model_next_same. apply with_vmmaps_self. }
  assert (Hpost_r : with_brk_next m req req = brk_grow_model req m).
  { unfold with_brk_next, brk_grow_model. cbv zeta. fold h b.
    unfold b. rewrite (brk_unmaps_grow h req Hb0 Hbal Hlt Hral). cbn [forget_vm_ranges].
    rewrite (brk_model_next_grow h req Hb0 Hbal Hlt Hral). reflexivity. }
  split.
  - intros (r & Hr & ->). rewrite Hok in Hr. apply andb_true_iff in Hr as [Hr Hg].
    apply orb_true_iff in Hr as [Hr | Hr]; apply bv_eqb_eq in Hr; subst r.
    + right. rewrite (brk_grow_ok_aligned m req Hb0 Hbal Hlt Hral) in Hg. split; [exact Hg |].
      unfold b. rewrite (brk_zeros_grow h req Hb0 Hbal Hlt Hral),
        (brk_unmaps_grow h req Hb0 Hbal Hlt Hral), Hpost_r. reflexivity.
    + left. rewrite brk_zeros_same, brk_unmaps_same, Hpost_b. reflexivity.
  - intros [-> | (Hg & ->)].
    + exists b. split.
      * rewrite Hok, bv_eqb_refl_true, orb_true_r. unfold b, h. rewrite brk_grow_ok_same. reflexivity.
      * rewrite brk_zeros_same, brk_unmaps_same, Hpost_b. reflexivity.
    + exists req. split.
      * rewrite Hok, bv_eqb_refl_true. cbn [orb andb].
        rewrite (brk_grow_ok_aligned m req Hb0 Hbal Hlt Hral). exact Hg.
      * unfold b. rewrite (brk_zeros_grow h req Hb0 Hbal Hlt Hral),
          (brk_unmaps_grow h req Hb0 Hbal Hlt Hral), Hpost_r. reflexivity.
Qed.

Lemma brk_refusal_old : forall ms x8 m,
  bv_unsigned x8 = 214 -> brk_grow_args ms m ->
  refusal_b (sys_input segs ms x8) m (vm_brk (m_vmmaps m)) = true.
Proof.
  intros ms x8 m Hno (Hb0 & Hbal & Hmin & Hlt & Hral).
  rewrite refusal_b_brk by exact Hno. rewrite in_arg0_sys_input. unfold brk_refusal_b. cbv zeta.
  rewrite (w_is0_pos (ms_gpr ms 0)) by lia. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite (bv_eqb_false_unsigned (ms_gpr ms 0) (vm_brk (m_vmmaps m))) by lia.
  rewrite bv_eqb_refl_true. reflexivity.
Qed.

Lemma brk_refusal_new : forall ms x8 m,
  bv_unsigned x8 = 214 -> brk_grow_args ms m ->
  refusal_b (sys_input segs ms x8) m (ms_gpr ms 0) = false.
Proof.
  intros ms x8 m Hno (Hb0 & Hbal & Hmin & Hlt & Hral).
  rewrite refusal_b_brk by exact Hno. rewrite in_arg0_sys_input. unfold brk_refusal_b. cbv zeta.
  rewrite (bv_eqb_false_unsigned (ms_gpr ms 0) (vm_brk (m_vmmaps m))) by lia.
  rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem brk_grow_step_iff : forall ms x8 m,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  brk_grow_b m (ms_gpr ms 0) = true ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms (ms_gpr ms 0)
                         (apply_zeros (ms_mem ms) (brk_grow_zeros (ms_gpr ms 0) m)))
                      (brk_grow_model (ms_gpr ms 0) m)).
Proof.
  intros ms x8 m Hc Hh Hl Hsvc Hno Hargs Hg e st.
  pose proof (brk_grow_spec_iff ms x8 m Hno Hargs) as Hspec.
  rewrite (sstep_cfg_filter_det_iff ms m x8
             (mkEffect (ms_gpr ms 0) [] (brk_grow_zeros (ms_gpr ms 0) m))
             (brk_grow_model (ms_gpr ms 0) m) []).
  - reflexivity.
  - apply alloc_family_off; [exact Hc | left; exact Hno].
  - exact Hh.
  - exact Hsvc.
  - apply Hspec. right. split; [exact Hg | reflexivity].
  - cbn [eff_ret]. apply brk_refusal_new; assumption.
  - exact Hh.
  - exact Hl.
  - intros o Ho. apply Hspec in Ho as [-> | (_ & ->)]; [right | left; reflexivity].
    eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
    split; [apply brk_refusal_old; assumption | split; assumption].
Qed.

(* [comment removed for export] *)
Theorem brk_grow_step_iff_blocked : forall ms x8 m,
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  brk_grow_b m (ms_gpr ms 0) = false ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\ st = SNext (mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m Hh Hl Hsvc Hno Hargs Hg e st.
  pose proof (brk_grow_spec_iff ms x8 m Hno Hargs) as Hspec.
  assert (Honly : forall o, syscall_spec (sys_input segs ms x8) m o <->
                            o = Ok (mkEffect (vm_brk (m_vmmaps m)) [] []) m []).
  { intros o. rewrite Hspec. split; [| intros ->; left; reflexivity].
    intros [-> | (Hg' & _)]; [reflexivity | rewrite Hg in Hg'; discriminate Hg']. }
  rewrite (sstep_cfg_det_iff ms m x8 _ _ _ Hh Hsvc Honly Hh Hl). reflexivity.
Qed.

Theorem node_brk_grow_cfg : forall ms x8 m,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  brk_grow_b m (ms_gpr ms 0) = true ->
  node_ok_cfg cfg segs (mkCfg ms m) unit (fun _ => [])
    (fun _ => mkCfg (sysret ms (ms_gpr ms 0)
                       (apply_zeros (ms_mem ms) (brk_grow_zeros (ms_gpr ms 0) m)))
                    (brk_grow_model (ms_gpr ms 0) m)).
Proof.
  intros ms x8 m Hc Hh Hl Hsvc Hno Hargs Hg. apply node_ok_cfg_of_step_iff_det.
  apply (brk_grow_step_iff ms x8 m); assumption.
Qed.

Theorem node_brk_grow_blocked_cfg : forall ms x8 m,
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  brk_grow_b m (ms_gpr ms 0) = false ->
  node_ok_cfg cfg segs (mkCfg ms m) unit (fun _ => [])
    (fun _ => mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m Hh Hl Hsvc Hno Hargs Hg. apply node_ok_cfg_of_step_iff_det.
  apply (brk_grow_step_iff_blocked ms x8 m); assumption.
Qed.

(* [comment removed for export] *)
Theorem rzc_brk_grow : forall ms x8 m T,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  (brk_grow_b m (ms_gpr ms 0) = true ->
   realizes_cfg cfg segs
     (mkCfg (sysret ms (ms_gpr ms 0)
               (apply_zeros (ms_mem ms) (brk_grow_zeros (ms_gpr ms 0) m)))
            (brk_grow_model (ms_gpr ms 0) m)) T) ->
  (brk_grow_b m (ms_gpr ms 0) = false ->
   realizes_cfg cfg segs (mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m) T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m T Hc Hh Hl Hsvc Hno Hargs HT HF.
  destruct (brk_grow_b m (ms_gpr ms 0)) eqn:Hg.
  - eapply rzc_silent1; [apply (node_brk_grow_cfg ms x8 m); assumption | apply HT; reflexivity].
  - eapply rzc_silent1; [apply (node_brk_grow_blocked_cfg ms x8 m); assumption
                        | apply HF; reflexivity].
Qed.

Theorem brk_grow_inv : forall R L c S ms m,
  ledger_inv R L c S (m_vmmaps m) ->
  brk_grow_args ms m ->
  brk_grow_b m (ms_gpr ms 0) = true ->
  ledger_inv R L (c + 1)
    (S + (bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps m))))
    (m_vmmaps (brk_grow_model (ms_gpr ms 0) m)).
Proof.
  intros R L c S ms m Hinv (Hb0 & Hbal & Hmin & Hlt & Hral) Hg.
  unfold brk_grow_b in Hg. cbv zeta in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Htop Hfree].
  apply Z.leb_le in Htop. rewrite (li_reserved _ _ _ _ _ Hinv) in Hfree.
  change (m_vmmaps (brk_grow_model (ms_gpr ms 0) m))
    with (ledger_brk_grow (ms_gpr ms 0) (m_vmmaps m)).
  apply ledger_inv_brk_grow; assumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_guard_args (ms : machine_state) (m : Model) (len : Z) : Prop :=
  let h := m_vmmaps m in
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  bv_unsigned (ms_gpr ms 1) = len /\ 0 < len
  /\ bv_unsigned (ms_gpr ms 2) = 0          (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 3) = 50         (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 5) = 0
  /\ bv_unsigned addr mod page_size = 0 /\ 0 < bv_unsigned addr
  /\ bv_unsigned addr + nZ <= alloc_top h
  /\ region_free (vm_reserved h) addr (Z_to_bv 64 nZ) = true
  /\ map_contains (vm_maps h) addr (Z_to_bv 64 nZ) = true.

Definition mmap_guard_model (addr : word) (nZ : Z) (m : Model) : Model :=
  with_vmmaps (ledger_guard addr (Z_to_bv 64 nZ) (m_vmmaps m)) m.

Definition mmap_guard_destroyed_model (addr : word) (nZ : Z) (m : Model) : Model :=
  with_mmap_destroyed addr (Z_to_bv 64 nZ)
    (mmap_fixed_destroyed_next (m_vmmaps m) addr (Z_to_bv 64 nZ)) m.

Lemma mmap_guard_spec_iff : forall ms x8 m len,
  bv_unsigned x8 = 222 ->
  model_nolazy m ->
  mmap_guard_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
    \/ o = Ok (mkEffectU addr [] [] [(addr, Z_to_bv 64 nZ)] [] []) (mmap_guard_model addr nZ m) []
    \/ o = Ok (mkEffectU (errno_ret ENOMEM) [] [] [(addr, Z_to_bv 64 nZ)] [] [])
              (mmap_guard_destroyed_model addr nZ m) [].
Proof.
  intros ms x8 m len Hno Hnl (Hlen & Hpos & Hprot & Hflags & Hoff & Hal & Ha0 & Htop & HfR & Hcont)
    addr nZ o.
  rewrite (syscall_spec_mmap segs ms x8 m o Hno).
  fold addr in Hal, Ha0, Htop, HfR, Hcont. fold nZ in Htop, HfR, Hcont.
  set (flags := ms_gpr ms 3) in *. set (off := ms_gpr ms 5) in *. set (prot := ms_gpr ms 2) in *.
  assert (G1 : mmap_off_aligned_b off = true)
    by (unfold mmap_off_aligned_b; rewrite Hoff; reflexivity).
  assert (G2 : mmap_anon_b flags = true) by (unfold mmap_anon_b; rewrite Hflags; reflexivity).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : mmap_modeled_b prot flags off = false)
    by (unfold mmap_modeled_b; rewrite Hprot; reflexivity).
  assert (G5 : mmap_noaccess_b prot flags off = false)
    by (unfold mmap_noaccess_b, mmap_flags_core; rewrite Hprot, Hflags; reflexivity).
  assert (G6 : mmap_fixed_noaccess_b prot flags off = true).
  { unfold mmap_fixed_noaccess_b, mmap_flags_core.
    rewrite Hprot, Hflags, (proj2 (w_is0_iff off) Hoff). reflexivity. }
  assert (G7 : mmap_noreserve_b flags = false)
    by (unfold mmap_noreserve_b; rewrite Hflags; reflexivity).
  pose proof (alloc_top_lt (m_vmmaps m)) as Hat.
  assert (G8 : (two_pow_64 <=? bv_unsigned addr + nZ) = false) by (apply Z.leb_gt; lia).
  assert (G9 : (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m)) = true) by (apply Z.leb_le; exact Htop).
  assert (G10 : (bv_unsigned addr mod page_size =? 0) = true) by (apply Z.eqb_eq; exact Hal).
  assert (G11 : (0 <? bv_unsigned addr) = true) by (apply Z.ltb_lt; exact Ha0).
  assert (Hrepl : with_mmap_replacement flags addr (Z_to_bv 64 nZ)
                    (with_vmmaps (ledger_guard addr (Z_to_bv 64 nZ) (m_vmmaps m)) m)
                  = mmap_guard_model addr nZ m).
  { unfold with_mmap_replacement, with_mmap_backing. rewrite G7.
    apply vm_forget_range_nolazy. apply model_nolazy_with_vmmaps. exact Hnl. }
  unfold mmap_spec. rewrite G1, G2, G3, G4, G5, G6. cbn [negb]. rewrite Hlen. fold nZ. fold addr.
  rewrite G8.
  rewrite bind_get_model. rewrite G9, G10, G11. cbn [negb]. rewrite HfR, Hcont. cbn [andb].
  fold (ledger_guard addr (Z_to_bv 64 nZ) (m_vmmaps m)). rewrite Hrepl.
  fold (mmap_guard_destroyed_model addr nZ m).
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, modify.
  split.
  - destruct o as [eff m' evs |].
    + intros [H | [H | H]]; sys_destruct.
      * left. match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end. reflexivity.
      * right. left. reflexivity.
      * right. right.
        match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end. reflexivity.
    + intros [H | [H | H]]; sys_destruct.
  - intros [-> | [-> | ->]].
    + left. exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
      split; reflexivity.
    + right. left. eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
    + right. right. exists ENOMEM, m, [], [].
      split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |]. split; [| reflexivity].
      eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Lemma mmap_guard_destroyed_facts : forall addr nZ m,
  m_halted (mmap_guard_destroyed_model addr nZ m) = m_halted m
  /\ (m_vm_lazy m = [] -> m_vm_lazy (mmap_guard_destroyed_model addr nZ m) = []).
Proof.
  intros addr nZ m. split; [reflexivity |]. intros Hl.
  unfold mmap_guard_destroyed_model, with_mmap_destroyed, vm_forget_range.
  change (m_vm_lazy (with_vm_backing ?l ?p ?x)) with l.
  change (m_vm_lazy (with_vmmaps ?h m)) with (m_vm_lazy m). rewrite Hl. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem mmap_guard_step_iff : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None -> model_nolazy m ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_guard_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms addr (apply_unmaps (ms_mem ms) [(addr, Z_to_bv 64 nZ)]))
                      (mmap_guard_model addr nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hnl Hsvc Hno Hargs addr nZ e st.
  pose proof (mmap_guard_spec_iff ms x8 m len Hno Hnl Hargs) as Hspec. cbv zeta in Hspec.
  fold addr nZ in Hspec.
  destruct Hargs as (_ & _ & _ & _ & _ & Hal & _). fold addr in Hal.
  rewrite (sstep_cfg_filter_det_iff ms m x8
             (mkEffectU addr [] [] [(addr, Z_to_bv 64 nZ)] [] [])
             (mmap_guard_model addr nZ m) []).
  - reflexivity.
  - apply alloc_family_off; [exact Hc | right; right; left; exact Hno].
  - exact Hh.
  - exact Hsvc.
  - apply Hspec. right. left. reflexivity.
  - cbn [eff_ret]. apply mmap_refusal_grant; assumption.
  - exact Hh.
  - exact (proj1 Hnl).
  - intros o Ho. apply Hspec in Ho as [-> | [-> | ->]]; [right | left; reflexivity | right].
    + eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
      split; [apply mmap_refusal_enomem; exact Hno | split; [exact Hh | exact (proj1 Hnl)]].
    + eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
      split; [apply mmap_refusal_enomem; exact Hno |].
      destruct (mmap_guard_destroyed_facts addr nZ m) as [H1 H2].
      split; [rewrite H1; exact Hh | apply H2; exact (proj1 Hnl)].
Qed.

Theorem node_mmap_guard_cfg : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None -> model_nolazy m ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_guard_args ms m len ->
  node_ok_cfg cfg segs (mkCfg ms m) unit (fun _ => [])
    (fun _ => mkCfg (sysret ms (ms_gpr ms 0)
                       (apply_unmaps (ms_mem ms)
                          [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z len))]))
                    (mmap_guard_model (ms_gpr ms 0) (page_round_up_Z len) m)).
Proof.
  intros ms x8 m len Hc Hh Hnl Hsvc Hno Hargs. apply node_ok_cfg_of_step_iff_det.
  apply (mmap_guard_step_iff ms x8 m len); assumption.
Qed.

Theorem rzc_mmap_guard : forall ms x8 m len T,
  sc_alloc cfg = false ->
  m_halted m = None -> model_nolazy m ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_guard_args ms m len ->
  realizes_cfg cfg segs
    (mkCfg (sysret ms (ms_gpr ms 0)
              (apply_unmaps (ms_mem ms) [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z len))]))
           (mmap_guard_model (ms_gpr ms 0) (page_round_up_Z len) m)) T ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m len T Hc Hh Hnl Hsvc Hno Hargs HT.
  eapply rzc_silent1; [apply (node_mmap_guard_cfg ms x8 m len); assumption | exact HT].
Qed.

(* [comment removed for export] *)
Lemma mmap_guard_args_of_inv : forall R L c S ms m len p,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned (ms_gpr ms 1) = len -> 0 < len ->
  bv_unsigned (ms_gpr ms 2) = 0 -> bv_unsigned (ms_gpr ms 3) = 50 ->
  bv_unsigned (ms_gpr ms 5) = 0 ->
  bv_unsigned (ms_gpr ms 0) mod page_size = 0 ->
  In p (vm_maps (m_vmmaps m)) ->
  e_lo p <= bv_unsigned (ms_gpr ms 0) ->
  bv_unsigned (ms_gpr ms 0) + page_round_up_Z len <= e_hi p ->
  mmap_guard_args ms m len.
Proof.
  intros R L c S ms m len p Hinv Hlen Hpos Hprot Hflags Hoff Hal Hp Hlo Hhi.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hat. unfold two_pow_64 in Hat.
  pose proof (page_round_up_Z_pos len Hpos) as Hnpos.
  pose proof (li_top _ _ _ _ _ Hinv) as Htp. pose proof (li_disj_R _ _ _ _ _ Hinv) as HdR.
  pose proof (li_reserved _ _ _ _ _ Hinv) as HR.
  rewrite Forall_forall in Htp, HdR.
  destruct (Htp p Hp) as [Hp0 Hptop].
  assert (Hu : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len)
    by (apply u64_lit; clear - Hnpos Hhi Hptop Hat Hlo Hp0; lia).
  assert (Hin : e_inside (ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z len)) p).
  { unfold e_inside, e_hi at 1, e_lo at 2, e_lo at 2, e_sz. cbn [fst snd]. rewrite Hu.
    split; assumption. }
  unfold mmap_guard_args. cbv zeta. repeat split; try assumption.
  - clear - Hp0 Hlo. lia.
  - clear - Hhi Hptop. lia.
  - rewrite HR. apply region_free_iff. apply Forall_forall. intros r Hr.
    specialize (HdR p Hp). rewrite Forall_forall in HdR.
    apply e_disj_sym. eapply e_disj_inside; [apply e_disj_sym; apply HdR; exact Hr | exact Hin].
  - eapply map_contains_intro; [exact Hp | exact Hin].
Qed.

Theorem mmap_guard_inv : forall R L c S (m : Model) addr nZ p,
  ledger_inv R L c S (m_vmmaps m) ->
  In p (vm_maps (m_vmmaps m)) ->
  e_inside (addr, Z_to_bv 64 nZ) p -> 0 < bv_unsigned (Z_to_bv 64 nZ) ->
  ledger_inv R L c S (m_vmmaps (mmap_guard_model addr nZ m)).
Proof.
  intros R L c S m addr nZ p Hinv Hp Hin Hn.
  exact (ledger_inv_guard R L c S _ addr (Z_to_bv 64 nZ) p Hinv Hp Hin Hn).
Qed.

(* [comment removed for export] *)

Definition mmap_na_args (ms : machine_state) (len : Z) : Prop :=
  bv_unsigned (ms_gpr ms 1) = len /\ 0 < len
  /\ bv_unsigned (ms_gpr ms 2) = 0          (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 3) = 34         (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 5) = 0.

Definition mmap_na_model (a : word) (nZ : Z) (m : Model) : Model :=
  with_vmmaps (ledger_grant_na a (Z_to_bv 64 nZ) (m_vmmaps m)) m.

Lemma mmap_na_spec_iff : forall ms x8 m len,
  bv_unsigned x8 = 222 ->
  mmap_na_args ms len ->
  let nZ := page_round_up_Z len in
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
    \/ exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true
                 /\ o = Ok (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []) (mmap_na_model a nZ m) [].
Proof.
  intros ms x8 m len Hno (Hlen & Hpos & Hprot & Hflags & Hoff) nZ o.
  rewrite (syscall_spec_mmap segs ms x8 m o Hno).
  set (flags := ms_gpr ms 3) in *. set (off := ms_gpr ms 5) in *. set (prot := ms_gpr ms 2) in *.
  assert (G1 : mmap_off_aligned_b off = true)
    by (unfold mmap_off_aligned_b; rewrite Hoff; reflexivity).
  assert (G2 : mmap_anon_b flags = true) by (unfold mmap_anon_b; rewrite Hflags; reflexivity).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : mmap_modeled_b prot flags off = false)
    by (unfold mmap_modeled_b; rewrite Hprot; reflexivity).
  assert (G5 : mmap_noaccess_b prot flags off = true).
  { unfold mmap_noaccess_b, mmap_flags_core.
    rewrite Hprot, Hflags, (proj2 (w_is0_iff off) Hoff). reflexivity. }
  assert (G6 : mmap_noreserve_b flags = false)
    by (unfold mmap_noreserve_b; rewrite Hflags; reflexivity).
  unfold mmap_spec. rewrite G1, G2, G3, G4, G5. cbn [negb].
  unfold with_mmap_backing. rewrite G6, Hlen. fold nZ.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify.
  split.
  - destruct o as [eff m' evs |].
    + intros [H | H]; sys_destruct.
      * left. match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end.
        reflexivity.
      * right. eexists. split; [apply mmap_grant_na_b_iff; repeat split; eassumption |].
        reflexivity.
    + intros [H | H]; sys_destruct.
  - intros [-> | (a & Ha & ->)].
    + left. exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
      split; reflexivity.
    + right. apply mmap_grant_na_b_iff in Ha as (A1 & A2 & A3 & A4).
      exists m, m, [], []. split; [reflexivity |]. split; [| reflexivity].
      exists a, m, [], []. split.
      { exists a. split; [| reflexivity]. repeat split; assumption. }
      split; [| reflexivity].
      exists tt, (mmap_na_model a nZ m), [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Theorem mmap_na_step_iff : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_na_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true /\ e = [] /\
      st = SNext (mkCfg (sysret ms a (apply_unmaps (ms_mem ms) [(a, Z_to_bv 64 nZ)]))
                        (mmap_na_model a nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hlazy Hsvc Hno Hargs nZ (a0 & Ha0) e st.
  pose proof (mmap_na_spec_iff ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec. fold nZ in Hspec.
  assert (Hoff : injected_family_off cfg (sys_input segs ms x8) = true)
    by (apply alloc_family_off; [exact Hc | right; right; left; exact Hno]).
  rewrite (sstep_cfg_svc_iff cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & Hns & ->). apply Hspec in Hs as [Hs | (a & Ha & Hs)].
      * exfalso. inversion Hs; subst. apply Hns. split; [exact Hoff |]. split.
        { cbn [eff_ret]. apply mmap_refusal_enomem. exact Hno. }
        exists (mkEffectU a0 [] [] [(a0, Z_to_bv 64 nZ)] [] []), (mmap_na_model a0 nZ m), [].
        split; [apply Hspec; right; exists a0; split; [exact Ha0 | reflexivity] |].
        cbn [eff_ret]. apply mmap_refusal_grant; [exact Hno |].
        apply mmap_grant_na_b_iff in Ha0. tauto.
      * inversion Hs; subst. exists a. split; [exact Ha |]. split; reflexivity.
    + intros (a & Ha & -> & ->).
      exists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []), (mmap_na_model a nZ m).
      split; [apply Hspec; right; exists a; split; [exact Ha | reflexivity] |].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. cbn [eff_ret].
      apply mmap_refusal_grant; [exact Hno |]. apply mmap_grant_na_b_iff in Ha. tauto.
  - intros Hun. apply Hspec in Hun as [Hun | (a & _ & Hun)]; discriminate Hun.
  - intros eff m' evs Hs. apply Hspec in Hs as [Hs | (a & _ & Hs)]; inversion Hs; subst.
    + split; assumption.
    + split; [exact Hh | exact Hlazy].
Qed.

Theorem rzc_mmap_na : forall ms x8 m len T,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_na_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true) ->
  (forall a, mmap_grant_na_b (m_vmmaps m) a nZ = true ->
     realizes_cfg cfg segs
       (mkCfg (sysret ms a (apply_unmaps (ms_mem ms) [(a, Z_to_bv 64 nZ)]))
              (mmap_na_model a nZ m)) T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m len T Hc Hh Hlazy Hsvc Hno Hargs nZ Hex HT.
  destruct Hex as (a0 & Ha0).
  pose (I := {a : word | mmap_grant_na_b (m_vmmaps m) a nZ = true}).
  eapply (rzc_cases_same cfg segs (mkCfg ms m) I
            (fun i => mkCfg (sysret ms (proj1_sig i)
                               (apply_unmaps (ms_mem ms) [(proj1_sig i, Z_to_bv 64 nZ)]))
                            (mmap_na_model (proj1_sig i) nZ m)) T (exist _ a0 Ha0)).
  - apply node_ok_cfg_of_step_iff. intros e st.
    rewrite (mmap_na_step_iff ms x8 m len Hc Hh Hlazy Hsvc Hno Hargs (ex_intro _ a0 Ha0) e st).
    fold nZ. split.
    + intros (a & Ha & -> & ->). exists (exist _ a Ha). split; reflexivity.
    + intros ([a Ha] & -> & ->). exists a. cbn [proj1_sig]. repeat split. exact Ha.
  - intros [a Ha]. cbn [proj1_sig]. apply HT. exact Ha.
Qed.

Theorem mmap_na_inv : forall R L c S (m : Model) a len,
  ledger_inv R L c S (m_vmmaps m) ->
  0 < len ->
  mmap_grant_na_b (m_vmmaps m) a (page_round_up_Z len) = true ->
  ledger_inv R L (c + 1) (S + page_round_up_Z len)
    (m_vmmaps (mmap_na_model a (page_round_up_Z len) m)).
Proof.
  intros R L c S m a len Hinv Hlen Ha.
  apply mmap_grant_na_b_iff in Ha as (A1 & A2 & A3 & A4).
  rewrite (li_reserved _ _ _ _ _ Hinv) in A4.
  change (m_vmmaps (mmap_na_model a (page_round_up_Z len) m))
    with (ledger_grant_na a (Z_to_bv 64 (page_round_up_Z len)) (m_vmmaps m)).
  apply ledger_inv_grant_na; try assumption.
  - apply page_round_up_Z_pos. exact Hlen.
  - apply page_round_up_Z_mod.
Qed.

(* [comment removed for export] *)
Definition mprotect_rw_args (ms : machine_state) (m : Model) (len : Z) : Prop :=
  let h := m_vmmaps m in
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  bv_unsigned (ms_gpr ms 1) = len /\ 0 < len
  /\ bv_unsigned (ms_gpr ms 2) = 3          (* [comment removed for export] *)
  /\ bv_unsigned addr mod page_size = 0
  /\ bv_unsigned addr + nZ < 2 ^ 64
  /\ map_contains (vm_noaccess h) addr (Z_to_bv 64 nZ) = true
  /\ map_contains (vm_maps h) addr (Z_to_bv 64 nZ) = true.

Definition mprotect_rw_model (addr : word) (nZ : Z) (m : Model) : Model :=
  with_vmmaps (ledger_expose addr (Z_to_bv 64 nZ) (m_vmmaps m)) m.

Lemma mprotect_model_next_eq : forall m addr n,
  mprotect_model_next m addr n = with_vmmaps (ledger_expose addr n (m_vmmaps m)) m.
Proof. reflexivity. Qed.

Lemma mprotect_rw_spec_iff : forall ms x8 m len,
  bv_unsigned x8 = 226 ->
  mprotect_rw_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
    \/ (mprotect_budget_ok m addr (Z_to_bv 64 nZ) = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, Z_to_bv 64 nZ)]) (mprotect_rw_model addr nZ m) []).
Proof.
  intros ms x8 m len Hno (Hlen & Hpos & Hprot & Hal & Hhi & Hcn & Hcm) addr nZ o.
  rewrite (syscall_spec_mprotect segs ms x8 m o Hno).
  fold addr in Hal, Hhi, Hcn, Hcm. fold nZ in Hhi, Hcn, Hcm.
  set (prot := ms_gpr ms 2) in *.
  assert (G1 : mprotect_grows_conflict_b prot = false)
    by (unfold mprotect_grows_conflict_b; rewrite Hprot; reflexivity).
  assert (G2 : (bv_unsigned addr mod page_size =? 0) = true) by (apply Z.eqb_eq; exact Hal).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : (two_pow_64 <=? bv_unsigned addr + nZ) = false)
    by (apply Z.leb_gt; unfold two_pow_64; exact Hhi).
  assert (G5 : mprotect_modeled_b prot = true)
    by (unfold mprotect_modeled_b; rewrite Hprot; reflexivity).
  unfold mprotect_spec. fold addr. rewrite G1, G2, G3. cbn [negb]. rewrite Hlen. fold nZ.
  rewrite G4, G5. rewrite bind_get_model. rewrite Hcn, Hcm. cbn [andb].
  rewrite mprotect_model_next_eq. fold (mprotect_rw_model addr nZ m).
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, modify.
  split.
  - destruct o as [eff m' evs |].
    + intros [H | H]; sys_destruct.
      * left. match goal with Hi : In _ mprotect_errnos |- _ => destruct Hi as [<- | []] end.
        reflexivity.
      * right. split; [assumption | reflexivity].
    + intros [H | H]; sys_destruct.
  - intros [-> | (Hb & ->)].
    + left. exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
      split; reflexivity.
    + right. exists tt, m, [], []. split; [exists tt; split; [exact Hb | reflexivity] |].
      split; [| reflexivity].
      eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Lemma mprotect_refusal_enomem : forall ms x8 m,
  bv_unsigned x8 = 226 ->
  refusal_b (sys_input segs ms x8) m (errno_ret ENOMEM) = true.
Proof.
  intros ms x8 m Hno. rewrite refusal_b_enomem_arm by (right; right; exact Hno).
  apply bv_eqb_eq. reflexivity.
Qed.

Lemma mprotect_refusal_zero : forall ms x8 m,
  bv_unsigned x8 = 226 ->
  refusal_b (sys_input segs ms x8) m (Z_to_bv 64 0) = false.
Proof.
  intros ms x8 m Hno. rewrite refusal_b_enomem_arm by (right; right; exact Hno).
  apply not_enomem_page_aligned. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem mprotect_rw_step_iff : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226 ->
  mprotect_rw_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  mprotect_budget_ok m addr (Z_to_bv 64 nZ) = true ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms (Z_to_bv 64 0) (apply_zeros (ms_mem ms) [(addr, Z_to_bv 64 nZ)]))
                      (mprotect_rw_model addr nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hl Hsvc Hno Hargs addr nZ Hb e st.
  pose proof (mprotect_rw_spec_iff ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec.
  fold addr nZ in Hspec.
  rewrite (sstep_cfg_filter_det_iff ms m x8
             (mkEffect (Z_to_bv 64 0) [] [(addr, Z_to_bv 64 nZ)])
             (mprotect_rw_model addr nZ m) []).
  - reflexivity.
  - apply alloc_family_off; [exact Hc | right; right; right; exact Hno].
  - exact Hh.
  - exact Hsvc.
  - apply Hspec. right. split; [exact Hb | reflexivity].
  - cbn [eff_ret]. apply mprotect_refusal_zero. exact Hno.
  - exact Hh.
  - exact Hl.
  - intros o Ho. apply Hspec in Ho as [-> | (_ & ->)]; [right | left; reflexivity].
    eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
    split; [apply mprotect_refusal_enomem; exact Hno | split; assumption].
Qed.

(* [comment removed for export] *)
Theorem mprotect_rw_step_iff_forced : forall ms x8 m len,
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226 ->
  mprotect_rw_args ms m len ->
  mprotect_budget_ok m (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z len)) = false ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\ st = SNext (mkCfg (sysret ms (errno_ret ENOMEM) (ms_mem ms)) m).
Proof.
  intros ms x8 m len Hh Hl Hsvc Hno Hargs Hb e st.
  pose proof (mprotect_rw_spec_iff ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec.
  assert (Honly : forall o, syscall_spec (sys_input segs ms x8) m o <->
                            o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []).
  { intros o. rewrite Hspec. split; [| intros ->; left; reflexivity].
    intros [-> | (Hb' & _)]; [reflexivity | rewrite Hb in Hb'; discriminate Hb']. }
  rewrite (sstep_cfg_det_iff ms m x8 _ _ _ Hh Hsvc Honly Hh Hl). reflexivity.
Qed.

Theorem rzc_mprotect_rw : forall ms x8 m len T,
  sc_alloc cfg = false ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226 ->
  mprotect_rw_args ms m len ->
  mprotect_budget_ok m (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  realizes_cfg cfg segs
    (mkCfg (sysret ms (Z_to_bv 64 0)
              (apply_zeros (ms_mem ms) [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z len))]))
           (mprotect_rw_model (ms_gpr ms 0) (page_round_up_Z len) m)) T ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m len T Hc Hh Hl Hsvc Hno Hargs Hb HT.
  eapply rzc_silent1; [| exact HT]. apply node_ok_cfg_of_step_iff_det.
  apply (mprotect_rw_step_iff ms x8 m len); assumption.
Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_acct : forall R L c S m addr n,
  ledger_inv R L c S (m_vmmaps m) ->
  m_vm_materialized m = [] ->
  S <= L ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros R L c S m addr n Hinv Hmat HSL.
  unfold mprotect_budget_ok, vm_backing_within_limit. rewrite mprotect_model_next_eq.
  apply Z.leb_le.
  pose proof (vm_backing_used_le_live (with_vmmaps (ledger_expose addr n (m_vmmaps m)) m) Hmat) as Hu.
  change (vm_maps (m_vmmaps (with_vmmaps (ledger_expose addr n (m_vmmaps m)) m)))
    with (vm_maps (m_vmmaps m)) in Hu.
  change (vm_limit (m_vmmaps (with_vmmaps (ledger_expose addr n (m_vmmaps m)) m)))
    with (vm_limit (m_vmmaps m)).
  pose proof (li_limit _ _ _ _ _ Hinv). pose proof (li_size _ _ _ _ _ Hinv). lia.
Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_of_premise : forall ms x8 m len,
  bv_unsigned x8 = 226 ->
  mprotect_rw_args ms m len ->
  alloc_budget_refused_b (sys_input segs ms x8) m = false ->
  mprotect_budget_ok m (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z len)) = true.
Proof.
  intros ms x8 m len Hno (Hlen & Hpos & Hprot & Hal & Hhi & Hcn & Hcm) Hb.
  unfold alloc_budget_refused_b in Hb. rewrite in_sysno_sys_input, Hno in Hb. cbv zeta in Hb.
  change (226 =? 214) with false in Hb. change (226 =? 216) with false in Hb.
  change (226 =? 222) with false in Hb. change (226 =? 226) with true in Hb. cbv iota in Hb.
  change (in_arg (sys_input segs ms x8) 0) with (ms_gpr ms 0) in Hb.
  change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1) in Hb.
  change (in_arg (sys_input segs ms x8) 2) with (ms_gpr ms 2) in Hb.
  set (prot := ms_gpr ms 2) in *.
  assert (G1 : mprotect_grows_conflict_b prot = false)
    by (unfold mprotect_grows_conflict_b; rewrite Hprot; reflexivity).
  assert (G5 : mprotect_modeled_b prot = true)
    by (unfold mprotect_modeled_b; rewrite Hprot; reflexivity).
  unfold mprotect_budget_refused_b in Hb.
  rewrite G1, (proj2 (Z.eqb_eq _ _) Hal), (w_is0_pos (ms_gpr ms 1)) in Hb by lia.
  cbn [negb] in Hb. rewrite Hlen in Hb.
  rewrite (proj2 (Z.leb_gt _ _)) in Hb by (unfold two_pow_64; exact Hhi).
  rewrite G5 in Hb. cbv zeta in Hb. rewrite Hcn, Hcm in Hb. cbn [andb] in Hb.
  apply negb_false_iff in Hb. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma mprotect_rw_args_of_inv : forall R L c S ms m len q,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned (ms_gpr ms 1) = len -> 0 < len ->
  bv_unsigned (ms_gpr ms 2) = 3 ->
  bv_unsigned (ms_gpr ms 0) mod page_size = 0 ->
  In q (vm_noaccess (m_vmmaps m)) ->
  e_lo q <= bv_unsigned (ms_gpr ms 0) ->
  bv_unsigned (ms_gpr ms 0) + page_round_up_Z len <= e_hi q ->
  mprotect_rw_args ms m len.
Proof.
  intros R L c S ms m len q Hinv Hlen Hpos Hprot Hal Hq Hlo Hhi.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hat. unfold two_pow_64 in Hat.
  pose proof (page_round_up_Z_pos len Hpos) as Hnpos.
  pose proof (li_noacc _ _ _ _ _ Hinv) as Hna. pose proof (li_top _ _ _ _ _ Hinv) as Htp.
  rewrite Forall_forall in Hna, Htp.
  destruct (Hna q Hq) as (_ & p & Hp & Hqp). destruct (Htp p Hp) as [Hp0 Hptop].
  destruct Hqp as [Hqp1 Hqp2]. pose proof (e_lo_nonneg q) as Hq0.
  assert (Hu : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len)
    by (apply u64_lit; clear - Hnpos Hhi Hptop Hat Hlo Hq0 Hqp2; lia).
  assert (Hinq : e_inside (ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z len)) q).
  { unfold e_inside, e_hi at 1, e_lo at 2, e_lo at 2, e_sz. cbn [fst snd]. rewrite Hu.
    split; assumption. }
  assert (Hinp : e_inside (ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z len)) p).
  { destruct Hinq as [H1 H2]. split; lia. }
  unfold mprotect_rw_args. cbv zeta. repeat split; try assumption.
  - clear - Hhi Hqp2 Hptop Hat. lia.
  - eapply map_contains_intro; [exact Hq | exact Hinq].
  - eapply map_contains_intro; [exact Hp | exact Hinp].
Qed.

Theorem mprotect_rw_inv : forall R L c S (m : Model) addr nZ,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned addr + bv_unsigned (Z_to_bv 64 nZ) < 2 ^ 64 ->
  ledger_inv R L c S (m_vmmaps (mprotect_rw_model addr nZ m)).
Proof.
  intros R L c S m addr nZ Hinv Hhi.
  exact (ledger_inv_expose R L c S _ addr (Z_to_bv 64 nZ) Hinv Hhi).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_anon_budget_of_premise : forall ms x8 m len,
  bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  alloc_budget_refused_b (sys_input segs ms x8) m = false ->
  vm_backing_used m + page_round_up_Z len <= vm_limit (m_vmmaps m).
Proof.
  intros ms x8 m len Hno (Hlen & Hpos & Hprot & Hflags & Hoff) Hb.
  unfold alloc_budget_refused_b in Hb. rewrite in_sysno_sys_input, Hno in Hb. cbv zeta in Hb.
  change (222 =? 214) with false in Hb. change (222 =? 216) with false in Hb.
  change (222 =? 222) with true in Hb. cbv iota in Hb.
  change (in_arg (sys_input segs ms x8) 0) with (ms_gpr ms 0) in Hb.
  change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1) in Hb.
  change (in_arg (sys_input segs ms x8) 2) with (ms_gpr ms 2) in Hb.
  change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3) in Hb.
  change (in_arg (sys_input segs ms x8) 4) with (ms_gpr ms 4) in Hb.
  change (in_arg (sys_input segs ms x8) 5) with (ms_gpr ms 5) in Hb.
  set (flags := ms_gpr ms 3) in *. set (off := ms_gpr ms 5) in *. set (prot := ms_gpr ms 2) in *.
  assert (G1 : mmap_off_aligned_b off = true)
    by (unfold mmap_off_aligned_b; rewrite Hoff; reflexivity).
  assert (G2 : mmap_anon_b flags = true) by (unfold mmap_anon_b; rewrite Hflags; reflexivity).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : mmap_modeled_b prot flags off = true).
  { unfold mmap_modeled_b, mmap_flags_core.
    rewrite Hprot, Hflags, (proj2 (w_is0_iff off) Hoff). reflexivity. }
  assert (G5 : mmap_noreserve_b flags = false)
    by (unfold mmap_noreserve_b; rewrite Hflags; reflexivity).
  unfold mmap_budget_refused_b in Hb. rewrite G1, G2, G3, G4 in Hb. cbn [negb] in Hb.
  unfold mmap_noreserve_backed_ok in Hb. rewrite G5, Hlen in Hb.
  apply negb_false_iff, Z.leb_le in Hb. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_budget_of_premise : forall ms x8 m,
  bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  alloc_budget_refused_b (sys_input segs ms x8) m = false ->
  vm_backing_used m + (bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps m)))
    <= vm_limit (m_vmmaps m).
Proof.
  intros ms x8 m Hno (Hb0 & Hbal & Hmin & Hlt & Hral) Hb.
  unfold alloc_budget_refused_b in Hb. rewrite in_sysno_sys_input, Hno in Hb. cbv zeta in Hb.
  change (214 =? 214) with true in Hb. cbv iota in Hb.
  change (in_arg (sys_input segs ms x8) 0) with (ms_gpr ms 0) in Hb.
  unfold brk_budget_refused_b in Hb. cbv zeta in Hb. unfold min_brk in Hb.
  rewrite (w_is0_pos (ms_gpr ms 0)) in Hb by lia.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned (ms_gpr ms 0)) (bv_unsigned (vm_start_brk (m_vmmaps m)))))
    in Hb by lia.
  rewrite (proj2 (Z.ltb_lt _ _) Hb0), (proj2 (Z.ltb_lt _ _) Hlt) in Hb. cbn [orb negb andb] in Hb.
  apply negb_false_iff in Hb. unfold brk_budget_ok in Hb. cbv zeta in Hb.
  apply Z.leb_le in Hb.
  pose proof (u64_range (ms_gpr ms 0)) as Hr. pose proof (u64_range (vm_brk (m_vmmaps m))) as Hbr.
  rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
  rewrite Z.mod_small in Hb by lia. exact Hb.
Qed.

(* [comment removed for export] *)
Theorem mmap_anon_grant_exists_src : forall R L c S ms x8 m len,
  ledger_inv R L c S (m_vmmaps m) ->
  within_budget_cfg cfg segs (mkCfg ms m) ->
  m_halted m = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  let nZ := page_round_up_Z len in
  page_size + (live_bytes R + S) + (Z.of_nat (length R) + c) * (nZ + page_size) + nZ
    <= alloc_lo_bound ->
  exists a, mmap_grant_b m a nZ = true.
Proof.
  intros R L c S ms x8 m len Hinv Hwb Hh Hsvc Hno Hargs nZ Hband.
  pose proof (within_budget_alloc_not_refused cfg segs ms m x8 Hwb Hh Hsvc) as Hnr.
  pose proof (mmap_anon_budget_of_premise ms x8 m len Hno Hargs Hnr) as Hbud.
  apply (mmap_grant_exists_inv_lim R L c S m nZ Hinv); [| exact Hband | exact Hbud].   (* [comment removed for export] *)
  destruct Hargs as (_ & Hpos & _). pose proof (page_round_up_Z_pos len Hpos). unfold nZ. lia.
Qed.

(* [comment removed for export] *)
Theorem brk_grow_b_src : forall R L c S ms x8 m,
  ledger_inv R L c S (m_vmmaps m) ->
  within_budget_cfg cfg segs (mkCfg ms m) ->
  m_halted m = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  bv_unsigned (ms_gpr ms 0) <= alloc_top (m_vmmaps m) ->
  region_free (vm_maps (m_vmmaps m)) (vm_brk (m_vmmaps m))
    (Z_to_bv 64 (bv_unsigned (ms_gpr ms 0) + page_size - bv_unsigned (vm_brk (m_vmmaps m)))) = true ->
  brk_grow_b m (ms_gpr ms 0) = true.
Proof.
  intros R L c S ms x8 m Hinv Hwb Hh Hsvc Hno Hargs Htop Hfree.
  pose proof (within_budget_alloc_not_refused cfg segs ms m x8 Hwb Hh Hsvc) as Hnr.
  pose proof (brk_grow_budget_of_premise ms x8 m Hno Hargs Hnr) as Hbud.
  exact (brk_grow_b_intro_lim R L c S m (ms_gpr ms 0) Hinv Htop Hfree Hbud).   (* [comment removed for export] *)
Qed.

End WithCfg2.
