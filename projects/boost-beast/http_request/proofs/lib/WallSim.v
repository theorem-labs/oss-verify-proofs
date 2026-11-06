(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import SimInv ExitSim CatSim PropExec SeqExec CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l H. unfold len_word. apply Z_to_bv_small.
  unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

(* [comment removed for export] *)

Lemma len_word_firstn_nat : forall n (bs : list byte),
  (n <= length bs)%nat ->
  len_word (firstn n bs) = nat_to_word n.
Proof.
  intros n bs Hn. unfold len_word, nat_to_word.
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat ->
  v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof.
  intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
  unfold v_add. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma word_add_nat_Z : forall (p : word) (k : nat),
  (Z.of_nat k < 2^64)%Z ->
  p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof.
  intros p k Hk. apply bv_eq.
  rewrite bv_add_unsigned. unfold nat_to_word.
  rewrite Z_to_bv_small
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.


Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

(* [comment removed for export] *)
Lemma msteps_to_wall_tail : forall ms ms' rest k,
  msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
  intros ms ms' rest k H; induction H; [auto|].
  intro Hw. eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wall_tail_nil_msteps : forall ms k,
  to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
  intros ms k H.
  remember ([] : list byte) as rest eqn:Hrest.
  induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
  - exists ms. split; [apply mst_refl | exact Hk].
  - subst rest. cbn in Hnb. lia.
  - destruct (IH Hrest) as (ms'' & Hm & Hk).
    exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma twl_write_rec : forall (k : machine_state -> Prop) rest regs pc mem rom,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fd ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None;
                   ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     to_wall_tail (mkst (regupd regs 10 (len_word (firstn n rest)))
                        (v_addi pc 4) mem rom)
       (skipn n rest) k) ->
  to_wall {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
             ms_svc_pending := Some (getr regs 17); ms_resv := None;
             ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |}
    rest k.
Proof.
  intros k rest regs pc mem rom H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  eapply twl_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

(* [comment removed for export] *)
Lemma to_wall_k_ex_mut :
  (forall ms rest k, to_wall ms rest k -> exists ms', k ms')
  /\ (forall ms rest k, to_wall_tail ms rest k -> exists ms', k ms').
Proof.
  apply (to_wall_mutind
           (fun ms rest k => exists ms', k ms')
           (fun ms rest k => exists ms', k ms')).
  - intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH.
    exact (IH (length rest) Hnb (Nat.le_refl _)).
  - intros ms k Hk. exists ms. exact Hk.
  - intros ms rest k Hnb Hw IH. exact IH.
  - intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.

Lemma to_wall_tail_k_ex : forall ms rest k,
  to_wall_tail ms rest k -> exists ms', k ms'.
Proof. exact (proj2 to_wall_k_ex_mut). Qed.

Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
  to_wallexit bufs code ms ->
  Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof.
  induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
  destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
  destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
  exact (IH code ms' Hk).
Qed.

(* [comment removed for export] *)
Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hsvc Hstep Hw.
  destruct bufs as [|buf rest].
  - eapply tw_step; eauto.
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply twt_step; eauto.
Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
  - exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply msteps_to_wall_tail; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wexit_nil_star_admits_aux : forall ms bufs code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  exists c, star segs (mkCfg ms model) [ExitEv code (m_fs model)] c.
Proof.
  intros ms bufs code model Hh Hlazy Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs;
    [| discriminate Hbufs |].
  - exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
    apply star_one.
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
      by (cbn; reflexivity).
    apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
    + exact Hh.
    + exact Hsvc.
    + apply (exit_dispatch_ok (sys_input segs ms x8) model).
      rewrite in_sysno_sys_input. exact Hx8.
    + cbn. reflexivity.
    + apply m_killed_with_halted.
  - destruct (IH Hbufs) as [c Hstar].
    exists c.
    replace [ExitEv code (m_fs model)]
      with ([] ++ [ExitEv code (m_fs model)]) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wexit_nil_star_admits : forall ms code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  exists c, star segs (mkCfg ms model) [ExitEv code (m_fs model)] c.
Proof.
  intros ms code model Hh Hlazy Hte.
  exact (to_wexit_nil_star_admits_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

Lemma to_wexit_nil_star_only_aux : forall ms bufs code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr [ExitEv code (m_fs model)].
Proof.
  intros ms bufs code model Hh Hlazy Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs;
    [| discriminate Hbufs |]; intros tr c Hstar.
  - inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst; [apply is_prefix_nil|].
    edestruct (sstep_exit_inv segs ms model x8 evs (SNext c2)) as [Hevs Hc2];
      [exact Hh | exact Hsvc | exact Hx8 | exact Hss |].
    subst evs. inversion Hc2; subst c2.
    assert (Hnh : m_halted (cfg_model (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))) <> None)
      by (cbn; discriminate).
    destruct (star_halted_nil segs _ _ _ Hnh Hstar2) as [Htr2 _]. subst tr2.
    rewrite app_nil_r. apply is_prefix_refl.
  - inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst; [apply is_prefix_nil|].
    edestruct (sstep_instr_inv segs ms model ms' evs (SNext c2)) as [Hevs Hc2];
      [exact Hlazy | exact Hsvc | exact Hstep | exact Hss |].
    subst evs. inversion Hc2; subst c2. cbn [app].
    eapply IH; [solve [assumption | reflexivity] | exact Hstar2].
Qed.

Lemma to_wexit_nil_star_only : forall ms code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr [ExitEv code (m_fs model)].
Proof.
  intros ms code model Hh Hlazy Hte.
  exact (to_wexit_nil_star_only_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wall_won_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   fdchan fd ch (cfg_model c) /\
   exists bufs code rest,
     buf_modeled rest /\ bufs_modeled bufs /\
     to_wall_tail (cfg_ms c) rest (to_wallexit bufs code))
  \/ m_halted (cfg_model c) <> None.

Lemma to_wallexit_wall_tail : forall bufs code ms,
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  exists bufs' rest, buf_modeled rest /\ bufs_modeled bufs' /\
    to_wall_tail ms rest (to_wallexit bufs' code).
Proof.
  intros [|buf rest'] code ms Hbm Hw.
  - exists [], []. split; [apply buf_modeled_nil|].
    split; [apply Forall_nil | apply twt_done; exact Hw].
  - destruct Hw as [Hnb Hw']. apply Forall_cons_iff in Hbm as [Hb Hbs].
    exists rest', buf. split; [exact Hb | split; [exact Hbs | exact Hw']].
Qed.

(* [comment removed for export] *)
Lemma to_wexit_nil_sstep_cases_aux : forall ms bufs code model evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  sstep segs (mkCfg ms model) evs st ->
  (exists model', st = SNext (mkCfg ms model') /\ m_halted model' <> None) \/
  (exists ms', st = SNext (mkCfg ms' model) /\ evs = [] /\
     to_wexit segs ms' [] code).
Proof.
  intros ms bufs code model evs st Hh Hlazy Hte.
  destruct Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont
    | ms ms' bufs code Hsvc Hstep Hte]; intros Hbufs Hss;
    [| discriminate Hbufs |].
  - destruct (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss)
      as [Hevs Hst].
    left. eexists. split; [exact Hst | cbn; discriminate].
  - destruct (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss)
      as [Hevs Hst].
    right. exists ms'. subst bufs. auto.
Qed.

Lemma to_wexit_nil_sstep_cases : forall ms code model evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  sstep segs (mkCfg ms model) evs st ->
  (exists model', st = SNext (mkCfg ms model') /\ m_halted model' <> None) \/
  (exists ms', st = SNext (mkCfg ms' model) /\ evs = [] /\
     to_wexit segs ms' [] code).
Proof.
  intros ms code model evs st Hh Hlazy Hte Hss.
  exact (to_wexit_nil_sstep_cases_aux ms [] code model evs st Hh Hlazy Hte eq_refl Hss).
Qed.


End WithSegsCh.

(* [comment removed for export] *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* [comment removed for export] *)
Lemma wevents_ch_fd1 : forall bufs,
  wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

