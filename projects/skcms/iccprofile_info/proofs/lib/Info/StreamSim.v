(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SimInv ExitSim CatSim WallSim.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_arg1_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.

Lemma in_arg2_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.

Lemma in_wmem_sys_input : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0.
Proof.
  apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_fs_with_stdin : forall s m, m_fs (with_stdin s m) = m_fs m.
Proof. reflexivity. Qed.

Lemma m_halted_with_stdin : forall s m, m_halted (with_stdin s m) = m_halted m.
Proof. reflexivity. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

Lemma m_vm_lazy_with_stdin : forall s m,
  m_vm_lazy (with_stdin s m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  m_halted model = None /\
  m_vm_lazy model = [].

Lemma init_M_loop : forall reserved brk0 mb sp lim inp,
  M_loop (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp. repeat split. Qed.

(* [comment removed for export] *)
Lemma M_loop_take : forall k model,
  M_loop model ->
  M_loop (with_stdin (snd (stream_take (m_stdin model) k)) model).
Proof. intros k model (H0 & H1 & Hh & Hlazy). repeat split; assumption. Qed.

Lemma M_loop_fd1chan : forall model, M_loop model -> fd1chan model.
Proof. intros model (H0 & H1 & Hh & Hlazy). exact H1. Qed.

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

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (bv_unsigned a) 1 with
      | Some seg =>
          (seg_writable seg
           && match segment_byte_at (seg_bytes seg)
                      (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
              | Some _ => true
              | None => false
              end
           && wseg_ok segs (a + 1) n')%bool
      | None => false
      end
  end.

Lemma wseg_ok_read_aux : forall segs n a ms,
  wseg_ok segs a n = true ->
  exists w, read_bytes_aux (ms_writable_byte segs ms) a n = Some w.
Proof.
  intros segs n; induction n as [|n IH]; intros a ms H.
  - exists []. reflexivity.
  - cbn [wseg_ok] in H.
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
    apply andb_true_iff in H as [H Hrec].
    apply andb_true_iff in H as [Hwr Hbyte].
    destruct (segment_byte_at (seg_bytes seg)
                (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
      [|discriminate].
    destruct (IH (a + 1) ms Hrec) as [w Hw].
    cbn [read_bytes_aux].
    assert (Hdef : exists b0, ms_writable_byte segs ms a = Some b0).
    { unfold ms_writable_byte, wview. destruct (ms_mem ms a) as [b'|].
      - eexists; reflexivity.
      - rewrite Hseg, Hwr, Hb. eexists; reflexivity. }
    destruct Hdef as [b0 Hb0]. rewrite Hb0, Hw. eexists; reflexivity.
Qed.

Lemma wseg_ok_wdef : forall segs (a len : word) ms,
  wseg_ok segs a (word_to_nat len) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) a len = Some w.
Proof.
  intros segs a len ms H. rewrite read_bytes_map_eq.
  apply wseg_ok_read_aux. exact H.
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
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
    (1 <= Z.of_nat (length bs))%Z ->
    (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
    fst (stream_take s (length bs)) = bs ->
    chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
    chunks cnt s (bs :: blocks) s''.

(* [comment removed for export] *)
Lemma chunks_app : forall cnt s l1 s1 l2 s2,
  chunks cnt s l1 s1 -> chunks cnt s1 l2 s2 -> chunks cnt s (l1 ++ l2) s2.
Proof.
  intros cnt s l1 s1 l2 s2 H1; revert l2 s2.
  induction H1 as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros l2 s2 H2; cbn [app]; [exact H2|].
  eapply chunks_cons; eauto.
Qed.

Lemma chunks_split : forall cnt l1 l2 s s2,
  chunks cnt s (l1 ++ l2) s2 ->
  exists s1, chunks cnt s l1 s1 /\ chunks cnt s1 l2 s2.
Proof.
  intros cnt l1; induction l1 as [|bs l1 IH]; intros l2 s s2 H; cbn [app] in H.
  - exists s. split; [constructor | exact H].
  - inversion H as [|s0 bs0 blocks0 s3 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
    destruct (IH l2 _ _ HC) as (s1 & H1 & H2).
    exists s1. split; [eapply chunks_cons; eauto | exact H2].
Qed.

(* [comment removed for export] *)
Lemma chunks_single_inv : forall cnt s bs s',
  chunks cnt s [bs] s' ->
  (1 <= Z.of_nat (length bs))%Z /\
  (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
  fst (stream_take s (length bs)) = bs /\
  s' = snd (stream_take s (length bs)).
Proof.
  intros cnt s bs s' H.
  inversion H as [|s0 bs0 blocks0 s2 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
  inversion HC; subst.
  repeat split; assumption || reflexivity.
Qed.

(* [comment removed for export] *)
Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
  map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.

(* [comment removed for export] *)
Definition iter_ev (bs : list byte) : list event :=
  iter_ev_ch (Z_to_bv 64 0) bs.

(* [comment removed for export] *)
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
    (s : InputStream) (tr : list event) : Prop :=
  exists blocks s',
    chunks cnt s blocks s' /\
    is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).

(* [comment removed for export] *)
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.

Lemma stream_traces_ch_prefix_closed : forall rch cnt fs s tr tr',
  stream_traces_ch rch cnt fs s tr -> is_prefix tr' tr ->
  stream_traces_ch rch cnt fs s tr'.
Proof.
  intros rch cnt fs s tr tr' (blocks & s' & HC & Hp) Hp'.
  exists blocks, s'. split; [exact HC | eapply is_prefix_trans; eauto].
Qed.

Lemma stream_traces_prefix_closed : forall cnt fs s tr tr',
  stream_traces cnt fs s tr -> is_prefix tr' tr -> stream_traces cnt fs s tr'.
Proof. exact (stream_traces_ch_prefix_closed (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.
(* [comment removed for export] *)
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

(* [comment removed for export] *)
Definition lh_next (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH ms'.

(* [comment removed for export] *)
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs lh_next.

(* [comment removed for export] *)
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wr bs ms' -> to_wr bs ms.

(* [comment removed for export] *)
Definition ReadPend (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z ->
     (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     to_wr bs (advance_past_svc (apply_effect ms
        (mkEffect (len_word bs) [(buf, bs)] [])))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma msteps_to_wr : forall bs ms ms',
  msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Hwr. eapply twr_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wr_wall_tail : forall bs ms,
  to_wr bs ms -> to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next.
Proof.
  intros bs ms H; induction H as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - destruct HWP as [Hnb Hw]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd ms' -> to_rd ms.

Lemma msteps_to_rd : forall ms ms',
  msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
  intros ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

(* [comment removed for export] *)
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

Lemma lh_next_to_rd : forall ms, lh_next ms -> to_rd ms.
Proof.
  intros ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_rd_star : forall ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_rd ms ->
  exists msR, ReadPend msR /\
    star segs (mkCfg ms model) [] (mkCfg msR model).
Proof.
  intros ms model Hh Hlazy Hrd.
  induction Hrd as [ms HRP | ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wr_star : forall bs ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_wr bs ms ->
  exists msW, WrPend bs msW /\
    star segs (mkCfg ms model) [] (mkCfg msW model).
Proof.
  intros bs ms model Hh Hlazy Hwr.
  induction Hwr as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - exists ms. split; [exact HWP | apply star_refl].
  - destruct IH as (msW & HWP & Hstar).
    exists msW. split; [exact HWP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
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

Definition sinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\
     (to_rd (cfg_ms c)
      \/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
           to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
  \/ on_path segs (Z_to_bv 64 0) c.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

