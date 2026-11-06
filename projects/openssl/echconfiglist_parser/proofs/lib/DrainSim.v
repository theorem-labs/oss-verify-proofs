(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamExec WallSim StreamSim.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.

Fixpoint procs (a : A) (bs : list byte) : option A :=
  match bs with
  | [] => Some a
  | b :: rest => match f a b with Some a' => procs a' rest | None => None end
  end.

Lemma procs_app : forall bs1 bs2 a,
  procs a (bs1 ++ bs2) =
  match procs a bs1 with Some a' => procs a' bs2 | None => None end.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 a; [reflexivity|].
  cbn [procs app]. destruct (f a b); [apply IH | reflexivity].
Qed.
End Proc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition block_ok (cnt : word) (bs : list byte) : Prop :=
  (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.

(* [comment removed for export] *)
Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
  flat_map (fun bs => map (ReadEv rch) bs) blocks.

Lemma reads_ch_cons : forall rch bs blocks,
  reads_ch rch (bs :: blocks) = map (ReadEv rch) bs ++ reads_ch rch blocks.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition reads (blocks : list (list byte)) : list event :=
  reads_ch (Z_to_bv 64 0) blocks.

Lemma reads_cons : forall bs blocks,
  reads (bs :: blocks) = map (ReadEv (Z_to_bv 64 0)) bs ++ reads blocks.
Proof. exact (reads_ch_cons (Z_to_bv 64 0)). Qed.

Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.

(* [comment removed for export] *)
Definition out_tail (s : InputStream) (a : A) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition drain_from_ch (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  (exists blocks s' a',
     chunks cnt s blocks s' /\
     procs f a (concat blocks) = Some a' /\
     is_prefix tr (reads_ch rch blocks ++ out_tail s' a' fs))
  \/ (exists blocks bs s' a',
     chunks cnt s (blocks ++ [bs]) s' /\
     procs f a (concat blocks) = Some a' /\
     procs f a' bs = None /\
     is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [ExitEv ec fs])).

(* [comment removed for export] *)
Definition drain_from (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  drain_from_ch (Z_to_bv 64 0) a fs s tr.

Lemma drain_from_ch_prefix : forall rch a fs s tr tr',
  drain_from_ch rch a fs s tr -> is_prefix tr' tr -> drain_from_ch rch a fs s tr'.
Proof.
  intros rch a fs s tr tr' [ (blocks & s' & a' & HC & Hp & Hpref)
                           | (blocks & bs & s' & a' & HC & Hp & Hn & Hpref) ] Hp'.
  - left. exists blocks, s', a'.
    split; [exact HC | split; [exact Hp | eapply is_prefix_trans; eauto]].
  - right. exists blocks, bs, s', a'.
    split; [exact HC | split; [exact Hp |
    split; [exact Hn | eapply is_prefix_trans; eauto]]].
Qed.

Lemma drain_from_prefix : forall a fs s tr tr',
  drain_from a fs s tr -> is_prefix tr' tr -> drain_from a fs s tr'.
Proof. exact (drain_from_ch_prefix (Z_to_bv 64 0)). Qed.

Lemma drain_from_ch_nil : forall rch a fs s, drain_from_ch rch a fs s [].
Proof.
  intros rch a fs s. left. exists [], s, a.
  split; [constructor | split; [reflexivity | apply is_prefix_nil]].
Qed.

Lemma drain_from_nil : forall a fs s, drain_from a fs s [].
Proof. exact (drain_from_ch_nil (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
Lemma drain_from_ch_out : forall rch a fs tr,
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
  drain_from_ch rch a fs IEof tr.
Proof.
  intros rch a fs tr Hp. left. exists [], IEof, a.
  split; [constructor | split; [reflexivity | exact Hp]].
Qed.

Lemma drain_from_out : forall a fs tr,
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
  drain_from a fs IEof tr.
Proof. exact (drain_from_ch_out (Z_to_bv 64 0)). Qed.

Lemma drain_from_ch_block : forall rch a a1 fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = Some a1 ->
  drain_from_ch rch a1 fs (snd (stream_take s (length bs))) tr ->
  drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof.
  intros rch a a1 fs s bs tr Hlo Hhi Hpre Hs
    [ (blocks & s' & a' & HC & Hp & Hpref)
    | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
  - left. exists (bs :: blocks), s', a'.
    split; [eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
  - right. exists (bs :: blocks), bsE, s', a'.
    split; [change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE]));
            eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    split; [exact Hn |].
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
Qed.

Lemma drain_from_block : forall a a1 fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = Some a1 ->
  drain_from a1 fs (snd (stream_take s (length bs))) tr ->
  drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_block (Z_to_bv 64 0)). Qed.

Lemma drain_from_ch_err : forall rch a fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = None ->
  is_prefix tr [ExitEv ec fs] ->
  drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof.
  intros rch a fs s bs tr Hlo Hhi Hpre Hn Hp. right.
  exists [], bs, (snd (stream_take s (length bs))), a.
  split; [cbn [app]; eapply chunks_cons;
          try eassumption; constructor |].
  split; [reflexivity |].
  split; [exact Hn |].
  cbn [app]. unfold reads_ch. cbn [flat_map]. rewrite app_nil_r.
  apply is_prefix_app_mono. exact Hp.
Qed.

Lemma drain_from_err : forall a fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = None ->
  is_prefix tr [ExitEv ec fs] ->
  drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_err (Z_to_bv 64 0)). Qed.

End Traces.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd1chan_with_stdin : forall s m, fd1chan m -> fd1chan (with_stdin s m).
Proof. intros s m H. exact H. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drain.
Context {A : Type}.
Variable segs : list Segment.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.

(* [comment removed for export] *)
Definition lh_next (a : A) (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH a ms'.

(* [comment removed for export] *)
Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).

(* [comment removed for export] *)
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_out bs ms' -> to_out bs ms.

(* [comment removed for export] *)
Definition ReadPend (a : A) (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
             = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (* [comment removed for export] *)
  buf_modeled (out a) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     match procs f a bs with
     | Some a' => lh_next a'
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     | None => to_exit segs ec
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     end).

(* [comment removed for export] *)
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd a ms' -> to_rd a ms.

Lemma msteps_to_rd : forall a ms ms',
  msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof.
  intros a ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

Lemma msteps_to_out : forall bs ms ms',
  msteps segs ms ms' -> to_out bs ms' -> to_out bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Ho. eapply tout_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_out_wall_tail : forall bs ms,
  to_out bs ms ->
  to_wall_tail segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).
Proof.
  intros bs ms H;
    induction H as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH].
  - apply twt_done. exact Hte.
  - destruct HWF as [Hnb Hwl]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

Lemma lh_next_to_rd : forall a ms, lh_next a ms -> to_rd a ms.
Proof.
  intros a ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_rd_star : forall a ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_rd a ms ->
  exists msR, ReadPend a msR /\
    star segs (mkCfg ms model) [] (mkCfg msR model).
Proof.
  intros a ms model Hh Hlazy Hrd.
  induction Hrd as [a ms HRP | a ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma msteps_star : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  star segs (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms ms' model Hh Hlazy H. induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
  - apply star_refl.
  - change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms1 model) | exact IH];
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\ exists a, to_rd a (cfg_ms c))
  \/ (fd1chan (cfg_model c) /\ m_halted (cfg_model c) = None /\
      m_vm_lazy (cfg_model c) = [] /\
      exists rest, buf_modeled rest /\
        to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) rest
          (to_exit segs (Z_to_bv 64 0)))
  \/ on_path segs (Z_to_bv 64 0) c
  \/ on_path segs ec c.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


End Drain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

