(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require NArith.
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.EquivalenceDefinition Require OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem Require OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Fs.ReadWrite.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require StreamSim.
Module DrainSim.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.SimInv OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.StreamExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Open Scope bv_scope.

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

Lemma to_out_star_admits : forall bs ms model,
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  to_out bs ms -> buf_modeled bs ->
  exists c, star segs (mkCfg ms model)
              (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]) c.
Proof.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH]; intro Hbm.
  - cbn [map app].
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms model Hh Hlazy Hte) as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 |].
    intros ms' Hex.
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex)
      as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct (IH Hbm) as [c Hstar]. exists c.
    replace (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
      with ([] ++ (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]))
      by reflexivity.
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_out_star_only : forall bs ms model,
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  to_out bs ms -> buf_modeled bs ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]).
Proof.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH];
    intros Hbm tr c Hstar.
  - cbn [map app].
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms model Hh Hlazy Hte tr c Hstar)
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_only segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 | | exact Hstar].
    intros ms' tr' c' Hex Hstar'.
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex tr' c' Hstar')
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst; [apply is_prefix_nil|].
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm tr2 _ Hstar2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read0_check_eof_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (Z_to_bv 64 0) [] []) model
    = CheckOk model [].
Proof. apply (StreamSim.read0_check_eof cnt Hcnt). Qed.

Lemma read0_ok_eof_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof. apply (StreamSim.read0_ok_eof cnt Hcnt). Qed.

Lemma read0_check_bytes_cnt : forall ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
    = CheckOk (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
              (map (ReadEv (Z_to_bv 64 0)) bs).
Proof. apply (StreamSim.read0_check_bytes cnt Hcnt). Qed.

Lemma read0_ok_bytes_cnt : forall ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
        (map (ReadEv (Z_to_bv 64 0)) bs)).
Proof. apply (StreamSim.read0_ok_bytes cnt Hcnt). Qed.

Lemma read0_ok_inv_cnt : forall ms x8 model buf w eff model' evs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  (m_stdin model = IEof /\ eff = mkEffect (Z_to_bv 64 0) [] [] /\
   model' = model /\ evs = [])
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        eff = mkEffect (len_word bs) [(buf, bs)] [] /\
        model' = with_stdin (snd (stream_take (m_stdin model) (length bs))) model /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs).
Proof. apply (StreamSim.read0_ok_inv cnt Hcnt). Qed.

Lemma read0_no_err_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. apply (StreamSim.read0_no_unmodeled cnt Hcnt). Qed.

Lemma sstep_read_inv_cnt : forall ms model buf x8 w evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  sstep segs (mkCfg ms model) evs st ->
  (m_stdin model = IEof /\ evs = [] /\
   st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs /\
        st = SNext (mkCfg
               (advance_past_svc (apply_effect ms
                  (mkEffect (len_word bs) [(buf, bs)] [])))
               (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                           model))).
Proof. apply (StreamSim.sstep_read_inv cnt Hcnt). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma drain_read_step : forall bs ms model buf x8 w,
  M_loop model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf ->
  ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  access_okb buf (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  sstep segs (mkCfg ms model) (map (ReadEv (Z_to_bv 64 0)) bs)
    (SNext (mkCfg (advance_past_svc (apply_effect ms
                     (mkEffect (len_word bs) [(buf, bs)] [])))
                  (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                              model))).
Proof.
  intros bs ms model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi Hpre.
  pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  apply (sstep_syscall segs ms model x8
           (mkEffect (len_word bs) [(buf, bs)] [])
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (map (ReadEv (Z_to_bv 64 0)) bs));
    [exact Hh | exact Hsvc | | exact Hh |].
  - rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
    apply read0_ok_bytes_cnt with (w := w); assumption.
  - rewrite (materialize_model_accesses_no_lazy _ _).
    + reflexivity.
    + rewrite m_vm_lazy_with_stdin. exact Hlazy.
Qed.

Lemma drain_star_admits_ok : forall s blocks s',
  chunks cnt s blocks s' ->
  forall a a' ms model,
  M_loop model -> m_stdin model = s -> to_rd a ms ->
  procs f a (concat blocks) = Some a' ->
  exists c, star segs (mkCfg ms model)
              (reads blocks ++ out_tail out s' a' (m_fs model)) c.
Proof.
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' ms model HM Hst Hrd Hp;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    unfold reads, reads_ch. cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* [comment removed for export] *)
      destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & _).
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok.
          exact (read0_ok_eof_cnt msR x8 model w Hno Hfd0 Hst Hg0 Hg2 Hw
                   Haok).
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      destruct (to_out_star_admits (out a) _ model Hfd1 Hh Hlazy Hout Hobm) as [c Hstar2].
      exists c. cbn [out_tail].
      replace (map (WriteEv (Z_to_bv 64 1)) (out a)
                 ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
        with (([] : list event)
                ++ ([] ++ (map (WriteEv (Z_to_bv 64 1)) (out a)
                             ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])))
        by reflexivity.
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* [comment removed for export] *)
      cbn [out_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* [comment removed for export] *)
    cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' advB model' HM' Hst' Hrd1 Hp) as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads blocks ++ out_tail out s'' a' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads blocks ++ out_tail out s'' a' (m_fs model))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

Lemma drain_star_admits_err : forall s blocks s1,
  chunks cnt s blocks s1 ->
  forall a a' bsE ms model,
  M_loop model -> m_stdin model = s -> to_rd a ms ->
  procs f a (concat blocks) = Some a' ->
  (1 <= Z.of_nat (length bsE))%Z -> (Z.of_nat (length bsE) <= bv_unsigned cnt)%Z ->
  fst (stream_take s1 (length bsE)) = bsE ->
  procs f a' bsE = None ->
  exists c, star segs (mkCfg ms model)
              (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)]) c.
Proof.
  intros s blocks s1 HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bsE HloE HhiE) as Hcont.
    rewrite Hn in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bsE) [(buf, bsE)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bsE))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (Hlazy' : m_vm_lazy model' = [])
      by (unfold model'; rewrite m_vm_lazy_with_stdin; exact Hlazy).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bsE)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bsE msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                HloE HhiE); rewrite Hst; exact HpreE. }
    destruct (to_exit_star_admits segs ec advB model' Hh' Hlazy' Hcont) as [c Hstar2].
    rewrite land_255_small in Hstar2 by exact Hec.
    change (m_fs model') with (m_fs model) in Hstar2.
    exists c.
    cbn [app]. unfold reads, reads_ch. cbn [flat_map]. rewrite app_nil_r.
    replace (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)]))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar2].
  - cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' bsE advB model' HM' Hst' Hrd1 Hp HloE HhiE HpreE Hn)
      as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma star_drain_only : forall c0 tr c', star segs c0 tr c' ->
  forall a ms model, c0 = mkCfg ms model -> M_loop model -> to_rd a ms ->
  drain_from cnt f out ec a (m_fs model) (m_stdin model) tr.
Proof.
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros a ms model Heq HM Hrd; subst.
  - apply drain_from_nil.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms' Hsvc Hstep Hrd'].
    + (* [comment removed for export] *)
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs (SNext c2)
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * (* [comment removed for export] *)
        pose proof (to_out_star_only (out a) _ model Hfd1 Hh Hlazy Hout Hobm
                      tr2 c3 Hstar) as Hpref.
        cbn [app]. rewrite Hs. apply drain_from_out. exact Hpref.
      * (* [comment removed for export] *)
        pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
           apply drain_from_block with (a1 := a1);
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           exact (IH a1 _ _ eq_refl (M_loop_take (length bs) model HM) Hrd1).
        -- apply drain_from_err;
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           destruct (to_exit_star_only segs ec _
                       (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                                   model) Hh ltac:(rewrite m_vm_lazy_with_stdin; exact Hlazy)
                       Hcont tr2 c3 Hstar)
             as [-> | ->].
           ++ apply is_prefix_nil.
           ++ change (m_fs (with_stdin
                              (snd (stream_take (m_stdin model) (length bs)))
                              model)) with (m_fs model).
              rewrite land_255_small by exact Hec. apply is_prefix_refl.
    + (* [comment removed for export] *)
      destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                  Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
      subst evs. inversion Hc2; subst c2. cbn [app].
      exact (IH a _ model eq_refl HM Hrd').
Qed.

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

Lemma wall_out_dinv_step : forall rest ms model evs ms' model',
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  buf_modeled rest ->
  to_wall_tail segs (Z_to_bv 64 1) ms rest (to_exit segs (Z_to_bv 64 0)) ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg ms' model')) ->
  dinv (mkCfg ms' model').
Proof.
  intros rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss.
  assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
    by (apply fd1chan_fdchan; exact Hfd1).
  revert Hbm.
  inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                  | msS msS' restS kS HsvcS HstepS Ht']; subst; intro Hbm.
  - (* [comment removed for export] *)
    right. right. left.
    apply (on_path_step segs (Z_to_bv 64 0) (mkCfg ms model) evs); [|exact Hss].
    left. repeat split; assumption.
  - (* [comment removed for export] *)
    destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                ms rest _ model evs (SNext (mkCfg ms' model'))
                Hh Hlazy Hfdc Hbm Hwl Hss) as (n & Hn1 & Hn2 & _ & Hc2 & Ht2).
    inversion Hc2; subst.
    right. left. cbn. repeat split; try assumption.
    exists (skipn n rest).
    split; [apply buf_modeled_skipn; exact Hbm | exact Ht2].
  - (* [comment removed for export] *)
    destruct (sstep_instr_inv segs ms model msS' evs (SNext (mkCfg ms' model'))
                Hlazy HsvcS HstepS Hss) as [_ Hc2].
    inversion Hc2; subst.
    right. left. cbn. repeat split; try assumption.
    exists rest. split; [exact Hbm | exact Ht'].
Qed.
Lemma dinv_step : forall c evs c',
  dinv c -> sstep segs c evs (SNext c') -> dinv c'.
Proof.
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs
                  (SNext (mkCfg ms' model'))
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * right. left. cbn. repeat split; try assumption.
        exists (out a).
        split; [exact Hobm | exact (to_out_wall_tail _ _ Hout)].
      * pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           left. cbn. split; [apply M_loop_take; exact HM|].
           exists a1. exact (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)).
        -- right. right. right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hcont].
    + destruct (sstep_instr_inv segs ms model ms1 evs
                  (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
      inversion Hc2; subst.
      left. cbn. split; [exact HM |]. exists a. exact Hrd'.
  - exact (wall_out_dinv_step rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss).
  - right. right. left. eapply on_path_step; eauto.
  - right. right. right. eapply on_path_step; eauto.
Qed.

Lemma dinv_no_error : forall c evs, dinv c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs SError
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
    + destruct (sstep_instr_inv segs ms model ms1 evs SError
                  Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
  - assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                    | msS msS' restS kS HsvcS HstepS Ht']; subst.
    + eapply (on_path_no_error segs (Z_to_bv 64 0) (mkCfg ms model));
        [left; repeat split; assumption | exact Hss].
    + exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               ms rest _ model evs Hh Hlazy Hfdc Hbm Hwl Hss).
    + destruct (sstep_instr_inv segs ms model msS' evs SError
                  Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
  - eapply on_path_no_error; eauto.
Qed.

Lemma star_dinv : forall c tr c', dinv c -> star segs c tr c' -> dinv c'.
Proof. exact (star_inv segs dinv dinv_step). Qed.

Lemma to_rd_no_error : forall a ms model,
  M_loop model -> to_rd a ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
  intros a ms model HM Hrd.
  apply (inv_no_reaches_error segs dinv dinv_step dinv_no_error).
  left; cbn; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma drain_obs_iff : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp) tr.
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
  set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    pose proof (star_drain_only _ _ _ Hstar a0 ms0 model0 eq_refl HM0 Hrd) as Hd.
    rewrite Hst0, Hfs0 in Hd.
    eapply drain_from_prefix; eauto.
  - intros [ (blocks & s' & a' & HC & Hp & Hpref)
           | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
    + destruct (drain_star_admits_ok _ blocks s' HC a0 a' ms0 model0
                  HM0 Hst0 Hrd Hp) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
    + destruct (chunks_split _ blocks [bsE] _ _ HC) as (s1 & HC1 & HC2).
      destruct (chunks_single_inv _ _ _ _ HC2) as (HloE & HhiE & HpreE & _).
      destruct (drain_star_admits_err _ blocks s1 HC1 a0 a' bsE ms0 model0
                  HM0 Hst0 Hrd Hp HloE HhiE HpreE Hn) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
Qed.

Lemma drain_no_error : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd.
  apply (to_rd_no_error a0); [apply init_M_loop | exact Hrd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_rd_coexec : forall a ms model,
  M_loop model -> to_rd a ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
  intros a ms model HM Hrd.
  apply (inv_coexec segs dinv dinv_step dinv_no_error).
  left; cbn. split; [exact HM | exists a; exact Hrd].
Qed.

Lemma drain_omni_corun : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_corun]. unfold init_config.
  apply (to_rd_coexec a0); [apply init_M_loop | exact Hrd].
Qed.

Lemma drain_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp)).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_cosafe].
  apply cosafe_obs_iff.
  - (* [comment removed for export] *)
    intros t t' Ht Hp.
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd).
    eapply obs_trace_prefix_closed; [| exact Hp].
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Ht.
  - intros tr Hobs. apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Hobs.
Qed.

End Drain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma drain_omni_strong_equiv :
  forall (A : Type) (cnt : word) (f : A -> byte -> option A)
         (out : A -> list byte) (ec : word) (a0 : A)
         source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
  (bv_unsigned ec < 256)%Z ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  (forall a ms, rLH a ms -> to_rd source_segs cnt f out ec rLH a ms) ->
  (forall a ms, aLH a ms -> to_rd target_segs cnt f out ec aLH a ms) ->
  to_rd source_segs cnt f out ec rLH a0
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_rd target_segs cnt f out ec aLH a0
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp Hec Hcnt HrLH HaLH Hr Ha.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (drain_omni_corun source_segs cnt Hcnt f out ec rLH HrLH
                rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr tr).
    rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha tr).
    reflexivity.
  - exact (drain_omni_corun target_segs cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha).
Qed.

Lemma drain_strong_equiv :
  forall (A : Type) (cnt : word) (f : A -> byte -> option A)
         (out : A -> list byte) (ec : word) (a0 : A)
         source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
  (bv_unsigned ec < 256)%Z ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  (forall a ms, rLH a ms -> to_rd source_segs cnt f out ec rLH a ms) ->
  (forall a ms, aLH a ms -> to_rd target_segs cnt f out ec aLH a ms) ->
  to_rd source_segs cnt f out ec rLH a0
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_rd target_segs cnt f out ec aLH a0
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp Hec Hcnt HrLH HaLH Hr Ha.
  split.
  { apply no_error_run_modeled.
    apply (drain_no_error source_segs cnt Hcnt f out ec rLH HrLH
             rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr). }
  right. split.
  - intro tr. cbn.
    rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr tr).
    rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd alim inp a0 Ha tr).
    reflexivity.
  - cbn.
    apply (drain_no_error target_segs cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd alim inp a0 Ha).
Qed.
End DrainSim.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require Import ExitSim PropExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatSim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.SeqExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.StreamExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require Import MmapSim WallSim StreamSim.
Import DrainSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac chain_step :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP2.
Ltac step_intro := chain_step.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP3.
Ltac expand_ctx_defs p :=
  match goal with
  | H := _ |- _ =>
      lazymatch p with
      | context [H] => let p' := eval unfold H in p in expand_ctx_defs p'
      end
  | _ => p
  end.

Section WithFP4.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP4.
Ltac check_closed_term p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif match goal with
             | H : _ |- _ => lazymatch p' with context [H] => idtac end
             end
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.

Section WithFP5.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP5.
Ltac vm_eval t :=
  let _ := match goal with _ => check_closed_term t end in
  eval vm_compute in t.

Section WithFP6.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP6.
Ltac word_lit p :=
  let u := vm_eval (bv_unsigned p) in
  constr:(@BV 64 u ltac:(vm_compute; exact I)).

Section WithFP7.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP7.
Ltac wlit_replace p :=
  let l := word_lit p in
  replace p with l by (apply bv_eq; vm_compute; reflexivity).

Section WithFP8.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP8.
Ltac wlit p :=
  try (lazymatch p with
       | @BV _ _ _ => idtac
       | _ => wlit_replace p
       end).

Section WithFP9.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP9.
Ltac wlits :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_replace (v_addi a b)
  | |- context [btgt ?a ?b] => wlit_replace (btgt a b)
  | |- context [v_jalr ?a ?b] => wlit_replace (v_jalr a b)
  | |- context [v_auipc ?a ?b] => wlit_replace (v_auipc a b)
  end.

Section WithFP10.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP10.
Ltac norm_pc_state st :=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => wlit p
       | _ => idtac
       end.
Ltac norm_pc :=
  try lazymatch goal with
  | |- msteps _ ?st _ => norm_pc_state st
  | |- to_wexit _ ?st _ _ => norm_pc_state st
  | |- twm _ ?st _ _ _ => norm_pc_state st
  | |- MmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- MmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- DrainSim.to_out _ _ ?st => norm_pc_state st
  | |- DrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.

Section WithFP12.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP12.
Ltac reduce_bv_eqb_ifs :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let v := eval vm_compute in (bv_eqb a b) in
              lazymatch v with
              | true => change (if bv_eqb a b then x else y) with x
              | false => change (if bv_eqb a b then x else y) with y
              end
          end
      end
  end.

Section WithFP13.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP13.
Ltac step_simpl := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.

Section WithFP14.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP14.
Ltac stepi_search F D :=
  first
    [ exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    (* [comment removed for export] *)
    | exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D) ].

Section WithFP15.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP15.
Ltac stepi F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLT _ _ _, _) =>
        exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_AND _ _ _, _) =>
        exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_OR _ _ _, _) =>
        exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_XOR _ _ _, _) =>
        exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) =>
        exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) =>
        exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRA _ _ _, _) =>
        exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLT _ _ _, _) =>
        exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLTU _ _ _, _) =>
        exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_ADD _ _ _, _) =>
        exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) =>
        exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SLL _ _ _, _) =>
        exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRL _ _ _, _) =>
        exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRA _ _ _, _) =>
        exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SLL _ _ _, _) =>
        exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRL _ _ _, _) =>
        exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRA _ _ _, _) =>
        exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Auipc _ _, _) =>
        exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Lui _ _, _) =>
        exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULH _ _ _, _) =>
        exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHSU _ _ _, _) =>
        exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHU _ _ _, _) =>
        exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIV _ _ _, _) =>
        exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_REM _ _ _, _) =>
        exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIVU _ _ _, _) =>
        eapply step_divu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul M_REMU _ _ _, _) =>
        eapply step_remu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul32 M_MUL _ _ _, _) =>
        exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIV _ _ _, _) =>
        exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIVU _ _ _, _) =>
        exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REM _ _ _, _) =>
        exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REMU _ _ _, _) =>
        exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | _ => stepi_search F D
    end
  | step_simpl ].

Section WithFP16.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP16.
Ltac stepiv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        eapply step_addi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        eapply step_andi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        eapply step_ori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        eapply step_xori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        eapply step_sltiu_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        eapply step_slli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        eapply step_srli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        eapply step_srai_at with (v := vv)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        eapply step_add_at with (v := vv)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        eapply step_sub_at with (v := vv)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        eapply step_addiw_at with (v := vv)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        eapply step_mul_at with (v := vv)
    | decode_any _ = Some (Lui _ _, _) =>
        eapply step_lui_at with (v := vv)
    | decode_any _ = Some (Auipc _ _, _) =>
        eapply step_auipc_at with (v := vv)
    | _ => eapply step_addi_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP17.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP17.
Ltac stepiwv F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP18.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP18.
Ltac stepj F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

Section WithFP19.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP19.
Ltac stepjr F D tv tac :=
  chain_step;
  [ reflexivity
  | first [ eapply step_jalr_x0 with (tgt := tv);
            [ exact F | reflexivity | exact D | tac ]
          | eapply step_jalr_link with (tgt := tv);
            [ exact F | reflexivity | exact D | reflexivity | tac ] ]
  | step_simpl ].

Section WithFP20.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m1 : forall x, (1 <= bv_unsigned x)%Z ->
  v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1).
Proof. intros x H1. apply (v_addi_m x 1); lia. Qed.

Lemma v_addi_m16 : forall x, (16 <= bv_unsigned x)%Z ->
  v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16).
Proof. intros x H16. apply (v_addi_m x 16); lia. Qed.

Lemma v_addi_m32 : forall x, (32 <= bv_unsigned x)%Z ->
  v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32).
Proof. intros x H32. apply (v_addi_m x 32); lia. Qed.

Lemma v_addi_m48 : forall x, (48 <= bv_unsigned x)%Z ->
  v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48).
Proof. intros x H48. apply (v_addi_m x 48); lia. Qed.

Lemma v_addi_m64 : forall x, (64 <= bv_unsigned x)%Z ->
  v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64).
Proof. intros x H64. apply (v_addi_m x 64); lia. Qed.

Lemma v_addi_m80 : forall x, (80 <= bv_unsigned x)%Z ->
  v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80).
Proof. intros x H80. apply (v_addi_m x 80); lia. Qed.

(* [comment removed for export] *)
Lemma v_addi_nneg_t : forall x imm, (0 <= imm)%Z ->
  (bv_unsigned x + imm < 2^64)%Z ->
  v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm).
Proof. intros x imm _ _. reflexivity. Qed.

(* [comment removed for export] *)
End WithFP20.
Ltac u_norm := repeat rewrite u_Z2bv by lia.

Section WithFP21.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP21.
Ltac imm_norm :=
  repeat match goal with
  | |- context [bv_signed ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_signed b) in
          change (bv_signed b) with v
      end
  | |- context [bv_unsigned ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_unsigned b) in
          change (bv_unsigned b) with v
      end
  end.

Section WithFP22.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP22.
Ltac sp_norm :=
  imm_norm;
  repeat (match goal with
  | |- context [v_addi ?x ?i] =>
      lazymatch x with
      | context [v_addi _ _] => fail
      | _ => first [ rewrite (v_addi_m80 x) by (u_norm; lia)
                   | rewrite (v_addi_m64 x) by (u_norm; lia)
                   | rewrite (v_addi_m48 x) by (u_norm; lia)
                   | rewrite (v_addi_m32 x) by (u_norm; lia)
                   | rewrite (v_addi_m16 x) by (u_norm; lia)
                   | rewrite (v_addi_m1 x) by (u_norm; lia)
                   | rewrite (v_addi_nneg_t x i) by (u_norm; lia) ]
      end
  end; u_norm; cbn [Z.to_N]).

Section WithFP23.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP23.
Ltac stepi_at F D val :=
  chain_step;
  [ reflexivity
  | eapply step_addi_at with (v := val);
    [ exact F | reflexivity | exact D
    | reflexivity
    | getr_resolve; regupd_resolve; reduce_bv_eqb_ifs; sp_norm;
      first [ reflexivity | lia | f_equal; lia
            | apply bv_eq;
              lazymatch goal with |- ?g => check_closed_term g end;
              vm_compute; reflexivity ] ]
  | step_simpl ].

Section WithFP24.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP24.
Ltac bveq :=
  apply bv_eq;
  lazymatch goal with
  | |- ?g =>
      tryif check_closed_term g then
        first
          [ (vm_compute; reflexivity)
          | fail 1 "bveq: vm_compute did not close this closed goal: "
                   "its two sides compute to different values." ]
      else tryif has_evar g then
        fail 1 "bveq: the goal contains an evar — vm_compute must not "
               "see it; instantiate the machine state (eexists / "
               "chain_step) before normalizing."
      else
        (* [comment removed for export] *)
        first
          [ reflexivity
          | fail 1 "bveq: the goal is OPEN (it mentions a context "
                   "variable) and kernel conversion did not close it — "
                   "resolve the register and memory projections first "
                   "(getr_resolve, regupd_resolve) and try again." ]
  end.

Section WithFP25.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP25.
Ltac stepw_addr :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].
Ltac stepw_val :=
  getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
  first [ reflexivity | sp_norm; first [ reflexivity | f_equal; lia ] | bveq ].

(* [comment removed for export] *)
Ltac stepw_addr_hyps :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : Sem.reg_get ?R ?r = _ |- context [Sem.reg_get ?R ?r] => rewrite H
  end;
  imm_norm; rewrite ?v_addi_0;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

Section WithFP27.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP27.
Ltac stepw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepsd F D aexp vexp vtac oktac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D | stepw_addr_hyps | vtac | oktac ]
  | step_simpl ].

Ltac stepld F D aexp vexp readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by stepw_addr_hyps
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

Section WithFP28.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP28.
Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP29.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP29.
Ltac wlit_closed p :=
  check_closed_term p;
  let u := vm_eval (bv_unsigned p) in
  replace p with (Z_to_bv 64 u) by bveq.

Section WithFP30.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP30.
Ltac wlits_closed :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_add ?a ?b] => wlit_closed (v_add a b)
  | |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
  end.

Section WithFP32.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP32.
Ltac rdn_ext_lit :=
  erewrite rdn_ext;
    [ (* [comment removed for export] *)
    | imm_norm; u_norm; lia
    | let x := fresh "x" in
      let Hx := fresh "Hx" in
      intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].

Section WithFP33.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma byte_nz_u : forall b : byte, b <> Z_to_bv 8 0 -> (bv_unsigned b <> 0)%Z.
Proof.
  intros b Hb Hc. apply Hb. apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_zext8 : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intro b. apply u_Z2bv; pose proof (u8_range b); lia.
Qed.

(* [comment removed for export] *)
Lemma zext8_byte : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
  intro b. apply bv_eq.
  rewrite Z_to_bv_unsigned, u_zext8.
  apply bv_wrap_small. pose proof (u8_range b).
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma byte_neq_lit_u : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z -> (bv_unsigned b <> z)%Z.
Proof.
  intros b z Hz Hb Hc. apply Hb. apply bv_eq.
  rewrite Hc, Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.mod_small; [reflexivity |].
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma c_eq_zext_lit_false : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z ->
  c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 z) = false.
Proof.
  intros b z Hz Hb. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  rewrite u_zext8, u_Z2bv by lia.
  exact (byte_neq_lit_u b z Hz Hb).
Qed.

(* [comment removed for export] *)
Lemma u_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  bv_unsigned (nat_to_word n) = Z.of_nat n.
Proof. intros n Hn. unfold nat_to_word. apply u_Z2bv; lia. Qed.

(* [comment removed for export] *)
Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_0 : forall x : word, x + nat_to_word 0 = x.
Proof.
  intro x. apply bv_eq. rewrite word_add_nat.
  rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_wrap : forall x y : word,
  (2^64 <= bv_unsigned x + bv_unsigned y)%Z ->
  v_add x y = Z_to_bv 64 (bv_unsigned x + bv_unsigned y - 2^64).
Proof.
  intros x y Hw. unfold v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- (Z.mod_add (bv_unsigned x + bv_unsigned y - 2^64) 1 (2^64)) by lia.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_sub_0_neg : forall y : word,
  v_sub (Z_to_bv 64 0) y = Z_to_bv 64 (- bv_unsigned y).
Proof.
  intro y. unfold v_sub.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  f_equal.
Qed.

(* [comment removed for export] *)
Lemma u_neg_small : forall z : Z, (0 < z)%Z -> (z <= 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 (- z)) = (2^64 - z)%Z.
Proof.
  intros z Hz0 Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  replace (- z)%Z with ((2^64 - z) + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_neg_S : forall d : nat,
  v_addi (Z_to_bv 64 (- Z.of_nat (S d))) 1 = Z_to_bv 64 (- Z.of_nat d).
Proof.
  intro d. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_bound : forall ph (sp : word) (a e : list (list byte)) uid hw rnd,
  valid_argv a -> valid_envp e ->
  (Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd)) <= 2240000)%Z.
Proof.
  intros ph sp a e uid hw rnd Hva Hve.
  pose proof (build_stack_bytes_within_span ph sp a e uid hw rnd).
  pose proof (entry_stack_span_bound a e Hva Hve).
  unfold entry_stack_span_max in *. lia.
Qed.

(* [comment removed for export] *)
Lemma range_avoids_two : forall (s0 s1 : Segment) (a n : Z),
  Z.ltb a (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) = false ->
  Z.ltb a (Z.of_N (seg_base s1) + Z.of_N (seg_size s1)) = false ->
  range_avoids_ro_segs [s0; s1] a n = true.
Proof.
  intros s0 s1 a n H0 H1. unfold range_avoids_ro_segs. cbn [forallb].
  rewrite H0, H1. rewrite !andb_false_r. cbn [negb]. rewrite !orb_true_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
          segs.

Lemma range_avoids_ro_above : forall (segs : list Segment) (data_base addr n : Z),
  ro_segs_below segs data_base = true ->
  (data_base <= addr)%Z ->
  range_avoids_ro_segs segs addr n = true.
Proof.
  intros segs data_base addr n Hbelow Haddr.
  unfold ro_segs_below in Hbelow. unfold range_avoids_ro_segs.
  rewrite forallb_forall in *. intros seg Hin.
  specialize (Hbelow seg Hin).
  destruct (seg_writable seg) eqn:W; cbn [orb] in *; [reflexivity|].
  apply Z.leb_le in Hbelow.
  apply negb_true_iff. apply andb_false_iff. right.
  apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section DispatchSmoke.
  Variable segs : list Segment.
  Variable regs : bvmap 5 word.
  Variable mem rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac smoke enc sh :=
    let F := fresh "F" in
    intro F;
    let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv;
    eexists; stepi F D; apply mst_refl.

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

End DispatchSmoke.
End WithFP33.
