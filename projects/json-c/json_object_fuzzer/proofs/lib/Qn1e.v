(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Fs.ReadWrite.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox QsV0 QsRG Qnhz Qrxj QSjk QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import Qpox QsV0 QsRG.Mq0 QsRG Qnhz.Mq0 Qrxj QSjk QSjk.Mq1 QiVh.Mq0.

Import ListNotations.
Open Scope bv_scope.

Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.

Fixpoint procs (a : A) (bs : list byte) : option A :=
match bs with
| [] => Some a
| b :: rest => match f a b with Some a' => procs a' rest | None => None end
end.

#[using="Type"] Lemma procs_app : forall bs1 bs2 a,
procs a (bs1 ++ bs2) =
match procs a bs1 with Some a' => procs a' bs2 | None => None end.
Proof.
induction bs1 as [|b bs1 IH]; intros bs2 a; [reflexivity|].
cbn [procs app]. destruct (f a b); [apply IH | reflexivity].
Qed.
End Proc.

Definition block_ok (cnt : word) (bs : list byte) : Prop :=
(1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.

Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
flat_map (fun bs => map (ReadEv rch) bs) blocks.

Lemma reads_ch_cons : forall rch bs blocks,
reads_ch rch (bs :: blocks) = map (ReadEv rch) bs ++ reads_ch rch blocks.
Proof. reflexivity. Qed.

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

Definition out_tail (s : InputStream) (a : A) (fs : Fs.Fs) : list event :=
match s with
| IEof => map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
| ICons _ _ => []
end.

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

Definition drain_from (a : A) (fs : Fs.Fs) (s : InputStream)
(tr : list event) : Prop :=
drain_from_ch (Z_to_bv 64 0) a fs s tr.

#[using="Type"] Lemma drain_from_ch_prefix : forall rch a fs s tr tr',
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

#[using="Type"] Lemma drain_from_prefix : forall a fs s tr tr',
drain_from a fs s tr -> is_prefix tr' tr -> drain_from a fs s tr'.
Proof. exact (drain_from_ch_prefix (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_nil : forall rch a fs s, drain_from_ch rch a fs s [].
Proof.
intros rch a fs s. left. exists [], s, a.
split; [constructor | split; [reflexivity | apply is_prefix_nil]].
Qed.

#[using="Type"] Lemma drain_from_nil : forall a fs s, drain_from a fs s [].
Proof. exact (drain_from_ch_nil (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_out : forall rch a fs tr,
is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
drain_from_ch rch a fs IEof tr.
Proof.
intros rch a fs tr Hp. left. exists [], IEof, a.
split; [constructor | split; [reflexivity | exact Hp]].
Qed.

#[using="Type"] Lemma drain_from_out : forall a fs tr,
is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
drain_from a fs IEof tr.
Proof. exact (drain_from_ch_out (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_block : forall rch a a1 fs s bs tr,
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

#[using="Type"] Lemma drain_from_block : forall a a1 fs s bs tr,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
procs f a bs = Some a1 ->
drain_from a1 fs (snd (stream_take s (length bs))) tr ->
drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_block (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_err : forall rch a fs s bs tr,
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

#[using="Type"] Lemma drain_from_err : forall a fs s bs tr,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
procs f a bs = None ->
is_prefix tr [ExitEv ec fs] ->
drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_err (Z_to_bv 64 0)). Qed.

End Traces.

Lemma fd1chan_with_stdin : forall s m, fd1chan m -> fd1chan (with_stdin s m).
Proof. intros s m H. exact H. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

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

Definition lh_next (a : A) (ms : machine_state) : Prop :=
exists ms', msteps segs ms ms' /\ LH a ms'.

Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
(1 <= length bs)%nat /\
to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).

Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_out bs ms' -> to_out bs ms.

Definition ReadPend (a : A) (ms : machine_state) : Prop :=
exists buf x8,
ms_svc_pending ms = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms 0 = Z_to_bv 64 0 /\
ms_gpr ms 1 = buf /\
ms_gpr ms 2 = cnt /\
(exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
= Some w) /\

access_okb buf (bv_unsigned cnt) = true /\
to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\

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

Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_rd a ms' -> to_rd a ms.

#[using="Type"] Lemma msteps_to_rd : forall a ms ms',
msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof.
intros a ms ms' H; induction H; [auto|].
intro Hrd. eapply trd_step; eauto.
Qed.

#[using="Type"] Lemma msteps_to_out : forall bs ms ms',
msteps segs ms ms' -> to_out bs ms' -> to_out bs ms.
Proof.
intros bs ms ms' H; induction H; [auto|].
intro Ho. eapply tout_step; eauto.
Qed.

#[using="Type"] Lemma to_out_wall_tail : forall bs ms,
to_out bs ms ->
to_wall_tail segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).
Proof.
intros bs ms H;
induction H as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH].
- apply twt_done. exact Hte.
- destruct HWF as [Hnb Hwl]. apply twt_more; assumption.
- eapply twt_step; eauto.
Qed.

Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

#[using="H_LH"] Lemma lh_next_to_rd : forall a ms, lh_next a ms -> to_rd a ms.
Proof.
intros a ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

#[using="Type"] Lemma to_rd_star : forall a ms model,
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

#[using="Type"] Lemma msteps_star : forall ms ms' model,
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

#[using="Type"] Lemma to_out_star_admits : forall bs ms model,
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

#[using="Type"] Lemma to_out_star_only : forall bs ms model,
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

#[using="Hcnt"] Lemma read0_check_eof_cnt : forall ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
m_stdin model = IEof ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->

access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
check_read (sys_input segs ms x8)
(fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
(mkEffect (Z_to_bv 64 0) [] []) model
= CheckOk model [].
Proof. apply (QiVh.Mq0.read0_check_eof cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_eof_cnt : forall ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
m_stdin model = IEof ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->

access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof. apply (QiVh.Mq0.read0_ok_eof cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_check_bytes_cnt : forall ms x8 model w bs,
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
Proof. apply (QiVh.Mq0.read0_check_bytes cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_bytes_cnt : forall ms x8 model w bs,
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
Proof. apply (QiVh.Mq0.read0_ok_bytes cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_inv_cnt : forall ms x8 model buf w eff model' evs,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->

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
Proof. apply (QiVh.Mq0.read0_ok_inv cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_no_err_cnt : forall ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->

access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. apply (QiVh.Mq0.read0_no_unmodeled cnt Hcnt). Qed.

#[using="Hcnt"] Lemma sstep_read_inv_cnt : forall ms model buf x8 w evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 63%Z ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->

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
Proof. apply (QiVh.Mq0.sstep_read_inv cnt Hcnt). Qed.

#[using="Hcnt"] Lemma drain_read_step : forall bs ms model buf x8 w,
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

#[using="Hcnt H_LH"] Lemma drain_star_admits_ok : forall s blocks s',
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
+
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
+
cbn [out_tail app]. exists (mkCfg ms model). apply star_refl.
-
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

#[using="Hcnt Hec H_LH"] Lemma drain_star_admits_err : forall s blocks s1,
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

#[using="Hcnt Hec H_LH"] Lemma star_drain_only : forall c0 tr c', star segs c0 tr c' ->
forall a ms model, c0 = mkCfg ms model -> M_loop model -> to_rd a ms ->
drain_from cnt f out ec a (m_fs model) (m_stdin model) tr.
Proof.
intros c0 tr c' Hstar.
induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
intros a ms model Heq HM Hrd; subst.
- apply drain_from_nil.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms' Hsvc Hstep Hrd'].
+
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
destruct (sstep_read_inv_cnt ms model buf x8 w evs (SNext c2)
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
inversion Hc2; subst.
*
pose proof (to_out_star_only (out a) _ model Hfd1 Hh Hlazy Hout Hobm
tr2 c3 Hstar) as Hpref.
cbn [app]. rewrite Hs. apply drain_from_out. exact Hpref.
*
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
+
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
subst evs. inversion Hc2; subst c2. cbn [app].
exact (IH a _ model eq_refl HM Hrd').
Qed.

Definition dinv (c : config) : Prop :=
(M_loop (cfg_model c) /\ exists a, to_rd a (cfg_ms c))
\/ (fd1chan (cfg_model c) /\ m_halted (cfg_model c) = None /\
m_vm_lazy (cfg_model c) = [] /\
exists rest, buf_modeled rest /\
to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) rest
(to_exit segs (Z_to_bv 64 0)))
\/ on_path segs (Z_to_bv 64 0) c
\/ on_path segs ec c.

#[using="Type"] Lemma wall_out_dinv_step : forall rest ms model evs ms' model',
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
-
right. right. left.
apply (on_path_step segs (Z_to_bv 64 0) (mkCfg ms model) evs); [|exact Hss].
left. repeat split; assumption.
-
destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms rest _ model evs (SNext (mkCfg ms' model'))
Hh Hlazy Hfdc Hbm Hwl Hss) as (n & Hn1 & Hn2 & _ & Hc2 & Ht2).
inversion Hc2; subst.
right. left. cbn. repeat split; try assumption.
exists (skipn n rest).
split; [apply buf_modeled_skipn; exact Hbm | exact Ht2].
-
destruct (sstep_instr_inv segs ms model msS' evs (SNext (mkCfg ms' model'))
Hlazy HsvcS HstepS Hss) as [_ Hc2].
inversion Hc2; subst.
right. left. cbn. repeat split; try assumption.
exists rest. split; [exact Hbm | exact Ht'].
Qed.
#[using="Hcnt H_LH"] Lemma dinv_step : forall c evs c',
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

#[using="Hcnt"] Lemma dinv_no_error : forall c evs, dinv c -> ~ sstep segs c evs SError.
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

#[using="Hcnt H_LH"] Lemma star_dinv : forall c tr c', dinv c -> star segs c tr c' -> dinv c'.
Proof. exact (star_inv segs dinv dinv_step). Qed.

#[using="Hcnt H_LH"] Lemma to_rd_no_error : forall a ms model,
M_loop model -> to_rd a ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
intros a ms model HM Hrd.
apply (inv_no_reaches_error segs dinv dinv_step dinv_no_error).
left; cbn; eauto.
Qed.

#[using="Hcnt Hec H_LH"] Lemma drain_obs_iff : forall pc ph sp brk0 mb rnd lim inp a0,
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

#[using="Hcnt H_LH"] Lemma drain_no_error : forall pc ph sp brk0 mb rnd lim inp a0,
to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros pc ph sp brk0 mb rnd lim inp a0 Hrd.
apply (to_rd_no_error a0); [apply init_M_loop | exact Hrd].
Qed.

#[using="Hcnt H_LH"] Lemma to_rd_coexec : forall a ms model,
M_loop model -> to_rd a ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
intros a ms model HM Hrd.
apply (inv_coexec segs dinv dinv_step dinv_no_error).
left; cbn. split; [exact HM | exists a; exact Hrd].
Qed.

#[using="Hcnt H_LH"] Lemma drain_omni_corun : forall pc ph sp brk0 mb rnd lim inp a0,
to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_corun]. unfold init_config.
apply (to_rd_coexec a0); [apply init_M_loop | exact Hrd].
Qed.

#[using="Hcnt Hec H_LH"] Lemma drain_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp a0,
to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
(drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp)).
Proof.
intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_cosafe].
apply cosafe_obs_iff.
-
intros t t' Ht Hp.
apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd).
eapply obs_trace_prefix_closed; [| exact Hp].
apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Ht.
- intros tr Hobs. apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Hobs.
Qed.

End Drain.

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
End Mq0.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Mm.Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.
Import Qpox QsV0 QsRG.Mq0 QsRG Qnhz.Mq0 Qrxj QiVh.Mq0 QiVh.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import ListNotations.
Open Scope bv_scope.

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma v_srli_div : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
bv_unsigned (v_srli x sh) = (bv_unsigned x / 2 ^ sh)%Z.
Proof.
intros x sh Hsh. unfold v_srli.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (u64_range x) as Hx.
assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
by (apply Z.div_le_upper_bound; nia).
assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
[Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
rewrite <- N_to_le_bytes_1_small.
apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.

#[using="Type"] Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
(a v : word) (b : byte),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
getr regs rs2 = v ->
Z_to_bv 8 (bv_unsigned v) = b ->
RiscvSemantics.store_ok segs mem a 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv, Hb. reflexivity.
- rewrite Ha. exact Hok.
Qed.

#[using="Type"] Lemma wbytes_snoc : forall (bs : list byte) (m : word -> option byte)
(a : word) (b : byte),
wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word (length bs)) [b].
Proof.
induction bs as [|x bs IH]; intros m a b.
- cbn [app wbytes length]. rewrite word_add_0. reflexivity.
- cbn [app wbytes length].
rewrite IH. f_equal.
rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.

Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
zmem m a n.

#[using="Type"] Lemma zfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
zfill a n m x = m x.
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.

#[using="Type"] Lemma rdn_zfill_out : forall segs a n m (x : word) k,
(bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
(bv_unsigned x + Z.of_nat k <= bv_unsigned a
\/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
rdn segs (zfill a n m) x k = rdn segs m x k.
Proof.
intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.

Definition munmap_model (addr n : word) (m : Model) : Model :=
with_mmap_destroyed addr n
(mkVmMapsFull (vm_reserved (m_vmmaps m))
(map_remove (vm_maps (m_vmmaps m)) addr)
(maps_subtract (vm_noaccess (m_vmmaps m))
(bv_unsigned addr)
(bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.

Definition mmap_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
(vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.

Definition page_round_up (len : word) : word :=
Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).

Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
&& (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

#[using="Type"] Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof. intros addr n m H. exact H. Qed.
#[using="Type"] Lemma munmap_model_no_lazy : forall addr n m,
m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
vm_forget_range, with_vm_backing, with_vmmaps.
cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
#[using="Type"] Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof. intros a n m H. exact H. Qed.
#[using="Type"] Lemma mmap_model_lazy : forall a n m,
m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma grant_ok_unpack : forall hint m a n,
grant_ok hint m a n = true ->
(bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
(bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
(vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof.
intros hint m a n H. unfold grant_ok in H.
rewrite !andb_true_iff in H.
destruct H as [[[[H1 H2] H3] H4] H5].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
apply Z.leb_le in H5.
auto 7.
Qed.

#[using="Type"] Lemma region_free_cons : forall (b s : word) r (lo n : word),
region_free ((b, s) :: r) lo n = true ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b
\/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
/\ region_free r lo n = true.
Proof.
intros b s r lo n H. cbn [region_free] in H.
apply andb_true_iff in H. destruct H as [H1 H2].
split; [|exact H2].
apply negb_true_iff in H1. unfold iv_overlap in H1.
apply andb_false_iff in H1.
destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.

#[using="Type"] Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma in_arg3_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.

#[using="Type"] Lemma in_arg4_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.

#[using="Type"] Lemma in_arg5_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.

Definition mmap_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.

#[using="Type"] Lemma mmap_args_ok_gates : forall ms,
mmap_args_ok ms ->
mmap_off_aligned_b (ms_gpr ms 5) = true /\
mmap_anon_b (ms_gpr ms 3) = true /\
w_is0 (ms_gpr ms 1) = false /\
mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
= true.
Proof.
intros ms (H1 & H2 & H3 & H4 & H5).
split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
(bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
ms_gpr ms 1 <> Z_to_bv 64 0 /\
(bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) = true.

Definition munmap_eff (ms : machine_state) : SyscallEffect :=
mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

#[using="Type"] Lemma syscall_spec_munmap : forall segs ms x8 model o,
bv_unsigned x8 = 215%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

#[using="Type"] Lemma munmap_check_modeled : forall ms model eff,
munmap_args_ok ms model ->
check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if w_is0 r
&& listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms model eff (Hal & Hlen & Hnw & Hhas).
unfold check_munmap.
rewrite (proj2 (Z.eqb_eq _ _) Hal).
unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
cbn [negb orb]. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.

#[using="Type"] Lemma munmap_ok : forall segs ms x8 model,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
syscall_spec (sys_input segs ms x8) model
(Ok (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros segs ms x8 model Hno Ha.
apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
rewrite (munmap_check_modeled ms model _ Ha).
unfold munmap_eff, w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

#[using="Type"] Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
eff = munmap_eff ms /\
model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model
/\ evs = [].
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply check_munmap_complete_ok in Hspec.
rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
[destruct zs as [|? ?]|]; try discriminate.
destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
destruct (w_is0 r
&& listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
eqn:HC; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in HC as [Hr Hus].
unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
apply listNN_eqb_eq in Hus; subst us.
unfold munmap_eff. auto.
Qed.

#[using="Type"] Lemma munmap_no_unmodeled : forall segs ms x8 model,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
destruct (w_is0 (Z_to_bv 64 0)
&& listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
discriminate.
Qed.

#[using="Type"] Lemma syscall_spec_mmap : forall segs ms x8 model o,
bv_unsigned x8 = 222%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
(ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

#[using="Type"] Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.

#[using="Type"] Lemma mmap_errno_range : forall e,
In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.

#[using="Type"] Lemma mmap_fail_ok : forall segs ms x8 model e,
bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> In e mmap_errnos ->
mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
intros segs ms x8 model e Hno Ha HIn Href.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

#[using="Type"] Lemma grant_not_errno : forall hint model a n,
(0 <= n)%Z -> grant_ok hint model a n = true ->
errno_ret_in mmap_errnos a = false.
Proof.
intros hint model a n Hn Hg.
destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
apply errno_ret_in_below; [reflexivity|].
alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Lemma grant_not_errno_when : forall hint model a n (c : bool),
(0 <= n)%Z -> grant_ok hint model a n = true ->
errno_ret_in (mmap_errnos_when c) a = false.
Proof.
intros hint model a n c Hn Hg. destruct c; cbn [mmap_errnos_when]; [|reflexivity].
exact (grant_not_errno hint model a n Hn Hg).
Qed.

Lemma errno_ret_in_when_true : forall c r,
errno_ret_in (mmap_errnos_when c) r = true -> c = true /\ errno_ret_in mmap_errnos r = true.
Proof. intros [|] r H; cbn [mmap_errnos_when] in H; [auto|discriminate H]. Qed.

Lemma grant_ok_not_refusable : forall hint m a n flags,
grant_ok hint m a n = true -> mmap_grant_refusable flags m n = false.
Proof.
intros hint m a n flags Hg. unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[[G1 G2] G3] G4] G5].
unfold mmap_grant_refusable, mmap_noreserve_backed_ok.
assert (Hgap : vm_gap_available (m_vmmaps m) n = true).
{ apply (proj2 (vm_gap_available_iff _ _)). exists a.
split; [apply Z.eqb_eq; exact G1|]. split; [apply Z.ltb_lt; exact G2|].
split; [apply Z.leb_le; exact G3| exact G4]. }
rewrite Hgap, G5. destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma not_refusable_grant_ok : forall hint m n,
mmap_grant_refusable (Z_to_bv 64 34) m n = false -> exists a, grant_ok hint m a n = true.
Proof.
intros hint m n H. unfold mmap_grant_refusable, mmap_noreserve_backed_ok in H.
replace (mmap_noreserve_b (Z_to_bv 64 34)) with false in H by (vm_compute; reflexivity).
apply Bool.orb_false_iff in H as [Hb Hgap]. apply Bool.negb_false_iff in Hb. apply Bool.negb_false_iff in Hgap.
apply (proj1 (vm_gap_available_iff _ _)) in Hgap as (a & A1 & A2 & A3 & A4).
exists a. unfold grant_ok.
rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3), A4, Hb. reflexivity.
Qed.

#[using="Type"] Lemma mmap_succ_ok : forall segs ms x8 model a,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
(mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros segs ms x8 model a Hno Ha Hg.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite (grant_not_errno (ms_gpr ms 0) model a
(page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
| exact Hg ].
unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[[H1 H2] H3] H4] H5].
rewrite Hflags.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
rewrite H1, H2, H3, H4, H5.
unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
reflexivity.
Qed.

#[using="Type"] Lemma mmap_ok_inv : forall segs ms x8 model eff model' evs,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\
((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
/\ model' = model) \/
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
/\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
/\ model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)).
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply check_mmap_complete_ok in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
rewrite Hflags in Hspec.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
rewrite Hnr in Hspec.
destruct eff as [r ws zs us cs copyins].
cbv beta iota zeta in Hspec.
destruct ws as [|w ws]; [|discriminate].
destruct us as [|u us]; [|discriminate].
destruct cs as [|c cs]; [|discriminate].
destruct copyins as [|copyin copyins]; [|discriminate].
match type of Hspec with context [errno_ret_in ?l r] =>
destruct (errno_ret_in l r) eqn:Herr end; rewrite ?Herr in Hspec;
cbv beta iota in Hspec.
- destruct zs as [|z zs]; [|discriminate].
inversion Hspec; subst.
split; [reflexivity|]. left.
apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
exists e. auto.
- destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
&& (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
&& region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
&& (vm_backing_used model
+ page_round_up_Z (bv_unsigned (ms_gpr ms 1))
<=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
rewrite ?Hcond in Hspec.
2:{ rewrite andb_false_l in Hspec. discriminate. }
destruct (listNN_eqb zs
[(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
rewrite ?Hzs in Hspec.
2:{ rewrite andb_false_r in Hspec. discriminate. }
cbn [andb] in Hspec.
apply listNN_eqb_eq in Hzs. subst zs.
inversion Hspec; subst.
split; [reflexivity|]. right.
exists r. split; [|split].
+ unfold grant_ok. exact Hcond.
+ unfold page_round_up. reflexivity.
+ reflexivity.
Qed.

#[using="Type"] Lemma mmap_no_unmodeled : forall segs ms x8 model,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno Ha Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
cbv beta iota zeta in Hspec.
change (errno_ret_in mmap_errnos (Z_to_bv 64 0)) with false in Hspec. cbv beta iota in Hspec.
match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
discriminate.
Qed.

#[using="Type"] Lemma adv_mmap_grant : forall regs pc sv mem rom a n,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}
(mkEffect a [] [(a, n)]))
= mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof.
intros regs pc sv mem rom a n.
assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
{ cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies
apply_writes apply_copies].
unfold mkst, regupd.
rewrite b_npc4, Hm. reflexivity.
Qed.

Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
&& Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
then None else m x.

#[using="Type"] Lemma unfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
unfill a n m x = m x.
Proof.
intros a n m x Hx. unfold unfill.
destruct Hx as [Hx | Hx].
- rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
rewrite andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma rdn_unfill_out : forall segs a n m (x : word) k,
(bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
(bv_unsigned x + Z.of_nat k <= bv_unsigned a
\/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
rdn segs (unfill a n m) x k = rdn segs m x k.
Proof.
intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
intros y Hy. apply unfill_out. lia.
Qed.

#[using="Type"] Lemma adv_munmap : forall regs pc sv mem rom a n,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}
(mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
= mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom.
Proof.
intros regs pc sv mem rom a n.
assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
= unfill a n mem).
{ cbn [apply_writes apply_zeros].
apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity. }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
unfold mkst, regupd.
rewrite b_npc4, Hm. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
(1 <= length buf)%nat ->
twm_pend ms model buf bufs code ->
twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm ms' model bufs code ->
twm ms model bufs code

with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
(skipn n rest) bufs code) ->
twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
twm ms model bufs code ->
twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
(1 <= length rest)%nat ->
twm_pend ms model rest bufs code ->
twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.

Scheme twm_min := Minimality for twm Sort Prop
with twm_pend_min := Minimality for twm_pend Sort Prop
with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

#[using="Type"] Lemma msteps_twm : forall ms ms' model bufs code,
msteps segs ms ms' -> twm ms' model bufs code -> twm ms model bufs code.
Proof.
intros ms ms' model bufs code H; induction H; [auto|].
intro Hw. eapply twm_step; eauto.
Qed.

#[using="Type"] Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.
Proof.
intros ms ms' model rest bufs code H; induction H; [auto|].
intro Hw. eapply twmt_step; eauto.
Qed.

#[using="Type"] Lemma twm_write_ret : forall regs pc mem rom model buf bufs code,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = Z_to_bv 64 1 ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
twm_tail (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
model (skipn n buf) bufs code) ->
twm {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
model (buf :: bufs) code.
Proof.
intros regs pc mem rom model buf bufs code H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
apply twm_write; [exact Hnb|].
eapply twmp_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

#[using="Type"] Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = Z_to_bv 64 1 ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
model (skipn n rest) bufs code) ->
twm_tail {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
model rest bufs code.
Proof.
intros regs pc mem rom model rest bufs code H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
apply twmt_more; [exact Hnb|].
eapply twmp_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

#[using="Type"] Lemma twm_munmap_rec : forall regs pc mem rom model bufs code (a nlen : word),
bv_unsigned (getr regs 17) = 215%Z ->
reg_get regs 10 = a ->
reg_get regs 11 = nlen ->
(bv_unsigned a mod page_size = 0)%Z ->
nlen <> Z_to_bv 64 0 ->
(bv_unsigned a + page_round_up_Z (bv_unsigned nlen) <= TASK_SIZE)%Z ->
map_has (vm_maps (m_vmmaps model)) a (page_round_up nlen) = true ->
twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(unfill a (page_round_up nlen) mem) rom)
(munmap_model a (page_round_up nlen) model) bufs code ->
twm {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
model bufs code.
Proof.
intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
eapply twm_munmap.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
rewrite E10, E11, Ha, Hn. auto.
- unfold munmap_eff, ms_gpr. cbn [ms_regs].
rewrite E10, E11, Ha, Hn.
rewrite adv_munmap. exact Hcont.
Qed.

#[using="Type"] Lemma twm_exit_coden : forall regs pc mem rom model (c : word),
bv_unsigned (getr regs 17) = 93%Z ->
reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
twm {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
model [] c.
Proof.
intros regs pc mem rom model c H17 H10 Hc.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |} 0)
(Z_to_bv 64 255) = c).
{ unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
apply land_255_small. exact Hc. }
rewrite <- Hg.
eapply twm_exit.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
Qed.

#[using="Type"] Lemma sstep_munmap_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
subst eff model' evs0
end.
match goal with
| Hmat : materialize_model_accesses
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
inversion Hmat; subst
end.
split; reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (Heff & Hm & Hevs); subst eff model' evs0;
rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hm & _);
subst model';
assert (Hhn : m_halted
(munmap_model (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite munmap_model_halted; exact Hh);
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.

Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.

Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
(fs : Fs.Fs) : post :=
fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
/\ exits_with code tr o.

#[using="Type"] Lemma twm_exec_mut :
(forall ms model bufs code, twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
/\ (forall ms model rest bufs code, twm_pend ms model rest bufs code ->
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
/\ (forall ms model rest bufs code, twm_tail ms model rest bufs code ->
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))).
Proof.
apply (twm_mutind
(fun ms model bufs code =>
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
(fun ms model rest bufs code =>
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
(fun ms model rest bufs code =>
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))).
-
intros ms model x8 Hsvc Hx8 Hbm Hh Hlazy Hfd.
apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold twm_post. cbn beta. rewrite app_nil_r. cbn [wevents app]. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
intros ms model buf bufs code Hnb Hp IH Hbm Hh Hlazy Hfd.
apply Forall_cons_iff in Hbm as [Hb Hbs].
eapply exec_conseq; [exact (IH Hb Hbs Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx].
rewrite Heq. cbn [wevents]. rewrite <- app_assoc. reflexivity.
-
intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hbm Hh Hlazy Hfd.
assert (Hh' : m_halted
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite munmap_model_halted; exact Hh).
assert (Hfd' : fd1chan
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
by (apply munmap_model_fd1chan; exact Hfd).
apply (exec_step_only segs _ _ []
(mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
+ apply (sstep_syscall segs ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
* exact Hh.
* exact Hsvc.
* apply munmap_ok; [exact Hno | exact Hargs].
* exact Hh'.
* apply materialize_model_accesses_no_lazy.
exact (munmap_model_no_lazy _ _ _ Hlazy).
+ intros evs st Hss.
exact (sstep_munmap_inv ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss).
+ eapply exec_conseq;
[exact (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') |].
intros tr o (Heq & Hx). split; [| exact Hx].
cbn [app]. rewrite Heq, munmap_model_fs. reflexivity.
-
intros ms ms' model bufs code Hsvc Hstep Hte IH Hbm Hh Hlazy Hfd.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
-
intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hbr Hbm Hh Hlazy Hfd.
apply exec_step; [exact Hh | | |].
+ eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv (Z_to_bv 64 1)) (firstn (length rest) rest))).
* exact Hh.
* exact Hsvc.
* apply write1_ok_n; try assumption. apply Nat.le_refl.
* exact Hh.
* apply materialize_model_accesses_no_lazy. exact Hlazy.
+ intros evs Hss.
destruct (sstep_write_inv segs ms model x8 rest evs SError
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & _ & _ & _ & Habs).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_write_inv segs ms model x8 rest evs (SNext c')
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
injection Hc' as ->.
eapply exec_conseq;
[exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx].
rewrite Heq. rewrite <- (firstn_skipn n rest) at 3.
rewrite map_app, <- !app_assoc. reflexivity.
-
intros ms model bufs code Hte IH Hbr Hbm Hh Hlazy Hfd.
eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx]. cbn [map app]. exact Heq.
-
intros ms model rest bufs code Hnb Hp IH Hbr Hbm Hh Hlazy Hfd.
exact (IH Hbr Hbm Hh Hlazy Hfd).
-
intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hbr Hbm Hh Hlazy Hfd.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbr Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma twm_exec : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)).
Proof. intros ms model bufs code Hte. exact (proj1 twm_exec_mut ms model bufs code Hte). Qed.

#[using="Type"] Lemma twm_star_admits : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
exists c, star segs (mkCfg ms model) (wevents bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd.
destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.

#[using="Type"] Lemma twm_star_only : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (wevents bufs ++ [ExitEv code (m_fs model)]).
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar))
as (tr' & o & _ & Heq & _).
rewrite <- Heq. apply is_prefix_app.
Qed.

Inductive tmw : machine_state -> Model -> list (list byte) -> word
-> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
(forall e, In e mmap_errnos ->
twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
(forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
tmw ms' model bf cf bs cs ->
tmw ms model bf cf bs cs.

#[using="Type"] Lemma msteps_tmw : forall ms ms' model bf cf bs cs,
msteps segs ms ms' -> tmw ms' model bf cf bs cs -> tmw ms model bf cf bs cs.
Proof.
intros ms ms' model bf cf bs cs H; induction H; [auto|].
intro Hw. eapply tmw_step; eauto.
Qed.

#[using="Type"] Lemma tmw_mmap_rec : forall regs pc mem rom model bf cf bs cs,
bv_unsigned (getr regs 17) = 222%Z ->
reg_get regs 11 <> Z_to_bv 64 0 ->
reg_get regs 12 = Z_to_bv 64 3 ->
reg_get regs 13 = Z_to_bv 64 34 ->
reg_get regs 14 = Z_to_bv 64 (-1) ->
reg_get regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf) ->
(forall a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true ->
twm (mkst (regupd regs 10 a) (v_addi pc 4)
(zfill a (page_round_up (reg_get regs 11)) mem) rom)
(mmap_model a (page_round_up (reg_get regs 11)) model) bs cs) ->
(exists a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) ->
tmw {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
model bf cf bs cs.
Proof.
intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
Hfail Hsucc Hex.
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
assert (E13 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
assert (E14 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
assert (E15 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
eapply tmw_mmap.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold mmap_args_ok, ms_gpr. cbn [ms_regs].
rewrite E11, E12, E13, E14, E15.
auto.
- intros e HIn. rewrite adv_set. apply Hfail; assumption.
- intros a Hg. rewrite adv_mmap_grant.
unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
apply Hsucc. exact Hg.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.

#[using="Type"] Lemma sstep_mmap_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\
((exists e, In e mmap_errnos /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
subst evs0
end.
split; [reflexivity|].
destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
+ left. exists e.
match goal with
| Hmat : materialize_model_accesses model _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
inversion Hmat; subst
end.
split; [assumption |].
rewrite apply_effect_no_write. reflexivity.
+ match goal with
| Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
inversion Hmat; subst
end.
right. exists a. auto.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
| rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite Hh in H6; discriminate
| rewrite mmap_model_halted, Hh in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
[ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
| assert (Hhn : m_halted
(mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite mmap_model_halted; exact Hh);
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.

Definition two_traces (bf : list (list byte)) (cf : word)
(bs : list (list byte)) (cs : word)
(fs : Fs.Fs) (tr : list event) : Prop :=
is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
is_prefix tr (wevents bs ++ [ExitEv cs fs]).

#[using="Type"] Lemma twm_exec_not_errors : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
~ OmniRun.exec segs (mkCfg ms model) OmniRun.errors.
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd Hex.
destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
destruct (exec_sound _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm)
as (_ & Hx).
exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

#[using="Type"] Lemma twm_exec_code_unique : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
forall code', OmniRun.exec segs (mkCfg ms model) (exits_with code') -> code' = code.
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd code' Hex.
destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as ->. reflexivity.
Qed.

End WithSegs.

End FPGEN1.
End Mq1.

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh.Mq0.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fs_fs : forall f m, m_fs (with_fs f m) = f.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fs_halted : forall f m, m_halted (with_fs f m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fs_fds : forall f m, m_fds (with_fs f m) = m_fds m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma adv_eff_ret : forall regs pc x8 mem rom r,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := Some x8;
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
intros regs pc x8 mem rom r.
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros apply_writes apply_zeros].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.

#[using="Type"] Lemma adv_eff_ret_copyins : forall regs pc x8 mem rom r copyins,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := Some x8;
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}
(with_copyins copyins (mkEffect r [] [])))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
intros regs pc x8 mem rom r copyins.
unfold with_copyins.
apply adv_eff_ret.
Qed.

#[using="Type"] Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_arg0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_arg1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_arg2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_wmem_si : forall segs ms x8,
in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

#[using="Type"] Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
apply path_eqb_eq in E. congruence.
Qed.

#[using="Type"] Lemma fs_lookup_set_eq : forall fs p d, fs_lookup (fs_set fs p d) p = Some d.
Proof.
induction fs as [|[q dq] fs IH]; intros p d; cbn.
- rewrite path_eqb_refl. reflexivity.
- destruct (path_ltb p q); cbn.
+ rewrite path_eqb_refl. reflexivity.
+ destruct (path_eqb p q) eqn:E; cbn.
* rewrite path_eqb_refl. reflexivity.
* rewrite E. apply IH.
Qed.

#[using="Type"] Lemma fs_lookup_set_neq : forall fs p d q, q <> p ->
fs_lookup (fs_set fs p d) q = fs_lookup fs q.
Proof.
induction fs as [|[r dr] fs IH]; intros p d q Hne; cbn.
- rewrite path_eqb_neq by exact Hne. reflexivity.
- destruct (path_ltb p r); cbn.
+ rewrite path_eqb_neq by exact Hne. reflexivity.
+ destruct (path_eqb p r) eqn:E; cbn.
* apply path_eqb_eq in E. subst r.
rewrite path_eqb_neq by exact Hne. reflexivity.
* destruct (path_eqb q r); [reflexivity | apply IH; exact Hne].
Qed.

#[using="Type"] Lemma path_ltb_irrefl : forall p, path_ltb p p = false.
Proof.
induction p as [|a p IH]; cbn; [reflexivity|].
unfold bv_ltu. rewrite Z.ltb_irrefl, bv_eqb_refl, IH. reflexivity.
Qed.

#[using="Type"] Lemma fs_set_set : forall fs p d d', fs_set (fs_set fs p d) p d' = fs_set fs p d'.
Proof.
induction fs as [|[q dq] fs IH]; intros p d d'; cbn.
- rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
- destruct (path_ltb p q) eqn:EL; cbn.
+ rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
+ destruct (path_eqb p q) eqn:EE; cbn.
* rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
* rewrite EL, EE, IH. reflexivity.
Qed.

#[using="Type"] Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
intros fds k e fd Hne. cbn.
rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

#[using="Type"] Lemma fd_lookup_cons_None : forall fds k e fd,
fd_lookup ((k, e) :: fds) fd = None -> k <> fd /\ fd_lookup fds fd = None.
Proof.
intros fds k e fd H. cbn in H.
destruct (bv_eqb k fd) eqn:E; [discriminate|].
split; [|exact H].
intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

#[using="Type"] Lemma fd_filter_id : forall fds fd,
fd_lookup fds fd = None ->
List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
induction fds as [|[k e] fds IH]; intros fd H; [reflexivity|].
apply fd_lookup_cons_None in H. destruct H as [Hne H].
cbn [List.filter fst]. rewrite (bv_eqb_neq k fd Hne). cbn [negb].
rewrite IH by exact H. reflexivity.
Qed.

#[using="Type"] Lemma fd_insert_fresh : forall fds fd e,
fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof.
intros fds fd e H. unfold fd_insert. rewrite fd_filter_id by exact H.
reflexivity.
Qed.

#[using="Type"] Lemma fd_lookup_filter_neq : forall fds fd fd', fd' <> fd ->
fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) fd' = fd_lookup fds fd'.
Proof.
induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
cbn [List.filter fst].
destruct (bv_eqb k fd) eqn:Hk.
- apply bv_eqb_eq in Hk. subst k.
cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
rewrite bv_eqb_neq by congruence. reflexivity.
- cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.

#[using="Type"] Lemma fd_lookup_insert_eq : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.

#[using="Type"] Lemma fd_lookup_insert_neq : forall fds fd e fd', fd' <> fd ->
fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd'.
Proof.
intros fds fd e fd' Hne. unfold fd_insert.
rewrite fd_lookup_cons_neq by congruence.
apply fd_lookup_filter_neq. exact Hne.
Qed.

#[using="Type"] Lemma fd_lookup_remove_neq : forall fds fd fd', fd' <> fd ->
fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd'.
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.

#[using="Type"] Lemma fd_lookup_some_none_neq : forall fds a b ea,
fd_lookup fds a = Some ea -> fd_lookup fds b = None -> a <> b.
Proof. intros fds a b ea Ha Hb ->. congruence. Qed.

#[using="Type"] Lemma free_fd_after_open : forall x y z fdin e,
exists w, fd_lookup (fd_insert
[(Z_to_bv 64 0, x); (Z_to_bv 64 1, y); (Z_to_bv 64 2, z)] fdin e) w = None
/\ (bv_unsigned w < 2 ^ 31)%Z.
Proof.
intros x y z fdin e.
destruct (decide (fdin = Z_to_bv 64 3)) as [->|Hne].
- exists (Z_to_bv 64 4). split.
+ rewrite fd_lookup_insert_neq
by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
reflexivity.
+ change (bv_unsigned (Z_to_bv 64 4)) with 4%Z. lia.
- exists (Z_to_bv 64 3). split.
+ rewrite fd_lookup_insert_neq by congruence. reflexivity.
+ change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
Qed.

#[using="Type"] Lemma filter_fd_cons_keep : forall {B} (fds : list (word * B)) k (e : B) fd,
k <> fd ->
List.filter (fun p => negb (bv_eqb (fst p) fd)) ((k, e) :: fds)
= (k, e) :: List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
intros B fds k e fd Hne. cbn [List.filter fst].
rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

#[using="Type"] Lemma filter_fd_cons_drop : forall {B} (fds : list (word * B)) fd (e : B),
List.filter (fun p => negb (bv_eqb (fst p) fd)) ((fd, e) :: fds)
= List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
intros B fds fd e. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma length_file_read : forall data off count,
length (file_read data off count)
= Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
intros data off count. rewrite file_read_unguarded.
rewrite length_firstn, length_skipn. reflexivity.
Qed.

#[using="Type"] Lemma file_read_nil : forall data off count,
(length data <= word_to_nat off)%nat -> file_read data off count = [].
Proof.
intros data off count H. rewrite file_read_unguarded.
rewrite skipn_all2 by exact H. apply firstn_nil.
Qed.

#[using="Type"] Lemma file_write_append : forall data off bs,
word_to_nat off = length data -> file_write data off bs = data ++ bs.
Proof.
intros data off bs Hoff. unfold file_write.
destruct bs as [|b bs]; [now rewrite app_nil_r|]. cbv zeta.
rewrite Hoff, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
rewrite firstn_all.
rewrite skipn_all2 by lia.
rewrite app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma firstn_add {A} : forall (l : list A) n m,
firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
induction l as [|x l IH]; intros n m.
- rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
- destruct n as [|n]; [reflexivity|].
cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma copy_step : forall data (off count : word),
firstn (word_to_nat off) data ++ file_read data off count
= firstn (word_to_nat off
+ Nat.min (word_to_nat count) (length data - word_to_nat off)) data.
Proof.
intros data off count. rewrite file_read_unguarded.
rewrite firstn_add. f_equal.
destruct (Nat.le_ge_cases (word_to_nat count)
(length data - word_to_nat off)) as [H|H].
- rewrite Nat.min_l by exact H. reflexivity.
- rewrite Nat.min_r by exact H.
rewrite firstn_all2 by (rewrite length_skipn; lia).
rewrite firstn_all2 by (rewrite length_skipn; lia).
reflexivity.
Qed.

Definition mrb (segs : list Segment) (mem : word -> option byte)
: word -> option byte :=
fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

#[using="Type"] Lemma ms_read_byte_mrb : forall segs regs pc mem,
ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_read_byte_rec_mrb : forall segs regs fr pc sv rv fc mem,
ms_read_byte {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := seg_rom segs |}
= mrb segs mem.
Proof. reflexivity. Qed.

#[using="Type"] Lemma mrb_first : forall segs mem a n b rest,
rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
as [b1|]; [|discriminate].
destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
injection H; intros; subst; congruence.
Qed.

#[using="Type"] Lemma rdn_tail : forall segs mem a n b rest,
rdn segs mem a (S n) = Some (b :: rest) -> rdn segs mem (a + 1) n = Some rest.
Proof.
intros segs mem a n b rest H. cbn [rdn] in H.
destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
as [b1|]; [|discriminate].
destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
injection H; intros; subst; reflexivity.
Qed.

#[using="Type"] Lemma read_cstr_aux_of_rdn : forall segs str fuel mem a,
(length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
read_cstr_aux (mrb segs mem) a fuel = CstrOk str.
Proof.
intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
- cbn [length] in *. destruct fuel as [|fuel]; [lia|].
assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
cbn [read_cstr_aux]. rewrite Hb0. reflexivity.
- cbn [length] in *. destruct fuel as [|fuel]; [lia|].
cbn [read_cstr_aux]. cbn [app] in Hr.
assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
assert (Hfirst : mrb segs mem a = Some b)
by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
exact Hr).
assert (Htail : rdn segs mem (a + 1) (length str + 1)
= Some (str ++ [Z_to_bv 8 0]))
by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
exact Hr).
rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
rewrite (IH fuel mem (a + 1) ltac:(lia)
ltac:(intro; apply Hnz; right; assumption) Htail).
reflexivity.
Qed.

#[using="Type"] Lemma read_cstr_of_rdn : forall segs mem a str,
(length str <= 4095)%nat -> ~ In (Z_to_bv 8 0) str ->
rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
read_cstr (mrb segs mem) a = CstrOk str.
Proof.
intros segs mem a str Hlen Hnz Hr.
unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hr].
change path_max with 4096%nat. lia.
Qed.

#[using="Type"] Lemma read_cstr_aux_toolong_of_rdn : forall segs fuel bs mem a,
length bs = fuel -> ~ In (Z_to_bv 8 0) bs ->
rdn segs mem a fuel = Some bs ->
read_cstr_aux (mrb segs mem) a fuel = CstrTooLong.
Proof.
intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hr;
[reflexivity|].
destruct bs as [|b bs]; [cbn in Hlen; lia|].
cbn [read_cstr_aux].
assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
assert (Hfirst : mrb segs mem a = Some b)
by (apply (mrb_first segs mem a fuel b bs); exact Hr).
assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
ltac:(intro; apply Hnz; right; assumption) Htail).
reflexivity.
Qed.

#[using="Type"] Lemma read_cstr_toolong_of_rdn : forall segs mem a bs,
length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs ->
rdn segs mem a 4096%nat = Some bs ->
read_cstr (mrb segs mem) a = CstrTooLong.
Proof.
intros segs mem a bs Hlen Hnz Hr.
unfold read_cstr. change path_max with 4096%nat.
eapply read_cstr_aux_toolong_of_rdn; eauto.
Qed.

#[using="Type"] Lemma read_argv_cstr_k : forall ph segs (sp : word) av ev k uid hw rnd,
(k < length av)%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
(cat_argv_ptr sp av ev k) (length (nth k av []) + 1)
= Some (nth k av [] ++ [Z_to_bv 8 0]).
Proof.
intros ph segs sp av ev k uid hw rnd Hk Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (nth k av [] ++ [Z_to_bv 8 0]) post (length (nth k av []) + 1)) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [exact E | | exact Hnw].
rewrite length_app. cbn [length]. lia.
Qed.

#[using="Type"] Lemma read_argv_prefix_k : forall ph segs (sp : word) av ev k n uid hw rnd,
(k < length av)%nat -> (n <= length (nth k av []))%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
(cat_argv_ptr sp av ev k) n
= Some (firstn n (nth k av [])).
Proof.
intros ph segs sp av ev k n uid hw rnd Hk Hn Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (firstn n (nth k av []))
((skipn n (nth k av []) ++ [Z_to_bv 8 0]) ++ post) n) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [| |exact Hnw].
- rewrite E. rewrite <- !app_assoc.
rewrite (app_assoc (firstn n (nth k av [])) (skipn n (nth k av []))).
rewrite firstn_skipn. reflexivity.
- apply firstn_length_le. exact Hn.
Qed.

Definition fout_trace (o : word * Fs.Fs) : list event := [ExitEv (fst o) (snd o)].

Section WithSegs.
Variable segs : list Segment.

Inductive to_fout : machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfo_exit : forall ms model x8 (U : (word * Fs.Fs) -> Prop),
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
(forall o, U o <-> o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) ->
to_fout ms model U
| tfo_step : forall ms ms' model U,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_fout ms' model U ->
to_fout ms model U
| tfo_sys : forall ms model x8
(T : SyscallEffect -> Model -> (word * Fs.Fs) -> Prop)
(U : (word * Fs.Fs) -> Prop),
ms_svc_pending ms = Some x8 ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) ->
(forall eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
(forall eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
to_fout (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
(forall o, U o <->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
/\ T eff model' o)) ->
to_fout ms model U.

#[using="Type"] Lemma tfo_msteps : forall ms ms' model U,
msteps segs ms ms' -> to_fout ms' model U -> to_fout ms model U.
Proof.
intros ms ms' model U H; induction H; [auto|].
intro Ht. eapply tfo_step; eauto.
Qed.

#[using="Type"] Lemma tfo_equiv : forall ms model U V,
to_fout ms model U ->
(forall o, V o <-> U o) ->
to_fout ms model V.
Proof.
intros ms model U V Hto; revert V.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros V HV.
- apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
intro o. rewrite (HV o). apply HU.
- eapply tfo_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
- apply (tfo_sys ms model x8 T V);
[exact Hsvc | exact Hne | exact Hrec | exact Hshape | exact Hcont |].
intro o. rewrite (HV o). apply HU.
Qed.

#[using="Type"] Lemma to_fout_nonempty : forall ms model U,
to_fout ms model U -> exists o, U o.
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ].
- exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
apply HU. reflexivity.
- exact IH.
- destruct Hrec as (eff & model' & evs & Hspec).
destruct (IH eff model' evs Hspec) as [o Ho].
exists o. apply HU. exists eff, model', evs. auto.
Qed.

#[using="Type"] Lemma sstep_fsys_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(forall eff model' evs',
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs') ->
evs' = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
sstep segs (mkCfg ms model) evs st ->
exists eff model',
syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
evs = [] /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (He & _ & Hlazy');
subst evs0;
match goal with
| Hmat : materialize_model_accesses model' _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
inversion Hmat; subst model''
end;
exists eff, model'; auto
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & _ & Hlazy');
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
congruence
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
assert (Hhn : m_halted model' = None) by congruence;
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
end.
Qed.

Definition fout_post (U : (word * Fs.Fs) -> Prop) : post :=
fun tr o => exists out, U out /\ tr = fout_trace out /\ exits_with (fst out) tr o.

#[using="Type"] Lemma to_fout_exec : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
OmniRun.exec segs (mkCfg ms model) (fout_post U).
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros Hh Hlazy.
-
apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_si. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold fout_post. cbn beta.
exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
split; [apply HU; reflexivity |].
split; [unfold fout_trace; cbn [fst snd app]; reflexivity |].
cbn [exits_with cfg_model fst]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
-
apply exec_step; [exact Hh | | |].
+ destruct Hrec as (eff & model' & evs & Hspec).
destruct (Hshape eff model' evs Hspec) as (-> & Hh' & Hlazy').
eexists; eexists.
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
+ intros evs Hss.
destruct (sstep_fsys_inv ms model x8 evs SError Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & _ & _ & Habs). discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_fsys_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' Hlazy') |].
intros tr o (out & Hout & Heq & Hx). exists out.
split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
split; [cbn [app]; exact Heq | exact Hx].
Qed.

#[using="Type"] Lemma to_fout_star_only : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
forall tr c, star segs (mkCfg ms model) tr c ->
exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
intros ms model U Hto Hh Hlazy tr c Hstar.
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_fout_exec ms model U Hto Hh Hlazy) Hstar))
as (tr' & o & _ & (out & Hout & Heq & _)).
exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Type"] Lemma to_fout_star_admits : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
forall o, U o ->
exists c, star segs (mkCfg ms model) (fout_trace o) c.
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros Hh Hlazy o Ho.
-
apply HU in Ho. subst o. unfold fout_trace; cbn [fst snd].
exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
apply star_one.
replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
+ exact Hh.
+ exact Hsvc.
+ apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_si. exact Hx8.
+ cbn. reflexivity.
+ apply m_killed_with_halted.
-
destruct (IH Hh Hlazy o Ho) as [c Hstar].
exists c.
replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
eapply star_step; [|exact Hstar].
apply (sstep_instr segs ms model ms' model); try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
-
apply HU in Ho.
destruct Ho as (eff & model' & evs & Hspec & Ht).
destruct (Hshape eff model' evs Hspec) as (He & Hh' & Hlazy'). subst evs.
destruct (IH eff model' [] Hspec Hh' Hlazy' o Ht) as [c Hstar].
exists c.
replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
eapply star_step; [|exact Hstar].
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
Qed.

#[using="Type"] Lemma to_fout_progress : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
forall evs st, sstep segs (mkCfg ms model) evs st ->
exists ms' model', st = SNext (mkCfg ms' model') /\
(m_halted model' <> None \/
(m_halted model' = None /\ m_vm_lazy model' = [] /\
exists U', to_fout ms' model' U')).
Proof.
intros ms model U Hto Hh Hlazy evs st Hss.
revert evs st Hss.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros evs st Hss.
-
destruct (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss)
as [_ Hst]. subst st.
do 2 eexists. split; [reflexivity|]. left. cbn. discriminate.
-
destruct (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss)
as [_ Hst]. subst st.
do 2 eexists. split; [reflexivity|]. right.
repeat split; try assumption. exists U. exact Hto.
-
destruct (sstep_fsys_inv ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & Hspec & _ & Hst). subst st.
destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
do 2 eexists. split; [reflexivity|]. right.
repeat split; try assumption.
exists (T eff model'). exact (Hcont eff model' [] Hspec).
Qed.

Definition fon_path (c : config) : Prop :=
(m_halted (cfg_model c) = None
/\ m_vm_lazy (cfg_model c) = []
/\ exists U, to_fout (cfg_ms c) (cfg_model c) U)
\/ m_halted (cfg_model c) <> None.

#[using="Type"] Lemma fon_path_step : forall c evs c',
fon_path c -> sstep segs c evs (SNext c') -> fon_path c'.
Proof.
intros [ms model] evs [ms' model'] Hop Hss.
unfold fon_path in *; cbn in Hop |- *.
destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
- destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
as (ms'' & model'' & Hst & Hcase).
inversion Hst; subst.
destruct Hcase as [Hhz | (Hhz & Hlazy' & U' & Hto')].
+ right. exact Hhz.
+ left. repeat split; try assumption. exists U'; exact Hto'.
- exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma fon_path_no_error : forall c evs, fon_path c -> ~ sstep segs c evs SError.
Proof.
intros [ms model] evs Hop Hss.
unfold fon_path in Hop; cbn in Hop.
destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
- destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
as (ms'' & model'' & Hst & _). discriminate.
- inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma star_fon_path : forall c tr c',
fon_path c -> star segs c tr c' -> fon_path c'.
Proof. exact (star_inv segs fon_path fon_path_step). Qed.

#[using="Type"] Lemma to_fout_no_error : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
~ reaches_error segs (mkCfg ms model).
Proof.
intros ms model U Hto Hh Hlazy. apply exec_no_error.
eapply exec_conseq; [exact (to_fout_exec ms model U Hto Hh Hlazy) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

#[using="Type"] Lemma star_syscall_nil : forall ms model x8 eff model',
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
m_halted model' = None ->
m_vm_lazy model' = [] ->
star segs (mkCfg ms model) []
(mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
intros ms model x8 eff model' Hh Hsvc Hspec Hh' Hlazy.
apply star_one.
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy). reflexivity.
Qed.

#[using="Type"] Lemma reaches_error_star : forall c tr c',
star segs c tr c' -> reaches_error segs c' -> reaches_error segs c.
Proof.
intros c tr c' Hstar (tr2 & c2 & evs & Hstar2 & Hss).
exists (tr ++ tr2), c2, evs. split; [eapply star_trans; eauto | exact Hss].
Qed.

#[using="Type"] Lemma spec_err_error : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model Unmodeled ->
reaches_error segs (mkCfg ms model).
Proof.
intros ms model x8 Hh Hsvc Hspec.
exists [], (mkCfg ms model), []. split; [apply star_refl|].
eapply sstep_syscall_unmodeled; eassumption.
Qed.

#[using="Type"] Lemma msteps_spec_err_error : forall ms ms' model x8,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = Some x8 ->
syscall_spec (sys_input segs ms' x8) model Unmodeled ->
reaches_error segs (mkCfg ms model).
Proof.
intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
eapply reaches_error_star.
- apply msteps_star_nil; eassumption.
- eapply spec_err_error; eassumption.
Qed.

#[using="Type"] Lemma spec_err_all_traces_error : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model Unmodeled ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms model x8 Hh Hsvc Hspec.
assert (Hno_ok : forall eff model' events,
~ syscall_spec (sys_input segs ms x8) model
(Ok eff model' events)).
{ intros eff model' events Hok.
pose proof Hspec as Herr.
apply (check_syscall_complete_unmodeled _ _ eff) in Herr.
apply check_syscall_complete_ok in Hok.
rewrite Herr in Hok. discriminate Hok. }
constructor.
- exists [], SError. eapply sstep_syscall_unmodeled; eassumption.
- intros evs c' Hnext. inversion Hnext; subst; try congruence.
all: exfalso;
match goal with
| Hno : forall (eff0 : SyscallEffect) (model0 : Model)
(events0 : list event),
~ syscall_spec (sys_input ?segs0 ?ms0 ?expected) ?m0
(Ok eff0 model0 events0),
Hexpected : ms_svc_pending ?ms0 = Some ?expected,
Hactual : ms_svc_pending ?ms0 = Some ?actual,
Hok : syscall_spec (sys_input ?segs0 ?ms0 ?actual) ?m0
(Ok ?eff ?model' ?events) |- _ =>
assert (actual = expected) by congruence; subst actual;
exact (Hno eff model' events Hok)
end.
Qed.

#[using="Type"] Lemma msteps_spec_err_all_traces_error : forall ms ms' model x8,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = Some x8 ->
syscall_spec (sys_input segs ms' x8) model Unmodeled ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
eapply msteps_all_traces_error; [exact Hh | exact Hlazy | exact Hm |].
eapply spec_err_all_traces_error; eassumption.
Qed.

#[using="Type"] Lemma tfo_exit_code : forall ms model x8 code,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
ms_gpr ms 0 = code ->
bv_and code (Z_to_bv 64 255) = code ->
to_fout ms model (fun o => o = (code, m_fs model)).
Proof.
intros ms model x8 code Hsvc Hx8 Hg Hland.
apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
intro o. rewrite Hg, Hland. tauto.
Qed.

#[using="Type"] Lemma tfo_sys_det : forall ms model x8 eff model' U,
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
(forall eff2 m2 evs2,
syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) ->
eff2 = eff /\ m2 = model' /\ evs2 = []) ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
m_halted model' = None ->
m_vm_lazy model' = [] ->
to_fout (advance_past_svc (apply_effect ms eff)) model' U ->
to_fout ms model U.
Proof.
intros ms model x8 eff model' U Hsvc Hok Huniq Hne Hh' Hlazy' Hcont.
apply (tfo_sys ms model x8 (fun _ _ => U) U); [exact Hsvc | exact Hne | | | |].
- exists eff, model', []. exact Hok.
- intros eff2 m2 evs2 Hs.
destruct (Huniq eff2 m2 evs2 Hs) as (_ & -> & ->).
repeat split; assumption.
- intros eff2 m2 evs2 Hs.
destruct (Huniq eff2 m2 evs2 Hs) as (-> & -> & _). exact Hcont.
- intro o. split.
+ intro Ho. exists eff, model', []. auto.
+ intros (e2 & m2 & ev2 & _ & Ht). exact Ht.
Qed.

End WithSegs.

#[using="Type"] Lemma check_syscall_56 : forall segs ms x8 eff m,
bv_unsigned x8 = 56%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
(ms_gpr ms 2) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

#[using="Type"] Lemma check_syscall_57 : forall segs ms x8 eff m,
bv_unsigned x8 = 57%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_close (fd32 (ms_gpr ms 0)) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

#[using="Type"] Lemma check_syscall_63 : forall segs ms x8 eff m,
bv_unsigned x8 = 63%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
(ms_gpr ms 2) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

#[using="Type"] Lemma check_syscall_64 : forall segs ms x8 eff m,
bv_unsigned x8 = 64%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
(ms_gpr ms 2) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

#[using="Type"] Lemma fd_not_error : forall fd : word,
(bv_unsigned fd < 2 ^ 31)%Z -> addr_is_error_b fd = false.
Proof.
intros fd H. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. lia.
Qed.

#[using="Type"] Lemma errno_ret_recover : forall e,
(1 <= e)%Z -> (e <= 4095)%Z ->
(two_pow_64 - bv_unsigned (errno_ret e))%Z = e.
Proof.
intros e H1 H2. rewrite (errno_ret_unsigned e H1 H2). lia.
Qed.

#[using="Type"] Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

#[using="Type"] Lemma openat_errno_range : forall e,
In e openat_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range openat_errnos e eq_refl HIn). Qed.

#[using="Type"] Lemma check_open_result_never_unmodeled : forall eff m mk,
check_open_result eff m mk <> CheckUnmodeled.
Proof.
intros [ret ws zs us cs copyins] m mk.
unfold check_open_result, check_new_fd_result.
destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
destruct cs as [|? ?];
destruct copyins as [|? ?];
try discriminate.
destruct (errno_ret_in openat_errnos ret); [discriminate|].
destruct (fd_lookup (m_fds m) ret); [discriminate|].
destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.

#[using="Type"] Lemma check_open_result_ok_iff : forall eff m (mk : word -> Model) m' evs,
check_open_result eff m mk = CheckOk m' evs <->
((exists e, In e openat_errnos /\ eff = mkEffect (errno_ret e) [] []
/\ m' = m /\ evs = [])
\/ (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m)
/\ eff = mkEffect fd [] [] /\ m' = mk fd /\ evs = [])).
Proof.
intros [ret ws zs us cs copyins] m mk m' evs.
unfold check_open_result, check_new_fd_result. split.
- intro H.
destruct ws as [|? ?]; [|discriminate].
destruct zs as [|? ?]; [|discriminate].
destruct us as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (errno_ret_in openat_errnos ret) eqn:Herr; try rewrite Herr in H.
+ inversion H; subst.
apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
left. exists e. auto.
+ destruct (fd_lookup (m_fds m) ret) eqn:Hlk; try rewrite Hlk in H;
[discriminate|].
destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; try rewrite Heq in H;
[|discriminate].
inversion H; subst.
right. exists ret. apply bv_eqb_eq in Heq. auto.
- intros [ (e & HIn & Heff & -> & ->)
| (fd & Hlk & Heq & Heff & -> & ->) ].
+ inversion Heff; subst.
rewrite (errno_ret_in_intro _ e HIn). reflexivity.
+ inversion Heff; subst.
rewrite errno_ret_in_alloc_fd by reflexivity.
rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.

Definition open_copyins (ms : machine_state) : list (word * nat) :=
[(ms_gpr ms 1,
cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].

Definition check_open_result_copyins (reads : list (word * nat))
(eff : SyscallEffect) (m : Model) (mk : word -> Model) : check_result :=
check_copyins reads eff (check_open_result (clear_copyins eff) m mk).

#[using="Type"] Lemma effect_from_copyins_and_clear : forall eff reads core,
eff_copyins eff = reads -> clear_copyins eff = core ->
eff = with_copyins reads core.
Proof.
intros [ret ws zs us cs copyins] reads core Hreads Hcore.
cbn [eff_copyins] in Hreads. subst copyins.
unfold clear_copyins, with_copyins in Hcore |- *.
cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies] in Hcore |- *.
inversion Hcore. reflexivity.
Qed.

#[using="Type"] Lemma check_open_result_copyins_never_unmodeled : forall reads eff m mk,
check_open_result_copyins reads eff m mk <> CheckUnmodeled.
Proof.
intros reads eff m mk.
unfold check_open_result_copyins, check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads);
[apply check_open_result_never_unmodeled|discriminate].
Qed.

#[using="Type"] Lemma check_open_result_copyins_ok_iff :
forall reads eff m (mk : word -> Model) m' evs,
check_open_result_copyins reads eff m mk = CheckOk m' evs <->
((exists e, In e openat_errnos /\
eff = with_copyins reads (mkEffect (errno_ret e) [] []) /\
m' = m /\ evs = [])
\/ (exists fd, fd_lookup (m_fds m) fd = None /\
fd = alloc_fd (m_fds m) /\
eff = with_copyins reads (mkEffect fd [] []) /\
m' = mk fd /\ evs = [])).
Proof.
intros reads eff m mk m' evs.
unfold check_open_result_copyins, check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
- apply access_ranges_eqb_eq in Hreads.
rewrite check_open_result_ok_iff. split.
+ intros [(e & HIn & Hcore & -> & ->)
| (fd & Hlk & Heq & Hcore & -> & ->)].
* left. exists e. repeat split; try assumption.
eapply effect_from_copyins_and_clear; eassumption.
* right. exists fd. repeat split; try assumption.
eapply effect_from_copyins_and_clear; eassumption.
+ intros [(e & HIn & Heff & -> & ->)
| (fd & Hlk & Heq & Heff & -> & ->)].
* left. exists e. repeat split; try assumption.
rewrite Heff. reflexivity.
* right. exists fd. repeat split; try assumption.
rewrite Heff. reflexivity.
- split; [discriminate|].
intros [(e & _ & Heff & _)
| (fd & _ & _ & Heff & _)].
all: rewrite Heff in Hreads; cbn [eff_copyins with_copyins] in Hreads;
pose proof (proj2 (access_ranges_eqb_eq reads reads) eq_refl) as Htrue;
congruence.
Qed.

#[using="Type"] Lemma check_copyins_after_ret_only : forall reads eff r m evs,
Prelude.check_copyins_after reads eff
(check_ret_only (clear_copyins eff) r m evs) =
check_ret_only_copyins reads eff r m evs.
Proof.
intros reads eff r m evs.
unfold Prelude.check_copyins_after, check_ret_only_copyins.
destruct (check_ret_only (clear_copyins eff) r m evs) eqn:Hresult.
- reflexivity.
- unfold check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads); reflexivity.
- exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

#[using="Type"] Lemma openat_rd_check : forall segs ms x8 model p d,
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
path_eqb p [] = false ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins (open_copyins ms) eff model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFile p (Z_to_bv 64 0))) model).
Proof.
intros segs ms x8 model p d Hno Hdirfd Hpath Hpe Hfl Hdot Hfs eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl, Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_read.
rewrite ?Hdot, ?Hfs.
unfold check_open_result_copyins, open_copyins.
destruct (check_open_result (clear_copyins eff) model
(fun fd : word =>
with_fds
(fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model))
eqn:Hresult.
- reflexivity.
- reflexivity.
- exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

#[using="Type"] Lemma openat_wr_check : forall segs ms x8 model p,
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
path_eqb p [] = false ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags ->
openat_plain_name p = true ->
fs_under (m_fs model) p = false ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins (open_copyins ms) eff model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)).
Proof.
intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl.
change (wr_create_flags =? 0)%Z with false. cbv beta iota.
rewrite Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_create, check_create_wronly.
rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
unfold check_open_result_copyins, open_copyins.
destruct (check_open_result (clear_copyins eff) model
(fun fd : word =>
with_fds
(fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)))
eqn:Hresult.
- reflexivity.
- reflexivity.
- exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

#[using="Type"] Lemma openat_wr_isdir_check : forall segs ms x8 model p,
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
path_eqb p [] = false ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags ->
openat_plain_name p = true ->
fs_under (m_fs model) p = true ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret EISDIR) model [].
Proof.
intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl.
change (wr_create_flags =? 0)%Z with false. cbv beta iota.
rewrite Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_create.
rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
apply check_copyins_after_ret_only.
Qed.

#[using="Type"] Lemma openat_toolong_check : forall segs ms x8 model,
bv_unsigned x8 = 56%Z ->
modeled_open_flags (ms_gpr ms 2) = true ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret ENAMETOOLONG) model [].
Proof.
intros segs ms x8 model Hno Hfl Hpath eff.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite Hfl. cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath.
unfold check_ret_only_copyins, open_copyins.
destruct (check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG)
model []) eqn:Hresult.
- reflexivity.
- unfold check_copyins.
destruct (access_ranges_eqb (eff_copyins eff)
[(ms_gpr ms 1,
cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]);
reflexivity.
- exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

Section OpenNodes.
Variable segs : list Segment.

#[using="Type"] Lemma tfo_open_core : forall ms model (mk : word -> Model) x8 reads
(Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
ms_svc_pending ms = Some x8 ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins reads eff model mk) ->
(forall fd, m_halted (mk fd) = None /\ m_vm_lazy (mk fd) = []) ->
(forall e, In e openat_errnos ->
to_fout segs (advance_past_svc
(apply_effect ms
(with_copyins reads (mkEffect (errno_ret e) [] []))))
model (Te e)) ->
(forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
to_fout segs (advance_past_svc
(apply_effect ms (with_copyins reads (mkEffect fd [] []))))
(mk fd) (Ts fd)) ->
(forall o, U o <->
((exists e, In e openat_errnos /\ Te e o)
\/ (exists fd, fd_lookup (m_fds model) fd = None
/\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
to_fout segs ms model U.
Proof.
intros ms model mk x8 reads Te Ts U Hsvc Hh Hlazy Hchk Hmk Herr Hok HU.
apply (tfo_sys segs ms model x8
(fun eff model' =>
if addr_is_error_b (eff_ret eff)
then Te ((two_pow_64 - bv_unsigned (eff_ret eff))%Z)
else Ts (eff_ret eff)) U); [exact Hsvc | | | | |].
-
intro Hspec.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
rewrite Hchk in Hspec.
exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hspec).
-
exists (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])), model, [].
apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. left. exists ENOMEM.
repeat split; try reflexivity. apply ENOMEM_in_openat_errnos.
-
intros eff model' evs Hspec.
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & _ & -> & -> & ->)
| (fd & _ & _ & -> & -> & ->) ].
+ repeat split; assumption.
+ destruct (Hmk fd) as [Hhalt Hlazy']. repeat split; assumption.
-
intros eff model' evs Hspec.
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & HIn & -> & -> & _)
| (fd & Hlk & Heq & -> & -> & _) ].
+ destruct (openat_errno_range e HIn) as [He1 He2].
cbn [eff_ret with_copyins].
rewrite (errno_ret_error_b e He1 He2).
rewrite (errno_ret_recover e He1 He2).
apply Herr; assumption.
+ cbn [eff_ret with_copyins].
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne.
apply Hok; assumption.
-
intro o. rewrite HU. split.
+ intros [ (e & HIn & Ht) | (fd & Hlk & Heq & Ht) ].
* destruct (openat_errno_range e HIn) as [He1 He2].
exists (with_copyins reads (mkEffect (errno_ret e) [] [])), model, [].
split.
{ apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. left. exists e. auto. }
{ cbn [eff_ret with_copyins]. rewrite (errno_ret_error_b e He1 He2).
rewrite (errno_ret_recover e He1 He2). exact Ht. }
* exists (with_copyins reads (mkEffect fd [] [])), (mk fd), [].
split.
{ apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. right. exists fd. auto. }
{ cbn [eff_ret with_copyins].
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne. exact Ht. }
+ intros (eff & model' & evs & Hspec & Ht).
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & HIn & -> & -> & _)
| (fd & Hlk & Heq & -> & -> & _) ].
* destruct (openat_errno_range e HIn) as [He1 He2].
cbn [eff_ret with_copyins] in Ht.
rewrite (errno_ret_error_b e He1 He2) in Ht.
rewrite (errno_ret_recover e He1 He2) in Ht.
left. exists e. auto.
* cbn [eff_ret with_copyins] in Ht.
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne in Ht.
right. exists fd. auto.
Qed.

#[using="Type"] Lemma open_ok_fd : forall ms model (mk : word -> Model) x8 reads fd,
(forall eff, check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins reads eff model mk) ->
fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
syscall_spec (sys_input segs ms x8) model
(Ok (with_copyins reads (mkEffect fd [] [])) (mk fd) []).
Proof.
intros ms model mk x8 reads fd Hchk Hlk Hlt.
apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. right. exists fd. auto.
Qed.

#[using="Type"] Lemma tfo_openat_toolong : forall ms model x8 U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 56%Z ->
modeled_open_flags (ms_gpr ms 2) = true ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (advance_past_svc
(apply_effect ms
(with_copyins (open_copyins ms)
(mkEffect (errno_ret ENAMETOOLONG) [] []))))
model U ->
to_fout segs ms model U.
Proof.
intros ms model x8 U Hsvc Hno Hfl Hpath Hh Hlazy Hcont.
pose proof (openat_toolong_check segs ms x8 model Hno Hfl Hpath) as Hchk.
apply (tfo_sys_det segs ms model x8
(with_copyins (open_copyins ms)
(mkEffect (errno_ret ENAMETOOLONG) [] [])) model U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

#[using="Type"] Lemma tfo_openat_enoent : forall ms model x8 p U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = None ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (advance_past_svc
(apply_effect ms
(with_copyins (open_copyins ms)
(mkEffect (errno_ret ENOENT) [] []))))
model U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p U Hsvc Hno Hdirfd Hpath Hfl Hdot Hfs Hh Hlazy Hcont.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret ENOENT) model []).
{ intro eff. rewrite (check_syscall_56 segs ms x8 eff model Hno).
unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.

destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
- apply check_copyins_after_ret_only.
- rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl, Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_read. rewrite Hdot, Hfs.
apply check_copyins_after_ret_only. }
apply (tfo_sys_det segs ms model x8
(with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] []))
model U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

#[using="Type"] Lemma tfo_read_file : forall ms model x8 p off data w U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFile p off) ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
fs_lookup (m_fs model) p = Some data ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some w ->
(bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
(0 < bv_unsigned (ms_gpr ms 2))%Z ->

access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms
(mkEffect (len_word (file_read data off (ms_gpr ms 2)))
(delivered_writes (ms_gpr ms 1)
(file_read data off (ms_gpr ms 2))) [])))
(with_fds
(fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word (file_read data off (ms_gpr ms 2)))))
model)
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p off data w U Hsvc Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok Hh Hlazy Hcont.
set (bs := file_read data off (ms_gpr ms 2)).
assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
<= bv_unsigned (ms_gpr ms 2))%Z).
{ unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (u64_range (ms_gpr ms 2)) as Hc.
rewrite length_file_read, Nat2Z.inj_min.
unfold word_to_nat.
rewrite Z.mod_small; lia. }
assert (Hchk : forall eff m' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
(eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
/\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word bs))) model
/\ evs = [])).
{ intros eff m' evs.
rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite Haok. cbn [negb]. cbv beta iota.
rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
rewrite Hfs. cbv beta iota zeta.
rewrite in_wmem_si.
rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
unfold bs.
destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
-
cbv beta iota.
rewrite check_ret_only_ok_iff. cbn [delivered_writes length].
tauto.
- destruct eff as [ret ws zs us cs copyins]. split.
+ intro H.
destruct ws as [|[a bs'] [|? ?]]; try discriminate.
destruct zs as [|? ?]; [|discriminate].
destruct us as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr)
&& bv_eqb ret (len_word (b :: bsr)))
eqn:Hb; try rewrite Hb in H; [|discriminate].
apply andb_true_iff in Hb as [Hb Hr].
apply andb_true_iff in Hb as [Ha Hbs].
apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
inversion H; subst. cbn [delivered_writes].
repeat split; congruence.
+ intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
inversion Heff; subst.
rewrite bv_eqb_refl.
rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
apply (tfo_sys_det segs ms model x8
(mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [])
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word bs))) model) U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. apply Hchk. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs.
unfold check_read in Hs.
rewrite Hfd32, Hfd in Hs. cbv beta iota in Hs.
rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
rewrite Hfs in Hs. cbv beta iota zeta in Hs.
rewrite in_wmem_si in Hs.
rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs.
cbv beta iota in Hs.
revert Hs.
destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs.
+ exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
+ discriminate.
Qed.

#[using="Type"] Lemma tfo_write_file : forall ms model x8 p off data bs U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
(bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
fs_lookup (m_fs model) p = Some data ->

negb (modeled_file_gap data off bs) = false ->

w_is0 (ms_gpr ms 2) = false ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms
(with_copyins [(ms_gpr ms 1, length bs)]
(mkEffect (ms_gpr ms 2) [] []))))
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hnz Hh Hlazy Hcont.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
{ rewrite in_mem_si. exact Hrd. }
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins [(ms_gpr ms 1, length bs)] eff (ms_gpr ms 2)
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
{ intro eff.
rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hret : len_word bs = ms_gpr ms 2).
{ unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
{ destruct (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) eqn:Hg'; [|reflexivity].
exfalso. apply andb_prop in Hg' as [Hnz' Hz].
apply Nat.eqb_eq in Hz. apply negb_true_iff in Hnz'.
rewrite Hz in Hlen. cbn in Hlen.
assert (Hzero : ms_gpr ms 2 = Z_to_bv 64 0).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (ms_gpr ms 2)). rewrite <- Hlen. reflexivity. }
unfold w_is0 in Hnz'. rewrite Hzero, bv_eqb_refl in Hnz'. discriminate. }
rewrite Hgate. cbv beta iota.
rewrite Hfs. cbv beta iota.
rewrite Hgap. cbv beta iota.
rewrite Hret.
rewrite Hnz. reflexivity. }
apply (tfo_sys_det segs ms model x8
(with_copyins [(ms_gpr ms 1, length bs)]
(mkEffect (ms_gpr ms 2) [] []))
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

#[using="Type"] Lemma tfo_write_file_zero : forall ms model x8 p off data bs U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
(bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
fs_lookup (m_fs model) p = Some data ->

negb (modeled_file_gap data off bs) = false ->
w_is0 (ms_gpr ms 2) = true ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms (mkEffect (ms_gpr ms 2) [] [])))
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hz Hok Hh Hlazy Hcont.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
{ rewrite in_mem_si. exact Hrd. }
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only eff (ms_gpr ms 2)
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
{ intro eff.
rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hret : len_word bs = ms_gpr ms 2).
{ unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
{ rewrite Hz. reflexivity. }
rewrite Hgate. cbv beta iota.
rewrite Hfs. cbv beta iota.
rewrite Hgap. cbv beta iota.
rewrite Hret.
rewrite Hz. cbv beta iota.
unfold check_access_ok_zero. rewrite Hok. reflexivity. }
apply (tfo_sys_det segs ms model x8
(mkEffect (ms_gpr ms 2) [] [])
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

#[using="Type"] Lemma tfo_close : forall ms model x8 e U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 57%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some e ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [])))
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model)
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 e U Hsvc Hno Hfd Hfd32 Hh Hlazy Hcont.
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only eff (Z_to_bv 64 0)
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) []).
{ intro eff.
rewrite (check_syscall_57 segs ms x8 eff model Hno). unfold check_close.
rewrite Hfd32, Hfd. reflexivity. }
apply (tfo_sys_det segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

#[using="Type"] Lemma record_gpr : forall regs fr pc sv rv fc mem rom k,
ms_gpr {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} k
= reg_get regs (Z_to_bv 5 (10 + Z.of_nat k)).
Proof. reflexivity. Qed.

#[using="Type"] Lemma tfo_exit_rec : forall regs pc mem rom model code fsv,
bv_unsigned (getr regs 17) = 93%Z ->
reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
m_fs model = fsv ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}
model (fun o => o = (code, fsv)).
Proof.
intros regs pc mem rom model code fsv H17 H10 Hc Hfs.
subst fsv.
eapply (tfo_exit segs _ model (getr regs 17)).
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
- intro o. rewrite record_gpr, arg_reg_0.
rewrite H10, (land_255_small code Hc). tauto.
Qed.

#[using="Type"] Lemma tfo_read_rec : forall regs pc mem rom model fdv p off data buf cnt U,
bv_unsigned (getr regs 17) = 63%Z ->
reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
fd_lookup (m_fds model) fdv = Some (FdFile p off) ->
fd32 fdv = fdv ->
fs_lookup (m_fs model) p = Some data ->
wseg_ok segs buf (word_to_nat cnt) = true ->
(bv_unsigned cnt <= rw_bytes_max)%Z ->
(0 < bv_unsigned cnt)%Z ->

access_okb buf (bv_unsigned cnt) = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
(write_to_mem mem buf (file_read data off cnt)) rom)
(with_fds (fd_insert (m_fds model) fdv
(FdFile p (off + len_word (file_read data off cnt)))) model)
U ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |} model U.
Proof.
intros regs pc mem rom model fdv p off data buf cnt U
H17 H10 H11 H12 Hfd Hfd32 Hfs Hwseg Hcnt Hpos Haok Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
assert (Hg1 : ms_gpr ms 1 = buf)
by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
assert (Hg2 : ms_gpr ms 2 = cnt)
by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
apply (tfo_read_file ms model (getr regs 17) p off data w U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- rewrite Hg0. exact Hfd.
- rewrite Hg0. exact Hfd32.
- exact Hfs.
- rewrite Hg1, Hg2. exact Hw.
- rewrite Hg2. exact Hcnt.
- rewrite Hg2. exact Hpos.
- rewrite Hg1, Hg2. exact Haok.
- exact Hh.
- exact Hlazy.
- rewrite Hg0, Hg1, Hg2. unfold ms.
rewrite adv_apply_delivered. exact Hcont.
Qed.

#[using="Type"] Lemma tfo_write_rec : forall regs pc mem model fdv p off data bs buf cnt U,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
fd_lookup (m_fds model) fdv = Some (FdFileW p off) ->
fd32 fdv = fdv ->
rdn segs mem buf (word_to_nat cnt) = Some bs ->
(bv_unsigned cnt <= rw_bytes_max)%Z ->
fs_lookup (m_fs model) p = Some data ->

negb (modeled_file_gap data off bs) = false ->

(access_okb buf (bv_unsigned cnt) = true \/ (0 < bv_unsigned cnt)%Z) ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs))
(with_fds (fd_insert (m_fds model) fdv (FdFileW p (off + cnt)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model fdv p off data bs buf cnt U
H17 H10 H11 H12 Hfd Hfd32 Hrd Hcnt Hfs Hgap Hok Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
assert (Hg1 : ms_gpr ms 1 = buf)
by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
assert (Hg2 : ms_gpr ms 2 = cnt)
by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
destruct (w_is0 cnt) eqn:Hz.
-
apply (tfo_write_file_zero ms model (getr regs 17) p off data bs U).
+ unfold ms. cbn [ms_svc_pending]. reflexivity.
+ exact H17.
+ rewrite Hg0. exact Hfd.
+ rewrite Hg0. exact Hfd32.
+ rewrite Hg1, Hg2.
rewrite read_bytes_map_read_byte.
rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
exact Hrd.
+ rewrite Hg2. exact Hcnt.
+ exact Hfs.
+ exact Hgap.
+ rewrite Hg2. exact Hz.
+ destruct Hok as [Hfl | Hp].
* rewrite Hg1, Hg2. exact Hfl.
*
rewrite (w_is0_pos cnt Hp) in Hz. discriminate.
+ exact Hh.
+ exact Hlazy.
+ rewrite Hg0, Hg2. unfold ms.
rewrite adv_eff_ret. exact Hcont.
-
apply (tfo_write_file ms model (getr regs 17) p off data bs U).
+ unfold ms. cbn [ms_svc_pending]. reflexivity.
+ exact H17.
+ rewrite Hg0. exact Hfd.
+ rewrite Hg0. exact Hfd32.
+ rewrite Hg1, Hg2.
rewrite read_bytes_map_read_byte.
rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
exact Hrd.
+ rewrite Hg2. exact Hcnt.
+ exact Hfs.
+ exact Hgap.
+ rewrite Hg2. exact Hz.
+ exact Hh.
+ exact Hlazy.
+ rewrite Hg0, Hg2. unfold ms.
rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

#[using="Type"] Lemma tfo_close_rec : forall regs pc mem rom model fdv e U,
bv_unsigned (getr regs 17) = 57%Z ->
reg_get regs 10 = fdv ->
fd_lookup (m_fds model) fdv = Some e ->
fd32 fdv = fdv ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fds (fd_remove (m_fds model) fdv) model) U ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |} model U.
Proof.
intros regs pc mem rom model fdv e U H17 H10 Hfd Hfd32 Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
apply (tfo_close ms model (getr regs 17) e U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- rewrite Hg0. exact Hfd.
- rewrite Hg0. exact Hfd32.
- exact Hh.
- exact Hlazy.
- rewrite Hg0. unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.

#[using="Type"] Lemma tfo_open_enoent_rec : forall regs pc mem model p U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = None ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
mem (seg_rom segs))
model U ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p U H17 H10 H12 Hpath Hdot Hfs Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_openat_enoent ms model (getr regs 17) p U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
- exact Hdot.
- exact Hfs.
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

#[using="Type"] Lemma tfo_open_rd_rec : forall regs pc mem model p d
(Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
path_eqb p [] = false ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall e, In e openat_errnos ->
to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
mem (seg_rom segs))
model (Te e)) ->
(forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd
(FdFile p (Z_to_bv 64 0))) model) (Ts fd)) ->
(forall o, U o <->
((exists e, In e openat_errnos /\ Te e o)
\/ (exists fd, fd_lookup (m_fds model) fd = None
/\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p d Te Ts U
H17 H10 H12 Hpath Hpe Hdot Hfs Hh Hlazy Herr Hok HU.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_open_core ms model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFile p (Z_to_bv 64 0))) model)
(getr regs 17) (open_copyins ms) Te Ts U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact Hh.
- exact Hlazy.
- intro eff. apply (openat_rd_check segs ms (getr regs 17) model p d).
+ exact H17.
+ unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
+ unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
+ exact Hpe.
+ unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
+ exact Hdot.
+ exact Hfs.
- intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
- intros e HIn.
unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
- intros fd Hlk Hlt.
unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
- exact HU.
Qed.

#[using="Type"] Lemma tfo_open_wr_rec : forall regs pc mem model p
(Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
path_eqb p [] = false ->
openat_plain_name p = true ->
fs_under (m_fs model) p = false ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall e, In e openat_errnos ->
to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
mem (seg_rom segs))
model (Te e)) ->
(forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)) (Ts fd)) ->
(forall o, U o <->
((exists e, In e openat_errnos /\ Te e o)
\/ (exists fd, fd_lookup (m_fds model) fd = None
/\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p Te Ts U
H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Herr Hok HU.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_open_core ms model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model))
(getr regs 17) (open_copyins ms) Te Ts U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact Hh.
- exact Hlazy.
- intro eff. apply (openat_wr_check segs ms (getr regs 17) model p).
+ exact H17.
+ unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
+ unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
+ exact Hpe.
+ unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
+ exact Hdot.
+ exact Hun.
- intro fd. split.
+ rewrite with_fds_halted, with_fs_halted. exact Hh.
+ exact Hlazy.
- intros e HIn.
unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
- intros fd Hlk Hlt.
unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
- exact HU.
Qed.

#[using="Type"] Lemma tfo_open_wr_isdir_rec : forall regs pc mem model p U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
path_eqb p [] = false ->
openat_plain_name p = true ->
fs_under (m_fs model) p = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4)
mem (seg_rom segs))
model U ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p U H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}).
assert (Hchk : forall eff,
check_syscall (sys_input segs ms (getr regs 17)) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret EISDIR) model []).
{ intro eff. apply (openat_wr_isdir_check segs ms (getr regs 17) model p).
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- exact Hpe.
- unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
- exact Hdot.
- exact Hun. }
apply (tfo_sys_det segs ms model (getr regs 17)
(with_copyins (open_copyins ms)
(mkEffect (errno_ret EISDIR) [] [])) model U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

#[using="Type"] Lemma tfo_open_toolong_rec : forall regs pc mem model U,
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (reg_get regs 12) = true ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrTooLong ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4)
mem (seg_rom segs))
model U ->
to_fout segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model U H17 Hfl Hpath Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_openat_toolong ms model (getr regs 17) U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

End OpenNodes.

#[using="Type"] Lemma fout_omni_run : forall segs pc ph sp brk0 mb rnd lim inp U,
to_fout segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (fout_post U).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto.
cbn [omni_run]. unfold init_config.
exact (to_fout_exec segs _ _ U Hto eq_refl eq_refl).
Qed.

#[using="Type"] Lemma fout_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
to_fout segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
unfold init_config.
set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
by reflexivity.
assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [])
by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (to_fout_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
as (o & Ho & Hp').
exists o. split; [exact Ho | eapply is_prefix_trans; eauto].
- intros (o & Ho & Hp).
destruct (to_fout_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
exists (fout_trace o), c. split; assumption.
Qed.

#[using="Type"] Lemma fout_no_error_run : forall segs pc ph sp brk0 mb rnd lim inp U,
to_fout segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
eapply exec_conseq; [exact (fout_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

#[using="Type"] Lemma fout_omni_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
to_fout source_segs
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U ->
to_fout target_segs
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
Hsource Htarget.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (fout_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
intros tr o (out & _ & _ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.

#[using="Type"] Lemma fout_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp,
to_fout source_segs
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U ->
to_fout target_segs
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved target_segs) abrk amb asp alim inp) U ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp
Hsource Htarget.
split.
{ apply no_error_run_modeled.
apply (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
right. split.
- intro tr. cbn.
rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
reflexivity.
- cbn. apply (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.

#[using="Type"] Lemma spec_err_escape_equiv :
forall segs pc ph sp brk0 mb rnd lim inp (target : behavior),
all_traces_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target Hall.
left. exact Hall.
Qed.
End FPGEN1.
