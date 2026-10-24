(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK1c YK1i YK1d.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section d.
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
End d.
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
Section e.
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
End e.
Lemma fd1chan_with_stdin : forall s m, fd1chan m -> fd1chan (with_stdin s m).
Proof. intros s m H. exact H. Qed.
Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.
Section g.
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
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.
Lemma lh_next_to_rd : forall a ms, lh_next a ms -> to_rd a ms.
Proof.
intros a ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.
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
Lemma read0_check_eof_cnt : forall ms x8 model w,
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
Proof. apply (YK1d.read0_check_eof cnt Hcnt). Qed.
Lemma read0_ok_eof_cnt : forall ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
m_stdin model = IEof ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof. apply (YK1d.read0_ok_eof cnt Hcnt). Qed.
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
Proof. apply (YK1d.read0_check_bytes cnt Hcnt). Qed.
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
Proof. apply (YK1d.read0_ok_bytes cnt Hcnt). Qed.
Lemma read0_ok_inv_cnt : forall ms x8 model buf w eff model' evs,
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
Proof. apply (YK1d.read0_ok_inv cnt Hcnt). Qed.
Lemma read0_no_err_cnt : forall ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. apply (YK1d.read0_no_unmodeled cnt Hcnt). Qed.
Lemma sstep_read_inv_cnt : forall ms model buf x8 w evs st,
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
Proof. apply (YK1d.sstep_read_inv cnt Hcnt). Qed.
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
-
intros t t' Ht Hp.
apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd).
eapply obs_trace_prefix_closed; [| exact Hp].
apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Ht.
- intros tr Hobs. apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Hobs.
Qed.
End g.
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
