(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Fs.ReadWrite.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l Qg4E QqRD QybZ Qqcs Qmth QlUm QKJt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import QU8l Qg4E QqRD QybZ Qqcs.Mq1 Qmth QlUm.Mq0 QlUm QKJt.Mq0.

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

End Proc.

Definition block_ok (cnt : word) (bs : list byte) : Prop :=
(1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.

Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
flat_map (fun bs => map (ReadEv rch) bs) blocks.

Definition reads (blocks : list (list byte)) : list event :=
reads_ch (Z_to_bv 64 0) blocks.

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

End Traces.

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

Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

Definition dinv (c : config) : Prop :=
(M_loop (cfg_model c) /\ exists a, to_rd a (cfg_ms c))
\/ (fd1chan (cfg_model c) /\ m_halted (cfg_model c) = None /\
m_vm_lazy (cfg_model c) = [] /\
exists rest, buf_modeled rest /\
to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) rest
(to_exit segs (Z_to_bv 64 0)))
\/ on_path segs (Z_to_bv 64 0) c
\/ on_path segs ec c.

End Drain.

End Mq0.

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU8l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg4E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqRD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqRD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmth. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKJt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKJt.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKJt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKJt.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
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

Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
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

Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
zmem m a n.

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

Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.

Lemma munmap_model_no_lazy : forall addr n m,
m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
vm_forget_range, with_vm_backing, with_vmmaps.
cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.

Lemma mmap_model_lazy : forall a n m,
m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Definition mmap_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.

Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
(bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
ms_gpr ms 1 <> Z_to_bv 64 0 /\
(bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) = true.

Definition munmap_eff (ms : machine_state) : SyscallEffect :=
mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
&& Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
then None else m x.

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

Lemma msteps_twm : forall ms ms' model bufs code,
msteps segs ms ms' -> twm ms' model bufs code -> twm ms model bufs code.
Proof.
intros ms ms' model bufs code H; induction H; [auto|].
intro Hw. eapply twm_step; eauto.
Qed.

Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.
Proof.
intros ms ms' model rest bufs code H; induction H; [auto|].
intro Hw. eapply twmt_step; eauto.
Qed.

Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.

Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
(fs : Fs.Fs) : post :=
fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
/\ exits_with code tr o.

Inductive tmw : machine_state -> Model -> list (list byte) -> word
-> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
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

Lemma msteps_tmw : forall ms ms' model bf cf bs cs,
msteps segs ms ms' -> tmw ms' model bf cf bs cs -> tmw ms model bf cf bs cs.
Proof.
intros ms ms' model bf cf bs cs H; induction H; [auto|].
intro Hw. eapply tmw_step; eauto.
Qed.

Definition tmw_post (bf : list (list byte)) (cf : word) (bs : list (list byte)) (cs : word)
(fs : Fs.Fs) : post :=
fun tr o => (tr = wevents bf ++ [ExitEv cf fs] /\ exits_with cf tr o)
\/ (tr = wevents bs ++ [ExitEv cs fs] /\ exits_with cs tr o).

Definition two_traces (bf : list (list byte)) (cf : word)
(bs : list (list byte)) (cs : word)
(fs : Fs.Fs) (tr : list event) : Prop :=
is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
is_prefix tr (wevents bs ++ [ExitEv cs fs]).

End WithSegs.

End WithFP1.
