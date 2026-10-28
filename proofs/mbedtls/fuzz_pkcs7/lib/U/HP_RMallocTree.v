(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocTree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Export HP_RMallocRep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMallocTree () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RAUXV_CELL"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64s"; "RP_2.rauxv_list"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rp_secret"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RP_2.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.bptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.unit"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.strip"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "RocqVerifyHarness.AgentSubmission.Heap.MallocCtrl.hdr_ok"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.pans_mem"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.pupd_mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cptr"; "rimplT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.free"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.tt"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.set_m"; "RocqVerifyHarness.AgentSubmission.Heap.Monad.implM"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.raw_free"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RP_2.rpres_except"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RP_2.rfresh_addr"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RP_2.ralloc_fp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_fa"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_so"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.am_rel"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.M"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.brk_link_ps"; "Stdlib.ZArith.BinInt.Z.sub"; "RP_2.RAM_STACK"; "RP_2.ram_post"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_meta"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_meta_entry"].


(* [comment removed for export] *)


Section RP_1. Context {hRP : run_params}.
Definition rimplT {R} (o : mem) (t : Malloc.M R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM rsegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

#[using="Type"] Lemma rimplT_ret {R} o (r : R) s Q ms : evt rsegs (Q r s) ms -> rimplT o (SRet r) s Q ms.
Proof. intros H. unfold rimplT. rewrite mrun_ret. cbn [membed]. apply implM_ret. exact H. Qed.

#[using="Type"] Lemma rimplT_peek {R} o p c h (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (pans_mem o p c h)) s Q ms -> rimplT o (SVis (EPeek p c h) k) s Q ms.
Proof. intros H. unfold rimplT. rewrite mrun_peek. exact H. Qed.

#[using="Type"] Lemma rimplT_undef {R} o w (k : Z -> Malloc.M R) s Q ms : rimplT o (SVis (EUndef w) k) s Q ms.
Proof.
  unfold rimplT. rewrite mrun_vis by exact I. cbn [membed ev_step].
  eapply (implM_bind rsegs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplT_vis {R} o e (k : Z -> Malloc.M R) s Q1 Q ms :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  implM rsegs (ev_step e) s Q1 ms ->
  (forall z s' ms', Q1 z s' ms' -> rimplT o (k z) s' Q ms') ->
  rimplT o (SVis e k) s Q ms.
Proof.
  intros He H K. unfold rimplT. rewrite mrun_vis by (destruct e; auto). cbn [membed].
  eapply implM_bind; [exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.

#[using="Type"] Lemma rimplT_mono {R} o (t : Malloc.M R) s Q Q' ms :
  rimplT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> rimplT o t s Q' ms.
Proof. intros H HQ. unfold rimplT in *. eapply implM_mono; [exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.

#[using="Type"] Lemma rimplT_evt {R} o (t : Malloc.M R) s Q P ms :
  evt rsegs P ms -> (forall ms', P ms' -> rimplT o t s Q ms') -> rimplT o t s Q ms.
Proof. intros H K. unfold rimplT in *. eapply implM_evt; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
  impl rsegs (at_node rsegs) (Vis n k) Q ms = evt rsegs (fun ms1 => at_node rsegs n ms1 /\ forall rsp, impl rsegs (at_node rsegs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. reflexivity. Qed.

#[using="Type"] Lemma rimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
  impl rsegs (at_node rsegs) (ITree.bind _ t f1) Q1 ms ->
  (forall r ms', impl rsegs (at_node rsegs) (f1 r) Q1 ms' -> impl rsegs (at_node rsegs) (f2 r) Q2 ms') ->
  impl rsegs (at_node rsegs) (ITree.bind _ t f2) Q2 ms.
Proof.
  revert ms. induction t as [r|n k IH]; intros ms H K; cbn [ITree.bind] in *.
  - apply K. exact H.
  - rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [exact H|].
    intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmembed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
  implM rsegs (membed t1) s Q1 ms ->
  (forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1. eapply HQ; eauto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1| exact HQ].
Qed.

#[using="Type"] Lemma rimplT_strel {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : Malloc.M R1) (t2 : Malloc.M R2) s Q1 Q2 ms :
  strel RR (mrun o t1) t2 ->
  rimplT o t1 s Q1 ms ->
  (forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof.
  intros Hs H HQ. unfold rimplT in H. eapply (rmembed_strel _ _ _ Hs); [exact H|]. intros [o1 r1] r2 s' ms'; cbn; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplM_membed_steq {R} (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> implM rsegs (membed t1) s Q ms -> implM rsegs (membed t2) s Q ms.
Proof.
  intros Hs H. apply strel_eq_steq in Hs. eapply (rmembed_strel eq t1 t2 Hs); [exact H|]. intros; subst; auto.
Qed.


#[using="Type"] Lemma rimplM_membed_sbind {R S} (T : Malloc.M R) (F : R -> Malloc.M S) s Q1 Q ms :
  implM rsegs (membed T) s Q1 ms ->
  (forall x s' ms', Q1 x s' ms' -> implM rsegs (membed (F x)) s' Q ms') ->
  implM rsegs (membed (sbind T F)) s Q ms.
Proof.
  revert s ms. induction T as [x|e k IH]; intros s ms H K.
  - cbn [sbind membed] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [exact H|]. intros ms' H1. exact (K x s ms' H1).
  - cbn [sbind membed] in *. unfold implM, mbind, ebind in *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplT_bind {R S} o (t : Malloc.M R) (f : R -> Malloc.M S) s Q1 Q ms :
  rimplT o t s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> rimplT o (f r) s' Q ms') ->
  rimplT o (sbind t f) s Q ms.
Proof.
  unfold rimplT, mrun, prun. revert s ms. induction t as [r|e k IH]; intros s ms H K.
  - cbn [sbind]. cbn [eruns membed] in H. unfold implM, mret in H. cbn in H.
    eapply implM_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
  - cbn [sbind eruns]. cbn [eruns] in H. unfold pupd_mem in *. destruct (psel pans_mem o e) as [a|].
    + eapply IH; [exact H|exact K].
    + cbn [membed]. cbn [membed] in H. unfold implM, mbind, ebind in H |- *.
      eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
      * exact H1.
      * eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplT_from_evt {R} o (t : Malloc.M R) s Q ms :
  evt rsegs (fun ms' => rimplT o t s Q ms') ms -> rimplT o t s Q ms.
Proof. intros H. eapply rimplT_evt; [exact H|]. intros ms' H'; exact H'. Qed.
End RP_1.
Ltac riprefixT := apply rimplT_from_evt.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_2. Context {hRP : run_params}.
#[using="Type"] Lemma rimplM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
      (s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
  (forall a ms', P a ms' -> evt rsegs (Q (f a) s) ms') ->
  implM rsegs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof.
  intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
  cbn [ITree.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec rsp) as [a|]; cbn in *.
  - eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
  - exact Hk.
Qed.


#[using="Type"] Lemma rimplT_mmap_rw {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
  rimplT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' dd_H; ddestruct dd_H as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_mmap_none {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
  rimplT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' dd_H; ddestruct dd_H as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_mmap_fixed {R} o addr len (k : Z -> Malloc.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (fixed_val addr a)) s Q ms') ->
  rimplT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' dd_H; ddestruct dd_H as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_munmap {R} o addr len (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
  rimplT o (SVis (EMunmap addr len) k) s Q ms.
Proof.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' dd_H; ddestruct dd_H as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplT_mprotect {R} o addr len prot (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
  rimplT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' dd_H; ddestruct dd_H as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplT_brk0 {R} o (k : Z -> Malloc.M R) s (P : Z -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
  (forall r ms', P r ms' -> rimplT o (k r) (set_brk_ps r s) Q ms') ->
  rimplT o (SVis (EBrk 0) k) s Q ms.
Proof.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
  - cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
    cbn [ITree.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk0 rsp) as [a|]; cbn in *; [|exact Hk].
    eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
  - intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplT_brk {R} o req (k : Z -> Malloc.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
  req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
  (forall a ms', P a ms' ->
     rimplT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
             (match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
  rimplT o (SVis (EBrk req) k) s Q ms.
Proof.
  intros Hr H K.
  eapply (rimplT_vis o _ k s (fun z s' ms' => exists a, P a ms' /\
            z = match a with BrkGrown => req | BrkSame => ps_brk s end /\
            s' = match a with BrkGrown => set_brk_ps req s | BrkSame => s end)); [exact I| |].
  - cbn [ev_step]. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
    unfold implM, mbind, msys, mget, mupd, mret, ebind, enode in *.
    cbn [ITree.bind fst snd]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|exact Hk].
    destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
  - (intros z s' ms' dd_H; ddestruct dd_H as (a & HP & -> & ->)). exact (K a ms' HP).
Qed.


#[using="Type"] Lemma rimplT_reach {R} o (t : Malloc.M R) : forall s Q ms,
  rimplT o t s Q ms -> rimplT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof.
  induction t as [r|e k IH]; intros s Q ms H.
  - unfold rimplT, implM in *. rewrite mrun_ret in *. cbn [membed] in *. unfold mret in *. cbn in *.
    eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| apply leaf_of_ret].
  - destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ apply rimplT_peek. eapply rimplT_mono; [apply IH; unfold rimplT in H |- *; rewrite mrun_peek in H; exact H|].
        cbn. intros r s' ms' [HQ HL]. split; [exact HQ|]. apply leaf_of_peek. exact HL. }
    5:{ apply rimplT_undef. }
    all: unfold rimplT in H |- *; rewrite mrun_vis in H |- * by exact I; cbn [membed] in H |- *;
         unfold implM, mbind, ebind in H |- *;
         eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         pose proof (IH z s' Q ms') as IH1; unfold rimplT, implM in IH1;
         eapply impl_epost_mono; [apply IH1; exact H1|];
         intros [[o1 r] s2] ms2; cbn; intros [HQ HL]; split; [exact HQ| apply (leaf_of_vis o _ k z); [exact I| exact HL]].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rauxv_list (x3 x4 x5 hw x6 x11 x12 x23 rnd : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 16; hw; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Definition rauxv_ok (m : mem) (B : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "(0.$1.Lav,$1.(0.$1.Lx3,$1.(0.$1.Lx4,$1.(0.$1.Lx5,$1.(0.$1.Lhw,$1.(0.$1.Lx6,$1.(0.$1.Lx11,$1.(0.$1.Lx12,$1.(0.$1.Lx23,$1.(0.$1.Lrnd,$1.(2.(3.$4.O2.$5.(6.$7.(8.(9.R:.))(:.$7.)))(2.(;.$4.O2.R:.(<.(=.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))(2.(;.$4.O2.(>.R1.+8.)(?.(9.(10.VhRP,))))(2.(11.(12.VhRP,)O1.)(2.(11.O1.R:.)(2.(11.(>.R:.+:0.)(13.+2.+40.))(2.(11.O1.(>.R1.+8.))(2.(11.(>.R1.+10.)(13.+2.+40.))(2.(2.(11.=R9.)(14.R9.(13.+2.+40.)))(2.(2.(11.=R8.)(14.R8.(13.+2.+40.)))(2.(2.(11.=R7.)(14.R7.(13.+2.+40.)))(2.(2.(11.=R6.)(14.R6.(13.+2.+40.)))(2.(2.(11.=R5.)(14.R5.(13.+2.+40.)))(2.(2.(11.=R4.)(14.R4.(13.+2.+40.)))(2.(2.(11.=R3.)(14.R3.(13.+2.+40.)))(2.(2.(11.=R2.)(14.R2.(13.+2.+40.)))(2.(11.=R1.)(14.R1.(13.+2.+40.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rauxv_ok_weaken : forall m B B', rauxv_ok m B -> rceil <= B' <= B -> rauxv_ok m B'.
Proof.
  (intros m B B' dd_H; ddestruct dd_H as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & H); intros HB).
  dexists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. repeat (split; [tauto|]). lia.
Qed.

#[using="Type"] Lemma rauxv_ok_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "Pm,$15.Pm',P,(16.&40.)(17.(16.&8.))PB,$1.PW,(18.$19.)P,(1:.R4.R2.)P,(1;.R2.R5.R4.)P,(1<.$4.R6.R5.)P,(1=.(1>.$1.$1.)Liv,(1>.$1.$1.)(2.(11.(1?.$1.$1.R1.)R6.)(20.(11.(1?.$1.$1.R1.)$5.)(11.(>.$5.+8.)(21.$1.$1.R1.))))R4.)(1:.R7.R6.)")
(* [comment removed for export] *).
Proof.
  (intros m m' B W dd_H; ddestruct dd_H as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H); intros MU WM FW).
  dexists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rw_cells_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [_ ?]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rraw_free_bridge : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "Pst,$22.Ps,$23.Pp,$24.Ppf,$25.Po,$15.PQ1,P,$22.P,$23.P,$26.SpPQ,Px,$27.Px0,$23.Px1,$26.SpPms,$26.P,(28.$22.(29.R8.)(2:.R7.))P,(2;.$15.$2<.$2=.R9.R6.(21.$2>.$1.R7.))P,(2?.$22.R6.(30.R:.(31.$25.R7.))R9.R5.R3.)P,Pst',$22.Ps',$23.Pms',$26.P,A3.R9.R3.R2.R1.A3.R9.$32.(33.(29.R4.)R3.)R2.(34.$23.$4.$27.(35.R:.)R;.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros st s p pf o Q1 Q ms Hst Hh H HQ. unfold raw_free.
  eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  (intros s0 s1 ms1 dd_H; ddestruct dd_H as (-> & -> & ->)). cbv beta.
  eapply (implM_bind rsegs _ _ _ (fun cs s' ms' => exists st', Q1 st' s' ms' /\ strip st' = cs)).
  { rewrite <- Hst. eapply (rimplT_strel FREL o (free st (Some pf)) (cfree (strip st) (Some (fst p))) s Q1).
    - unfold mrun. apply free_control. exact Hh.
    - exact H.
    - intros o1 st' cs s' ms' HR H1. exists st'. split; [exact H1|]. unfold FREL in HR. exact HR. }
  (intros cs s' ms' dd_H; ddestruct dd_H as (st' & H1 & <-)). cbv beta.
  apply implM_upd. apply evt_done. eapply HQ. exact H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rpres_except (C : Z -> Prop) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "Pa,$1.P,(2.(11.=R1.)(14.R1.(13.+2.+40.)))P,(36.A1.O3.R2.)(2.(28.(17.(16.&8.))A1.O1.(37.R3.)A1.O2.(37.R3.))P,(36.(28.(17.(16.&8.))(38.$4.O2.(37.R3.))(39.(16.&8.))))(36.(28.(17.(16.&8.))(38.$4.O1.(37.R4.))(39.(16.&8.)))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rpres_except_refl C m : rpres_except C m m.
Proof. intros a _ _; auto. Qed.
#[using="Type"] Lemma rpres_except_trans C m1 m2 m3 : rpres_except C m1 m2 -> rpres_except C m2 m3 -> rpres_except C m1 m3.
Proof. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
#[using="Type"] Lemma rpres_except_mono (C C' : Z -> Prop) m m' : rpres_except C m m' -> (forall a, C a -> C' a) -> rpres_except C' m m'.
Proof. intros H HC a Ha Hc. apply H; [exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rpres_except_of_munch C W m m' : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "P,(1;.O3.O2.O1.)P,(1<.$4.O2.O1.)P,Pa,$1.P,(2.(11.=R1.)(14.R1.(13.+2.+40.)))P,(36.A1.O4.R2.)(3:.O3.R3.)(3;.O4.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros MU WM HW a Ha Hc. split.
  - apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
  - apply WM.
Qed.

#[using="Type"] Lemma rpres_except_bytes_at C m m' A bs : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "P,(3;.O5.O4.O3.)P,(;.$4.O4.O2.O1.)P,Pa,$1.P,(2.(11.O2.R1.)(14.R1.(>.O2.(3<.(3=.(16.&8.)O1.)))))(36.A1.O5.R2.)(;.$4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  (intros HP dd_H; ddestruct dd_H as (H0 & H1 & HB); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma rpres_except_wr_at C m m' A n : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "P,(3;.O5.O4.O3.)P,(3>.$4.O4.O2.O1.)P,Pa,$1.P,(2.(11.O2.R1.)(14.R1.(>.O2.O1.)))(36.A1.O5.R2.)(3>.$4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  (intros HP dd_H; ddestruct dd_H as (H0 & H1 & HW); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

#[using="Type"] Lemma rpres_except_rw_cells C m m' A cs : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "P,(3;.O5.O4.O3.)P,(3.$4.O4.O2.O1.)P,Pa,$1.P,(2.(11.O2.R1.)(14.R1.(>.O2.(3<.(3?.O1.)))))(36.A1.O5.R2.)(3.$4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rpres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rpres_except_wr_at; eauto.
Qed.

#[using="Type"] Lemma rpres_except_stk C m m' lo hi : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "P,(3;.O5.O4.O3.)P,(40.$4.O4.O2.O1.)P,Pa,$1.P,(2.(11.O2.R1.)(14.R1.O1.))(36.A1.O5.R2.)(40.$4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  (intros HP dd_H; ddestruct dd_H as (H0 & H1 & HW); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Definition ralloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "(20.(2.(11.O3.O1.)(14.O1.O2.))(20.(2.(11.(>.(41.&40.(42.&40.+5=0<8.))-:4.)O1.)(14.O1.(>.(>.(41.&40.(42.&40.+5=0<8.))-:4.)+4.)))(20.(2.(11.$43.O1.)(14.O1.(>.$43.+3:0.)))(0.$44.Lrid,$44.(0.$45.Lr,$45.(2.(28.(17.$45.)(46.$44.$45.(47.$44.$48.$49.$45.)(4:.$44.$48.$49.$45.)R2.(4;.O4.))(31.$45.R1.))(2.A1.O5.(4<.R1.)(2.(11.(4=.R1.)O1.)(14.O1.(>.(4>.R1.)(4?.(50.R1.))))))))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)

Definition RAM_STACK : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rfresh_addr (st : mstate) (a : Z) : Prop :=
  a < rceil /\ ranges_free (live_ranges st) a 1 = true.

#[using="Type"] Lemma rfresh_addr_anti st st' a : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "P,(28.(18.(1>.$1.$1.))(51.O2.)(51.O3.))P,Prid,$44.Pr,$45.P,(28.(17.$45.)(46.$44.$45.(47.$44.$48.$49.$45.)(4:.$44.$48.$49.$45.)R2.(4;.O3.))(31.$45.R1.))(0.$45.Lr',$45.(2.(28.(17.$45.)(46.$44.$45.(47.$44.$48.$49.$45.)(4:.$44.$48.$49.$45.)R4.(4;.O2.))(31.$45.R1.))(2.(28.$52.(4<.R1.)(4<.R3.))(2.(28.$1.(4>.R1.)(4>.R3.))(11.(50.R3.)(50.R1.))))))P,(53.O2.O1.)(53.O3.O1.)")
(* [comment removed for export] *).
Proof.
  intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. ddestruct HI as ([rid r] & E & HI). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    ddestruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma rfresh_image st a : rfresh_addr st a -> s_reserved st = ref_reserved -> a < 0x10000 \/ 0x7e000 <= a.
Proof.
  intros [_ FR] RS. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). lia.
Qed.

Definition ram_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (s : PState) (lo : Z) (m : mem)
    (st1 : mstate) (mo : optr) (s' : PState) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "Lms',$26.(0.(16.&40.)Lt0,(16.&40.)(0.(16.&40.)Lt1,(16.&40.)(0.(16.&40.)Lt2,(16.&40.)(0.(16.&40.)La1,(16.&40.)(0.(16.&40.)La2,(16.&40.)(0.(16.&40.)La3,(16.&40.)(0.(16.&40.)La4,(16.&40.)(0.(16.&40.)La5,(16.&40.)(0.(16.&40.)La6,(16.&40.)(0.(16.&40.)La7,(16.&40.)(0.(16.&40.)Lt3,(16.&40.)(0.(16.&40.)Lt4,(16.&40.)(0.(16.&40.)Lt5,(16.&40.)(0.(16.&40.)Lt6,(16.&40.)(0.P,(16.&40.)(17.(16.&8.))Lm',P,(16.&40.)(17.(16.&8.))(0.(16.&40.)Lerrv',(16.&40.)(2.(28.$26.R11.(54.(55.O19.O18.O17.O16.R10.R?.R>.O15.O14.(56.O3.O2.)R=.R<.R;.R:.R9.R8.R7.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R6.R5.R4.R3.)O9.(57.O19.)O8.(39.(16.&40.))R2.(58.$4.)))(2.(59.$4.R2.)(2.(40.$4.R2.O5.(41.&40.O18.))(2.(3.$4.R2.(>.(41.&40.O16.)-:4.)(6.$7.(5:.R1.)(:.$7.)))(2.(1:.R2.(41.&40.O18.))(2.(3;.La,$1.(20.(5;.Lk,$52.(36.(28.$52.R1.$5<.))O3.O5.(41.&40.O18.)R1.)(53.O7.R1.))O4.R2.)(2.(5=.VhRP,O3.R2.)(2.(5>.O3.)(2.(28.$22.(2:.O1.)(2:.O6.))(2.(28.(1>.$1.$1.)(5?.O1.)(5?.O6.))(2.(28.$27.(60.O1.)(60.O6.))(61.O7.O3.O2.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ralloc_meta_stmt (am_pre : mstate -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocTree ()) "PR,StPk,P,$22.P,$62.(63.R3.)Pbail,(63.R2.)Po,$15.Ps,$23.PQ,P,R5.P,$23.P,$26.SpPra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(64.&5.(16.&40.))Pfc,(16.&20.)Pm,$15.Pst,$22.Plo,$1.Perrv,(16.&40.)P,A1.O1.R3.P,(5=.VhRP,R4.R5.)P,(5>.R5.)P,(65.R6.R2:.)P,(1:.R8.(41.&40.R28.))P,(40.$4.R9.R7.(41.&40.R29.))P,(11.(12.VhRP,)R8.)P,(11.R9.(66.(41.&40.R2;.)$67.))P,(3.$4.R<.(>.(41.&40.R2:.)-:4.)(6.$7.(5:.R9.)(:.$7.)))P,(59.$4.R=.)P,(28.(16.&40.)R2<.(42.&40.+5=0<8.))P,Pst1,$22.Pmo,$62.Ps',$23.Pms',$26.P,(68.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R12.R36.R11.R13.R4.R3.R2.R1.)P,(65.R5.R3.)(2?.R3<.R39.A2.R3;.R6.R5.R4.R37.R3.)(2?.R37.R34.(69.R37.R?.R36.R35.)R33.R32.(54.(55.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(42.&40.$6:.)R11.(39.(16.&40.))R10.(58.$4.)))")
(* [comment removed for export] *).

End RP_2.
