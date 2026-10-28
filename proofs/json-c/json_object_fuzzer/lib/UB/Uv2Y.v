(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QytA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export UQXM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition ralloc_meta_entry := UKNz.ralloc_meta_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QCa8.Mq5.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rimplT {R} (o : mem) (t : QUZl.M R) (s : PState)
(Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
implM rsegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

#[using="Type"] Lemma rimplT_ret {R} o (r : R) s Q ms : evt rsegs (Q r s) ms -> rimplT o (SRet r) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_ret) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_ret)]. Qed.

#[using="Type"] Lemma rimplT_peek {R} o p c h (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (pans_mem o p c h)) s Q ms -> rimplT o (SVis (EPeek p c h) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_peek) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_peek)]. Qed.

#[using="Type"] Lemma rimplT_undef {R} o w (k : Z -> QUZl.M R) s Q ms : rimplT o (SVis (EUndef w) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_undef) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_undef)]. Qed.

#[using="Type"] Lemma rimplT_vis {R} o e (k : Z -> QUZl.M R) s Q1 Q ms :
match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
implM rsegs (ev_step e) s Q1 ms ->
(forall z s' ms', Q1 z s' ms' -> rimplT o (k z) s' Q ms') ->
rimplT o (SVis e k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_vis) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_vis)]. Qed.

#[using="Type"] Lemma rimplT_mono {R} o (t : QUZl.M R) s Q Q' ms :
rimplT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> rimplT o t s Q' ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mono)]. Qed.

#[using="Type"] Lemma rimplT_evt {R} o (t : QUZl.M R) s Q P ms :
evt rsegs P ms -> (forall ms', P ms' -> rimplT o t s Q ms') -> rimplT o t s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_evt) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_evt)]. Qed.

#[using="Type"] Lemma rimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
impl rsegs (at_node rsegs) (Vis n k) Q ms = evt rsegs (fun ms1 => at_node rsegs n ms1 /\ forall rsp, impl rsegs (at_node rsegs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimpl_vis_unfold) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimpl_vis_unfold)]. Qed.

#[using="Type"] Lemma rimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
impl rsegs (at_node rsegs) (QlEo.Mq0.bind _ t f1) Q1 ms ->
(forall r ms', impl rsegs (at_node rsegs) (f1 r) Q1 ms' -> impl rsegs (at_node rsegs) (f2 r) Q2 ms') ->
impl rsegs (at_node rsegs) (QlEo.Mq0.bind _ t f2) Q2 ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimpl_bind_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimpl_bind_mono)]. Qed.

#[using="Type"] Lemma rmembed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : QUZl.M R1) (t2 : QUZl.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
implM rsegs (membed t1) s Q1 ms ->
(forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM rsegs (membed t2) s Q2 ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rmembed_strel) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rmembed_strel)]. Qed.

#[using="Type"] Lemma rimplT_strel {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : QUZl.M R1) (t2 : QUZl.M R2) s Q1 Q2 ms :
strel RR (mrun o t1) t2 ->
rimplT o t1 s Q1 ms ->
(forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM rsegs (membed t2) s Q2 ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_strel) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_strel)]. Qed.

#[using="Type"] Lemma rimplM_membed_steq {R} (t1 t2 : QUZl.M R) s Q ms :
steq t1 t2 -> implM rsegs (membed t1) s Q ms -> implM rsegs (membed t2) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplM_membed_steq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplM_membed_steq)]. Qed.

#[using="Type"] Lemma rimplM_membed_sbind {R S} (T : QUZl.M R) (F : R -> QUZl.M S) s Q1 Q ms :
implM rsegs (membed T) s Q1 ms ->
(forall x s' ms', Q1 x s' ms' -> implM rsegs (membed (F x)) s' Q ms') ->
implM rsegs (membed (sbind T F)) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplM_membed_sbind) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplM_membed_sbind)]. Qed.

#[using="Type"] Lemma rimplT_bind {R S} o (t : QUZl.M R) (f : R -> QUZl.M S) s Q1 Q ms :
rimplT o t s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> rimplT o (f r) s' Q ms') ->
rimplT o (sbind t f) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_bind) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_bind)]. Qed.

#[using="Type"] Lemma rimplT_from_evt {R} o (t : QUZl.M R) s Q ms :
evt rsegs (fun ms' => rimplT o t s Q ms') ms -> rimplT o t s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_from_evt) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_from_evt)]. Qed.
End RC__1.
Ltac riprefixT := apply rimplT_from_evt.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rimplM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
(s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
(forall a ms', P a ms' -> evt rsegs (Q (f a) s) ms') ->
implM rsegs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplM_msys_ret) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplM_msys_ret)]. Qed.

#[using="Type"] Lemma rimplT_mmap_rw {R} o len (k : Z -> QUZl.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
rimplT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mmap_rw) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mmap_rw)]. Qed.

#[using="Type"] Lemma rimplT_mmap_none {R} o len (k : Z -> QUZl.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
rimplT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mmap_none) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mmap_none)]. Qed.

#[using="Type"] Lemma rimplT_mmap_fixed {R} o addr len (k : Z -> QUZl.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (fixed_val addr a)) s Q ms') ->
rimplT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mmap_fixed) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mmap_fixed)]. Qed.

#[using="Type"] Lemma rimplT_munmap {R} o addr len (k : Z -> QUZl.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
rimplT o (SVis (EMunmap addr len) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_munmap) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_munmap)]. Qed.

#[using="Type"] Lemma rimplT_mprotect {R} o addr len prot (k : Z -> QUZl.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
rimplT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mprotect) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_mprotect)]. Qed.

#[using="Type"] Lemma rimplT_brk0 {R} o (k : Z -> QUZl.M R) s (P : Z -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
(forall r ms', P r ms' -> rimplT o (k r) (set_brk_ps r s) Q ms') ->
rimplT o (SVis (EBrk 0) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_brk0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_brk0)]. Qed.

#[using="Type"] Lemma rimplT_brk {R} o req (k : Z -> QUZl.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
req <> 0 ->
impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
(forall a ms', P a ms' ->
rimplT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
(match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
rimplT o (SVis (EBrk req) k) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_brk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_brk)]. Qed.

#[using="Type"] Lemma rimplT_reach {R} o (t : QUZl.M R) : forall s Q ms,
rimplT o t s Q ms -> rimplT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_reach) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rimplT_reach)]. Qed.

#[using="Type"] Lemma rraw_malloc_bridge : forall st s n (o : mem) Q1 Q ms,
strip st = ps_m s ->
rimplT o (malloc st n) s Q1 ms ->
(forall st' (p : optr) s' ms' (r : option bptr),
Q1 (st', p) s' ms' -> ptr_rel p r ->
(forall b, r = Some b -> snd b = fresh_off (strip st') (fst b) n) ->
Q r (set_m (strip st') s') ms') ->
implM rsegs (raw_malloc n) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rraw_malloc_bridge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rraw_malloc_bridge)]. Qed.

Definition rauxv_list (x3 x4 x5 x16 x6 x11 x12 x23 rnd : Z) : list word :=
map wz [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].
Lemma gw_eq_rauxv_list : @rauxv_list = ltac:(GwInst.gw_term (@QCa8.Mq5.rauxv_list) (@rauxv_list)). Proof. unfold rauxv_list, QCa8.Mq5.rauxv_list; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rauxv_list : gw_eqs.

Definition rauxv_ok (m : mem) (B : Z) : Prop :=
exists av x3 x4 x5 x16 x6 x11 x12 x23 rnd,
rw_cells rsegs m RAUXV_CELL [C8 (wz av)]
/\ bytes_at rsegs m av (u64s (rauxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd))
/\ bytes_at rsegs m (rnd + 8) (le8 (wz rc_secret))
/\ alloc_ceiling <= B /\ B <= av /\ av + 160 <= 2^64 /\ B <= rnd + 8 /\ rnd + 16 <= 2^64
/\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= x16 < 2^64 /\ 0 <= x6 < 2^64
/\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64
/\ av mod 8 = 0.

#[using="Type"] Lemma rauxv_ok_weaken : forall m B B', rauxv_ok m B -> alloc_ceiling <= B' <= B -> rauxv_ok m B'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rauxv_ok_weaken) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rauxv_ok_weaken)]. Qed.

#[using="Type"] Lemma rauxv_ok_frame : forall m m' B W,
rauxv_ok m B -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) W ->
rauxv_ok m' B.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rauxv_ok_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rauxv_ok_frame)]. Qed.

#[using="Type"] Lemma rraw_free_bridge : forall st s (p : bptr) (pf : aptr) (o : mem) Q1 Q ms,
strip st = ps_m s ->
hdr_ok pans_mem pupd_mem st pf (fst p) ->
rimplT o (free st (Some pf)) s Q1 ms ->
(forall st' s' ms', Q1 st' s' ms' -> Q tt (set_m (strip st') s') ms') ->
implM rsegs (raw_free p) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rraw_free_bridge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rraw_free_bridge)]. Qed.

Definition rpres_except (C : Z -> Prop) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> ~ C a ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).
Lemma gw_eq_rpres_except : @rpres_except = ltac:(GwInst.gw_term (@QCa8.Mq5.rpres_except rsegs) (@rpres_except)). Proof. unfold rpres_except, QCa8.Mq5.rpres_except; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rpres_except : gw_eqs.

#[using="Type"] Lemma rpres_except_refl C m : rpres_except C m m.
Proof. rewrite ?gw_eq_rpres_except; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_refl) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_refl)]. Qed.
#[using="Type"] Lemma rpres_except_trans C m1 m2 m3 : rpres_except C m1 m2 -> rpres_except C m2 m3 -> rpres_except C m1 m3.
Proof. rewrite ?gw_eq_rpres_except; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_trans) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_trans)]. Qed.
#[using="Type"] Lemma rpres_except_mono (C C' : Z -> Prop) m m' : rpres_except C m m' -> (forall a, C a -> C' a) -> rpres_except C' m m'.
Proof. rewrite ?gw_eq_rpres_except; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_mono)]. Qed.

#[using="Type"] Lemma rpres_except_of_munch C W m m' :
munch W m m' -> wmono rsegs m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. rewrite ?gw_eq_rpres_except; ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_of_munch) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_of_munch)]. Qed.

#[using="Type"] Lemma rpres_except_bytes_at C m m' A bs :
rpres_except C m m' -> bytes_at rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) ->
bytes_at rsegs m' A bs.
Proof. rewrite ?gw_eq_rpres_except; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_bytes_at) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_bytes_at)]. Qed.

#[using="Type"] Lemma rpres_except_wr_at C m m' A n :
rpres_except C m m' -> wr_at rsegs m A n -> (forall a, A <= a < A + n -> ~ C a) -> wr_at rsegs m' A n.
Proof. rewrite ?gw_eq_rpres_except; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_wr_at) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_wr_at)]. Qed.

#[using="Type"] Lemma rpres_except_rw_cells C m m' A cs :
rpres_except C m m' -> rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) ->
rw_cells rsegs m' A cs.
Proof. rewrite ?gw_eq_rpres_except; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_rw_cells) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_rw_cells)]. Qed.

#[using="Type"] Lemma rpres_except_stk C m m' lo hi :
rpres_except C m m' -> stk rsegs m lo hi -> (forall a, lo <= a < hi -> ~ C a) -> stk rsegs m' lo hi.
Proof. rewrite ?gw_eq_rpres_except; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_stk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rpres_except_stk)]. Qed.

Definition ralloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ errno_addr (Z_to_bv 64 0x77c00) <= a < errno_addr (Z_to_bv 64 0x77c00) + 4
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
Lemma gw_eq_ralloc_fp : @ralloc_fp = ltac:(GwInst.gw_term (@QCa8.Mq5.ralloc_fp UKNz.RATP) (@ralloc_fp)). Proof. unfold ralloc_fp, QCa8.Mq5.ralloc_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ralloc_fp : gw_eqs.

Definition RAM_STACK : Z := 144.
Lemma gw_eq_RAM_STACK : @RAM_STACK = ltac:(GwInst.gw_term (@QCa8.Mq5.RAM_STACK) (@RAM_STACK)). Proof. unfold RAM_STACK, QCa8.Mq5.RAM_STACK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RAM_STACK : gw_eqs.

#[using="Type"] Lemma rfresh_image st a : fresh_addr st a -> s_reserved st = ref_reserved -> a < 0x10000 \/ 0x99000 <= a.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rfresh_image) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq5.rfresh_image)]. Qed.

Definition ram_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (s : PState) (lo : Z) (m : mem)
(st1 : mstate) (mo : optr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (pw st1 mo) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' (bv_unsigned sp)
/\ rpres_except (fun a => ralloc_fp (fun k => k <> RKGroup) st1 lo (bv_unsigned sp) a \/ fresh_addr st a) m m'
/\ rmrep st1 m' /\ ticks_ok st1
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ am_rel st st1 mo
/\ (mo = None -> errv' = Z_to_bv 64 12).

Definition ralloc_meta_stmt (am_pre : mstate -> Prop) : Prop :=
forall (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 0x77c00 ->
(forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms') ->
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs)).

End RC__2.
Lemma gw_eq_rauxv_list__2 : @rauxv_list = ltac:(GwInst.gw_term (@QCa8.Mq5.rauxv_list) (@rauxv_list)). Proof. unfold rauxv_list, QCa8.Mq5.rauxv_list; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rauxv_list__2 : gw_eqs.
Lemma gw_eq_rpres_except__2 : @rpres_except = ltac:(GwInst.gw_term (@QCa8.Mq5.rpres_except rsegs) (@rpres_except)). Proof. unfold rpres_except, QCa8.Mq5.rpres_except; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rpres_except__2 : gw_eqs.
Lemma gw_eq_ralloc_fp__2 : @ralloc_fp = ltac:(GwInst.gw_term (@QCa8.Mq5.ralloc_fp UKNz.RATP) (@ralloc_fp)). Proof. unfold ralloc_fp, QCa8.Mq5.ralloc_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ralloc_fp__2 : gw_eqs.
Lemma gw_eq_RAM_STACK__2 : @RAM_STACK = ltac:(GwInst.gw_term (@QCa8.Mq5.RAM_STACK) (@RAM_STACK)). Proof. unfold RAM_STACK, QCa8.Mq5.RAM_STACK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RAM_STACK__2 : gw_eqs.
