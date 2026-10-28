(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U55E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U55E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMt2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaOl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UaOl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section Amb.
Context {AMB : Amb}.

Definition A0 : hstate := mkHS (ps_init_s rc_secret (reservedZ rsegs)) (led_init (reservedZ rsegs)).

#[using="Type"] Lemma A0_hshift : hshift A0 = 0. Proof. apply hshift_init. Qed.
#[using="Type"] Lemma A0_GSH : GSH (ps_m (hs_s A0)) None. Proof. apply GSH_initA. Qed.

Section Init.
Variables (m : mem) (md : Model) (B : Z).

Hypothesis CTX : forall a : word, 0x97f78 <= bv_unsigned a < 0x98320 -> m a = None.
Hypothesis NL : rw_cells rsegs m RNEED_LOCKS [C1 (Z_to_bv 8 0)].
Hypothesis PS : rw_cells rsegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)].
Hypothesis GOT : rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)].
Hypothesis GUARD : rw_cells rsegs m RSSP_GUARD [C8 rc_canary].
Hypothesis MI : mem_inv rsegs m.
Hypothesis AUX : rauxv_ok m B.
Hypothesis CAN : bytes_at rsegs m (RATP - 16) (le8 rc_canary).

Hypothesis HEX0 : forall a : Z, RHEX_GOT <= a < RHEX_PTR + 8 -> m (wa a) = None.

Hypothesis Hh : m_halted md = None.
Hypothesis Hlazy : m_vm_lazy md = [].
Hypothesis Hmat : m_vm_materialized md = [].
Hypothesis Hmaps : vm_maps (m_vmmaps md) = [].
Hypothesis Hna : vm_noaccess (m_vmmaps md) = [].
Hypothesis Hresv : vm_reserved (m_vmmaps md) = segments_reserved rsegs.
Hypothesis Hbrk : vm_brk (m_vmmaps md) = vm_start_brk (m_vmmaps md).
Hypothesis Hvbrk : valid_brk rsegs (vm_start_brk (m_vmmaps md)).
Hypothesis Hlim : 2^31 <= vm_limit (m_vmmaps md).
Hypothesis Hceil : alloc_top (m_vmmaps md) = alloc_ceiling.

#[using="Type"] Lemma reservedZ_eq : map wwZ (segments_reserved rsegs) = reservedZ rsegs.
Proof. vm_compute. reflexivity. Qed.

#[using="AMB"] Lemma bytes_at_img : forall (a : Z) (bs : list byte),
(forall i, a <= i < a + Z.of_nat (length bs) -> m (wa i) = None) -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
QBpc.rw_bytes_b rsegs a bs = true -> bytes_at rsegs m a bs.
Proof.
intros a bs Hn Ha Hhi Hb. split; [lia|]. split; [lia|]. intros i Hi.
destruct (nth_error bs i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
refine (proj1 (QBpc.rw_bytes_b_sound rsegs bs a m Hb _ Ha Hhi i b E)).
intros w Hw. pose proof (Hn (bv_unsigned w) Hw) as X. unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

#[using="CAN HEX0"] Lemma hcells0 : HCELLS m.
Proof.
split; [exact CAN|]. unfold RHEX_GOT, RHEX_PTR, RHEX_STR in *.
split; (apply bytes_at_img; [ rewrite length_le8; intros i Hi; apply HEX0; lia | lia | rewrite length_le8; lia | vm_compute; reflexivity ]).
Qed.

#[using="CTX NL PS GOT GUARD MI AUX CAN HEX0 Hh Hlazy Hmaps Hna Hresv Hbrk Hvbrk Hceil"] Theorem drv_heap_init : HEAPc B A0 [] m md.
Proof.
pose proof Hvbrk as (R1 & R2 & R3).
assert (RT : reserved_top (segments_reserved rsegs) = 0x99000) by (vm_compute; reflexivity).
unfold A0. apply (heapc_init B m md 0).
- apply RHEAP_at_main; assumption.
- exact MI.
- rewrite <- reservedZ_eq, <- Hresv. rewrite RT in R1, R2. unfold brk_aslr_max in R2. unfold page_size in R3.
apply KL_init; try assumption.
all: try (rewrite Hresv, RT; lia).
all: pose proof alloc_ceiling_ge; unfold PGSZ; lia.
- reflexivity.
- exact AUX.
- exact hcells0.
Qed.

#[using="AMB Hlazy Hmat Hmaps Hresv Hlim"] Theorem drv_bud_init : forall (W : Z) (D : nat), 0 <= W <= 2^31 -> Z.of_nat D <= 30000 -> BUD md W D.
Proof.
intros W D HW HD. apply BUD_init; try assumption.
- lia.
- rewrite Hresv. unfold MAXINT. replace (Z.of_nat (length (segments_reserved rsegs))) with 4 by (vm_compute; reflexivity). lia.
- rewrite Hresv. replace (segments_reserved rsegs) with [(Z_to_bv 64 65536, Z_to_bv 64 65536); (Z_to_bv 64 131072, Z_to_bv 64 270336); (Z_to_bv 64 401408, Z_to_bv 64 16384); (Z_to_bv 64 417792, Z_to_bv 64 208896)] by (vm_compute; reflexivity).
repeat apply Forall_cons; try apply Forall_nil; cbn [snd]; rewrite unsigned_lit by lia; lia.
Qed.
End Init.
End Amb.
