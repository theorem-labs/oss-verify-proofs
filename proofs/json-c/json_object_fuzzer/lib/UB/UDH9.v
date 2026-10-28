(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE QWxq QlEo QbVh QEpW QBpc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz Uv2Y Uqqm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH Qpox QsV0 Q9ox QBxa Qn1e QiVh QMz4 QO3A Q7m0 QSpR QuJV QCPB QH7x QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN Udbv UFOH UWQV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC U1zM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y Qod2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U87U U7J3 U4FC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QXup.
Import UEQM.

Import QBpc.
Import UKNz Uv2Y.
Import Uqqm.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH Q9ox.Mq2 QBxa.Mq4 Qn1e.Mq1 QiVh Qn1e QBxa.Mq0 QMz4 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES QBxa.Mq5 QSpR.Mq2 QBxa.Mq3.
Import UeDN Udbv UFOH.Mq0 UWQV.Mq0.
Import QSjk.Mq0 QBxa.Mq2 QSpR.Mq1 QuJV.Mq0 QBxa.Mq6.
Import U1oC.Mq2 U1zM.
Import Qe4Y Qod2.
Import U87U U7J3 U4FC U7J3.Mq0.

Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block1" constr(scr) constr(NX) := run_block_gen FUEL STOPS1 scr NX false.
Tactic Notation "run_block1_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS1 scr NX true.

Lemma canonR_getr : forall R,
canonR R = QWxq.mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
(getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
(getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
(getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).
Proof. intros R. unfold canonR, getr. cbn -[reg_get]. reflexivity. Qed.
Lemma lit_add_1 : forall a : Z, (Z_to_bv 64 a + 1 : word) = Z_to_bv 64 (a + 1).
Proof.
intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1%Z.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma store_ok_wr_at : forall segs m (a : Z) (n : nat),
(0 <= a)%Z -> (a + Z.of_nat n <= 2^64)%Z ->
store_ok segs m (Z_to_bv 64 a) n = true -> QZDE.wr_at segs m a (Z.of_nat n).
Proof.
intros segs m a n Ha Hn H. split; [exact Ha|]. split; [exact Hn|].
revert a Ha Hn H. induction n as [|n IH]; intros a Ha Hn H i Hi; [lia|].
cbn [store_ok] in H. destruct (wview segs m (Z_to_bv 64 a)) eqn:W; [|discriminate].
destruct (Z.eq_dec i 0) as [->|NZ].
- unfold QZDE.wa. rewrite Z.add_0_r, W. discriminate.
- unfold QZDE.wa. replace (a + i)%Z with ((a + 1) + (i - 1))%Z by lia.
apply (IH (a + 1)%Z); [lia| lia| | lia].
rewrite <- lit_add_1. exact H.
Qed.

Lemma rw_cells_of_rdn : forall segs m (a : Z) cs,
QbVh.cells_wf cs ->
(0 <= a)%Z -> (a + Z.of_nat (QbVh.cells_size cs) <= 2^64)%Z ->
rdn segs m (Z_to_bv 64 a) (QbVh.cells_size cs) = Some (QbVh.cells_bytes cs) ->
store_ok segs m (Z_to_bv 64 a) (QbVh.cells_size cs) = true ->
QlEo.rw_cells segs m a cs.
Proof.
intros segs m a cs WF Ha Hn RD SO. split; [split; [exact WF|]|].
- rewrite <- (QbVh.cells_bytes_length cs WF) in RD, Hn. exact (rdn_bytes_at segs m a _ Ha Hn RD).
- apply store_ok_wr_at; assumption.
Qed.

Lemma add_lit_Z : forall (x : word) (k : Z), (x + Z_to_bv 64 k : word) = Z_to_bv 64 (bv_unsigned x + k).
Proof.
intros x k. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Ltac eval_sr SR :=
repeat match goal with |- context [sr_get SR ?r] => let e := eval vm_compute in (sr_get SR r) in change (sr_get SR r) with e end.

Lemma ref_ro_addr_rw : forall x : word, (0x62000 <= bv_unsigned x)%Z -> QZDE.ro_addr rsegs x = false.
Proof.
intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R.
destruct (Z.lt_ge_cases (bv_unsigned x) 0x99000) as [LT|GE]; [| apply ref_ro_addr_false; lia].
unfold QZDE.ro_addr. unfold rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 0x20000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 0x42000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 0x62000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 0x4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 0x66000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
set (z := bv_unsigned x) in *.
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x10000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x20000 z); destruct (Z.leb_spec0 (z + 1) (0x20000 + 0x42000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x62000 z); destruct (Z.leb_spec0 (z + 1) (0x62000 + 0x4000)); cbn [andb]; try lia.
all: try (vm_compute; reflexivity).
all: destruct (Z.leb_spec0 0x66000 z); destruct (Z.leb_spec0 (z + 1) (0x66000 + 0x33000)); cbn [andb]; try lia.
all: try (vm_compute; reflexivity).
Qed.

Lemma mem_inv_of_img : forall m : mem,
(forall i, (0x10000 <= i < 0x62000)%Z -> m (Z_to_bv 64 i) = None) -> QZDE.mem_inv rsegs m.
Proof.
intros m H a b Hab. pose proof (bv_unsigned_in_range 64 a) as R.
destruct (Z.lt_ge_cases (bv_unsigned a) 0x10000) as [LT|GE]; [apply ref_ro_addr_false; lia|].
destruct (Z.lt_ge_cases (bv_unsigned a) 0x62000) as [LT2|GE2]; [| apply ref_ro_addr_rw; lia].
exfalso. rewrite <- (Z_to_bv_bv_unsigned a), (H (bv_unsigned a)) in Hab by lia. discriminate.
Qed.

Lemma rw_cells_img : forall (m : mem) A bs cs,
(forall i, (A <= i < A + Z.of_nat (length bs))%Z -> m (Z_to_bv 64 i) = None) ->
QBpc.rw_bytes_b rsegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
QbVh.cells_wf cs -> QbVh.cells_bytes cs = bs -> QbVh.cells_size cs = length bs ->
QlEo.rw_cells rsegs m A cs.
Proof.
intros m A bs cs Hn Hb HA Hhi WF E1 E2.
apply (QBpc.rw_cells_recast rsegs m A [CB (length bs) bs] cs); [| exact WF| cbn; rewrite app_nil_r; exact E1| cbn; rewrite Nat.add_0_r; exact E2].
apply QBpc.rw_cells_image0; [| exact Hb| exact HA| exact Hhi].
intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply Hn. exact Ha.
Qed.

Lemma stk_of_store_ok : forall (m : mem) lo hi,
(0x99000 <= lo)%Z -> (hi <= 2^64)%Z ->
(forall a, (lo <= a < hi)%Z -> store_ok rsegs m (Z_to_bv 64 a) 1 = true) ->
QWxq.stk rsegs m lo hi.
Proof.
intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
specialize (H a Ha). cbn [store_ok] in H. unfold QZDE.wa.
destruct (wview rsegs m (Z_to_bv 64 a)) eqn:W; [|discriminate].
rewrite ref_wview_overlay in W by (rewrite unsigned_lit by lia; lia).
split; [discriminate| exists b; unfold QZDE.mrd; rewrite W; reflexivity].
Qed.

Lemma alu_add_lit : forall (x : word) (k : Z), alu64 ALU_ADD x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros. unfold alu64. cbn. apply add_lit_Z. Qed.

Lemma rw_C8_of_rdn : forall (m : mem) (a : Z) (v : word),
(0 <= a)%Z -> (a + 8 <= 2^64)%Z ->
rdn rsegs m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> store_ok rsegs m (Z_to_bv 64 a) 8 = true ->
QlEo.rw_cells rsegs m a [C8 v].
Proof. intros m a v Ha Hh RD SO. apply rw_cells_of_rdn; [cbn; exact (conj I I)| exact Ha| cbn; lia| cbn [QbVh.cells_size QbVh.csize QbVh.cells_bytes QbVh.cbytes Nat.add]; rewrite app_nil_r; exact RD| exact SO]. Qed.

Lemma rw_cells_cons : forall (m : mem) (a : Z) c cs,
QlEo.rw_cells rsegs m a [c] -> QlEo.rw_cells rsegs m (a + Z.of_nat (QbVh.csize c)) cs -> QlEo.rw_cells rsegs m a (c :: cs).
Proof.
intros m a c cs H1 H2. apply (proj2 (QULt.Mq2.rw_cells_app rsegs m a [c] cs)). cbn [QbVh.cells_size]. rewrite Nat.add_0_r. exact (conj H1 H2).
Qed.
Lemma bytes_at_of_rdn : forall (m : mem) (a : Z) n bs,
(0 <= a)%Z -> (a + Z.of_nat n <= 2^64)%Z -> rdn rsegs m (Z_to_bv 64 a) n = Some bs -> length bs = n -> QZDE.bytes_at rsegs m a bs.
Proof. intros m a n bs Ha Hn RD <-. exact (rdn_bytes_at rsegs m a bs Ha Hn RD). Qed.

Lemma bytes_at_eqmem : forall segs (m m0 : mem) a bs,
QZDE.bytes_at segs m0 a bs -> (forall x, (a <= x < a + Z.of_nat (length bs))%Z -> m (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) ->
QZDE.bytes_at segs m a bs.
Proof.
intros segs m m0 a bs (H1 & H2 & H3) E. split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold QZDE.mrd, QZDE.wa in *. rewrite E by lia. apply H3. exact Hi.
Qed.

Section Conv.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Context {SL : SrcLim}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
Hypothesis Hbrk : valid_brk RSEGS brk.
Hypothesis Hpne : path <> [].
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis FRM0 : QCcH.frm0 fC.
Hypothesis ASP : a_sp = sp0.
Variable fd3 : FdEntry.
Variable KB : TSet.

Notation ENV := (U1zM.ENV a0s path).
Notation model1g := (U1zM.model1g sp0 tid brk mbase fs0 stdin0).
Notation above_sp0 := (U1zM.above_sp0 sp0 mem0).
Notation usp0 := (bv_unsigned sp0).
Notation pp := (bv_unsigned (p1 sp0 a0s path envv)).

#[using="envv tid regs0 Hva Hvsp ME Hplen"] Lemma M_locale : forall vals M, vals_ev vals 0 = sp0 -> M = mem_denot (ENV vals) mem0 logA ->
QZDE.bytes_at rsegs M 0x77bd0 (QZDE.le8 (wz 0x97ec8)).
Proof.
intros vals M P0 ->. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
eapply (bytes_at_of_rdn _ _ 8); [lia| lia| | reflexivity].
transitivity (rdn RSEGS mem0 (Z_to_bv 64 0x77bd0) 8).
{ apply rdn_agree. intros j Hj. apply (mem_denot_below (ENV vals) mem0 logA 0 (-8388608)); [exact logA_stack| |];
cbn [ev ENV]; rewrite P0; [lia|]. change (bv_unsigned (Z_to_bv 64 490448)) with 490448%Z. rewrite u_small; lia. }
rewrite (main_entry_rdn_data sp0 [a0s; path] envv tid regs0 mem0 ME) by (rewrite stack_max_size_val; unorm; lia).
apply (D_main_locale sp0 [a0s; path] envv tid Hva).
Qed.

#[using="regs0 Hva Hve Hvsp Htid ME Hplen ASP"] Lemma drv_entry_of_know : forall vals M,
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 5 = tid -> vals_ev vals 38 = ssp_canary ->
know_ok RSEGS (ENV vals) M knA -> above_sp0 M ->
QZDE.bytes_at rsegs M 0x77bd0 (QZDE.le8 (wz 0x97ec8)) ->
drv_entry usp0 pp (bv_unsigned tid) path M.
Proof.
intros vals M HL P0 P2 P3 P5t P38 HK HA LOCF.
pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
unfold sp_window_lo, sp_window_hi in *.

Ltac kimg HK i := let H := fresh "KI" in
pose proof (know_nth RSEGS _ _ knA i _ HK ltac:(vm_compute; reflexivity)) as H; cbn [kentry_ok] in H;
destruct H as (_ & _ & H).
kimg HK 51%nat. kimg HK 52%nat. kimg HK 53%nat. kimg HK 56%nat. kimg HK 57%nat. kimg HK 58%nat. kimg HK 59%nat.
kimg HK 61%nat. kimg HK 62%nat. kimg HK 63%nat. kimg HK 65%nat. kimg HK 66%nat. kimg HK 69%nat. kimg HK 70%nat.

Ltac kword HK i := let H := fresh "KW" in
pose proof (know_nth RSEGS _ _ knA i _ HK ltac:(vm_compute; reflexivity)) as H; cbn [kentry_ok] in H;
destruct H as (_ & _ & H); rewrite adenot_lit0 in H; cbn [edenot ev eb U1zM.ENV] in H.
kword HK 54%nat. kword HK 55%nat. kword HK 60%nat. kword HK 64%nat. kword HK 67%nat. kword HK 68%nat.
rewrite ?P5t, ?P3, ?P38 in *.

assert (WD : forall k m, (0x66000 <= k)%Z -> (k + Z.of_nat m <= 0x99000)%Z -> store_ok RSEGS M (Z_to_bv 64 k) m = true).
{ intros k m Hk Hm. eapply (kwr_store_ok_lit RSEGS _ M knA 50); [exact HK| vm_compute; reflexivity| lia| lia| lia]. }
assert (WS : forall k m, (usp0 - 8388608 <= k)%Z -> (k + Z.of_nat m <= usp0)%Z -> store_ok RSEGS M (Z_to_bv 64 k) m = true).
{ intros k m Hk Hm.
pose proof (kwr_store_ok RSEGS (ENV vals) M knA 21 (EVar 0) (-8388608) 8388608 (k - usp0) m HK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as W.
unfold adenot, v_addi in W. cbn [a_base a_off edenot ev U1zM.ENV] in W. rewrite P0 in W.
replace (usp0 + (k - usp0))%Z with k in W by lia. exact W. }

Ltac kwordv HK i P0 := let H := fresh "KF" in
pose proof (know_nth RSEGS _ _ knA i _ HK ltac:(vm_compute; reflexivity)) as H; cbn [kentry_ok] in H;
destruct H as (_ & _ & H); unfold adenot, v_addi in H; cbn [a_base a_off edenot ev eb U1zM.ENV alu] in H;
rewrite ?P0, ?add_lit_Z in H.
kwordv HK 10%nat P0. kwordv HK 11%nat P0. kwordv HK 12%nat P0. kwordv HK 13%nat P0.
kwordv HK 14%nat P0. kwordv HK 15%nat P0. kwordv HK 16%nat P0. kwordv HK 17%nat P0. kwordv HK 18%nat P0.
rewrite ?alu_add_lit in *.
pose proof (u64_range tid) as TR.
constructor.
-  lia.
-  apply stk_of_store_ok; [lia| lia|]. intros a Ha. apply WS; lia.
-
unfold main_frame. change (wz 0) with (Z_to_bv 64 0).
Ltac fcell H WS nxt := apply rw_cells_cons; [eapply rw_C8_of_rdn; [lia| lia| exact H| apply WS; lia]
| match goal with |- QlEo.rw_cells _ _ ?A _ => replace A with nxt by (cbn; lia) end].
replace (usp0 - 120)%Z with (usp0 + -120)%Z by lia.
fcell KF WS (usp0 + -112)%Z. fcell KF0 WS (usp0 + -104)%Z. fcell KF1 WS (usp0 + -96)%Z. fcell KF2 WS (usp0 + -88)%Z.
fcell KF3 WS (usp0 + -80)%Z. fcell KF4 WS (usp0 + -72)%Z. fcell KF5 WS (usp0 + -64)%Z. fcell KF6 WS (usp0 + -56)%Z.
eapply rw_C8_of_rdn; [lia| lia| exact KF7| apply WS; lia].
-  apply (rw_cells_img M RERRNO (QbVh.cells_bytes [C4 (wz 0)]) [C4 (wz 0)]); [| vm_compute; reflexivity| unfold RERRNO; lia| cbn; unfold RERRNO; lia| cbn; exact (conj I I)| reflexivity| reflexivity].
cbn [length QbVh.cells_bytes QbVh.cbytes app QZDE.le4 word_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]. unfold RERRNO. intros i Hi.
cbn in *; first [apply KI; lia| apply KI0; lia| apply KI1; lia| apply KI2; lia| apply KI3; lia| apply KI4; lia| apply KI5; lia| apply KI6; lia| apply KI7; lia| apply KI8; lia| apply KI9; lia| apply KI10; lia| apply KI11; lia| apply KI12; lia].
-  intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). cbn in *; first [apply KI; lia| apply KI0; lia| apply KI1; lia| apply KI2; lia| apply KI3; lia| apply KI4; lia| apply KI5; lia| apply KI6; lia| apply KI7; lia| apply KI8; lia| apply KI9; lia| apply KI10; lia| apply KI11; lia| apply KI12; lia].
-  apply (rw_cells_img M RNEED_LOCKS (QbVh.cells_bytes [C1 (Z_to_bv 8 0)]) [C1 (Z_to_bv 8 0)]); [| vm_compute; reflexivity| unfold RNEED_LOCKS; lia| cbn; unfold RNEED_LOCKS; lia| cbn; exact (conj I I)| reflexivity| reflexivity].
cbn [length QbVh.cells_bytes QbVh.cbytes app]. unfold RNEED_LOCKS. intros i Hi.
cbn in *; first [apply KI; lia| apply KI0; lia| apply KI1; lia| apply KI2; lia| apply KI3; lia| apply KI4; lia| apply KI5; lia| apply KI6; lia| apply KI7; lia| apply KI8; lia| apply KI9; lia| apply KI10; lia| apply KI11; lia| apply KI12; lia].
-  unfold RPAGE_SIZE. eapply rw_C8_of_rdn; [lia| lia| | apply WD; lia].
match goal with H : rdn RSEGS M (Z_to_bv 64 622272) 8 = _ |- _ => exact H end.
-  apply (rw_cells_img M RGOT_SSP (QbVh.cells_bytes [C8 (Z_to_bv 64 RSSP_GUARD)]) [C8 (Z_to_bv 64 RSSP_GUARD)]); [| vm_compute; reflexivity| unfold RGOT_SSP; lia| cbn; unfold RGOT_SSP; lia| cbn; exact (conj I I)| reflexivity| reflexivity].
cbn [length QbVh.cells_bytes QbVh.cbytes app QZDE.le8 word_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]. unfold RGOT_SSP. intros i Hi.
cbn in *; first [apply KI; lia| apply KI0; lia| apply KI1; lia| apply KI2; lia| apply KI3; lia| apply KI4; lia| apply KI5; lia| apply KI6; lia| apply KI7; lia| apply KI8; lia| apply KI9; lia| apply KI10; lia| apply KI11; lia| apply KI12; lia].
-  unfold RSSP_GUARD. change (@rc_canary amb_rc) with ssp_canary. eapply rw_C8_of_rdn; [lia| lia| | apply WD; lia].
match goal with H : rdn RSEGS M (Z_to_bv 64 622192) 8 = _ |- _ => exact H end.
-  unfold RATP. change (@rc_canary amb_rc) with ssp_canary. eapply (bytes_at_of_rdn M _ 8); [lia| lia| | reflexivity].
match goal with H : rdn RSEGS M (Z_to_bv 64 490480) 8 = _ |- _ => exact H end.
-  apply mem_inv_of_img. intros i Hi. cbn in *; first [apply KI; lia| apply KI0; lia| apply KI1; lia| apply KI2; lia| apply KI3; lia| apply KI4; lia| apply KI5; lia| apply KI6; lia| apply KI7; lia| apply KI8; lia| apply KI9; lia| apply KI10; lia| apply KI11; lia| apply KI12; lia].
-
assert (ABOVE : forall x, (usp0 <= x < 2^64)%Z -> M (Z_to_bv 64 x) = QsRG.Mq0.wrap_mem RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd (Z_to_bv 64 x)).
{ intros x Hx. rewrite (HA (Z_to_bv 64 x)) by (rewrite u_small by lia; lia).
apply (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small by lia. lia. }
pose proof (lay_bsb_nw RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as NW.
pose proof (QBpc.build_stack_bytes_length RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd) as BL.
pose proof (QBpc.raw_len_nonneg RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd) as RLN.
unfold QBpc.raw_len, QBpc.struct_size, QBpc.argc, QBpc.envc in BL, RLN. cbn [length] in BL, RLN.
destruct (QBpc.init_pieces rsegs RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd ltac:(rewrite stack_max_size_val; lia) ltac:(lia)) as (_ & _ & _ & AUXW & _ & _ & RND).
pose proof (proj1 (@auxvp_u AMB sp0 a0s path envv Hva Hve Hvsp)) as AU.
set (avz := (usp0 + 8 * (QBpc.argc [a0s; path] + QBpc.envc envv + 3))%Z) in AUXW.
assert (EAV : bv_unsigned (auxvp sp0 a0s path envv) = avz).
{ rewrite AU. subst avz. unfold auxv_off, QBpc.argc, QBpc.envc. cbn [length]. lia. }
exists avz, (Z.of_N (ph_addr RPH)), (Z.of_N (ph_ent RPH)), (Z.of_N (ph_num RPH)), (bv_unsigned a_hwcap), 4096%Z, (bv_unsigned a_uid), (bv_unsigned a_uid), 0%Z, (QBpc.rnd_addr sp0 [a0s; path] envv).
pose proof (u64_range a_uid) as UR. pose proof (u64_range a_hwcap) as HR'.
assert (PH : (Z.of_N (ph_addr RPH) = 0x10040 /\ Z.of_N (ph_ent RPH) = 56 /\ Z.of_N (ph_num RPH) = 11)%Z) by (vm_compute; repeat split; reflexivity).
destruct PH as (PH1 & PH2 & PH3).
split. { unfold RAUXV_CELL. eapply rw_C8_of_rdn; [lia| lia| | apply WD; lia]. unfold wz. rewrite <- EAV, Z_to_bv_bv_unsigned.
match goal with H : rdn RSEGS M (Z_to_bv 64 622232) 8 = _ |- _ => exact H end. }
split. { replace (rauxv_list _ _ _ _ _ _ _ _ _) with (QBpc.auxv_words RPH sp0 [a0s; path] envv a_uid a_hwcap).
2:{ unfold rauxv_list, QBpc.auxv_words, wz. cbn [map]. rewrite PH1, PH2, PH3, !Z_to_bv_bv_unsigned. reflexivity. }
eapply bytes_at_eqmem; [exact AUXW|]. intros x Hx. apply ABOVE.
rewrite Q5Rg.u64s_length in Hx. unfold QBpc.auxv_words in Hx. cbn [length] in Hx.
subst avz. unfold QBpc.argc, QBpc.envc in Hx. cbn [length] in Hx. lia. }
split. {
change (StackLayout.at_random_bytes (ed_random a_rnd)) with (@rnd_bytes AMB) in RND.
rewrite (@rnd_bytes_split AMB) in RND. apply QZDE.bytes_at_app in RND as [_ RND].
change (Z.of_nat (length _)) with 8%Z in RND.
replace (le8 (wz rc_secret)) with (@secret_bytes AMB).
2:{ unfold le8, wz. change (@rc_secret amb_rc) with rnd_secret. unfold rnd_secret. rewrite Z_to_bv_bv_unsigned. symmetry. apply ssp_secret_bytes. }
eapply bytes_at_eqmem; [exact RND|]. intros x Hx. apply ABOVE. rewrite secret_bytes_length in Hx.
unfold QBpc.rnd_addr, QBpc.raw_len, QBpc.struct_size, QBpc.argc, QBpc.envc in Hx. cbn [length] in Hx. lia. }
subst avz. unfold QBpc.argc, QBpc.envc, QBpc.rnd_addr, QBpc.raw_len, QBpc.struct_size in *. cbn [length] in *.
repeat split; unfold QBpc.argc, QBpc.envc in *; cbn [length] in *; try lia.
+  change (@alloc_ceiling amb_rc) with (bv_unsigned a_sp - 8388608)%Z. rewrite ASP. lia.
+ replace (usp0 + 8 * (Z.of_nat 2 + Z.of_nat (length envv) + 3))%Z with ((Z.of_nat (length envv) + 5 + usp0 / 8) * 8)%Z.
2:{ pose proof (Z.div_mod usp0 16 ltac:(lia)) as DM. rewrite SPal in DM.
replace (usp0 / 8)%Z with (2 * (usp0 / 16))%Z; [lia|].
rewrite DM at 2. replace (16 * (usp0 `div` 16) + 0)%Z with ((2 * (usp0 / 16)) * 8)%Z by lia. rewrite Z_div_mult by lia. reflexivity. }
apply Z_mod_mult.
-  split; [| lia]. eapply (bytes_at_of_rdn M _ 4); [lia| lia| | reflexivity].
rewrite Z_to_bv_bv_unsigned. match goal with H : rdn RSEGS M (Z_to_bv 64 490328) 4 = _ |- _ => exact H end.
-  eapply (bytes_at_of_rdn M _ 8); [lia| lia| | reflexivity]. match goal with H : rdn RSEGS M (Z_to_bv 64 490296) 8 = _ |- _ => exact H end.
-  unfold pris, PRIS. repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; unfold QZDE.wa;
cbn in *; first [apply KI; lia| apply KI0; lia| apply KI1; lia| apply KI2; lia| apply KI3; lia| apply KI4; lia| apply KI5; lia| apply KI6; lia| apply KI7; lia| apply KI8; lia| apply KI9; lia| apply KI10; lia| apply KI11; lia| apply KI12; lia] |]). apply Forall_nil.
-  intros a Ha. unfold QZDE.wa, RSTAGE, RSTAGE_SZ in *.
cbn in *; first [apply KI; lia| apply KI0; lia| apply KI1; lia| apply KI2; lia| apply KI3; lia| apply KI4; lia| apply KI5; lia| apply KI6; lia| apply KI7; lia| apply KI8; lia| apply KI9; lia| apply KI10; lia| apply KI11; lia| apply KI12; lia].
-
destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen). cbn [nth app] in Sr, Slo, Shi, Slen.
change (cat_argv_ptr sp0 [a0s; path] envv 1) with (p1 sp0 a0s path envv) in Sr, Slo, Shi.
pose proof (u64_range (p1 sp0 a0s path envv)) as PR.
split; [| split; lia].
assert (RD : rdn RSEGS M (Z_to_bv 64 pp) (length (path ++ [Z_to_bv 8 0])) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite length_app. cbn [length]. rewrite Z_to_bv_bv_unsigned, <- Sr. apply rdn_agree. intros j Hj. apply HA.
rewrite u_small by (clear -Hj PR Shi SPhi Slen; lia). clear -Hj Slo PR. lia. }
apply (rdn_bytes_at rsegs M pp _); [clear -PR; lia| | exact RD]. rewrite length_app. cbn [length]. clear -PR Shi SPhi Slen. lia.
-
pose proof (lay_bsb_nw RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as NW.
pose proof (QBpc.build_stack_bytes_length RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd) as BL.
pose proof (QBpc.raw_len_nonneg RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd) as RLN.
unfold QBpc.raw_len, QBpc.struct_size, QBpc.argc, QBpc.envc in BL, RLN. cbn [length] in BL, RLN.
pose proof (u_cat_argv_ptr sp0 [a0s; path] envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(cbn; lia)) as PP.
unfold cat_struct_size, auxv_size in PP. cbn [length firstn total_arg_bytes_nat fold_right] in PP.
change (cat_argv_ptr sp0 [a0s; path] envv 1) with (p1 sp0 a0s path envv) in PP.
unfold total_arg_bytes in BL, RLN. cbn [fold_right] in BL, RLN.
pose proof (QBpc.init_stack_bytes rsegs RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd ltac:(rewrite stack_max_size_val; lia) ltac:(lia)) as SB.
set (off := Z.to_nat (pp + Z.of_nat (length path) - usp0)).
exists (firstn 8 (skipn off (build_stack_bytes RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd))). split.
+ replace (pp + Z.of_nat (length path))%Z with (usp0 + Z.of_nat off)%Z by (subst off; lia).
eapply bytes_at_eqmem.
* apply (QBpc.bytes_at_slice rsegs RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd). { exact SB. } subst off. lia.
* intros x Hx. rewrite length_firstn, length_skipn in Hx.
rewrite (HA (Z_to_bv 64 x)) by (rewrite u_small by lia; lia).
apply (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small by lia. lia.
+ rewrite length_firstn, length_skipn. subst off. lia.
-  exact LOCF.
-  change (@alloc_ceiling amb_rc) with (bv_unsigned a_sp - 8388608)%Z. rewrite ASP. reflexivity.
Qed.

Hypothesis KLIB : read_entry_stmt usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path (U1zM.fds1g fd3) fs0 KB.

#[using="regs0 Hva Hve Hvsp Htid ME Hbrk Hplen FRM0 ASP KLIB"] Theorem conv_open_ok : open_ok_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 fd3 KB.
Proof.
intros vals R M HL P0 P1 P2 P3 P4 P5t P38 HR HK HA EQM.
pose proof (M_locale vals M P0 EQM) as LOCF.
pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
unfold sp_window_lo, sp_window_hi in *.

run_block1_keep scr0 39%nat.
lazymatch goal with H : ?Mx = mem_denot _ M [] |- _ => assert (EM0 : Mx = M) by (rewrite H; reflexivity); subst Mx; clear H end.

change (mkst R0 (Z_to_bv 64 336372) M (seg_rom RSEGS)) with (QEpW.MS R0 fF (Z_to_bv 64 336372) fC None M (seg_rom RSEGS)).
apply (realizes_canon RSEGS). rewrite canonR_getr. rewrite !(reg_val _ _ _ _ HR).
lazymatch type of HR with regs_ok _ ?SR _ => eval_sr SR end.
cbn [edenot ev eb U1zM.ENV alu]. rewrite ?P0, ?P2, ?alu_add_lit.
replace (mem_denot (ENV vals) M []) with M by reflexivity.
replace (usp0 + -128)%Z with (usp0 - 128)%Z by lia.
pose proof (drv_entry_of_know vals M HL P0 P2 P3 P5t P38 HK HA LOCF) as DE.
pose proof DE as [SPB STK FRM ERRC CTX NL PS GOT GUARD CAN MI AUX TID SELF PRS STG PTH PTH8 LOCc CEIL].
pose proof Hbrk as (R1 & R2 & R3).
pose proof KLIB as K. unfold read_entry_stmt in K. eapply K; clear K.
- exact DE.
- assert (HEX0 : forall a : Z, (UmAj.RHEX_GOT <= a < UmAj.RHEX_PTR + 8)%Z -> M (QZDE.wa a) = None).
{ intros a Ha. unfold UmAj.RHEX_GOT, UmAj.RHEX_PTR in Ha.
exact (proj1 (Forall_forall _ _) PRS (0x10000, 0x66f30)%Z ltac:(cbn; tauto) a ltac:(cbn; lia)). }
apply (drv_heap_init M (model1g fd3) usp0 CTX NL PS GOT GUARD MI AUX CAN HEX0); try reflexivity;
first [exact Hbrk
|  unfold alloc_top; rewrite U1zM.m1_vmmaps; unfold U1zM.vm0; cbn [vm_init_sp]; rewrite stack_max_size_val; symmetry; exact CEIL
| idtac].
- apply (drv_bud_init (model1g fd3)); try reflexivity.
all: try exact LIM_ge.
all: try (unfold DRV_W; cbn; lia).
all: try (unfold DRV_D; cbn; lia).
- reflexivity.
- reflexivity.
- exact FRM0.
Qed.
End Conv.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4FC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4FC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uqqm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uqqm.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Fixpoint T_rem (data : list byte) (fs : Fs.Fs) (n : nat) (cap : Z) : TSet :=
match n with
| O => t_body data fs
| S n' => if cap <=? Z.of_nat (length data) then T_rem data fs n' (2 * cap) else t_body data fs
end.

Lemma T_rem_body : forall data fs n cap, T_rem data fs n cap = t_body data fs.
Proof.
intros data fs n. induction n as [|n IH]; intros cap; cbn [T_rem]; [reflexivity|].
destruct (cap <=? Z.of_nat (length data)); [apply IH| reflexivity].
Qed.

Lemma T_rem_oom_eq : forall data fs n cap,
t_eq (T_rem data fs n cap) (t_opened data fs).
Proof. intros. rewrite T_rem_body. unfold t_opened. apply t_eq_refl. Qed.

Lemma T_rem_grow : forall data fs n cap, cap <= Z.of_nat (length data) ->
T_rem data fs (S n) cap = T_rem data fs n (2 * cap).
Proof. intros. cbn [T_rem]. replace (cap <=? Z.of_nat (length data)) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma T_rem_small : forall data fs n cap, Z.of_nat (length data) < cap -> T_rem data fs n cap = t_body data fs.
Proof. intros data fs [|n] cap H; cbn [T_rem]; [reflexivity|]. replace (cap <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

Lemma ref_ro_addr_text : forall x : word, 0x10000 <= bv_unsigned x < 0x62000 -> ro_addr rsegs x = true.
Proof.
intros x Hx.
unfold ro_addr. unfold rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 0x20000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 0x42000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 0x62000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 0x4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 0x66000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
set (z := bv_unsigned x) in *.
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x10000)); cbn [andb]; try lia.
all: try reflexivity.
all: destruct (Z.leb_spec0 0x20000 z); destruct (Z.leb_spec0 (z + 1) (0x20000 + 0x42000)); cbn [andb]; try lia.
all: try reflexivity.
Qed.

Lemma mem_inv_text_none : forall m (a : Z), mem_inv rsegs m -> 0x10000 <= a < 0x62000 -> m (wa a) = None.
Proof.
intros m a MI Ha. destruct (m (wa a)) as [b|] eqn:E; [|reflexivity]. exfalso.
pose proof (MI _ _ E) as R. rewrite ref_ro_addr_text in R; [discriminate|]. unfold wa. rewrite unsigned_lit by lia. exact Ha.
Qed.

Lemma pris_transport : forall m m',
pris m -> mem_inv rsegs m' ->
(forall x, 0x62000 <= x < 0x99000 -> ~ (RCTX <= x < RCTX + 928) -> ~ (RERRNO <= x < RERRNO + 4) -> m' (wa x) = m (wa x)) ->
pris m'.
Proof.
intros m m' PRS MI' EQ. unfold pris in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0.
destruct (Z.lt_ge_cases a 0x62000) as [LT|GE].
- apply mem_inv_text_none; [exact MI'|]. unfold PRIS in IN. cbn in IN.
repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
- rewrite EQ; [exact E0| | |]; unfold PRIS, RCTX, RERRNO in *; cbn in IN;
repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
Qed.

Lemma stage_img : QBpc.rw_bytes_b rsegs RSTAGE (repeat (Z_to_bv 8 0) (Z.to_nat RSTAGE_SZ)) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma stage_stk_of_none : forall m : mem,
(forall a, RSTAGE <= a < RSTAGE + RSTAGE_SZ -> m (wa a) = None) -> stk rsegs m RSTAGE (RSTAGE + RSTAGE_SZ).
Proof.
intros m NONE. pose proof stage_img as IMG.
set (n := Z.to_nat RSTAGE_SZ) in *. assert (Hn : Z.of_nat n = RSTAGE_SZ) by (subst n; apply Z2Nat.id; unfold RSTAGE_SZ; lia).
clearbody n.
pose proof (QBpc.rw_cells_image0 rsegs m RSTAGE (repeat (Z_to_bv 8 0) n)) as RW.
rewrite repeat_length, Hn in RW.
replace (RSTAGE + RSTAGE_SZ) with (RSTAGE + Z.of_nat (cells_size [CB n (repeat (Z_to_bv 8 0) n)])) by (cbn [cells_size csize]; rewrite Nat.add_0_r, Hn; reflexivity).
apply stk_of_rw_cells. apply RW.
- intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply NONE. exact Ha.
- exact IMG.
- unfold RSTAGE. lia.
- unfold RSTAGE, RSTAGE_SZ. lia.
Qed.

Lemma stage_bounds : 0x62000 <= RSTAGE /\ RSTAGE + RSTAGE_SZ <= 0x99000
/\ (RSTAGE + RSTAGE_SZ <= RCTX \/ RCTX + 928 <= RSTAGE) /\ (RSTAGE + RSTAGE_SZ <= RERRNO \/ RERRNO + 4 <= RSTAGE).
Proof. unfold RSTAGE, RSTAGE_SZ, RCTX, RERRNO. lia. Qed.

Lemma stk_carve_lo : forall (m : mem) lo hi (n : nat),
stk rsegs m lo hi -> lo + Z.of_nat n <= hi ->
stk rsegs m (lo + Z.of_nat n) hi /\ exists junk, rw_cells rsegs m lo [CB n junk].
Proof.
intros m lo hi n ST Hn. destruct (stk_split rsegs m lo (lo + Z.of_nat n) hi ST ltac:(pose proof ST as (S1 & _); lia)) as [SL SH].
split; [exact SH|].
destruct (stk_carve rsegs m lo (lo + Z.of_nat n) n SL ltac:(lia)) as [_ (junk & RW)].
exists junk. replace lo with (lo + Z.of_nat n - Z.of_nat n) at 1 by lia. exact RW.
Qed.

Section AmbL.
Context {AMB : Amb}.

Record DF (usp0 pp tid : Z) (path : list byte) (m : mem) : Prop := MKDF {
f_sp    : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0;
f_stk   : stk rsegs m (usp0 - 8388608) usp0;
f_frame : rw_cells rsegs m (usp0 - 120) (main_frame usp0);
f_tid   : bytes_at rsegs m 0x77b58 (le4 (Z_to_bv 64 tid)) /\ 0 < tid < 2^22;
f_self  : bytes_at rsegs m 0x77b38 (le8 (Z_to_bv 64 0x77b38));
f_pris  : pris m;
f_stage : stk rsegs m RSTAGE (RSTAGE + RSTAGE_SZ);
f_path  : bytes_at rsegs m pp (path ++ [Z_to_bv 8 0]) /\ usp0 <= pp /\ pp + Z.of_nat (length path) + 9 <= usp0 + 4194304;
f_path8 : exists t8, bytes_at rsegs m (pp + Z.of_nat (length path)) t8 /\ length t8 = 8%nat;
f_loc   : bytes_at rsegs m 0x77bd0 (le8 (wz 0x97ec8));
f_ceil  : alloc_ceiling = usp0 - 8388608
}.

#[using="Type"] Lemma DF_of_entry usp0 pp tid path m : drv_entry usp0 pp tid path m -> DF usp0 pp tid path m.
Proof. intros H. destruct H. constructor; try assumption. apply stage_stk_of_none. assumption. Qed.

#[using="Type"] Lemma rheap_pres_stk_data : forall LB SP (m m' : mem) lo hi,
rheap_pres LB SP m m' -> stk rsegs m lo hi -> 0x62000 <= lo -> hi <= 0x99000 ->
(hi <= RCTX \/ RCTX + 928 <= lo) -> (hi <= RERRNO \/ RERRNO + 4 <= lo) -> stk rsegs m' lo hi.
Proof.
intros LB SP m m' lo hi HP ST H1 H2 H3 H4. destruct ST as (S0 & S1 & SW). split; [exact S0|]. split; [exact S1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(right; left; unfold ralloc_static; lia)) as [E W]. destruct (SW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

#[using="Type"] Lemma bytes_at_agree : forall (m m' : mem) a bs,
bytes_at rsegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at rsegs m' a bs.
Proof.
intros m m' a bs (H1 & H2 & H3) E. split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold mrd in *. rewrite E by lia. apply H3. exact Hi.
Qed.

#[using="Type"] Lemma DF_alloc usp0 pp tid path m m' LB0 SP lo :
DF usp0 pp tid path m ->
rheap_pres LB0 SP m m' -> mem_inv rsegs m' -> stk rsegs m' lo SP ->
lo = usp0 - 8388608 -> lo <= SP <= usp0 - 120 ->
DF usp0 pp tid path m'.
Proof.
intros [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL] HP MI' ST' -> HSP.
assert (EQ : forall x, (SP <= x \/ (0x62000 <= x < 0x99000 /\ ~ (RCTX <= x < RCTX + 928) /\ ~ (RERRNO <= x < RERRNO + 4))) ->
0 <= x < 2^64 -> m' (wa x) = m (wa x)).
{ intros x Hx Hr. apply (HP x Hr). destruct Hx as [Hx|Hx]; [left; exact Hx| right; left].
unfold ralloc_static. split; [lia|]. intros [X|X]; tauto. }
constructor.
- exact SPB.
- apply (stk_merge rsegs m' _ SP); [exact ST'| | lia]. eapply rheap_pres_stk; [exact HP| | lia].
destruct (stk_split rsegs m _ SP _ STK ltac:(lia)) as [_ S2]. exact S2.
- eapply rheap_pres_rw_cells; [exact HP| exact FRM| left; lia].
- destruct TID as [T1 T2]. split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RCTX, RERRNO; lia| lia].
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RCTX, RERRNO; lia| lia].
- eapply pris_transport; [exact PRS| exact MI'|]. intros x Hx N1 N2. apply EQ; [right; tauto| lia].
- pose proof stage_bounds as (SB1 & SB2 & SB3 & SB4). eapply rheap_pres_stk_data; [exact HP| exact STG| exact SB1| exact SB2| exact SB3| exact SB4].
- destruct PTH as (P1 & P2 & P3). split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
apply EQ; [left; lia| lia].
- destruct PTH as (P1 & P2 & P3). destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2].
eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; [left; lia| lia].
- eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RCTX, RERRNO; lia| lia].
- exact CEIL.
Qed.

Definition leaf_oom_stmt (usp0 pp tid : Z) (path : list byte) : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) A LB (pc : Z),
DF usp0 pp tid path m -> HEAPc usp0 A LB m md ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
(pc = 0x20dec \/ pc = 0x20e2c) ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR ra (Z_to_bv 64 (usp0 - 128)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)) md) (t_die msg_oom (m_fs md)).

Definition leaf_refused_stmt (usp0 pp tid : Z) (path : list byte) : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) A LB,
DF usp0 pp tid path m -> HEAPc usp0 A LB m md ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR ra (Z_to_bv 64 (usp0 - 128)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x20dcc) fc None m (seg_rom rsegs)) md) (t_die msg_refused (m_fs md)).

Definition leaf_readerr_stmt (usp0 pp tid : Z) (path : list byte) : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) A LB,
DF usp0 pp tid path m -> HEAPc usp0 A LB m md -> path = QBxa.Mq5.dot_path ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR ra (Z_to_bv 64 (usp0 - 128)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pp) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x20db0) fc None m (seg_rom rsegs)) md) (t_die (msg_read_error path) (m_fs md)).
End AmbL.
