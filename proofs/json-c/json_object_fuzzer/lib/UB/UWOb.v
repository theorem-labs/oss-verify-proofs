(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qod2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qod2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5Hp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5Hp. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtkK.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTWd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTWd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQ4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQ4u. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDfH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDfH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section GetRall.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
Notation R := (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
#[using="Type"] Lemma g1 : QsRG.Mq0.getr R 1 = x1. Proof. reflexivity. Qed.
#[using="Type"] Lemma g2 : QsRG.Mq0.getr R 2 = x2. Proof. reflexivity. Qed.
#[using="Type"] Lemma g3 : QsRG.Mq0.getr R 3 = x3. Proof. reflexivity. Qed.
#[using="Type"] Lemma g4 : QsRG.Mq0.getr R 4 = x4. Proof. reflexivity. Qed.
#[using="Type"] Lemma g8 : QsRG.Mq0.getr R 8 = x8. Proof. reflexivity. Qed.
#[using="Type"] Lemma g9 : QsRG.Mq0.getr R 9 = x9. Proof. reflexivity. Qed.
#[using="Type"] Lemma g11 : QsRG.Mq0.getr R 11 = x11. Proof. reflexivity. Qed.
#[using="Type"] Lemma g18 : QsRG.Mq0.getr R 18 = x18. Proof. reflexivity. Qed.
#[using="Type"] Lemma g19 : QsRG.Mq0.getr R 19 = x19. Proof. reflexivity. Qed.
#[using="Type"] Lemma g20 : QsRG.Mq0.getr R 20 = x20. Proof. reflexivity. Qed.
#[using="Type"] Lemma g21 : QsRG.Mq0.getr R 21 = x21. Proof. reflexivity. Qed.
#[using="Type"] Lemma g22 : QsRG.Mq0.getr R 22 = x22. Proof. reflexivity. Qed.
#[using="Type"] Lemma g23 : QsRG.Mq0.getr R 23 = x23. Proof. reflexivity. Qed.
#[using="Type"] Lemma g24 : QsRG.Mq0.getr R 24 = x24. Proof. reflexivity. Qed.
#[using="Type"] Lemma g25 : QsRG.Mq0.getr R 25 = x25. Proof. reflexivity. Qed.
#[using="Type"] Lemma g26 : QsRG.Mq0.getr R 26 = x26. Proof. reflexivity. Qed.
#[using="Type"] Lemma g27 : QsRG.Mq0.getr R 27 = x27. Proof. reflexivity. Qed.
End GetRall.

Lemma stk_ok_of_stk : forall (m : mem) lo (sp : word), stk rsegs m lo (bv_unsigned sp) ->
stk_ok rsegs m sp (bv_unsigned sp - lo).
Proof.
intros m lo sp (S1 & S2 & S3) a n H1 H2. pose proof (bv_unsigned_in_range 64 a).
rewrite <- (Z_to_bv_bv_unsigned a). apply (QuJV.Mq0.wr_at_store_ok rsegs m (bv_unsigned a) n).
split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S3 (bv_unsigned a + i) ltac:(lia))).
Qed.

Lemma zero_lines_snoc' : forall k, zero_lines k ++ [Z_to_bv 8 0x30; Z_to_bv 8 0x0a] = zero_lines (S k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines app]. rewrite IH. reflexivity. Qed.

Section AmbP.
Context {AMB : Amb}.
#[using="Type"] Theorem printfk_ok : forall usp0, printfk_stmt usp0.
Proof.
intros usp0. unfold printfk_stmt. intros until K. cbv zeta. intros MOK Hk SW IMG ST MI SPB SPA Htp HK. subst tp.
destruct IMG as (IM1 & HEX & IM1b & IM2 & GOT & CAN).
set (sp := Z_to_bv 64 (usp0 - 208)).
assert (U : bv_unsigned sp = usp0 - 208) by (subst sp; apply unsigned_lit; lia).
set (R := mkR (Z_to_bv 64 PRINTF_RET) sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
assert (PH : pfH m sp (0x98350 + 2 * Z.of_nat k) (bv_unsigned rc_canary)).
{ destruct SW as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13]. unfold Um90.Mq0.cell in *.
constructor; rewrite ?U; try lia; try assumption.
- replace (usp0 - 208) with (usp0 + (-13) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
- destruct (stk_split rsegs m (usp0 - 208 - 1536) (usp0 - 208 - 1056) (usp0 - 208) ST ltac:(lia)) as [_ ST1].
replace PF_FR with (bv_unsigned sp - (usp0 - 208 - 1056)) by (rewrite U; unfold PF_FR; lia). apply stk_ok_of_stk. rewrite U. exact ST1.
- exact (QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ HEX).
- exact (QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ GOT).
- rewrite Z_to_bv_bv_unsigned. exact (QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ CAN).
- pose proof (u64_range rc_canary) as RC. lia. }
destruct (printf0_buffered (fF:=F) (fC:=fc) R m (seg_rom rsegs) sp _ (bv_unsigned rc_canary) PH (g1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (g2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (g11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
as (R' & m' & STEPS & KCS & [FM GR] & B2 & WP & FL).

change (QEpW.MS R F (Z_to_bv 64 PRINTF_SYM) fc None m (seg_rom rsegs)) with (@mkst F fc R (Z_to_bv 64 PRINTF_SYM) m (seg_rom rsegs)).
unfold PRINTF_SYM. eapply (QRjH.rz_msteps rsegs); [exact (proj1 MOK)| exact (proj2 MOK)| exact STEPS|].

change (mkst R' (Z_to_bv 64 0x20f30) m' (seg_rom rsegs)) with (QEpW.MS R' F (Z_to_bv 64 0x20f30) fc None m' (seg_rom rsegs)).
apply (realizes_canon rsegs). rewrite canonR_getr.
rewrite (KCS 2%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 3%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 4%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 8%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 9%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 18%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 19%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 20%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 21%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 22%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 23%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 24%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 25%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 26%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
rewrite (KCS 27%bv ltac:(cbn; repeat (first [left; reflexivity| right]))).
subst R.
rewrite ?g1, ?g2, ?g3, ?g4, ?g8, ?g9, ?g18, ?g19, ?g20, ?g21, ?g22, ?g23, ?g24, ?g25, ?g26, ?g27.
set (w := 0x98350 + 2 * Z.of_nat k) in *.
assert (EQ : forall x, 0 <= x < 2^64 -> ~ (usp0 - 208 - 1056 <= x < usp0 - 208) -> ~ (0x66e28 <= x < 0x66e2c) ->
~ (0x66e50 <= x < 0x66e58) -> ~ (w <= x < w + 2) -> m' (wa x) = m (wa x)).
{ intros x Hx N1 N2 N3 N4. apply FM. cbn [QBxa.Mq1.outside]. unfold in_rng, wa. rewrite !unsigned_lit by lia. lia. }
pose proof (wmono_of_grows _ _ GR) as WM.
assert (MI' : mem_inv rsegs m').
{ eapply mem_inv_of_agree; [exact MI|]. intros x Hx. pose proof (bv_unsigned_in_range 64 x). rewrite <- (Z_to_bv_bv_unsigned x). apply EQ; unfold bv_modulus in *; lia. }
subst sp. eapply HK.
- intros x OUT. pose proof (bv_unsigned_in_range 64 x). rewrite <- (Z_to_bv_bv_unsigned x). apply EQ; [unfold bv_modulus in *; lia| | | |];
unfold PFW in OUT; cbn [QWxq.outside] in OUT; lia.
- exact WM.
- exact MI'.
- eapply stk_grows; [exact ST| exact GR| lia].
- destruct SW as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13]. unfold Um90.Mq0.cell in *.
assert (AG : forall segs a n, 0 <= a -> a + Z.of_nat n <= 0x99000 ->
(a + Z.of_nat n <= 0x66e28 \/ 0x66e2c <= a) -> (a + Z.of_nat n <= 0x66e50 \/ 0x66e58 <= a) -> (a + Z.of_nat n <= w \/ w + 2 <= a) ->
QsRG.Mq0.rdn segs m' (Z_to_bv 64 a) n = QsRG.Mq0.rdn segs m (Z_to_bv 64 a) n).
{ intros segs a n H1 H2 H3 H4 H5. apply rdn_agree; [lia| lia|]. intros x Hx. apply EQ; lia. }
assert (Hw : 0x98350 <= w /\ w + 2 <= 0x98350 + 8) by (subst w; lia).
constructor; unfold Um90.Mq0.cell; try (rewrite AG by (cbn; lia); assumption).
+ exact FL.
+ replace (0x98350 + 2 * Z.of_nat (S k)) with (w + 2) by lia. exact WP.
+ replace (2 * S k)%nat with (2 * k + 2)%nat by lia. rewrite <- zero_lines_snoc'.
apply QUeZ.rdn_app_Z; [| | lia| lia].
* rewrite AG by lia. exact F13.
* replace (0x98350 + Z.of_nat (2 * k)) with w by lia. exact B2.
Qed.
End AmbP.
