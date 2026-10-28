(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW QWxq QlEo QbVh QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz Uv2Y UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz QRjH QBxa QSpR QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90 U9ch UmsF UFeQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD QqWy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj Uc9I. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qod2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4FC Uqqm UDH9 U5Hp UtkK UBap. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import QEpW QWxq QlEo QbVh QZDE.
Import UKNz Uv2Y UXT6.
Import QsRG.Mq0 Qnhz.Mq0 QRjH QBxa.Mq5 QSpR.Mq1 QuJV.Mq0 QRjH.Mq3.
Import Um90.Mq0 U9ch.Mq0 UmsF.Mq0 UFeQ.Mq0.
Import QeZD QqWy.
Import UmAj Uc9I.
Import Qod2.
Import U4FC Uqqm UDH9 U5Hp U5Hp.Mq0 UtkK.Mq0 UtkK UBap.Mq0.
Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section GetRall.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
Notation R := (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
#[using="Type"] Lemma getr_mk1 : QsRG.Mq0.getr R 1 = x1. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk2 : QsRG.Mq0.getr R 2 = x2. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk3 : QsRG.Mq0.getr R 3 = x3. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk4 : QsRG.Mq0.getr R 4 = x4. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk5 : QsRG.Mq0.getr R 5 = x5. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk6 : QsRG.Mq0.getr R 6 = x6. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk7 : QsRG.Mq0.getr R 7 = x7. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk8 : QsRG.Mq0.getr R 8 = x8. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk9 : QsRG.Mq0.getr R 9 = x9. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk10 : QsRG.Mq0.getr R 10 = x10. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk11 : QsRG.Mq0.getr R 11 = x11. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk12 : QsRG.Mq0.getr R 12 = x12. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk13 : QsRG.Mq0.getr R 13 = x13. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk14 : QsRG.Mq0.getr R 14 = x14. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk15 : QsRG.Mq0.getr R 15 = x15. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk16 : QsRG.Mq0.getr R 16 = x16. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk17 : QsRG.Mq0.getr R 17 = x17. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk18 : QsRG.Mq0.getr R 18 = x18. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk19 : QsRG.Mq0.getr R 19 = x19. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk20 : QsRG.Mq0.getr R 20 = x20. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk21 : QsRG.Mq0.getr R 21 = x21. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk22 : QsRG.Mq0.getr R 22 = x22. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk23 : QsRG.Mq0.getr R 23 = x23. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk24 : QsRG.Mq0.getr R 24 = x24. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk25 : QsRG.Mq0.getr R 25 = x25. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk26 : QsRG.Mq0.getr R 26 = x26. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk27 : QsRG.Mq0.getr R 27 = x27. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk28 : QsRG.Mq0.getr R 28 = x28. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk29 : QsRG.Mq0.getr R 29 = x29. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk30 : QsRG.Mq0.getr R 30 = x30. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_mk31 : QsRG.Mq0.getr R 31 = x31. Proof. reflexivity. Qed.
End GetRall.

Ltac rdn_img_solve := lazymatch goal with |- ?l = Some ?r =>
let v := eval vm_compute in l in lazymatch v with Some ?bs =>
apply (rdn_val_eq l bs r); [vm_compute; reflexivity | vm_compute; reflexivity] end end.

Section HdrLeaf.
Context {AMB : Amb}.
Variables (usp0 tid : Z) (ppw : word) (path : list byte) (data : list byte) (fs : Fs.Fs).
Notation pp := (bv_unsigned ppw).
Variables (fds0 : list (word * FdEntry)).
Let sp0w : word := Z_to_bv 64 usp0.

#[using="sp0w"] Theorem hdr_leaf_ok : hdr_leaf_stmt usp0 tid ppw path.
Proof.
unfold hdr_leaf_stmt. intros until fc. intros Hpc HK D HP (errv & ERR) Hgp Htp FD2 CONT. subst gp tp.
destruct (leaf_facts usp0 pp tid path m A [(buf, cap)] md D HP) as (VSP & U & STW & IMG & CT & HT & CS & CC & CPG).
pose proof (heapc_model_ok usp0 _ _ _ _ HP) as [Hh Hl].
pose proof (f_sp _ _ _ _ _ D) as SPB.
match goal with |- realizes _ (mkCfg (QEpW.MS ?R0 F ?pcw fc None m ?ro) _) _ =>
change (QEpW.MS R0 F pcw fc None m ro) with (@mkst F fc R0 pcw m ro); set (R := R0) end.
eapply (ref_hdr_msg (fF:=F) (fC:=fc) sp0w [] md VSP Hh Hl FD2 tid (bv_unsigned rc_canary) R m); try assumption;
try (subst R; cbn [getr]; rewrite ?U; reflexivity).
intros R' M' G10 G1 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 [PA PG PW1 PW2 PW3 PR1 PR2].
change (mkst R' (Z_to_bv 64 0x520b4) M' (seg_rom RSEGS)) with (QEpW.MS R' F (Z_to_bv 64 0x520b4) fc None M' (seg_rom RSEGS)).
apply (realizes_canon RSEGS). rewrite canonR_getr.
rewrite G10, G1, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27, U.
subst R. rewrite ?getr_mk1, ?getr_mk2, ?getr_mk3, ?getr_mk4, ?getr_mk5, ?getr_mk6, ?getr_mk7, ?getr_mk8, ?getr_mk9, ?getr_mk10, ?getr_mk11, ?getr_mk12, ?getr_mk13, ?getr_mk14, ?getr_mk15, ?getr_mk16, ?getr_mk17, ?getr_mk18, ?getr_mk19, ?getr_mk20, ?getr_mk21, ?getr_mk22, ?getr_mk23, ?getr_mk24, ?getr_mk25, ?getr_mk26, ?getr_mk27, ?getr_mk28, ?getr_mk29, ?getr_mk30, ?getr_mk31.
pose proof (heapc_mem_inv usp0 _ _ _ _ HP) as MI.
assert (EQ : forall x, 0 <= x < 2^64 -> ~ (usp0 - 8388608 <= x < usp0 - 128) ->
~ (0x66d40 <= x < 0x66d50) -> ~ (0x66d58 <= x < 0x66d68) -> ~ (0x66d70 <= x < 0x66d78) -> ~ (0x66dc0 <= x < 0x66dc4) ->
M' (wa x) = m (wa x)).
{ unfold sp0w in PA. rewrite !(unsigned_lit usp0) in PA by lia. intros x Hx N1 N2 N3 N4 N5. apply PA; unfold wa; rewrite unsigned_lit by lia; lia. }
pose proof (wmono_of_grows _ _ PG) as WM.
assert (MI' : mem_inv rsegs M').
{ eapply mem_inv_of_agree; [exact MI|]. intros x Hx. pose proof (bv_unsigned_in_range 64 x). rewrite <- (Z_to_bv_bv_unsigned x). apply EQ; unfold bv_modulus in *; lia. }
unfold FREE_SYM, MAIN_FREE_RET in CONT. apply CONT.
-
destruct D as [SPB' STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL]. destruct PTH as (P1 & P2 & P3). destruct TID as [T1 T2]. constructor.
+ exact SPB'.
+ eapply stk_grows; [exact STK| exact PG| lia].
+ destruct FRM as [[WF BA] WR]. split; [split; [exact WF|]|].
* eapply bytes_at_agree; [exact BA|]. intros x Hx. rewrite cells_bytes_length in Hx by exact WF. cbn in Hx. apply EQ; lia.
* eapply wr_at_transport; [exact WR| exact WM].
+ split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; lia.
+ eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; lia.
+ pose proof (pris_prisx _ PRS) as PX. unfold prisx in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PX _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0. apply EQ;
unfold PRIS2 in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
+ eapply stk_img_agree; [exact STG|]. intros a Ha. unfold RSTAGE, RSTAGE_SZ in Ha. apply EQ; lia.
+ split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; lia.
+ destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2]. eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; lia.
+ eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; lia.
+ exact CEIL.
+ exists false. eapply atx_state_agree; [apply pris_atx_idle; exact PRS|]. intros x Hx. unfold atx_cell in Hx. apply EQ; lia.
-
eapply (heapc_frame usp0); [exact HP| | exact WM| exact MI']. intros a Ha NCW.
assert (NS : ~ (usp0 - 8388608 <= a < usp0 - 128)) by (intros X; apply NCW; right; left; pose proof (f_ceil _ _ _ _ _ D); unfold alloc_ceiling in *; lia).
assert (NF : ~ (0x66d38 <= a < 0x66e20)) by (intros X; apply NCW; right; right; unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR; lia).
apply EQ; lia.
- exists errv. destruct ERR as [[WF BA] WR]. split; [split; [exact WF|]| eapply wr_at_transport; [exact WR| exact WM]].
eapply bytes_at_agree; [exact BA|]. intros x Hx. cbn in Hx. unfold RERRNO, RATP in Hx. apply EQ; lia.
- intros a Ha. rewrite EQ by lia. apply (pris_pointwise m (f_pris _ _ _ _ _ D)). lia.
- unfold UFeQ.Mq0.file_clean. unfold cell in *. repeat split; try assumption.
erewrite (rdn_agree _ m M'); [| lia| cbn; lia| intros; apply EQ; lia].
pose proof (pris_pointwise m (f_pris _ _ _ _ _ D)) as PW.
rewrite (QBxa.Mq7.rdn_img rsegs m _ _ 0x66d38 0x66e20); try lia; [rdn_img_solve|]. intros i Hi. apply (PW i). lia.
Qed.
End HdrLeaf.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UotY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UotY. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGNu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGNu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujk3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QwQw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwQw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaOl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UaOl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udkw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYot. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4FC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4FC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uqqm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uqqm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5Hp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5Hp. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtkK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtkK.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBap.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.

Local Ltac ivs_lia := repeat (lazymatch goal with |- _ \/ _ => fail | |- _ => constructor end); cbn [fst snd]; lia.
Open Scope Z_scope.

Section AmbT.
Context {AMB : Amb}.

Definition PRINTF_SYM : Z := 0x20fdc.
Definition PRINTF_RET : Z := 0x20f30.
Definition TLOOP : Z := 0x20f0c.

Record STDOUTW (m : mem) (k : nat) : Prop := MKSW {
sw_flags : Um90.Mq0.cell m 0x66e28 4 5;
sw_rpos  : Um90.Mq0.cell m 0x66e30 8 0;
sw_rend  : Um90.Mq0.cell m 0x66e38 8 0;
sw_wend  : Um90.Mq0.cell m 0x66e48 8 0x98750;
sw_wpos  : Um90.Mq0.cell m 0x66e50 8 (0x98350 + 2 * Z.of_nat k);
sw_wbase : Um90.Mq0.cell m 0x66e60 8 0x98350;
sw_write : Um90.Mq0.cell m 0x66e70 8 0x551dc;
sw_buf   : Um90.Mq0.cell m 0x66e80 8 0x98350;
sw_bsz   : Um90.Mq0.cell m 0x66e88 8 1024;
sw_fd    : Um90.Mq0.cell m 0x66ea0 4 1;
sw_lock  : Um90.Mq0.cell m 0x66eb4 4 4294967295;
sw_lbf   : Um90.Mq0.cell m 0x66eb8 4 4294967295;
sw_bytes : QsRG.Mq0.rdn rsegs m (Z_to_bv 64 0x98350) (2 * k) = Some (zero_lines k) }.

#[using="Type"] Lemma hglob_P_rpres : forall LB SP (m m' : mem), rheap_pres LB SP m m' -> hglob_P m -> hglob_P m'.
Proof.
intros LB SP m m' PRES G. eapply hglob_P_pointwise; [exact G|]. intros a Ha. unfold hglob_rng_P in Ha.
apply PRES; [lia|]. right; left. unfold ralloc_static, RCTX, RERRNO. lia.
Qed.

Definition PFIMG (m : mem) : Prop :=
(forall a, 0x10000 <= a < 0x658d8 -> m (wa a) = None) /\ bytes_at rsegs m 0x658d8 (le8 (Z_to_bv 64 0x66a30))
/\ (forall a, 0x658e0 <= a < 0x659d0 -> m (wa a) = None) /\ (forall a, 0x659d8 <= a < 0x66000 -> m (wa a) = None)
/\ bytes_at rsegs m 0x659d0 (le8 (wz 0x97e70)) /\ bytes_at rsegs m 0x97e70 (le8 rc_canary).

Definition PFW (sp : Z) : list ivl := [(sp - 1536, sp); (0x66e28, 0x66f10); (0x98350, 0x98750)].

Definition printf1_stmt (usp0 : Z) : Prop :=
forall (gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (K : TSet),
let sp := usp0 - 208 in
model_ok md -> fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
(forall a, 0x66e28 <= a < 0x66f10 -> m (wa a) = None) -> PFIMG m ->
stk rsegs m (sp - 1536) sp -> mem_inv rsegs m ->
0x7fff80000000 <= usp0 <= 0x800000000000 -> usp0 mod 16 = 0 ->
tp = Z_to_bv 64 0x77c00 ->
K [] ->
(forall (m' : mem) (F' : bvmap 5 word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch (PFW sp) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (sp - 1536) sp ->
STDOUTW m' 0 ->
realizes rsegs (mkCfg (MS (mkR ra' (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 PRINTF_RET) fc None m' (seg_rom rsegs)) md) K) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 PRINTF_RET) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PRINTF_SYM) fc None m (seg_rom rsegs)) md)
(t_emit (W 1 (zero_lines 1)) K).

Definition printfk_stmt (usp0 : Z) : Prop :=
forall (k : nat) (gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (K : TSet),
let sp := usp0 - 208 in
model_ok md -> (k <= 2)%nat ->
STDOUTW m k -> PFIMG m ->
stk rsegs m (sp - 1536) sp -> mem_inv rsegs m ->
0x7fff80000000 <= usp0 <= 0x800000000000 -> usp0 mod 16 = 0 ->
tp = Z_to_bv 64 0x77c00 ->
(forall (m' : mem) (F' : bvmap 5 word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch (PFW sp) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (sp - 1536) sp ->
STDOUTW m' (S k) ->
realizes rsegs (mkCfg (MS (mkR ra' (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 PRINTF_RET) fc None m' (seg_rom rsegs)) md) K) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 PRINTF_RET) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PRINTF_SYM) fc None m (seg_rom rsegs)) md) K.

Definition clearr (m : mem) (lo hi : Z) : Prop := forall a, lo <= a < hi -> m (wa a) = None.

#[using="Type"] Lemma clearr_munch : forall m m' lo hi W, clearr m lo hi -> munch W m m' ->
Forall (fun iv => snd iv <= lo \/ hi <= fst iv) W -> 0 <= lo -> hi <= 2^64 -> clearr m' lo hi.
Proof.
intros m m' lo hi W C MU FW H0 H1 a Ha. rewrite <- (C a Ha). apply MU. unfold wa. rewrite unsigned_lit by lia.
clear -FW Ha. induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in FW as [F1 FW]. cbn [fst snd] in *. split; [lia| apply IH; exact FW].
Qed.

#[using="Type"] Lemma clearr_img_agree : forall m m' lo hi, clearr m lo hi -> img_agree m m' -> 0x62000 <= lo -> hi <= 0x99000 ->
(hi <= RCTX \/ RCTX + 928 <= lo) -> (hi <= RERRNO \/ RERRNO + 4 <= lo) -> clearr m' lo hi.
Proof. intros m m' lo hi C IA H1 H2 H3 H4 a Ha. rewrite IA by lia. apply C. exact Ha. Qed.

#[using="Type"] Lemma data_wr_at : forall (m : mem) a n, 0x66000 <= a -> a + Z.of_nat n <= 0x99000 -> wr_at rsegs m a (Z.of_nat n).
Proof.
intros m a n H1 H2. apply (store_ok_wr_at rsegs m a n); [lia| lia|]. apply UFeQ.Mq0.store_ok_data; rewrite unsigned_lit by lia; lia.
Qed.

#[using="Type"] Lemma rw_cells_img_agree : forall (m m' : mem) A cs, rw_cells rsegs m A cs -> img_agree m m' ->
0x66000 <= A -> A + Z.of_nat (cells_size cs) <= 0x99000 ->
(A + Z.of_nat (cells_size cs) <= RCTX \/ RCTX + 928 <= A) -> (A + Z.of_nat (cells_size cs) <= RERRNO \/ RERRNO + 4 <= A) ->
rw_cells rsegs m' A cs.
Proof.
intros m m' A cs [[WF BA] WR] IA H1 H2 H3 H4. split; [split; [exact WF|]|].
- eapply bytes_at_agree; [exact BA|]. rewrite cells_bytes_length by exact WF. intros x Hx. apply IA; lia.
- apply data_wr_at; lia.
Qed.

Notation presx LB SP m m' := (heap_presx S4L (xtgt S4L) LB SP m m').

#[using="Type"] Lemma presx_static : forall LB SP m m' a, presx LB SP m m' -> 0x62000 <= a < 0x99000 ->
~ (0x97e90 <= a < 0x97ef8) -> ~ (0x97f78 <= a < 0x98320) -> ~ (0x659d0 <= a < 0x659d8) -> ~ (0x97e70 <= a < 0x97e78) ->
~ (0x77bf0 <= a < 0x77bf8) -> ~ (0x77b5c <= a < 0x77b60) -> ~ (0x66a40 <= a < 0x66a44) -> ~ (0x66f20 <= a < 0x66f28) ->
~ (0x77bd0 <= a < 0x77bd8) -> ~ (0x658d8 <= a < 0x658e0) -> ~ (0x66a30 <= a < 0x66a38) ->
~ (0x76fbc <= a < 0x770bc) ->
m' (wa a) = m (wa a).
Proof.
intros LB SP m m' a HP Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12. refine (proj1 (HP a ltac:(lia) _)). right; left. split.
- cbn. unfold s4_client_static. lia.
- unfold xtgt, T_LOCCELL. cbn. unfold s4_volatile. lia.
Qed.

#[using="Type"] Lemma clearr_presx : forall LB SP m m' lo hi, clearr m lo hi -> presx LB SP m m' -> 0x62000 <= lo -> hi <= 0x99000 ->
(forall a, lo <= a < hi -> ~ (0x97e90 <= a < 0x97ef8) /\ ~ (0x97f78 <= a < 0x98320) /\ ~ (0x659d0 <= a < 0x659d8) /\ ~ (0x97e70 <= a < 0x97e78)
/\ ~ (0x77bf0 <= a < 0x77bf8) /\ ~ (0x77b5c <= a < 0x77b60) /\ ~ (0x66a40 <= a < 0x66a44) /\ ~ (0x66f20 <= a < 0x66f28) /\ ~ (0x77bd0 <= a < 0x77bd8)
/\ ~ (0x658d8 <= a < 0x658e0) /\ ~ (0x66a30 <= a < 0x66a38) /\ ~ (0x76fbc <= a < 0x770bc)) ->
clearr m' lo hi.
Proof.
intros LB SP m m' lo hi C HP H1 H2 OK a Ha. destruct (OK a Ha) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
rewrite (presx_static LB SP m m' a HP ltac:(lia) N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12). apply C. exact Ha.
Qed.

Definition FLAG : Z := 0x76f84.
#[using="Type"] Lemma DFX_harness : forall usp0 pp tid path LB (m m1 m' m2 : mem),
DFX usp0 pp tid path m ->
munch [(FLAG, FLAG + 1)] m m1 -> wmono rsegs m m1 ->
presx LB (usp0 - 208) m1 m' ->
munch [(FLAG, FLAG + 1)] m' m2 -> wmono rsegs m' m2 -> mem_inv rsegs m2 ->
stk rsegs m2 (usp0 - 8388608) (usp0 - 208) -> bytes_at rsegs m2 0x77bd0 (le8 (wz 0x97ec8)) ->
QsRG.Mq0.rdn rsegs m2 (Z_to_bv 64 FLAG) 1%nat = Some [Z_to_bv 8 0] ->
DFX usp0 pp tid path m2.
Proof.
intros usp0 pp tid path LB m m1 m' m2 [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL ATX] MU1 WM1 HP MU2 WM2 MI2 ST2 LOC2 FL.
unfold FLAG in *.
assert (O1 : forall x, x <> 0x76f84 -> outside [(0x76f84, 0x76f84 + 1)] x) by (intros x Hx; cbn; lia).
assert (E1 : forall x, x <> 0x76f84 -> 0 <= x < 2^64 -> m1 (wa x) = m (wa x)).
{ intros x Hx Hr. apply MU1. unfold wa. rewrite unsigned_lit by lia. apply O1. exact Hx. }
assert (E3 : forall x, x <> 0x76f84 -> 0 <= x < 2^64 -> m2 (wa x) = m' (wa x)).
{ intros x Hx Hr. apply MU2. unfold wa. rewrite unsigned_lit by lia. apply O1. exact Hx. }
assert (UP : forall x, usp0 - 208 <= x -> 0 <= x < 2^64 -> m2 (wa x) = m (wa x)).
{ intros x Hx Hr. rewrite E3 by lia. rewrite (proj1 (HP x Hr ltac:(left; lia))). apply E1; lia. }
assert (STAT : forall x, 0x62000 <= x < 0x99000 -> x <> 0x76f84 ->
~ (0x97e90 <= x < 0x97ef8) -> ~ (0x97f78 <= x < 0x98320) -> ~ (0x659d0 <= x < 0x659d8) -> ~ (0x97e70 <= x < 0x97e78) ->
~ (0x77bf0 <= x < 0x77bf8) -> ~ (0x77b5c <= x < 0x77b60) -> ~ (0x66a40 <= x < 0x66a44) -> ~ (0x66f20 <= x < 0x66f28) ->
~ (0x77bd0 <= x < 0x77bd8) -> ~ (0x658d8 <= x < 0x658e0) -> ~ (0x66a30 <= x < 0x66a38) -> ~ (0x76fbc <= x < 0x770bc) ->
m2 (wa x) = m (wa x)).
{ intros x Hx NF N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12. rewrite E3 by lia.
rewrite (presx_static LB _ m1 m' x HP Hx N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12). apply E1; lia. }
destruct PTH as (P1 & P2 & P3). destruct TID as [T1 T2].
constructor.
- exact SPB.
- apply (stk_merge rsegs m2 _ (usp0 - 208)); [| | lia].
+ exact ST2.
+ destruct (stk_split rsegs m _ (usp0 - 208) _ STK ltac:(lia)) as [_ S2].
destruct S2 as (A0 & A1 & AW). split; [exact A0|]. split; [exact A1|].
intros a Ha. destruct (AW a Ha) as [Wv [b Hb]]. split.
* apply WM2. refine (proj2 (HP a ltac:(lia) ltac:(left; lia)) _). apply WM1. exact Wv.
* exists b. unfold mrd in *. rewrite UP by lia. exact Hb.
- destruct FRM as [[WF BA] WR]. split; [split; [exact WF|]|].
+ eapply bytes_at_agree; [exact BA|]. intros x Hx. rewrite cells_bytes_length in Hx by exact WF. cbn in Hx. apply UP; lia.
+ eapply wr_at_transport; [| exact WM2]. eapply (heap_presx_wr_at S4L); [exact HP| | left; cbn; lia]. eapply wr_at_transport; [exact WR| exact WM1].
- split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply STAT; lia.
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply STAT; lia.
- unfold prisx in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0.
destruct (Z.lt_ge_cases a 0x62000) as [LT|GE].
+ apply mem_inv_text_none; [exact MI2|]. unfold PRIS2 in IN. cbn in IN.
repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
+ rewrite <- E0. apply STAT; unfold PRIS2 in IN; cbn in IN;
repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
- destruct STG as (G0 & G1 & GW). split; [exact G0|]. split; [exact G1|]. intros a Ha.
assert (E : m2 (wa a) = m (wa a)) by (apply STAT; unfold RSTAGE, RSTAGE_SZ in Ha; lia).
destruct (GW a Ha) as [Wv [b Hb]]. split.
+ apply WM2. refine (proj2 (HP a ltac:(unfold RSTAGE, RSTAGE_SZ in Ha; lia) _) _); [| apply WM1; exact Wv].
right; left. split; [cbn; unfold s4_client_static, RSTAGE, RSTAGE_SZ in *; lia| unfold xtgt, T_LOCCELL; cbn; unfold s4_volatile, RSTAGE, RSTAGE_SZ in *; lia].
+ exists b. unfold mrd in *. rewrite E. exact Hb.
- split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply UP; lia.
- destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2].
eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply UP; lia.
- exact LOC2.
- exact CEIL.
- destruct ATX as [armed AT]. exists armed. unfold UFeQ.Mq0.atx_state in *.
assert (R : forall a n, (forall x, a <= x < a + Z.of_nat n -> (0x97c4c <= x < 0x97c70) \/ (0x97d68 <= x < 0x97d70)) -> 0 <= a -> a + Z.of_nat n <= 0x99000 ->
QsRG.Mq0.rdn rsegs m2 (Z_to_bv 64 a) n = QsRG.Mq0.rdn rsegs m (Z_to_bv 64 a) n).
{ intros a n H H0 H1. apply QsRG.Mq0.rdn_ext; rewrite unsigned_lit by lia; [lia|].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply STAT; pose proof (H (bv_unsigned x) Hx); lia. }
destruct armed.
+ destruct AT as (A1 & A2 & A3 & A4 & A5 & A6 & A7). rewrite !R by (first [lia | cbn; intros; lia]).
repeat split; try assumption.
+ destruct AT as (A1 & A2). rewrite !R by (first [lia | cbn; intros; lia]). split; assumption.
Qed.

Definition ARMW (usp0 : Z) : list ivl :=
[(usp0 - 256, usp0 - 128); (0x76f80, 0x76f81); (0x97c50, 0x97c54); (0x97c58, 0x97c60); (0x97c68, 0x97c70); (0x97d68, 0x97d70)].
#[using="Type"] Lemma DFX_arm : forall usp0 pp tid path m m',
DFX usp0 pp tid path m -> munch (ARMW usp0) m m' -> wmono rsegs m m' -> stk rsegs m' (usp0 - 8388608) (usp0 - 128) ->
UFeQ.Mq0.atx_state true m' ->
DFX usp0 pp tid path m'.
Proof.
intros usp0 pp tid path m m' D MU WM ST' AT. destruct D as [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL _].
assert (OUT : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ x <> 0x76f80 /\ ~ (0x97c50 <= x < 0x97c54) /\ ~ (0x97c58 <= x < 0x97c60)
/\ ~ (0x97c68 <= x < 0x97c70) /\ ~ (0x97d68 <= x < 0x97d70))) -> outside (ARMW usp0) x).
{ intros x Hx. cbn. lia. }
assert (EQ : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ x <> 0x76f80 /\ ~ (0x97c50 <= x < 0x97c54) /\ ~ (0x97c58 <= x < 0x97c60)
/\ ~ (0x97c68 <= x < 0x97c70) /\ ~ (0x97d68 <= x < 0x97d70))) -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)).
{ intros x Hx Hr. apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT. exact Hx. }
destruct PTH as (P1 & P2 & P3). destruct TID as [T1 T2].
constructor.
- exact SPB.
- destruct (stk_split rsegs m (usp0 - 8388608) (usp0 - 128) usp0 STK ltac:(lia)) as [_ S2].
apply (stk_merge rsegs m' (usp0 - 8388608) (usp0 - 128) usp0 ST'); [| lia].
eapply stk_transport; [exact S2| exact MU| exact WM|]. intros x Hx. left. apply OUT. lia.
- destruct FRM as [[WF BA] WR]. split; [split; [exact WF|]|].
+ eapply bytes_at_agree; [exact BA|]. intros x Hx. apply EQ; [left; lia|]. rewrite cells_bytes_length in Hx by exact WF. cbn in Hx. lia.
+ destruct WR as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM. apply W3. exact Hi.
- split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- unfold prisx in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0. apply EQ; [right|];
unfold PRIS2 in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
- eapply stk_transport; [exact STG| exact MU| exact WM|]. intros x Hx. left. apply OUT. right. unfold RSTAGE, RSTAGE_SZ in *. lia.
- split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; [left; lia| lia].
- destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2]. eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; [left; lia| lia].
- eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- exact CEIL.
- exists true. exact AT.
Qed.

#[using="Type"] Lemma PFIMG_of : forall B A LB m md, prisx m -> HEAPc B A LB m md ->
bytes_at rsegs m 0x658d8 (le8 (Z_to_bv 64 0x66a30)) -> PFIMG m.
Proof.
intros B A LB m md PRS HP HEX. pose proof (heapc_guard_cells B _ _ _ _ HP) as [[[_ G1] _] [[_ G2] _]].
cbn [cells_bytes cbytes app] in G1, G2. rewrite app_nil_r in G1, G2.
unfold PFIMG. split; [| split; [exact HEX| split; [| split; [| split; [exact G1| exact G2]]]]].
- intros a Ha. exact (proj1 (Forall_forall _ _) PRS (0x10000, 0x658d8) ltac:(cbn; tauto) a Ha).
- intros a Ha. exact (proj1 (Forall_forall _ _) PRS (0x658e0, 0x659d0) ltac:(cbn; tauto) a Ha).
- intros a Ha. exact (proj1 (Forall_forall _ _) PRS (0x659d8, 0x66a30) ltac:(cbn; tauto) a ltac:(cbn; lia)).
Qed.

#[using="Type"] Lemma STDOUTW_presx : forall LB SP m m' k, (k <= 3)%nat -> STDOUTW m k -> presx LB SP m m' -> STDOUTW m' k.
Proof.
intros LB SP m m' k Hk SW HP.
assert (EQ : forall x, (0x66e28 <= x < 0x66f10 \/ 0x98350 <= x < 0x98750) -> m' (wa x) = m (wa x)).
{ intros x Hx. apply (presx_static LB SP m m' x HP); lia. }
destruct SW; constructor; unfold Um90.Mq0.cell in *;
(erewrite (rdn_agree _ m m'); [eassumption| lia| lia| intros; apply EQ; lia]).
Qed.

#[using="Type"] Lemma STDOUTW_img_agree : forall m m' k, (k <= 3)%nat -> STDOUTW m k -> img_agree m m' -> STDOUTW m' k.
Proof.
intros m m' k Hk SW IA.
assert (EQ : forall x, (0x66e28 <= x < 0x66f10 \/ 0x98350 <= x < 0x98750) -> m' (wa x) = m (wa x)).
{ intros x Hx. apply IA; unfold RCTX, RERRNO, RATP; lia. }
destruct SW; constructor; unfold Um90.Mq0.cell in *;
(erewrite (rdn_agree _ m m'); [eassumption| lia| lia| intros; apply EQ; lia]).
Qed.

#[using="Type"] Lemma zero_lines_length : forall k, length (zero_lines k) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.

#[using="Type"] Lemma STDOUT_of_W : forall B A LB m md k, (k <= 3)%nat -> STDOUTW m k -> HEAPc B A LB m md ->
fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
STDOUT m md (zero_lines k).
Proof.
intros B A LB m md k Hk SW HP FD1. pose proof (heapc_guard_cells B _ _ _ _ HP) as [[[_ G1] _] [[_ G2] _]].
cbn [cells_bytes cbytes app] in G1, G2. rewrite app_nil_r in G1, G2.
destruct SW as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13]. unfold Um90.Mq0.cell in *.
destruct k as [|k].
- left. split; [reflexivity|]. exists (Z_to_bv 64 0x98350), (Z_to_bv 64 0). unfold UFeQ.Mq0.file_clean.
rewrite Z.add_0_r in F5. cbn [Z.of_nat Z.mul Z.add] in F5. repeat split; assumption.
- right. exists (0x98350 + 2 * Z.of_nat (S k)), (Z_to_bv 64 0), rc_canary. split; [| split; [lia| exact FD1]].
constructor; try assumption.
+ cbn. lia.
+ rewrite zero_lines_length. lia.
+ rewrite zero_lines_length. unfold Uaccess.rw_bytes_max. cbn. lia.
+ rewrite zero_lines_length. exact F13.
+ split; [exact (QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ G1)| exact (QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ G2)].
Qed.

Definition FLAGC (i f : Z) : list cell := [C1 (Z_to_bv 8 i); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C1 (Z_to_bv 8 f)].

#[using="Type"] Lemma STDOUTW_flag : forall m m' k, (k <= 3)%nat -> STDOUTW m k -> munch [(FLAG, FLAG + 1)] m m' -> STDOUTW m' k.
Proof.
intros m m' k Hk SW MU. unfold FLAG in MU.
assert (EQ : forall x, (0x66e28 <= x < 0x66f10 \/ 0x98350 <= x < 0x98750) -> m' (wa x) = m (wa x)).
{ intros x Hx. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. lia. }
destruct SW; constructor; unfold Um90.Mq0.cell in *;
(erewrite (rdn_agree _ m m'); [eassumption| lia| lia| intros; apply EQ; lia]).
Qed.

Lemma atx_of_chunks : forall (m : mem) z3 z4 z248 zi,
rw_cells rsegs m 0x97c48 [C1 (Z_to_bv 8 0); CB 3 z3; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 z4; C8 (Z_to_bv 64 0x97c60); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0x50e18); CB 248 z248; C8 (Z_to_bv 64 0x20fac)] ->
rw_cells rsegs m 0x76f80 [C1 (Z_to_bv 8 1); CB 3 zi; C1 (Z_to_bv 8 0)] ->
UFeQ.Mq0.atx_state true m.
Proof.
intros m z3 z4 z248 zi CH FL. unfold UFeQ.Mq0.atx_state.
pose proof (QlEo.rw_cells_read rsegs _ _ _ 4%nat _ CH eq_refl) as R1.
pose proof (QlEo.rw_cells_read rsegs _ _ _ 8%nat _ CH eq_refl) as R2.
pose proof (QlEo.rw_cells_read rsegs _ _ _ 16%nat _ CH eq_refl) as R3.
pose proof (QlEo.rw_cells_read rsegs _ _ _ 24%nat _ CH eq_refl) as R4.
pose proof (QlEo.rw_cells_read rsegs _ _ _ 32%nat _ CH eq_refl) as R5.
pose proof (QlEo.rw_cells_read rsegs _ _ _ 288%nat _ CH eq_refl) as R6.
pose proof (QlEo.rw_cells_read rsegs _ _ _ 4%nat _ FL eq_refl) as R7.
rewrite QsRG.Mq0.ov_rdn in R1, R2, R3, R4, R5, R6, R7. cbn [csize cbytes Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add wa] in R1, R2, R3, R4, R5, R6, R7.
unfold wa in *. cbn [Z.add Pos.add Pos.succ] in R1, R2, R3, R4, R5, R6, R7.
repeat split; first [exact R1 | exact R3 | exact R2 | exact R4 | exact R5 | exact R6 | exact R7].
Qed.

Section Target.
Variables (usp0 tid : Z) (ppw : word) (path : list byte) (data : list byte) (fs : Fs.Fs).
Notation pp := (bv_unsigned ppw).
Variables (fds0 : list (word * FdEntry)).
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Notation B := usp0.
Notation LO := (usp0 - 8388608).
Hypothesis HBlt : alloc_ceiling < usp0.
Hypothesis HCEIL : alloc_ceiling = usp0 - 8388608.
Let HIx : heap_iface S4L := S4_heap B HBlt.
#[using="Type"] Lemma hexgot_of : forall A LB m md, HEAPc B A LB m md -> bytes_at rsegs m 0x658d8 (le8 (Z_to_bv 64 0x66a30)).
Proof. intros A LB m md HP. exact (proj1 (heapc_consts B _ _ _ _ HP)). Qed.

Hypothesis TGT : target_stmt S4L HIx 0x21024 hglob_P.
Hypothesis PF1 : printf1_stmt usp0.
Hypothesis PFK : printfk_stmt usp0.

Notation cl := (cfglen_of data).
Notation pl := (Z.of_nat (length data) - 6 - cfglen_of data).
Notation payload := (skipn (Z.to_nat (6 + cfglen_of data)) data).

Definition trun_frame (j0 : list byte) (s7v s6v s5v : word) (buf : Z) : list cell :=
[CB 8 j0; C8 s7v; C8 s6v; C8 s5v; C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 (buf + 6 + cl)); C8 (Z_to_bv 64 cl);
C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (buf + 2)); C8 (Z_to_bv 64 TRUN_RET)].

Definition OWN (al : Z) : list (Z * Z) := if pl =? 0 then [] else [(al, pl)].

Section Loop.
Variables (buf cap : Z) (x5 x6 x7 x8 x9 x10 x11 : word) (Tok : TSet).
Hypothesis TOKN : Tok [].
Hypothesis Hcap : 65536 <= cap <= 2^26.
Hypothesis Hlen : Z.of_nat (length data) < cap.
Hypothesis FIT : 6 + cl <= Z.of_nat (length data).

Hypothesis KOK : forall (m' : mem) (md' : Model) (A' : hstate) (LK : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
RPOST usp0 tid ppw path fs buf cap LK m' md' A' (zero_lines (Nat.pred (calls_of data))) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (usp0 - 128)) gp' (Z_to_bv 64 0x77c00) t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 cl) (Z_to_bv 64 (buf + 6 + cl)) (Z_to_bv 64 pl)
x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET) fc' None m' (seg_rom rsegs)) md') Tok.

Record TI (i : nat) (al ow : Z) (LK : list (Z * Z)) (m : mem) (md : Model) (A : hstate) : Prop := MKTI {
ti_dfx  : DFX usp0 pp tid path m;
ti_heap : HEAPc B A (OWN al ++ (buf, cap) :: LK) m md;
ti_errno: exists errv, rw_cells rsegs m RERRNO [C4 errv];
ti_loc  : rw_cells rsegs m 0x77bd0 [C8 (Z_to_bv 64 0x97ec8)];
ti_lock : rw_cells rsegs m 0x97f68 [C4 (Z_to_bv 64 0)];
ti_flag : rw_cells rsegs m 0x76f80 (FLAGC 1 0);
ti_pay  : bytes_at rsegs m al payload;
ti_al   : (pl = 0 /\ al = 0x76f90 /\ ow = 0) \/ (0 < pl /\ ow = al /\ rblock_range al pl);
ti_out  : match i with O => clearr m 0x66e28 0x66f10 | S i' => STDOUTW m i' end;
ti_err  : clearr m 0x66d38 0x66e20;
ti_fds  : CFDS fds0 (m_fds md);
ti_fs   : m_fs md = fs;
ti_stk  : stk rsegs m LO (usp0 - 208);
ti_frame: exists j0, rw_cells rsegs m (usp0 - 208) (trun_frame j0 x7 x6 x5 buf);
ti_glob : hglob_P m }.

Definition tloop_stmt (i j : nat) : Prop :=
forall (al ow : Z) (LK : list (Z * Z)) (m : mem) (md : Model) (A : hstate)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TI i al ow LK m md A -> QCcH.frm0 fc ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 pl) (Z_to_bv 64 al) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) s3 (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551614) x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 TLOOP) fc None m (seg_rom rsegs)) md)
(match i with O => t_emit (W 1 (zero_lines 1)) Tok | S _ => Tok end).

#[using="Type"] Lemma model_vm_only_fds : forall md md', model_vm_only md md' -> m_fds md' = m_fds md.
Proof. intros md md' (H & _). unfold m_fds. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma model_vm_only_fs : forall md md', model_vm_only md md' -> m_fs md' = m_fs md.
Proof. intros md md' (_ & _ & H & _). unfold m_fs. rewrite H. reflexivity. Qed.
#[using="AMB data"] Lemma neq13 : Z_to_bv 64 1 <> Z_to_bv 64 3.
Proof. intros E. assert (X : bv_unsigned (Z_to_bv 64 1) = bv_unsigned (Z_to_bv 64 3)) by (rewrite E; reflexivity). rewrite !unsigned_lit in X by lia. lia. Qed.
#[using="AMB data FD1"] Lemma CFDS_1 : forall fds, CFDS fds0 fds -> fd_lookup fds (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. intros fds H. rewrite (H _ neq13). exact FD1. Qed.

#[using="FD1 HCEIL Hcap FIT KOK"] Lemma tloop_after : forall i j, (1 <= j)%nat -> (i + j = calls_of data)%nat ->
((2 <= j)%nat -> tloop_stmt (S i) (j - 1)) ->
forall (al ow : Z) (LK : list (Z * Z)) (m : mem) (md : Model) (A : hstate)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TI (S i) al ow LK m md A -> QCcH.frm0 fc ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 pl) (Z_to_bv 64 al) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) (Z_to_bv 64 0) (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551614) x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 PRINTF_RET) fc None m (seg_rom rsegs)) md) Tok.
Proof.
intros i j Hj Hij IH. intros until fc. intros TIH FRM.
pose proof TIH as [D HP (errv & ERR) LOCC LOCK FL PAY AL OUT ERRP Hfds Hfs ST (j0 & FRt) GL].
pose proof (x_sp _ _ _ _ _ D) as SPB.
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
assert (CALLS4 : (calls_of data <= 4)%nat).
{ unfold calls_of. destruct (Z.to_nat (cfglen_of data)); [lia|]. pose proof (Z.mod_pos_bound (hb data 2) 4 ltac:(lia)). lia. }
unfold RERRNO, RATP in ERR. unfold trun_frame in FRt.
apply rz_evt; [exact MOK|]. unfold PRINTF_RET.
step.
step. if_truex.
step. rewrite (unsigned_lit (Z.of_nat j)) by lia. rewrite swrap32_id by lia. step.
destruct (Nat.eq_dec j 1) as [J1|J2].
2:{
if_truex. apply evt_RZ_done. replace (Z.of_nat j + -1) with (Z.of_nat (j - 1)) by lia.
apply (IH ltac:(lia) al ow LK m md A); [exact TIH| exact FRM]. }

subst j. if_falsex. step. step. apply evt_RZ_done.
assert (Hi : i = Nat.pred (calls_of data)) by lia.
assert (Hi3 : (i <= 3)%nat) by lia.

assert (EPI : forall (m' : mem) (md' : Model) (A' : hstate) (q0 q1 q2 r w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 : word),
DFX usp0 pp tid path m' -> HEAPc B A' ((buf, cap) :: LK) m' md' -> (exists e, rw_cells rsegs m' (RATP - 164) [C4 e]) ->
STDOUTW m' i -> clearr m' 0x66d38 0x66e20 -> CFDS fds0 (m_fds md') -> m_fs md' = fs ->
rw_cells rsegs m' (usp0 - 208) (trun_frame j0 x7 x6 x5 buf) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x20f4c) (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) q0 q1 q2
(Z_to_bv 64 pl) (Z_to_bv 64 al) r w1 w2 w3 w4 w5 w6 w7
(Z_to_bv 64 ow) (Z_to_bv 64 (-1)) (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat 1 + -1)) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551614) x8 x9 x10 x11 q3 q4 q5 q6)
F (ret_pc (Z_to_bv 64 0x20f4c)) fc None m' (seg_rom rsegs)) md') Tok).
{ intros m' md' A' q0 q1 q2 r w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 D' HP' ERR' SW' ERRP' Hfds' Hfs' FRt'.
pose proof (x_sp _ _ _ _ _ D') as SPB'. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'.
unfold trun_frame in FRt'.
reenter MOK'. do 3 step. do 9 step. step. step.
apply evt_RZ_done.
replace (ret_pc (Z_to_bv 64 TRUN_RET)) with (Z_to_bv 64 TRUN_RET : word) by (symmetry; apply ret_pc_even; [unfold TRUN_RET; lia| reflexivity]).
replace (usp0 - 208 + 80) with (usp0 - 128) by lia.
apply (KOK m' md' A' LK). rewrite <- Hi. constructor.
- exact D'.
- exact HP'.
- unfold RERRNO, RATP in *. exact ERR'.
- exact Hfs'.
- eapply (STDOUT_of_W B); [exact Hi3| exact SW'| exact HP'| exact (CFDS_1 _ Hfds')].
- left. exact ERRP'. }
destruct AL as [(A1 & A2 & A3)|(A1 & A2 & RB)].
-
subst ow. apply (heapc_free_null RFREE_SYM rfree_null_at_sym); [exact MOK| reflexivity|].
apply (EPI m md A); [exact D| | exists errv; unfold RATP; exact ERR| exact OUT| exact ERRP| exact Hfds| exact Hfs| unfold trun_frame; exact FRt].
unfold OWN in HP. replace (pl =? 0) with true in HP by (symmetry; apply Z.eqb_eq; lia). exact HP.
-
subst ow. unfold OWN in HP. replace (pl =? 0) with false in HP by (symmetry; apply Z.eqb_neq; lia). cbn [app] in HP.
pose proof (heapc_blk_nodup B _ _ _ _ HP) as ND. cbn [map fst] in ND.
assert (NE : al <> buf) by (inversion ND; subst; cbn in *; intros E; subst; tauto).
destruct (stk_split rsegs m LO (usp0 - 208) usp0 (x_stk _ _ _ _ _ D) ltac:(lia)) as [ST1 _].
eapply (heapc_free B RFREE_SYM (rfree_stmt_at_sym rfree_spec_proof)
(Z_to_bv 64 0x20f4c) (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 al) (Z_to_bv 64 al)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 al) (Z_to_bv 64 (-1)) (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat 1 + -1)) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551614) x8 x9 x10 x11 t3 t4 t5 t6
F fc m md _ A ((al, pl) :: (buf, cap) :: LK) al pl LO errv HP ltac:(left; reflexivity));
[rewrite unsigned_lit by lia; exact ST1| unfold alloc_ceiling; lia| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
| rewrite unsigned_lit by lia; lia| exact ERR| reflexivity| reflexivity|].
intros ms' m' md' A' r RS VM ST' (LBx & PLBx & PRES) ERR' HP'.
replace (zlb_remove al ((al, pl) :: (buf, cap) :: LK)) with ((buf, cap) :: LK) in * by (cbn [zlb_remove fst]; rewrite Z.eqb_refl; reflexivity).
open_ret RS. pose proof (heapc_mem_inv B _ _ _ _ HP') as MI'. rewrite unsigned_lit in ST', PRES by lia.
pose proof (img_agree_of_pres _ _ _ _ PRES) as IA.
apply (EPI m' md' A').
+ eapply (DFX_alloc usp0 pp tid path m m' LBx (usp0 - 208) LO D PRES MI' ST' eq_refl ltac:(lia)).
+ exact HP'.
+ exists errv. exact ERR'.
+ eapply STDOUTW_img_agree; [exact Hi3| exact OUT| exact IA].
+ eapply clearr_img_agree; [exact ERRP| exact IA| lia| lia| unfold RCTX; lia| unfold RERRNO, RATP; lia].
+ rewrite (vm_only_fds md md' VM). exact Hfds.
+ rewrite (vm_only_fs md md' VM). exact Hfs.
+ unfold trun_frame. eapply rheap_pres_rw_cells; [exact PRES| exact FRt| left; lia].
Qed.

#[using="FD1 HBlt HCEIL HIx TGT PF1 PFK TOKN Hcap Hlen FIT KOK"] Lemma tloop_step : forall i j, (1 <= j)%nat -> (i + j = calls_of data)%nat ->
((2 <= j)%nat -> tloop_stmt (S i) (j - 1)) ->
tloop_stmt i j.
Proof.
intros i j Hj Hij IH. unfold tloop_stmt. intros until fc. intros TIH FRM.
destruct TIH as [D HP (errv & ERR) LOCC LOCK FL PAY AL OUT ERRP Hfds Hfs ST (j0 & FRt) GL].
pose proof (x_sp _ _ _ _ _ D) as SPB.
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
pose proof (heapc_blk B _ _ _ _ buf cap HP ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & Bpos & Bhi & _ & Bimg).
unfold alloc_ceiling in Bhi. unfold RIMG_LO, RIMG_HI in Bimg.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
assert (CALLS4 : (calls_of data <= 4)%nat).
{ unfold calls_of. destruct (Z.to_nat (cfglen_of data)); [lia|]. pose proof (Z.mod_pos_bound (hb data 2) 4 ltac:(lia)). lia. }
unfold RERRNO, RATP in ERR. unfold trun_frame in FRt.

assert (PAY1 : forall mq, munch [(FLAG, FLAG + 1)] m mq -> bytes_at rsegs mq al payload).
{ intros mq MUq. destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))].
- destruct PAY as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
- eapply bytes_at_transport; [exact PAY| exact MUq|]. rewrite length_skipn. unfold FLAG, alloc_ceiling in *. cbn. lia. }
clear PAY.
pose proof (munch_refl [(FLAG, FLAG + 1)] m) as MUf. pose proof (wmono_refl rsegs m) as WMf. unfold FLAG in MUf. unfold FLAGC in FL.
apply rz_evt; [exact MOK|]. unfold TLOOP.
step. stepz. step. step. step. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m1 end.
pose proof (PAY1 _ MUf) as PAY.
assert (PLEN : Z.of_nat (length payload) = pl) by (rewrite length_skipn; lia).
assert (HP1 : HEAPc B A (OWN al ++ (buf, cap) :: LK) m1 md).
{ eapply (heapc_frame B); [exact HP| | exact WMf| exact MI].
intros a Ha NCW; apply MUf; unfold wa; rewrite unsigned_lit by lia; cbn; split; [| exact I].
intros [X1 X2]; apply NCW; right; right.
unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR; lia. }
assert (GL1 : hglob_P m1) by (eapply hglob_P_munch; [exact GL| exact MUf| exact WMf| constructor; [cbn [fst snd]; lia| constructor]]).
assert (ERRP1 : clearr m1 0x66d38 0x66e20) by (eapply clearr_munch; [exact ERRP| exact MUf| constructor; [cbn [fst snd]; lia| constructor]| lia| lia]).
assert (OUT1 : match i with O => clearr m1 0x66e28 0x66f10 | S i' => STDOUTW m1 i' end).
{ destruct i as [|i'].
- eapply clearr_munch; [exact OUT| exact MUf| constructor; [cbn [fst snd]; lia| constructor]| lia| lia].
- eapply STDOUTW_flag; [lia| exact OUT| exact MUf]. }
clear ERRP OUT.
eapply (TGT (Z_to_bv 64 0x20f20) (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 pl) (Z_to_bv 64 al) (Z_to_bv 64 al) (Z_to_bv 64 pl) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) s3 (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551614) x8 x9 x10 x11 t3 t4 t5 t6
F fc m1 md _ A (OWN al ++ (buf, cap) :: LK) al pl LO payload errv);
[exact HP1| exact PAY| exact PLEN| lia| | | | | exact LOCC| exact LOCK| exact GL1
| rewrite unsigned_lit by lia; exact ST| lia| rewrite unsigned_lit by lia; unfold TGT_STACK; lia
| rewrite unsigned_lit by lia; replace (usp0 - 208) with (usp0 + (-13) * 16) by lia; rewrite Z.mod_add by lia; exact (proj2 SPB)
| rewrite unsigned_lit by lia; cbn; lia| cbn; lia| exact ERR| reflexivity| reflexivity| exact FRM| reflexivity| reflexivity|].
{ destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))]; lia. }
{ destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))]; unfold alloc_ceiling in *; lia. }
{
destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))];
[subst; lia| exact R4]. }
{ destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))]; [left; lia| right]. unfold OWN. replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
intros ms' m' md' A' errv' gp' LK' RSW VM ST' PRESX LOCC' ERR' GL' HP'.
destruct RSW as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS & FRM').
specialize (FRM' FRM). cbn [hl_segs hl_tp S4L] in ST', PRESX, LOCC', ERR', HP' |- *.
change (AS S4L HIx) with hstate in A'. change (HEAP S4L HIx) with (HEAPc B) in HP'.
rewrite <- app_assoc in HP'. cbn [app] in HP'.
pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. pose proof (heapc_mem_inv B _ _ _ _ HP') as MI'.
rewrite unsigned_lit in ST', PRESX by lia.
pose proof (model_vm_only_fds _ _ VM) as FDS'. pose proof (model_vm_only_fs _ _ VM) as FS'.
assert (FL' : rw_cells rsegs m' 0x76f80 (FLAGC 1 1)).
{ unfold FLAGC. eapply (heap_presx_rw_cells S4L); [exact PRESX| exact FL|]. right; left. intros a Ha. cbn in Ha. split; [cbn; unfold s4_client_static; lia| unfold xtgt, T_LOCCELL; cbn; unfold s4_volatile; lia]. }
assert (PAY' : bytes_at rsegs m' al payload).
{ destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))].
- destruct PAY as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
- eapply (heap_presx_bytes_at S4L); [exact PRESX| exact PAY|]. right; right. exists (al, pl). split; [| cbn; rewrite length_skipn; lia].
unfold OWN. replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
assert (ERRP' : clearr m' 0x66d38 0x66e20) by (eapply clearr_presx; [exact ERRP1| exact PRESX| lia| lia| intros; lia]).
assert (LOCK' : rw_cells rsegs m' 0x97f68 [C4 (Z_to_bv 64 0)]).
{ eapply (heap_presx_rw_cells S4L); [exact PRESX| exact LOCK|]. right; left. intros a Ha. cbn in Ha. split; [cbn; unfold s4_client_static; lia| unfold xtgt, T_LOCCELL; cbn; unfold s4_volatile; lia]. }
assert (FRt' : rw_cells rsegs m' (usp0 - 208) (trun_frame j0 x7 x6 x5 buf)) by (unfold trun_frame; eapply (heap_presx_rw_cells S4L); [exact PRESX| exact FRt| left; lia]).
destruct (stk_split rsegs m' LO (usp0 - 208 - 1536) (usp0 - 208) ST' ltac:(lia)) as [STlo STpf].

pose proof (munch_refl [(FLAG, FLAG + 1)] m') as MUg. pose proof (wmono_refl rsegs m') as WMg. unfold FLAG in MUg. unfold FLAGC in FL'.
pose proof (stk_merge rsegs m' _ _ _ STlo STpf ltac:(lia)) as STall.
unfold T_LOCCELL, T_GLOBLOC in LOCC'. cbn [hl_tp hl_segs S4L Z.sub Z.add] in LOCC'.
assert (PAY2 : forall mq, munch [(FLAG, FLAG + 1)] m' mq -> bytes_at rsegs mq al payload).
{ intros mq MUq. destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))].
- destruct PAY' as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
- eapply bytes_at_transport; [exact PAY'| exact MUq|]. rewrite length_skipn. unfold FLAG, alloc_ceiling in *. cbn. lia. }
clear PAY'.
reenter MOK'. step. stepz. step. step. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m'' end.
pose proof (PAY2 _ MUg) as PAY'.
assert (FLr : QsRG.Mq0.rdn rsegs m'' (Z_to_bv 64 FLAG) 1%nat = Some [Z_to_bv 8 0]).
{ unfold FLAG. pose proof (rw_cells_bytes_at _ _ _ _ FL') as Bf. cbn [cells_bytes cbytes app] in Bf.
change [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] with ([Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ++ [Z_to_bv 8 0]) in Bf.
apply bytes_at_app in Bf as [_ Bf]. cbn [length Z.of_nat Nat.add Pos.of_succ_nat Pos.add Pos.succ Z.add Pos.add] in Bf.
exact (QuJV.Mq0.bytes_at_rdn0 rsegs m'' 0x76f84 [Z_to_bv 8 0] Bf). }
assert (D' : DFX usp0 pp tid path m'').
{ eapply (DFX_harness usp0 pp tid path _ m _ m' m''); [exact D| exact MUf| exact WMf| exact PRESX| exact MUg| exact WMg| exact MI'| exact STall| | exact FLr].
pose proof (rw_cells_bytes_at _ _ _ _ LOCC') as BL. cbn [cells_bytes cbytes app] in BL. rewrite app_nil_r in BL. exact BL. }
assert (HP'' : HEAPc B A' (OWN al ++ (buf, cap) :: LK ++ LK') m'' md').
{ eapply (heapc_frame B); [exact HP'| | exact WMg| exact MI'].
intros a Ha NCW; apply MUg; unfold wa; rewrite unsigned_lit by lia; cbn; split; [| exact I].
intros [X1 X2]; apply NCW; right; right.
unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR; lia. }
assert (ERRP'' : clearr m'' 0x66d38 0x66e20) by (eapply clearr_munch; [exact ERRP'| exact MUg| constructor; [cbn [fst snd]; lia| constructor]| lia| lia]).
pose proof (PFIMG_of B _ _ _ _ (x_pris _ _ _ _ _ D') HP'' (hexgot_of _ _ _ _ HP'')) as IMG'.
assert (GL'' : hglob_P m'') by (eapply hglob_P_munch; [exact GL'| exact MUg| exact WMg| constructor; [cbn [fst snd]; lia| constructor]]).

assert (AFTER : forall (m2 : mem) (F2 : bvmap 5 word) (ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 : word),
munch (PFW (usp0 - 208)) m'' m2 -> wmono rsegs m'' m2 -> mem_inv rsegs m2 -> stk rsegs m2 (usp0 - 208 - 1536) (usp0 - 208) ->
STDOUTW m2 i ->
realizes rsegs (mkCfg (MS (mkR ra' (Z_to_bv 64 (usp0 - 208)) gp' (Z_to_bv 64 0x77c00) q0 q1 q2 (Z_to_bv 64 pl) (Z_to_bv 64 al) r0 r1 r2 r3 r4 r5 r6 r7
(Z_to_bv 64 ow) (Z_to_bv 64 0) (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551614) x8 x9 x10 x11 q3 q4 q5 q6)
F2 (Z_to_bv 64 PRINTF_RET) fc' None m2 (seg_rom rsegs)) md') Tok).
{ intros m2 F2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2.
refine (tloop_after i j Hj Hij IH al ow (LK ++ LK') m2 md' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc' _ FRM').
assert (FRt2 : rw_cells rsegs m2 (usp0 - 208) (trun_frame j0 x7 x6 x5 buf)).
{ unfold trun_frame. eapply rw_cells_transport; [exact FRt'| exact MU2| exact WM2|]. cbn. repeat split; lia. }
assert (STK2 : stk rsegs m2 LO (usp0 - 128)).
{ apply (stk_merge rsegs m2 LO (usp0 - 208) (usp0 - 128)); [| | lia].
- apply (stk_merge rsegs m2 LO (usp0 - 208 - 1536) (usp0 - 208)); [| exact ST2| lia].
eapply stk_transport_disjoint; [exact STlo| exact MU2| exact WM2| cbn; repeat split; lia].
- pose proof (stk_of_rw_cells rsegs m2 _ _ FRt2) as S3. unfold trun_frame in S3. cbn [cells_size csize Nat.add] in S3.
replace (usp0 - 208 + Z.of_nat 80) with (usp0 - 128) in S3 by lia. exact S3. }
constructor.
- eapply DFX_munch; [exact D'| exact MU2| exact WM2| exact STK2|]. unfold PFW. ivs_lia.
- eapply (heapc_frame B); [exact HP''| | exact WM2| exact MI2]. intros a Ha NCW. apply MU2. unfold wa. rewrite unsigned_lit by lia.
unfold PFW. cbn [outside]. repeat split; intros [X1 X2]; apply NCW.
+ right; left. unfold alloc_ceiling. lia.
+ right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
+ right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
- exists errv'. eapply rw_cells_transport; [exact ERR'| exact MU2| exact WM2| cbn; unfold RERRNO, RATP; repeat split; lia].
- eapply rw_cells_transport; [exact LOCC'| exact MU2| exact WM2| cbn; repeat split; lia].
- eapply rw_cells_transport; [exact LOCK'| exact MU2| exact WM2| cbn; repeat split; lia].
- unfold FLAGC. eapply rw_cells_transport; [exact FL'| exact MU2| exact WM2| cbn; repeat split; lia].
- destruct AL as [(A1 & A2 & A3)|(A1 & A2 & (R1 & R2 & R3 & R4 & R5))].
+ destruct PAY' as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
+ eapply bytes_at_transport; [exact PAY'| exact MU2|]. rewrite length_skipn. unfold alloc_ceiling in R4. cbn; repeat split; lia.
- exact AL.
- exact SW2.
- eapply clearr_munch; [exact ERRP''| exact MU2| unfold PFW; ivs_lia| lia| lia].
- rewrite FDS'. exact Hfds.
- rewrite FS'. exact Hfs.
- apply (stk_merge rsegs m2 LO (usp0 - 208 - 1536) (usp0 - 208)); [| exact ST2| lia].
eapply stk_transport_disjoint; [exact STlo| exact MU2| exact WM2| cbn; repeat split; lia].
- exists j0. exact FRt2.
- eapply hglob_P_munch; [exact GL''| exact MU2| exact WM2|]. unfold PFW. ivs_lia. }
destruct i as [|i'].
-
eapply (PF1 gp' (Z_to_bv 64 0x77c00)); [exact MOK'| rewrite FDS'; exact (CFDS_1 _ Hfds)| | exact IMG'| exact STpf| exact MI'| lia| lia| reflexivity| exact TOKN|].
{ eapply clearr_munch; [eapply clearr_presx; [exact OUT1| exact PRESX| lia| lia| intros; lia]| exact MUg| constructor; [cbn [fst snd]; lia| constructor]| lia| lia]. }
intros m2 F2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2.
exact (AFTER m2 F2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2).
-
eapply (PFK i' gp' (Z_to_bv 64 0x77c00)); [exact MOK'| lia| | exact IMG'| exact STpf| exact MI'| lia| lia| reflexivity|].
{ eapply STDOUTW_flag; [lia| eapply STDOUTW_presx; [| exact OUT1| exact PRESX]; lia| exact MUg]. }
intros m2 F2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2.
exact (AFTER m2 F2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2).
Qed.
#[using="FD1 HBlt HCEIL HIx TGT PF1 PFK TOKN Hcap Hlen FIT KOK"] Lemma tloop_all : forall j i, (1 <= j)%nat -> (i + j = calls_of data)%nat -> tloop_stmt i j.
Proof.
induction j as [|j IHj]; intros i Hj Hij; [lia|].
apply tloop_step; [exact Hj| exact Hij|]. intros H2. replace (S j - 1)%nat with j by lia. apply IHj; lia.
Qed.

Record PRE1 (m1 : mem) (md : Model) (A : hstate) : Prop := MKP1 {
p_dfx  : DFX usp0 pp tid path m1;
p_heap : HEAPc B A [(buf, cap)] m1 md;
p_dsh  : DSH A;
p_sh   : hshift A <= 12;
p_bud  : BUD md (WL 10) (DL 10);
p_errno: exists errv, rw_cells rsegs m1 RERRNO [C4 errv];
p_loc  : rw_cells rsegs m1 0x77bd0 [C8 (Z_to_bv 64 0x97ec8)];
p_lock : rw_cells rsegs m1 0x97f68 [C4 (Z_to_bv 64 0)];
p_flag : rw_cells rsegs m1 0x76f80 (FLAGC 1 0);
p_blk  : exists junk, rw_cells rsegs m1 buf [CB (length data) data; CB (Z.to_nat (cap - Z.of_nat (length data))) junk];
p_out  : clearr m1 0x66e28 0x66f10;
p_err  : clearr m1 0x66d38 0x66e20;
p_fds  : CFDS fds0 (m_fds md);
p_fs   : m_fs md = fs;
p_stk  : stk rsegs m1 LO (usp0 - 208);
p_frame: exists j0, rw_cells rsegs m1 (usp0 - 208) (trun_frame j0 x7 x6 x5 buf);
p_glob : hglob_P m1 }.

#[using="FD1 HBlt HCEIL HIx TGT PF1 PFK TOKN Hcap Hlen FIT KOK"] Lemma seg_empty : forall (m1 : mem) (md : Model) (A : hstate)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PRE1 m1 md A -> QCcH.frm0 fc -> pl = 0 ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 pl) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat (calls_of data))) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 0x20efc) fc None m1 (seg_rom rsegs)) md)
(t_emit (W 1 (zero_lines 1)) Tok).
Proof.
intros until fc. intros P FRM PL0. destruct P as [D HP DSH SH HBUD (errv & ERR) LOCC LOCK FL (junk & BLK) OUT ERRP Hfds Hfs ST (j0 & FRt) GL].
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK.
assert (CALLS1 : (1 <= calls_of data)%nat) by (unfold calls_of; destruct (Z.to_nat (cfglen_of data)); lia).
apply rz_evt; [exact MOK|]. step. step. step. step. apply evt_RZ_done.
replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 18446744073709551614 : word) by (apply bv_eq; reflexivity).
apply (tloop_all (calls_of data) 0 CALLS1 eq_refl 0x76f90 0 [] m1 md A); [| exact FRM].
constructor; [exact D| | exists errv; exact ERR| exact LOCC| exact LOCK| exact FL| | left; lia| exact OUT| exact ERRP| exact Hfds| exact Hfs| exact ST| exists j0; exact FRt| exact GL].
- unfold OWN. rewrite PL0. cbn [Z.eqb app]. exact HP.
- replace payload with (@nil byte) by (symmetry; apply skipn_all2; lia). split; [lia|]. split; [cbn; lia|]. intros k Hk. cbn in Hk. lia.
Qed.

#[using="FD1 HBlt HCEIL HIx TGT PF1 PFK TOKN Hcap Hlen FIT KOK"] Lemma seg_alloc : forall (Tfail : TSet) (m1 : mem) (md : Model) (A : hstate)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PRE1 m1 md A -> QCcH.frm0 fc -> 0 < pl ->
(forall (m' : mem) (md' : Model) (A' : hstate) (LK : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
RPOST usp0 tid ppw path fs buf cap LK m' md' A' [] ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (usp0 - 128)) gp' (Z_to_bv 64 0x77c00) t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 2) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 cl) (Z_to_bv 64 (buf + 6 + cl)) (Z_to_bv 64 pl)
x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET) fc' None m' (seg_rom rsegs)) md') Tfail) ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 pl) (Z_to_bv 64 (buf + 6 + cl)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat (calls_of data))) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 0x20eb0) fc None m1 (seg_rom rsegs)) md)
((t_emit (W 1 (zero_lines 1)) Tok)   ).
Proof.
intros until fc. intros P FRM PLP KFAIL. destruct P as [D HP DSH SH HBUD (errv & ERR) LOCC LOCK FL (junk & BLK) OUT ERRP Hfds Hfs ST (j0 & FRt) GL].
pose proof (x_sp _ _ _ _ _ D) as SPB.
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
pose proof (heapc_blk B _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _ & Bimg).
unfold alloc_ceiling in Bhi. unfold RIMG_LO, RIMG_HI in Bimg.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
assert (CALLS1 : (1 <= calls_of data)%nat) by (unfold calls_of; destruct (Z.to_nat (cfglen_of data)); lia).
unfold RERRNO, RATP in ERR.
apply rz_evt; [exact MOK|]. step. step. apply evt_RZ_done.
eapply (heapc_malloc_site3 B rmalloc_spec
(Z_to_bv 64 0x20eb8) (Z_to_bv 64 (usp0 - 208)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 (buf + 6 + cl)) (Z_to_bv 64 pl)
a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat (calls_of data))) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6
F fc m1 md Tfail _ A [(buf, cap)] pl LO errv 12 0 0%nat HP DSH SH ltac:(lia) ltac:(lia));
[unfold IB, UNIT; lia| | lia| rewrite unsigned_lit by lia; exact ST| unfold alloc_ceiling; lia| rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia
| rewrite unsigned_lit by lia; lia| exact ERR| reflexivity| reflexivity| |].
{ eapply BUD_mono; [exact HBUD| |].
- unfold S3W, BIGW, SMALLW, LW, AMW, PGSZ, WL, DRV_W. replace (FRESHW 0) with 1064960 by reflexivity.
pose proof (round_up_pg_le_al (pl + IB + UNIT) (2^26 + 4096) ltac:(unfold IB, UNIT; lia) ltac:(reflexivity)) as RU.
pose proof (QYTG.Mq0.round_up_pg_ge (pl + IB + UNIT)) as RU0.
destruct (MMAP_THRESHOLD <=? pl); change (2 ^ (12 + 1)) with 8192; change (2 ^ (12 + 1 + 1)) with 16384; change (2^31) with 2147483648; change (2 ^ Z.of_nat 10) with 1024; change (2^20) with 1048576; unfold IB, UNIT in *; lia.
- unfold S3D, SMALLD, DL, DRV_D, FRESHD. lia. }
-
intros ms' m' md' A' errv' RS VM ST' (LB0 & PLB & PRES) ERR' HP' SH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. pose proof (heapc_mem_inv B _ _ _ _ HP') as MI'.
rewrite unsigned_lit in ST', PRES by lia.
pose proof (img_agree_of_pres _ _ _ _ PRES) as IA.
assert (D' : DFX usp0 pp tid path m') by (eapply (DFX_alloc usp0 pp tid path m1 m' LB0 (usp0 - 208) LO D PRES MI' ST' eq_refl ltac:(lia))).
assert (FRt' : rw_cells rsegs m' (usp0 - 208) (trun_frame j0 x7 x6 x5 buf)) by (eapply rheap_pres_rw_cells; [exact PRES| exact FRt| left; lia]).
unfold trun_frame in FRt'.
reenter MOK'. step. if_truex. step. step. do 9 step. step. step.
apply evt_RZ_done.
replace (ret_pc (Z_to_bv 64 TRUN_RET)) with (Z_to_bv 64 TRUN_RET : word) by (symmetry; apply ret_pc_even; [unfold TRUN_RET; lia| reflexivity]).
replace (usp0 - 208 + 80) with (usp0 - 128) by lia.
apply (KFAIL m' md' A' []). constructor.
+ exact D'.
+ exact HP'.
+ exists errv'. unfold RERRNO, RATP. exact ERR'.
+ rewrite (vm_only_fs md md' VM). exact Hfs.
+ left. split; [reflexivity|]. exists (wz 0), (wz 0). apply file_clean_pristine; [right; reflexivity|].
eapply clearr_img_agree; [exact OUT| exact IA| lia| lia| unfold RCTX; lia| unfold RERRNO, RATP; lia].
+ left. eapply clearr_img_agree; [exact ERRP| exact IA| lia| lia| unfold RCTX; lia| unfold RERRNO, RATP; lia].
-
intros ms' m' md' A' r errv' RS VM ST' (LB0 & PLB & PRES) ERR' Hr (junk2 & NB) RNG HP' SH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. pose proof (heapc_mem_inv B _ _ _ _ HP') as MI'.
rewrite unsigned_lit in ST', PRES by lia.
pose proof (img_agree_of_pres _ _ _ _ PRES) as IA.
assert (D' : DFX usp0 pp tid path m') by (eapply (DFX_alloc usp0 pp tid path m1 m' LB0 (usp0 - 208) LO D PRES MI' ST' eq_refl ltac:(lia))).
assert (FRt' : rw_cells rsegs m' (usp0 - 208) (trun_frame j0 x7 x6 x5 buf)) by (eapply rheap_pres_rw_cells; [exact PRES| exact FRt| left; lia]).
pose proof (pres_block [(buf, cap)] LB0 (usp0 - 208) m1 m' buf cap _ PLB ltac:(left; reflexivity) PRES BLK ltac:(cbn; lia)) as BLK'.
pose proof BLK' as [[[WF1 _] BA] _]. cbn [cells_bytes cbytes app] in BA. apply bytes_at_app in BA as [BA _].

assert (SRC : bytes_at rsegs m' (buf + 6 + cl) payload).
{ destruct BA as (B1 & B2 & B3). split; [lia|]. split; [rewrite length_skipn; lia|]. intros k Hk. rewrite length_skipn in Hk.
replace (buf + 6 + cl + Z.of_nat k) with (buf + Z.of_nat (Z.to_nat (6 + cl) + k)) by lia. rewrite B3 by lia.
rewrite nth_error_skipn. reflexivity. }
destruct RNG as (R1 & R2 & R3 & R4 & R5).
pose proof (heapc_blk_disjoint B _ _ _ _ r pl buf cap HP' ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as DISJ.
pose proof (heapc_blk_nodup B _ _ _ _ HP') as ND. cbn [map fst] in ND.
assert (NE : r <> buf) by (inversion ND; subst; cbn in *; intros E; subst; tauto). specialize (DISJ NE).
unfold trun_frame in FRt'. unfold alloc_ceiling in R4.
reenter MOK'. step. if_falsex. step. step. step. step.
eapply evt_cut; [eapply memcpy_spec; rewrite ?unsigned_lit by lia; [exact SRC| rewrite length_skipn; lia| exact NB| lia| exact MI']|].
intros ms2 PO2. destruct PO2 as (w0 & w1 & w2 & wa1 & wa2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & m2 & -> & MU2 & WM2 & MI2 & DST2 & _).
rewrite !unsigned_lit in MU2, DST2 by lia.
replace (ret_pc (Z_to_bv 64 0x20ecc)) with (Z_to_bv 64 0x20ecc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. step. step. apply evt_RZ_done.
replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 18446744073709551614 : word) by (apply bv_eq; reflexivity).
apply (tloop_all (calls_of data) 0 CALLS1 eq_refl r r [] m2 md' A'); [| exact FRM].
assert (FRt2 : rw_cells rsegs m2 (usp0 - 208) (trun_frame j0 x7 x6 x5 buf)).
{ unfold trun_frame. eapply rw_cells_transport; [exact FRt'| exact MU2| exact WM2|]. cbn. split; [lia| exact I]. }
constructor.
+ eapply DFX_munch; [exact D'| exact MU2| exact WM2| |]. 2:{ constructor; [cbn [fst snd]; lia| constructor]. }
apply (stk_merge rsegs m2 LO (usp0 - 208) (usp0 - 128)); [| | lia].
* eapply stk_transport_disjoint; [exact ST'| exact MU2| exact WM2| cbn; lia].
* pose proof (stk_of_rw_cells rsegs m2 _ _ FRt2) as S3. unfold trun_frame in S3. cbn [cells_size csize Nat.add] in S3.
replace (usp0 - 208 + Z.of_nat 80) with (usp0 - 128) in S3 by lia. exact S3.
+ unfold OWN. replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app].
eapply (heapc_frame B); [exact HP'| | exact WM2| exact MI2]. intros a Ha NCW. apply MU2. unfold wa. rewrite unsigned_lit by lia. cbn. split; [| exact I].
intros [X1 X2]. apply NCW. left. exists (r, pl). split; [left; reflexivity|]. cbn. lia.
+ exists errv'. eapply rw_cells_transport; [exact ERR'| exact MU2| exact WM2| cbn; unfold RERRNO, RATP; lia].
+ eapply rw_cells_transport; [| exact MU2| exact WM2| cbn; lia]. eapply rw_cells_img_agree; [exact LOCC| exact IA| lia| cbn; lia| unfold RCTX; cbn; lia| unfold RERRNO, RATP; cbn; lia].
+ eapply rw_cells_transport; [| exact MU2| exact WM2| cbn; lia]. eapply rw_cells_img_agree; [exact LOCK| exact IA| lia| cbn; lia| unfold RCTX; cbn; lia| unfold RERRNO, RATP; cbn; lia].
+ unfold FLAGC in *. eapply rw_cells_transport; [| exact MU2| exact WM2| cbn; lia]. eapply rw_cells_img_agree; [exact FL| exact IA| lia| cbn; lia| unfold RCTX; cbn; lia| unfold RERRNO, RATP; cbn; lia].
+ pose proof DST2 as [[_ BA2] _]. cbn [cells_bytes cbytes app] in BA2. rewrite app_nil_r in BA2. exact BA2.
+ right. split; [lia|]. split; [reflexivity|]. unfold rblock_range. unfold alloc_ceiling. repeat split; lia.
+ eapply clearr_munch; [| exact MU2| constructor; [cbn [fst snd]; lia| constructor]| lia| lia].
eapply clearr_img_agree; [exact OUT| exact IA| lia| lia| unfold RCTX; lia| unfold RERRNO, RATP; lia].
+ eapply clearr_munch; [| exact MU2| constructor; [cbn [fst snd]; lia| constructor]| lia| lia].
eapply clearr_img_agree; [exact ERRP| exact IA| lia| lia| unfold RCTX; lia| unfold RERRNO, RATP; lia].
+ rewrite (vm_only_fds md md' VM). exact Hfds.
+ rewrite (vm_only_fs md md' VM). exact Hfs.
+ eapply stk_transport_disjoint; [exact ST'| exact MU2| exact WM2| cbn; lia].
+ exists j0. exact FRt2.
+ eapply hglob_P_munch; [eapply hglob_P_rpres; [exact PRES| exact GL]| exact MU2| exact WM2|].
constructor; [cbn [fst snd]; lia| constructor].
Qed.
End Loop.

#[using="FD1 HBlt HCEIL HIx TGT PF1 PFK"] Theorem trun_ok : trun_stmt usp0 tid ppw path data fs fds0.
Proof.
unfold trun_stmt. intros until fc. intros HI FIT Hgp Htp FRM TOKN KOK KFAIL. subst gp tp.
destruct HI as [D HP DSH SH Hcap Hlen (junk & BLK) (errv & ERR) Hfds Hfs HBUD].
pose proof (f_sp _ _ _ _ _ D) as SPB. pose proof (f_ceil _ _ _ _ _ D) as CEIL.
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
pose proof (heapc_blk B _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _ & Bimg).
unfold alloc_ceiling in Bhi. unfold RIMG_LO, RIMG_HI in Bimg.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
assert (LEN26 : Z.of_nat (length data) < 2^26) by lia.
word_range ppw PPR.
destruct (stk_split rsegs m LO (usp0 - 128) usp0 (f_stk _ _ _ _ _ D) ltac:(lia)) as [ST _].
pose proof (pris_pointwise m (f_pris _ _ _ _ _ D)) as PW.

assert (INIT : rw_cells rsegs m 0x76f80 (FLAGC 0 0)).
{ unfold FLAGC. apply (rw_cells_img m 0x76f80 (repeat (Z_to_bv 8 0) 5)); change (Z.of_nat (length (repeat (Z_to_bv 8 0) 5))) with 5%Z;
[| vm_compute; reflexivity| lia| lia| cbn; repeat split; exact I| reflexivity| reflexivity].
intros i Hi. apply (PW i). lia. }
unfold FLAGC in INIT.

assert (GOTC : rw_cells rsegs m 0x658b0 [C8 (Z_to_bv 64 0)]).
{ apply (rw_cells_img m 0x658b0 (le8 (Z_to_bv 64 0))); change (Z.of_nat (length (le8 (Z_to_bv 64 0)))) with 8%Z;
[| vm_compute; reflexivity| lia| lia| cbn; exact (conj I I)| reflexivity| reflexivity].
intros i Hi. apply (PW i). lia. }

assert (LOCC : rw_cells rsegs m 0x77bd0 [C8 (Z_to_bv 64 0x97ec8)]).
{ split; [split; [cbn; exact (conj I I)| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact (f_loc _ _ _ _ _ D)]| apply (data_wr_at m 0x77bd0 8); lia]. }
assert (LOCK : rw_cells rsegs m 0x97f68 [C4 (Z_to_bv 64 0)]).
{ apply (rw_cells_img m 0x97f68 (le4 (Z_to_bv 64 0))); change (Z.of_nat (length (le4 (Z_to_bv 64 0)))) with 4%Z;
[| vm_compute; reflexivity| lia| lia| cbn; exact (conj I I)| reflexivity| reflexivity].
intros i Hi. apply (PW i). lia. }

assert (ATXC : rw_cells rsegs m 0x97c48 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 248 (repeat (Z_to_bv 8 0) 248); C8 (Z_to_bv 64 0)]).
{ apply (rw_cells_img m 0x97c48 (repeat (Z_to_bv 8 0) 296)); change (Z.of_nat (length (repeat (Z_to_bv 8 0) 296))) with 296%Z;
[| vm_compute; reflexivity| lia| lia| vm_compute; repeat split; exact I| vm_compute; reflexivity| reflexivity].
intros i Hi. apply (PW i). lia. }

pose proof (heapc_need_locks B _ _ _ _ HP) as NL. unfold RLIBC in NL. cbn [Z.add] in NL.
assert (NLC : QlEo.ro_cells rsegs m 0x97e93 [C1 (Z_to_bv 8 0)]) by (split; [cbn; exact (conj I I)| cbn [QbVh.cells_bytes QbVh.cbytes app]; exact NL]).

assert (GL : hglob_P m).
{ apply hglob_P_init. intros a Ha. unfold hglob_rng_P in Ha. apply (PW a). lia. }
unfold RERRNO, RATP in ERR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl (ARMW usp0) m) as MU. unfold ARMW in MU.
apply rz_evt; [exact MOK|]. unfold TRUN_SYM.
carve_frame 80%nat ST.
replace (usp0 + -128 + -80) with (usp0 + -208) in * by lia.
carve_frame 48%nat ST.
replace (usp0 + -208 + -48) with (usp0 + -256) in * by lia.
do 10 step.
do 5 step.
step.
step. step.
change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). if_truex.
step. stepz.
step. step. step.

step. stepz. stepz. stepz. stepz. stepz.
do 5 step.
step.
step. step.
step. try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). if_truex.
step.
step.
step. step. try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). if_falsex.
step. step. if_falsex.
step. stepz.
step. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; reflexivity).
step. step. if_truex.
do 6 step.
stepz. stepz. stepz.
step. step.
step. step. if_falsex. step.
step.
do 5 step. step. step.
step. if_truex.
step. step.
step. if_truex.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (P1 : PRE1 buf cap s5 s6 s7 mx md A) end.
{ lazymatch goal with |- PRE1 _ _ _ _ _ ?mx _ _ =>
assert (SK1 : stk rsegs mx LO (usp0 - 208));
[ apply (stk_merge rsegs mx LO (usp0 - 256) (usp0 - 208)); [replace (usp0 - 256) with (usp0 + -256) by lia; exact ST| | lia];
pose proof (stk_of_rw_cells rsegs mx _ _ FR0) as S3; cbn [cells_size csize Nat.add length take] in S3;
replace (usp0 + -256 + Z.of_nat 48) with (usp0 - 208) in S3 by lia; replace (usp0 + -256) with (usp0 - 256) in S3 by lia; exact S3 |];
assert (SK : stk rsegs mx LO (usp0 - 128));
[ apply (stk_merge rsegs mx LO (usp0 - 208) (usp0 - 128)); [exact SK1| | lia];
pose proof (stk_of_rw_cells rsegs mx _ _ FR) as S3; cbn [cells_size csize Nat.add length take] in S3;
replace (usp0 + -208 + Z.of_nat 80) with (usp0 - 128) in S3 by lia; replace (usp0 + -208) with (usp0 - 208) in S3 by lia; exact S3 |] end.
constructor.
- eapply DFX_arm; [apply DF_DFX; exact D| exact MU| exact WM| exact SK| eapply atx_of_chunks; [exact ATXC| exact INIT]].
- eapply (heapc_frame B); [exact HP| | exact WM| exact MI].
intros a Ha NCW. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. repeat split; intros [X1 X2]; apply NCW.
+ right; left. unfold alloc_ceiling. lia.
+ right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
+ right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
+ right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
+ right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
+ right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
- exact DSH.
- exact SH.
- exact HBUD.
- exists errv. unfold RERRNO, RATP. exact ERR.
- exact LOCC.
- exact LOCK.
- exact INIT.
- exists junk. exact BLK.
- eapply clearr_munch; [intros a Ha; apply (PW a); lia| exact MU| ivs_lia| lia| lia].
- eapply clearr_munch; [intros a Ha; apply (PW a); lia| exact MU| ivs_lia| lia| lia].
- exact Hfds.
- exact Hfs.
- exact SK1.
- eexists. unfold trun_frame. replace (usp0 - 208) with (usp0 + -208) by lia. exact FR.
- eapply hglob_P_munch; [exact GL| exact MU| exact WM| ivs_lia]. }

pose proof BLK as [[[WFb _] BAb] _]. cbn [cells_bytes cbytes app] in BAb. apply bytes_at_app in BAb as [BAb _].
pose proof (bytes_at_read rsegs _ buf data 2 1 BAb ltac:(lia) ltac:(lia)) as HR2.
change (Z.to_nat 2) with 2%nat in HR2. rewrite (nth_read 2%nat data (Z_to_bv 8 0)) in HR2 by lia.
pose proof (bv_unsigned_in_range 8 (nth 2 data (Z_to_bv 8 0))) as R2. unfold bv_modulus in R2. cbn in R2. fold (hb data 2) in R2.
assert (KF : forall (m' : mem) (md' : Model) (A' : hstate) (LK : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
RPOST usp0 tid ppw path fs buf cap LK m' md' A' [] -> 0 < pl ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (usp0 - 128)) gp' (Z_to_bv 64 0x77c00) t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 2) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 cl) (Z_to_bv 64 (buf + 6 + cl)) (Z_to_bv 64 pl)
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET) fc' None m' (seg_rom rsegs)) md') Tfail).
{ intros. eapply KFAIL; [eassumption| lia]. }

assert (DISPATCH : forall (mx : mem) (rax q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 w2 w3 q3 q4 q5 q6 : word) (pcz : Z),
PRE1 buf cap s5 s6 s7 mx md A -> (pcz = 0x20eac \/ pcz = 0x20ef8) ->
realizes rsegs (mkCfg (MS (mkR rax (Z_to_bv 64 (usp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77c00) q0 q1 q2
(Z_to_bv 64 pl) (Z_to_bv 64 (buf + 6 + cl)) r0 r1 r2 r3 r4 r5 r6 r7
w2 w3 (Z_to_bv 64 0x76f80) (Z_to_bv 64 (Z.of_nat (calls_of data))) s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 pcz) fc None mx (seg_rom rsegs)) md)
(if pl =? 0 then t_emit (W 1 (zero_lines 1)) Tok else (t_emit (W 1 (zero_lines 1)) Tok)   )).
{ intros mx rax q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 w2 w3 q3 q4 q5 q6 pcz P1x Hpc.
pose proof (heapc_model_ok B _ _ _ _ (p_heap _ _ _ _ _ _ _ _ P1x)) as MOKx.
apply rz_evt; [exact MOKx|].
destruct (Z.eq_dec pl 0) as [PL0|PLP].
- replace (pl =? 0) with true by (symmetry; apply Z.eqb_eq; exact PL0).
destruct Hpc as [-> | ->]; step; [if_truex| if_falsex]; apply evt_RZ_done;
(eapply (seg_empty buf cap s5 s6 s7 s8 s9 s10 s11 Tok TOKN Hcap Hlen FIT KOK); [exact P1x| exact FRM| exact PL0]).
- replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; exact PLP).
destruct Hpc as [-> | ->]; step; [if_falsex| if_truex]; apply evt_RZ_done;
(eapply (seg_alloc buf cap s5 s6 s7 s8 s9 s10 s11 Tok TOKN Hcap Hlen FIT KOK Tfail); [exact P1x| exact FRM| lia| intros; eapply KF; [eassumption| lia]]). }
step.
destruct (Z.eq_dec cl 0) as [CL0|CLP].
-
if_truex. step. apply evt_RZ_done.
replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat (calls_of data)) : word) by (unfold calls_of; rewrite CL0; reflexivity).
eapply DISPATCH; [exact P1| right; reflexivity].
-
if_falsex. step. step. step. apply evt_RZ_done.
unfold zxb. fold (hb data 2).
match goal with |- context [Z_to_bv 64 ?e] =>
lazymatch e with context [Z.land] =>
replace e with (Z.of_nat (calls_of data));
[| unfold calls_of; destruct (Z.to_nat (cfglen_of data)) eqn:E; [lia|];
rewrite !unsigned_lit by lia; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4;
pose proof (Z.mod_pos_bound (hb data 2) 4 ltac:(lia)); lia] end end.
eapply DISPATCH; [exact P1| left; reflexivity].
Qed.
End Target.
End AmbT.
