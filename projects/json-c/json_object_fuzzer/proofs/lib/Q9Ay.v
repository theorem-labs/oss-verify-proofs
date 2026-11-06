(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QnDM_c1 Q2qa Qy5Y QytA QJE4 QZAi QUZl Q7S0 Ql2m QGeV QLsg QWTl QDUx Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ag_frame (sc : Z) (j : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
[C8 (Z_to_bv 64 (sc * 2)); CB 40 j; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section AG1.
Variables (sc lo : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.

End AG1.

Section EPI.
Variables (lo : Z).
Hypothesis CLO : alloc_ceiling <= lo.

End EPI.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5 QDUx.Mq7.
Import QDUx.Mqb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lxor_b2z_1 b : Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. destruct b; reflexivity. Qed.

#[using="Type"] Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma ltb99_leb100 b : (99 <? b) = (100 <=? b).
Proof. destruct (Z.ltb_spec 99 b), (Z.leb_spec 100 b); try reflexivity; lia. Qed.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition seqW : list (Z * Z) := [(CTX + 848, CTX + 913)]%Z.

End SEQ.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition mm_usage1 (st1 : mstate) (sc usage0 : Z) : Z :=
if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0.

Definition mm_cnt_red (sc size cnt usage1 : Z) (nosmall : bool) : Z :=
if (usage1 <? 4 * cnt) && negb nosmall then
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt
else cnt.

Definition mm_small (size req usage1 cnt needed : Z) : Z * Z :=
let req := round_up_pg (req + IB + UNIT) in
if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed).

Definition mm_final (size req usage1 cnt : Z) (nosmall : bool) : Z * Z :=
let needed := round_up_pg (size * cnt + UNIT) in
if negb nosmall && (cnt <=? 7) then mm_small size req usage1 cnt needed else (cnt, needed).

#[using="Type"] Lemma land_4095_wrap x : 0 <= x -> x + 16 <= 2^64 ->
Z.land (18446744073709551600 - x) 4095 = Z.land (- (x + 16)) 4095.
Proof.
intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
replace (18446744073709551600 - x) with (- (x + 16) + 2^52 * 2^12) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

#[using="Type"] Lemma land_4095_wrap20 x : 0 <= x -> x + 20 <= 2^64 ->
Z.land (18446744073709551596 - x) 4095 = Z.land (- (x + 20)) 4095.
Proof.
intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
replace (18446744073709551596 - x) with (- (x + 20) + 2^52 * 2^12) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

#[using="Type"] Lemma land_4095_word z : Z.land (bv_unsigned (Z_to_bv 64 z)) 4095 = Z.land z 4095.
Proof.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^52 * 2^12).
change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
apply Z.mod_mod_divide. exists (2^52). reflexivity.
Qed.

#[using="Type"] Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof. change (Z.land x 3) with (Z.land x (Z.ones 2)). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^2) ltac:(lia)). lia. Qed.

#[using="Type"] Lemma land_4095_range y : 0 <= Z.land y 4095 < 4096.
Proof. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

#[using="Type"] Lemma round_up_pg_alt x : Z.land (- x) 4095 + x = round_up_pg x.
Proof. unfold round_up_pg. change (PGSZ - 1) with 4095. lia. Qed.

#[using="Type"] Lemma round_up_pg_range x : 0 <= x -> x <= round_up_pg x < x + 4096.
Proof. intros. unfold round_up_pg. change (PGSZ - 1) with 4095. pose proof (land_4095_range (- x)). lia. Qed.
End RC__1.

Ltac bool_hyp b K := destruct b; cbn in K; first [reflexivity | discriminate | congruence | (exfalso; apply K; reflexivity)].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

End MMC.

End RC__2.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma meta_word_upd_af mr a f' : meta_word (m_set_avail a (m_set_freed f' mr)) = meta_word mr.
Proof. reflexivity. Qed.

#[using="Type"] Lemma decay_bounces_eq sc st :
decay_bounces sc st =
if ((7 <=? sc) && (sc <? 39)) && negb (bounces st (sc - 7) =? 0) then set_bounce (sc - 7) (bounces st (sc - 7) - 1) st else st.
Proof. reflexivity. Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.

Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.

End AVZ.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.

Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

Definition t1_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 (Z_to_bv 64 (CTX + 8 * (sc + 10))) a4 a5 a6 a7
(Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

End T1.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

#[using="Type"] Lemma dequeue_self_eq sc g st :
m_next (get_meta_rec st g) = Some g ->
dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
rewrite upd_meta_put. reflexivity.
Qed.

#[using="Type"] Lemma dequeue_other_eq sc g nx pv st :
m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
active st sc = Some g ->
dequeue (LActive sc) g st =
let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
let st3 := set_active sc (Some nx) st2 in
put_meta g (clr (get_meta_rec st g)) st3.
Proof.
intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
rewrite !upd_meta_put.
match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.

Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

Definition deq_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 (Z_to_bv 64 (CTX + 8 * (sc + 10))) a4 a5 a6 a7
(Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

End DEQ.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.

Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

Definition m_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition full_skip : bool := (f =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0).

End M.

End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

End SPANLOOP.

Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.

Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

Definition act_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

End ACT.

End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ENTRY.
Variables (st : mstate) (m : mem) (sc lo : Z).

Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

End ENTRY.

End RC__1.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import Q9A7.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 Q4J3.Mq2.
Import QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 QDUx.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition mm_ok_st (st : mstate) (rid : N) (n : Z) : mstate :=
upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1) (set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, 4096)) c))) st.

End RC__1.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 QDUx.Mq1 QPjm.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma unk_agree_ext st st' o m :
unk_agree st o m -> s_regions st' = s_regions st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
s_groups st' = s_groups st -> unk_agree st' o m.
Proof.
intros UA ER ES EG rid r off h Hr Hk Ho Hc NG. rewrite ER in Hr. rewrite ES in Hc.
apply (UA rid r off h Hr Hk Ho Hc). intros (b & gh & Hb & Hf & Hx). apply NG. exists b, gh. rewrite EG. auto.
Qed.

#[using="Type"] Lemma unk_agree_munch st o m m' W :
unk_agree st o m -> munch W m m' ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> disjoint_from W (r_base r) (round_up_pg (r_len r))) ->
(forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
unk_agree st o m'.
Proof.
intros UA MU HD HB rid r off h Hr Hk Ho Hc NG.
rewrite <- (UA rid r off h Hr Hk Ho Hc NG). apply MU.
destruct (HB rid r Hr) as [B0 B1]. rewrite wa_unsigned by lia.
eapply disjoint_outside; [apply (HD rid r Hr Hk)| lia].
Qed.

#[using="Type"] Lemma unk_agree_write st o m a bs :
unk_agree st o m ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
a + Z.of_nat (length bs) <= r_base r \/ r_base r + round_up_pg (r_len r) <= a) ->
(forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
unk_agree st o (write_to_mem m (wa a) bs).
Proof.
intros UA HD HB A0 A1 rid r off h Hr Hk Ho Hc NG.
rewrite <- (UA rid r off h Hr Hk Ho Hc NG). destruct (HB rid r Hr) as [B0 B1].
rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (HD rid r Hr Hk);
destruct (Z.leb_spec0 a (r_base r + off)); destruct (Z.ltb_spec0 (r_base r + off) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity; exfalso; lia.
Qed.

#[using="Type"] Lemma mrel_same st st' :
s_regions st' = s_regions st -> s_next_rid st' = s_next_rid st -> s_reserved st' = s_reserved st -> mrel st st'.
Proof.
intros ER EN ES. split; [| rewrite EN; lia | exact ES].
intros rid r H. exists r. rewrite ER. repeat split; auto. lia.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).

Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

End FASTCORE.

#[using="Type"] Lemma malloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> malloc_fp st st2 lo sp1 a -> malloc_fp st st2 lo sp2 a.
Proof.
intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

#[using="Type"] Lemma malloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> malloc_fp st sta lo sp a -> malloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply malloc_fp_mono; [exact HR| exact H]. Qed.

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (bail : QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).

Hypothesis MF : MFACTS st LB.

Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

End ASCALL.

End RC__1.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3.
Import QPjm.Mq3 QWTl.Mq4 QDUx.Mqa.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition seq_st (ns sc : Z) (st : mstate) : mstate := record_seq sc (upd_ctx (set_seq ns) st).

#[using="Type"] Lemma free_fp_ctx_only : forall st st' lo sp a,
s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
free_fp st' lo sp a -> free_fp st lo sp a.
Proof. intros st st' lo sp a ER ES EG H. eapply (free_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

#[using="Type"] Lemma fm_facts_ctx : forall st f g,
c_free_meta_head (f (s_ctx st)) = c_free_meta_head (s_ctx st) -> fm_facts st g -> fm_facts (upd_ctx f st) g.
Proof. intros st f g E H hd Hh. unfold ctx in *. cbn [upd_ctx s_ctx] in Hh. rewrite E in Hh. exact (H hd Hh). Qed.

#[using="Type"] Lemma seq_range_test sc : 0 <= sc <= 63 ->
(31 < Z.land (sc + -7) 18446744073709551615 <-> sc_in_seq_range sc = false).
Proof.
intros Hsc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
unfold sc_in_seq_range.
destruct (Z.lt_ge_cases sc 7) as [L|GE].
- replace ((sc + -7) mod 2 ^ 64) with (sc + -7 + 2^64).
2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try lia.
- rewrite Z.mod_small by lia.
destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try discriminate; lia.
Qed.

#[using="Type"] Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.

End RC__1.
End Mqb.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QDUx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Qy5Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Lemma f128_ge_canon : forall a b, f128_ge (canon a) (canon b) = f128_ge a b.
Proof. intros. unfold f128_ge. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_to_d_canon : forall a, f128_to_d (canon a) = f128_to_d a.
Proof. intros. unfold f128_to_d. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.

Tactic Notation "callw" tactic3(tac) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
end.

Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).

Local Open Scope bv_scope.

