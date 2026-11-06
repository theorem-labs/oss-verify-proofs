(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QnDM_c1 Q2qa Qy5Y QytA QJE4 QZAi QUZl Q7S0 Ql2m QGeV QLsg QWTl Q6q3.
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
Import QLsg.
Import QWTl.Mq5.
Import QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ta_frame (s1v s2v rav : word) (j0 j1 : list byte) : list cell :=
[CB 64 j0; C8 s2v; C8 s1v; CB 8 j1; C8 rav].

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.

Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

End FIN.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3 Qnxq QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QPjm.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition AS_STACK (fuel : nat) : Z := 128 + 96 * Z.of_nat fuel.

#[using="Type"] Lemma AS_STACK_S f : AS_STACK (S f) = AS_STACK f + 96.
Proof. unfold AS_STACK. rewrite Nat2Z.inj_succ. lia. Qed.
#[using="Type"] Lemma AS_STACK_ge f : 128 <= AS_STACK f.
Proof. unfold AS_STACK. lia. Qed.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import Q9A7.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 Q4J3.Mq2.
Import QJE4.Mq0 QJE4.Mq1 QWTl.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma carve_st_regions st p : s_regions (carve_st st p) = s_regions st.
Proof.
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx st)); reflexivity.
Qed.

Definition mp_strict (a : range_ans) : Prop := match a with RgErr e => e <> 38 | RgDone b => b = true end.
#[using="Type"] Lemma dec_mprotect_rw_weaken A L rsp a : dec_mprotect_rw A L rsp = Some a -> dec_mprotect A L rsp = Some a /\ mp_strict a.
Proof.
unfold dec_mprotect_rw. destruct (dec_mprotect A L rsp) as [[e|b]|]; [| | discriminate].
- destruct (Z.eqb_spec e ENOSYS); [discriminate|]. intros H; inversion H; subst. split; [reflexivity|]. cbn. unfold ENOSYS in *. exact n.
- destruct b; [| discriminate]. intros H; inversion H; subst. split; reflexivity.
Qed.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1.
Import QWTl.Mq5.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq2 QPjm.Mq3 Q4J3.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Module A2 := QWTl.Mq5.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma area_in_live : forall st a ar r x, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st a ar r x WF Ha Hr Hx. destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
pose proof (area_lr_lo st a ar r WF Ha Hr). lia.
Qed.

#[using="Type"] Lemma group_in_live : forall st b gh r x, regions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st b gh r x WF Hb Hr Hx. destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

Definition clear_range (st : mstate) (lo n : Z) : Prop :=
forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

#[using="Type"] Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="Type"] Lemma image_clear_of_ranges_free st lo n x : s_reserved st = agent_reserved -> ranges_free (live_ranges st) lo n = true ->
0x10000 <= x < 0x1b000 -> ~ (lo <= x < lo + n).
Proof.
intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)). cbn in *. lia.
Qed.

#[using="Type"] Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).

Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

#[using="Hr"] Lemma gr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="Type"] Lemma gr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma gr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
rewrite gr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
- rewrite lookup_insert_eq in H. left. split; congruence.
- rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
#[using="Type"] Lemma gr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite gr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma gr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite gr_regions, lookup_insert_eq. reflexivity. Qed.
#[using="Hr"] Lemma gr_conc q : conc st' q = conc st q.
Proof.
unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
- rewrite E, gr_lookup_new, Hr. reflexivity.
- rewrite gr_lookup_old by exact NE. reflexivity.
Qed.
#[using="RC__ OFF OAL"] Lemma gr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma ptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QytA.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 QWTl.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma self_word2 b3 : 0 <= b3 < 256 ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (Z.land b3 31 mod 32))) = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
intros.
assert (0 <= Z.land b3 31 < 32).
{ split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QytA.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 QWTl.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1.
Import Q9A7.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QytA.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 QWTl.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma le4_sx32 (v : word) : le4 (sx32 v) = le4 v.
Proof.
apply le4_congr. unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite mod64_mod32, swrap32_eq'.
set (u := bv_unsigned v) in *. clearbody u. Z.div_mod_to_equations. lia.
Qed.

End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.
End RC__1.

Import QLsg.
Import QWTl.Mq5.

Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.

Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate :=
upd_ctx (set_mmap_counter v)
(put_meta g (big_meta rid n)
(put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st)))).

#[using="Type"] Lemma big_ml_eq n : 0 <= n < 2^63 -> big_ml n = (n + 4115) / 4096.
Proof.
intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma cell_read_hdr_havoc_fresh : forall st b o,
(s_shadow st) !! (fst b) = None -> snd b mod 16 = 0 -> 0 <= o < 12 ->
exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.

#[using="Type"] Lemma big_word_eq rid n : 0 <= n < 2^63 ->
Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (n + 4115))) 12))) 12))) 4064)
= wz (meta_word (big_meta rid n)).
Proof.
intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
rewrite (unsigned_lit (n + 4115)) by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite (unsigned_lit ((n + 4115) / 2 ^ 12)) by (Z.div_mod_to_equations; lia). rewrite Z.shiftl_mul_pow2 by lia.
rewrite unsigned_lit by (Z.div_mod_to_equations; lia). change (2 ^ 12) with 4096.
rewrite (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.lor_add _ _ 12); [| lia| lia| change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia].
unfold wz. f_equal. lia.
Qed.

#[using="Type"] Lemma meta_word_big_range rid n : 0 <= n < 2^63 -> 0 <= meta_word (big_meta rid n) < 2^64.
Proof.
intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma ctr_word c : 0 <= c -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv c)) + 1)) = wz (sxv (u32 (c + 1))).
Proof.
intros Hc. rewrite addw_word. rewrite wz_unsigned by apply sxv_range. f_equal. apply sxv_congr.
unfold u32. rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="Type"] Lemma le4_sxv v : le4 (wz (sxv v)) = le4 (wz v).
Proof.
apply le4_congr. rewrite wz_unsigned by apply sxv_range. rewrite sxv_mod32.
unfold wz. rewrite Z_to_bv_unsigned. change (bv_modulus 64) with (2^64). symmetry. apply QnDM_c1.Mq0.mod_mod_pow2. lia.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.

Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^63 - 4097.
Hypothesis CLO : alloc_ceiling <= lo.

End SUCC.

End RC__2.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition enf_off0 (o : mem) (st1 : mstate) (b : aptr) (stride idx : Z) : Z :=
let q := snd b + (16 + stride * idx) in
if rdv pans_mem o st1 (fst b, q + -3) =? 0 then Z.land (c_mmap_counter (ctx st1)) 255
else Z.land (rdv pans_mem o st1 (fst b, q + -2) + 256 * rdv pans_mem o st1 (fst b, q + -2 + 1) + 1) 255.

Definition enf_leaf (o : mem) (st1 : mstate) (g b : aptr) (idx n : Z) (st' : mstate) (p : aptr) : Prop :=
exists off, 0 <= off /\ 16 * off + n + 4 <= get_stride (get_meta_rec st1 g)
/\ p = (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx + 16 * off)
/\ st' = havoc p n (fst (enframe_at st1 g idx n off))
/\ p = snd (enframe_at st1 g idx n off)
/\ off = fold_off (enf_off0 o st1 b (get_stride (get_meta_rec st1 g)) idx) ((get_stride (get_meta_rec st1 g) - 4 - n) / 16).

#[using="Type"] Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof. destruct e; reflexivity. Qed.

End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma srliw_small a k : 0 <= a < 2^31 -> 0 <= k -> bv_swrap 32 (Z.shiftr (bv_wrap 32 a) k) = Z.shiftr a k.
Proof.
intros Ha Hk. change (bv_wrap 32 a) with (a mod 2^32). rewrite Z.mod_small by lia.
apply swrap32_small. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

#[using="Type"] Lemma lor_small n a b : 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
intros Hn Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as NN. split; [exact NN|].
destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
assert (P : 0 < Z.lor a b).
{ destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply zb_lor_eq0 in E; lia|]. lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia.
- apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia))). lia.
Qed.

#[using="Type"] Lemma shiftr_small n a k : 0 <= a < 2^n -> 0 <= k -> 0 <= Z.shiftr a k < 2^n.
Proof.
intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Definition clz_pow (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
let v2 := Z.lor v1 (Z.shiftr v1 2) in
let v3 := Z.lor v2 (Z.shiftr v2 4) in
let v4 := Z.lor v3 (Z.shiftr v3 8) in
Z.land (v4 + 1) (Z.lxor v4 18446744073709551615).
Definition clz_notv (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
let v2 := Z.lor v1 (Z.shiftr v1 2) in
let v3 := Z.lor v2 (Z.shiftr v2 4) in
let v4 := Z.lor v3 (Z.shiftr v3 8) in
Z.lxor v4 18446744073709551615.
Definition clz_fn (x : Z) : bool := (clz_pow x =? 2 ^ Z.log2 x) && (0 <=? clz_notv x) && (clz_notv x <? 2^64).
#[using="Type"] Lemma clz_check_true : forallb clz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma clz_pow_eq x : 11 <= x < 8192 -> clz_pow x = 2 ^ Z.log2 x /\ 0 <= clz_notv x < 2^64.
Proof.
intros Hx. pose proof (forallb_zseq clz_fn 11 8181 x clz_check_true ltac:(lia) ltac:(lia)) as X. unfold clz_fn in X.
apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.leb_le in X2. apply Z.ltb_lt in X3. split; [exact X1| split; [exact X2| exact X3]].
Qed.

Definition stc_q (q : Z) : Z :=
if q <? 10 then q else
let x := q + 1 in
let i := 4 * Z.log2 x - 4 in
let i := if size_class (i + 1) <? x then i + 2 else i in
if size_class i <? x then i + 1 else i.
Definition stc_fn (q : Z) : bool :=
let sc := stc_q q in (0 <=? sc) && (sc <? 48) && (q + 1 <=? size_class sc)
&& ((q <? 10) || ((3 <=? Z.log2 (q + 1)) && (Z.log2 (q + 1) <=? 12))).
#[using="Type"] Lemma stc_check_true : forallb stc_fn (zseq 0 8191) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma size_to_class_q n : 0 <= n -> size_to_class n = stc_q ((n + 3) / 16).
Proof.
intros Hn. unfold size_to_class, stc_q, IB, clz32.
replace (Z.shiftr (n + 4 - 1) 4) with ((n + 3) / 16) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
set (q := (n + 3) / 16). cbv zeta.
replace ((28 - (31 - Z.log2 (q + 1))) * 4 + 8) with (4 * Z.log2 (q + 1) - 4) by lia.
reflexivity.
Qed.

#[using="Type"] Lemma size_to_class_props n : 0 <= n < MMAP_THRESHOLD ->
0 <= size_to_class n < 48 /\ n + 4 <= 16 * size_class (size_to_class n)
/\ (10 <= (n + 3) / 16 -> 3 <= Z.log2 ((n + 3) / 16 + 1) <= 12).
Proof.
intros Hn. unfold MMAP_THRESHOLD in Hn. rewrite size_to_class_q by lia.
assert (Q : 0 <= (n + 3) / 16 < 8191) by (Z.div_mod_to_equations; lia).
pose proof (forallb_zseq stc_fn 0 8191 ((n + 3) / 16) stc_check_true ltac:(lia) ltac:(lia)) as X. unfold stc_fn in X. cbv zeta in X.
apply andb_prop in X. destruct X as [X X4]. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3.
split; [lia|]. split; [Z.div_mod_to_equations; lia|].
intros HQ. apply orb_prop in X4. destruct X4 as [X4|X4]; [apply Z.ltb_lt in X4; lia|].
apply andb_prop in X4. destruct X4 as [X5 X6]. apply Z.leb_le in X5. apply Z.leb_le in X6. lia.
Qed.

End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3.
Import QPjm.Mq3 QWTl.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma bounces_set st i v j :
bounces (set_bounce i v st) j = if Z.eqb j i then v else bounces st j.
Proof.
unfold bounces, set_bounce, upd_ctx. cbn [ctx s_ctx c_bounces set_bounces_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma bouncess_set st i v : 0 <= i < 32 ->
bouncess (set_bounce i v st) = upd (bouncess st) (Z.to_nat i) (b8 v).
Proof.
intros Hi. unfold bouncess.
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (bounces st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite bounces_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

#[using="Type"] Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
#[using="Type"] Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

#[using="Type"] Lemma addiw_small v c : 0 <= v < 2^31 -> -2^31 <= v + c < 2^31 ->
Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + c)) = Z_to_bv 64 ((v + c) mod 2^64).
Proof.
intros Hv Hc. rewrite unsigned_lit by lia. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (v + c))). f_equal.
rewrite swrap32_eq'.
change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
Z.div_mod_to_equations. lia.
Qed.
End RC__1.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma set_group_ai_eq st b gh ai :
get_group st b = Some gh -> set_group_active_idx b ai st = put_group b (g_meta gh) ai (del_group b st).
Proof.
intros Hb. unfold set_group_active_idx, put_group, del_group. rewrite Hb. cbn [s_groups set_groups].
rewrite insert_delete_eq. reflexivity.
Qed.

#[using="Type"] Lemma put_group_del st b mo ai : put_group b mo ai (del_group b st) = put_group b mo ai st.
Proof. unfold put_group, del_group. cbn [s_groups set_groups]. rewrite insert_delete_eq. reflexivity. Qed.

#[using="Type"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. intros MW. rewrite <- (meta_word_last_idx mr MW). change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

#[using="Type"] Lemma sxv_inj a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> sxv a = sxv b -> a = b.
Proof.
intros Ha Hb E. pose proof (sxv_mod32 a) as Ea. pose proof (sxv_mod32 b) as Eb. rewrite E in Ea. rewrite Ea in Eb.
rewrite !Z.mod_small in Eb by lia. exact Eb.
Qed.

#[using="Type"] Lemma mask_upto_range k : 0 <= k <= 31 -> 0 < mask_upto k < 2^32.
Proof.
intros Hk. unfold mask_upto. split.
- assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. lia.
- assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

#[using="Type"] Lemma land_mask_31 x : 0 <= x -> x mod 32 = Z.land x 31.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

#[using="Type"] Lemma lxor_range31 a b : 0 <= a < 2^31 -> 0 <= b < 2^31 -> 0 <= Z.lxor a b < 2^31.
Proof.
intros Ha Hb. split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
assert (Ha' : Z.log2 a < 31) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
assert (Hb' : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed.

#[using="Type"] Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
intros MW. pose proof (meta_word_sc mr MW) as E. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range mr MW) as WR.
apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, Z.shiftr_spec by lia.
destruct (Z.eq_dec n 0) as [->|NZ].
- rewrite Z.testbit_even_0. replace (Z.testbit 126 0) with false by reflexivity. apply Bool.andb_false_r.
- replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_even_succ by lia.
rewrite <- E. rewrite Z.land_spec, Z.shiftr_spec by lia.
change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia.
replace (Z.succ (n - 1) + 5) with (n - 1 + 6) by lia. reflexivity.
Qed.

#[using="Type"] Lemma span_loop_bounds F : forall cnt span size, cnt <= span_loop F cnt span size <= cnt + Z.of_nat F.
Proof.
induction F as [|F IH]; intros; cbn [span_loop]; [lia|].
rewrite Nat2Z.inj_succ. destruct (_ <? _); [|lia]. pose proof (IH (cnt + 1) (span + size) size). lia.
Qed.

#[using="Type"] Lemma ai_byte_land w v : 0 <= w -> 0 <= v ->
Z.land ((Z.lor (Z.land w (2^64 - 32)) (Z.land v 31)) mod 256) 31 = Z.land v 31.
Proof.
intros Hw Hv. apply Z.bits_inj'. intros n Hn.
change 256 with (2^8). change 31 with (Z.ones 5).
rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
replace (2^64 - 32) with (Z.shiftl (2^59 - 1) 5) by reflexivity.
destruct (Z.ltb_spec n 5).
- rewrite Z.shiftl_spec_low by lia. replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia). rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l. reflexivity.
- replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !Bool.andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma le1_mod z : le1 (Z_to_bv 64 z) = [b8 (z mod 256)].
Proof.
unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.

#[using="Type"] Lemma land31_range x : 0 <= Z.land x 31 <= 31.
Proof.
split; [apply Z.land_nonneg; right; lia|].
apply Z.ldiff_le; [lia|].
apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit x n), (Z.testbit 31 n); reflexivity.
Qed.

#[using="Type"] Lemma swrap32_small z : - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
intros. rewrite swrap32_eq'.
change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma sraiw1_small v : 0 <= v < 2^31 ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (wz v))) 1)) = wz (Z.shiftr v 1).
Proof.
intros Hv. rewrite wz_unsigned by lia. rewrite (swrap32_small v) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
rewrite swrap32_small by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

#[using="Type"] Lemma land1_mod2 a : Z.land a 1 = a mod 2.
Proof. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma even_of_land1 a : Z.even a = (Z.land a 1 =? 0).
Proof.
rewrite land1_mod2, Zeven.Zeven_odd_bool, Zmod_odd. destruct (Z.odd a); reflexivity.
Qed.

End RC__2.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2; idtac "ra=" x1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le1_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 1 z = le1 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_lit z) by lia
| _ => idtac
end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Local Open Scope Z_scope.

Definition bz (l : list byte) : list Z := map bv_unsigned l.
Lemma bz_length : forall l, length (bz l) = length l.
Proof. intros. apply length_map. Qed.

Lemma zsub_length : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l -> length (zsub l i n) = Z.to_nat n.
Proof. intros l i n Hi Hn H. unfold zsub, zlength in *. rewrite length_firstn, length_skipn. lia. Qed.

Lemma znth_nth : forall l i, 0 <= i -> znth l i = nth (Z.to_nat i) l 0.
Proof. intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|reflexivity]. Qed.

Lemma nth_error_zsub : forall l i n k, 0 <= i -> (k < Z.to_nat n)%nat -> (Z.to_nat i + k < length l)%nat ->
nth_error (zsub l i n) k = Some (znth l (i + Z.of_nat k)).
Proof.
intros l i n k Hi Hk Hl. unfold zsub.
rewrite nth_error_firstn. destruct (Nat.ltb_spec k (Z.to_nat n)); [|lia].
rewrite nth_error_skipn. rewrite znth_nth by lia.
replace (Z.to_nat (i + Z.of_nat k)) with (Z.to_nat i + k)%nat by lia.
apply nth_error_nth'. exact Hl.
Qed.

Lemma zsub_ext : forall l1 l2 i n, 0 <= i -> 0 <= n -> i + n <= zlength l1 -> i + n <= zlength l2 ->
(forall j, i <= j < i + n -> znth l1 j = znth l2 j) -> zsub l1 i n = zsub l2 i n.
Proof.
intros l1 l2 i n Hi Hn H1 H2 HE. unfold zlength in *.
apply nth_error_ext. intros k.
destruct (Nat.lt_ge_cases k (Z.to_nat n)) as [Hk|Hk].
- rewrite !nth_error_zsub by lia. f_equal. apply HE. lia.
- rewrite !(proj2 (nth_error_None _ _)) by (rewrite zsub_length by (unfold zlength; lia); lia). reflexivity.
Qed.

Lemma zsub_split3 : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l ->
l = firstn (Z.to_nat i) l ++ zsub l i n ++ skipn (Z.to_nat i + Z.to_nat n) l.
Proof.
intros l i n Hi Hn H. unfold zsub, zlength in *.
rewrite <- (firstn_skipn (Z.to_nat i) l) at 1. f_equal.
rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) l)) at 1. f_equal.
rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.
Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. intros. unfold canon. apply lo64_words. apply lo64_range. Qed.
Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. intros. unfold canon. apply hi64_words; [apply lo64_range | apply hi64_range]. Qed.
Lemma mk128_canon : forall x, mk128 (hi64 x) (lo64 x) = canon x.
Proof.
intros. unfold mk128, canon. pose proof (lo64_range x). pose proof (hi64_range x).
rewrite Z.shiftl_mul_pow2 by lia. rewrite lor_disjoint_add; [lia|].
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.mul_pow2_bits_low by lia. reflexivity.
+ replace (Z.testbit (lo64 x) i) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec (lo64 x) 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma canon_small : forall x, 0 <= x < 2^128 -> canon x = x.
Proof.
intros x Hx. unfold canon, lo64, hi64, wrap64, ONES64. rewrite !land_W64, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (x / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.div_mod x (2^64) ltac:(lia)). lia.
Qed.
Lemma canon_range : forall x, 0 <= canon x < 2^128.
Proof. intros. unfold canon. pose proof (lo64_range x). pose proof (hi64_range x). lia. Qed.
Lemma f128_mul_canon : forall a b, f128_mul (canon a) (canon b) = f128_mul a b.
Proof. intros. unfold f128_mul. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_div_canon : forall a b, f128_div (canon a) (canon b) = f128_div a b.
Proof. intros. unfold f128_div. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon : forall a b, f128_add (canon a) (canon b) = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon_l : forall a b, f128_add (canon a) b = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_sub_canon : forall a b, f128_sub (canon a) (canon b) = f128_sub a b.
Proof. intros. unfold f128_sub. rewrite !lo64_canon, !hi64_canon. apply f128_add_canon_l. Qed.
Lemma f128_le_canon : forall a b, f128_le (canon a) (canon b) = f128_le a b.
Proof. intros. unfold f128_le. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma fixunstfsi_a0_canon : forall a, fixunstfsi_a0 (canon a) = fixunstfsi_a0 a.
Proof. intros. unfold fixunstfsi_a0. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma ulit_lo64 : forall x, bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. intros. apply unsigned_lit. apply lo64_range. Qed.
Lemma ulit_hi64 : forall x, bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. intros. apply unsigned_lit. apply hi64_range. Qed.

Local Open Scope bv_scope.

Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. intros. apply sext32_congr. apply sext32_low. Qed.

