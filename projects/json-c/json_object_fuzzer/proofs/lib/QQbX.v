(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Q2qa QHpk QQWe QTCB QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QHpk QQWe QTCB.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Definition subtf3_entry := 0xd089c%Z.

Lemma land_shl64_low : forall h l, (0 <= l < 2^64)%Z -> Z.land (Z.shiftl h 64) l = 0%Z.
Proof.
intros h l Hl. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- replace (Z.testbit l i) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec l 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma f128_sub_split : forall aLo aHi bLo bHi,
(0 <= bLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
f128_sub (aLo + 2^64 * aHi) (bLo + 2^64 * bHi) = f128_add (aLo + 2^64 * aHi) (bLo + 2^64 * Z.lxor bHi 9223372036854775808).
Proof.
intros aLo aHi bLo bHi Hl Hh. unfold f128_sub. rewrite lo64_words, hi64_words by lia.
unfold mk128, SIGN64. rewrite Z.lor_comm, lor_disjoint_add.
- rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
- rewrite Z.land_comm. apply land_shl64_low. lia.
Qed.

Lemma subtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk rsegs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
mem_inv rsegs m ->
frm0 fc ->
evt rsegs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
(f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd089c) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros ST MI FRM. pose_word_ranges.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
rewrite f128_sub_split by lia.
do 4 zstep.
eapply evt_mono; [ eapply addtf3_spec; eassumption | ].
intros ms' PO. unfold addtf3_post in *.
rewrite (inr64_unsigned_lit (Z.lxor (bv_unsigned a3) 9223372036854775808)) in PO by zrange.
exact PO.
Qed.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 Q5Rg QytA Q4J3 QPjm Qy5Y QJE4 QZAi QUZl Q7S0 QCwx QFqQ Q98Z QkLq QdZ1 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

#[using="Type"] Lemma ram_fp_alloc_fp st lo sp a : ram_fp st lo sp a -> ralloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold ram_fp, ralloc_fp. tauto. Qed.
#[using="Type"] Lemma ram_fp_stack st lo sp a : lo <= a < sp -> ram_fp st lo sp a.
Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> ram_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> ram_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma ram_fp_not_errno st lo sp a : ram_fp st lo sp a -> rregions_wf st -> alloc_ceiling <= lo ->
~ (errno_addr (Z_to_bv 64 0x622e60) <= a < errno_addr (Z_to_bv 64 0x622e60) + 4).
Proof.
intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; unfold RCTX, alloc_ceiling in *; rewrite ?unsigned_lit by lia; try lia.
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2).
pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
Qed.
#[using="Type"] Lemma ram_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> ram_fp st lo sp a.
Proof.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.

#[using="Type"] Lemma ram_fp_area : forall st m lo sp ak ar a, rmrep st m -> (s_areas st) !! ak = Some ar ->
conc st ak <= a < conc st ak + 4096 -> ram_fp st lo sp a.
Proof.
intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
#[using="Type"] Lemma ram_fp_same st st' lo sp a : s_regions st' = s_regions st -> ram_fp st' lo sp a <-> ram_fp st lo sp a.
Proof. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.

Definition ram_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except (ram_fp stF lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 junk; C8 rc_canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma ram_tail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv rsegs m -> meta_slot st q ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (upd_meta q clr_links st) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce5cc) fc None m (seg_rom rsegs)).
Proof.
intros until q. intros MR MI MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
rmeta_chunk MR MSq CH.
unfold alloc_ceiling, RSSP_GUARD, ram_frame in *.
rmeta_open (conc st q) MUq WMq.

st1. st1.
rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
rewrite <- upd_meta_put in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl rsegs mX) as WMs end.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta q clr_links st) mX)
by (eapply rmrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply ram_fp_stack. lia.
- intros x Hx. eapply ram_fp_meta; [exact MR | exact MSq | lia]. }
apply evt_done. unfold ram_ret_post. do 15 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.

#[using="Type"] Lemma ram_b0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo cnt : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv rsegs m -> meta_slot st q -> 0 <= cnt < 2^64 ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (am_took st q cnt) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) (Z_to_bv 64 cnt) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce5c0) fc None m (seg_rom rsegs)).
Proof.
intros until q. intros MR MI MSq HC FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1.
unfold alloc_ceiling, RCTX, RMLOCK in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 24, RCTX + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.

st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
rewrite (conc_aadd st q META_SIZE) by (destruct MSq as (a & ar & k & Ha & Hk & ->); cbn; pose proof MR as (WF' & _);
destruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
unfold META_SIZE, wz. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
change (conc st q) with (conc st1 q).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
[exact MR1 | assumption | exact MSq | exact FR | exact ST | unfold alloc_ceiling; lia | lia]. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq3.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a0 a2 a3 a5 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce300) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
conc st q = conc st g -> q = g.
Proof.
intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
- rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
- exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

#[using="Type"] Lemma rntf_qpath : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
(active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
(active st sc <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
qa_facts st sc g ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rqpath_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc lo st g m (qpath_st st sc g) fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (Z_to_bv 64 sc) a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce0e4) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
unfold alloc_ceiling, RCTX in *.

st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.

pose proof (rmrep_active_read st m sc (wa (RCTX + 80 + 8 * sc)) MR SC eq_refl) as RDA. unfold RCTX in RDA.
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
replace (Z_to_bv 64 (6566376 + sc * 8 + 80)) with (wa (6566376 + 80 + 8 * sc)) by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. if_cases K; zify_cond K.
{
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
unfold qpath_st. rewrite HA, optr_eqb_refl.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [apply rpres_except_refl|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR]. }
assert (HA : active st sc <> Some g).
{ intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
destruct (GNP HA) as [GN GP].
assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
{ unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
rewrite QS. clear QS K.

rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
clear CH.

st1. destruct (active st sc) as [hd|] eqn:HD.
-
destruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
assert (NEh : hd <> g) by congruence.
pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; exact MSL).

rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1. clear CHh.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; exact MSp).

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
st1.
rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
st1. clear CH. st1.

rmeta_open (conc st hd) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSh | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
-
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (6566376, 6566376 + 928)]%Z m) as MU.

st1.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.

pose proof MRb as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives stB) sc (Z_to_bv 64 (6566376 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (RCTX + 80 + 8 * sc)) (le8 (pw stB (Some g))))
by (unfold RCTX, pw, wz; cbn [oconc]; f_equal; unfold wa; f_equal; lia);
pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
end.
assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3 SOK.

pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
pose proof (length_le8 (pw stB (Some g))) as L8;
apply (rw_cells_frame rsegs mX _ _ A bs) in FR; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8, FRL; unfold RCTX; cbn; lia];
apply (stk_write rsegs mX _ _ A bs) in ST; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia];
apply (munch_write _ _ mX A bs) in MU; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs) in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs) in HI;
[| rewrite L8; destruct ACTS as [_ AW]; unfold RCTX; apply (wr_at_store_ok rsegs mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
end;
remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
end.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
Qed.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 Qnxq QLsg Ql2m QGeV Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Export QLsg.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QCwx.Mq1 QFqQ.Mq0 Qn9M.Mq0 QdZ1.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation RMFACTS := (@MFACTS_g ref_reserved).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
(b + n <= 0x10000 \/ 0xe2000 <= b) /\ (b + n <= 0xe2000 \/ 0x645000 <= b).
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.

#[using="Type"] Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof.
intros Hf Hs.
assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
{ intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

#[using="Hr"] Lemma rconc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

#[using="b off B P0 K0 S16"] Lemma rsk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr8_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
0 <= v < 256 ->
rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr8; exact TKx].
apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr16_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 65536 ->
rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr16; exact TKx].
apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr32_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 2^32 ->
rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof.
intros Hf H0 H1. unfold wr16.
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof.
intros Hf H1. unfold wr32.
rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

#[using="r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16"] Lemma renframe_mrep :
let res := enframe_at st2 g k n off in
rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
/\ ticks_ok (fst res)
/\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof.
pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
unfold aadd. cbn [fst snd].

set (stC := if negb (off =? 0) then _ else _).
assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
/\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
/\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
/\ (forall q, conc (fst stC) q = conc st2 q)).
{ subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
- subst off. rewrite Z.mul_0_r, Z.add_0_r.
split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
-
rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
unfold UNIT in *.
replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
cbn [fst snd].
unfold renframe_tail_mem. cbv zeta.

set (po := snd b + (UNIT + stride * k) + UNIT * off).
assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
{ unfold po, P0, UNIT. f_equal; lia. }
rewrite Eq.
assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
{ unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
split; [apply Z.div_pos; lia| exact Q16]. }

rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.

unfold set_size, aadd. cbn [fst snd id].
set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
rewrite Ersv.
assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
set (stF := if negb (rsv =? 0) then _ else _).
set (mF := if rsv =? 0 then _ else _).
assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
{ subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
- split; [exact ME|]. split; [exact TE|]. split; assumption.
- destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
split; [exact MF|]. split; [exact TF|]. split; assumption. }
clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
set (stG := if 5 <=? rsv then _ else _).
set (mG := if 5 <=? rsv then _ else _).
assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
/\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
{ subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
-
rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
- split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
destruct PG as (MG & TG & -> & R2 & ERg & EGg).
assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
{ rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
split; [exact MH|]. split; [exact TH|].
split; [|split; [reflexivity| unfold po, UNIT; lia]].
rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

#[using="Type"] Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
rpres_except C m0 m4 ->
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
(forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof.
intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
{ unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
unfold renframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : rpres_except C m0 mE).
{ subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : rpres_except C m0 mF).
{ subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
- split; [exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

#[using="Type"] Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
rmrep st m1 -> unk_agree st o m1 ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
~ grp_hdr_cov st (fst q) (snd q) ->
bytes_at rsegs m1 (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof.
intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read rsegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rmeta_chunk_facts : forall st m g,
rmrep st m -> meta_slot st g ->
let G := conc st g in
rw_cells rsegs m G (meta_cells st (get_meta_rec st g))
/\ 0 < G /\ G + 40 <= alloc_ceiling
/\ (G + 40 <= 0x10000 \/ 0xe2000 <= G) /\ (G + 40 <= 0xe2000 \/ 0x645000 <= G)
/\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
/\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
/\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof.
intros st m g MR MS G.
split; [apply rmrep_meta_chunk; assumption|].
pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
destruct MS as (a & ara & kk & Ha & Hkk & Eg).
destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
{ subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
- intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
- exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.

#[using="Type"] Lemma rregion_facts : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe2000 <= r_base r)
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0xe2000 \/ 0x645000 <= r_base r).
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.

Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

#[using="MR UA Hr Hk B0 IDX SPAN S16 B16 SMOD HDR0"] Lemma rslot_facts :
exists x3 x2 x1 : byte,
wr_at rsegs m1 (P0 - 4) stride
/\ bytes_at rsegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
/\ B = r_base r + snd b /\ 4096 <= r_base r
/\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe2000 <= r_base r).
Proof.
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC |- *.
assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
assert (WRs : wr_at rsegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
assert (WR3 : wr_at rsegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
exists x3, x2, x1.
assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
{ intros d Hd (b' & gh & Hb' & Hf & Hc).
pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
clear - Hd Hc AL' B16 SMOD IDX S16.
destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
pose proof Ybs as (_ & _ & YB).
assert (Y3 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
{ split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
assert (Y2 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
{ split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
assert (Y1 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
{ split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
split; [exact WRs|].
split.
{ rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y3| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y2| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y1| lia]. }
split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed.
End SLOT.

Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
\/ fresh_addr st a.

#[using="Type"] Lemma rmalloc_fp_mono st sta stb lo sp a :
(forall rid r, (s_regions sta) !! rid = Some r ->
exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof.
intros HR [H|[H|H]]; [| right; left | right; right; exact H].
- destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
- destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

#[using="Type"] Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

#[using="LB sc MF ACT AV K0 LBK N0 NFIT"] Lemma rfast_slot_ok : exists b r,
slot_ok st2 g b r k n
/\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
free_slot_addr st a)
/\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
unfold UNIT, IB in *.
assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
pose proof (AVAI k K0 TBk) as KAI.
assert (K32 : k < 32) by lia.
assert (P2k : 0 < 2 ^ k <= m_avail mr).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
rewrite LBK in E'. rewrite E'. exact LE'. }
assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
exists b, r. pose proof rget_meta_rec_st2 as E2.
split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
- pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
| (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
| (intros off O0 OF;
assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
apply Z.div_lt_upper_bound; lia)
| lia ].
- intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End FASTFACTS.

End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRsj Q0aA Q1m9 QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QRsj Q0aA Q1m9.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Definition subtf3_entry := 0xd2f60%Z.

Lemma land_shl64_low : forall h l, (0 <= l < 2^64)%Z -> Z.land (Z.shiftl h 64) l = 0%Z.
Proof.
intros h l Hl. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- replace (Z.testbit l i) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec l 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma f128_sub_split : forall aLo aHi bLo bHi,
(0 <= bLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
f128_sub (aLo + 2^64 * aHi) (bLo + 2^64 * bHi) = f128_add (aLo + 2^64 * aHi) (bLo + 2^64 * Z.lxor bHi 9223372036854775808).
Proof.
intros aLo aHi bLo bHi Hl Hh. unfold f128_sub. rewrite lo64_words, hi64_words by lia.
unfold mk128, SIGN64. rewrite Z.lor_comm, lor_disjoint_add.
- rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
- rewrite Z.land_comm. apply land_shl64_low. lia.
Qed.

Lemma subtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk usegs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
mem_inv usegs m ->
frm0 fc ->
evt usegs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
(f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2f60) fc None m (seg_rom usegs)).
Proof.
intros until m. intros ST MI FRM. pose_word_ranges.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
rewrite f128_sub_split by lia.
do 4 zstep.
eapply evt_mono; [ eapply addtf3_spec; eassumption | ].
intros ms' PO. unfold addtf3_post in *.
rewrite (inr64_unsigned_lit (Z.lxor (bv_unsigned a3) 9223372036854775808)) in PO by zrange.
exact PO.
Qed.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1.Mq7.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

#[using="Type"] Lemma ram_fp_alloc_fp st lo sp a : ram_fp st lo sp a -> ralloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold ram_fp, ralloc_fp. tauto. Qed.
#[using="Type"] Lemma ram_fp_stack st lo sp a : lo <= a < sp -> ram_fp st lo sp a.
Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> ram_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> ram_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma ram_fp_not_errno st lo sp a : ram_fp st lo sp a -> rregions_wf st -> alloc_ceiling <= lo ->
~ (errno_addr (Z_to_bv 64 0x625520) <= a < errno_addr (Z_to_bv 64 0x625520) + 4).
Proof.
intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; unfold RCTX, alloc_ceiling in *; rewrite ?unsigned_lit by lia; try lia.
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2).
pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
Qed.
#[using="Type"] Lemma ram_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> ram_fp st lo sp a.
Proof.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.

#[using="Type"] Lemma ram_fp_area : forall st m lo sp ak ar a, rmrep st m -> (s_areas st) !! ak = Some ar ->
conc st ak <= a < conc st ak + 4096 -> ram_fp st lo sp a.
Proof.
intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
#[using="Type"] Lemma ram_fp_same st st' lo sp a : s_regions st' = s_regions st -> ram_fp st' lo sp a <-> ram_fp st lo sp a.
Proof. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.

Definition ram_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ rpres_except (ram_fp stF lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 junk; C8 rc_canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma ram_tail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv usegs m -> meta_slot st q ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (upd_meta q clr_links st) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c90) fc None m (seg_rom usegs)).
Proof.
intros until q. intros MR MI MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
rmeta_chunk MR MSq CH.
unfold alloc_ceiling, RSSP_GUARD, ram_frame in *.
rmeta_open (conc st q) MUq WMq.

st1. st1.
rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
rewrite <- upd_meta_put in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl usegs mX) as WMs end.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta q clr_links st) mX)
by (eapply rmrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply ram_fp_stack. lia.
- intros x Hx. eapply ram_fp_meta; [exact MR | exact MSq | lia]. }
apply evt_done. unfold ram_ret_post. do 15 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.

#[using="Type"] Lemma ram_b0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo cnt : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv usegs m -> meta_slot st q -> 0 <= cnt < 2^64 ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (am_took st q cnt) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) (Z_to_bv 64 cnt) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c84) fc None m (seg_rom usegs)).
Proof.
intros until q. intros MR MI MSq HC FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1.
unfold alloc_ceiling, RCTX, RMLOCK in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 24, RCTX + 40)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.

st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
rewrite (conc_aadd st q META_SIZE) by (destruct MSq as (a & ar & k & Ha & Hk & ->); cbn; pose proof MR as (WF' & _);
destruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
unfold META_SIZE, wz. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
change (conc st q) with (conc st1 q).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
[exact MR1 | assumption | exact MSq | exact FR | exact ST | unfold alloc_ceiling; lia | lia]. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq3.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1.Mq7.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a0 a2 a3 a5 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd09c4) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -96)
/\ rw_cells usegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
conc st q = conc st g -> q = g.
Proof.
intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
- rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
- exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

#[using="Type"] Lemma rntf_qpath : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g -> 0 <= sc < 48 ->
(active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
(active st sc <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
qa_facts st sc g ->
rw_cells usegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rqpath_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc lo st g m (qpath_st st sc g) fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (Z_to_bv 64 sc) a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd07a8) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
unfold alloc_ceiling, RCTX in *.

st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.

pose proof (rmrep_active_read st m sc (wa (RCTX + 80 + 8 * sc)) MR SC eq_refl) as RDA. unfold RCTX in RDA.
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
replace (Z_to_bv 64 (6576296 + sc * 8 + 80)) with (wa (6576296 + 80 + 8 * sc)) by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. if_cases K; zify_cond K.
{
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
unfold qpath_st. rewrite HA, optr_eqb_refl.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [apply rpres_except_refl|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR]. }
assert (HA : active st sc <> Some g).
{ intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
destruct (GNP HA) as [GN GP].
assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
{ unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
rewrite QS. clear QS K.

rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
clear CH.

st1. destruct (active st sc) as [hd|] eqn:HD.
-
destruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
assert (NEh : hd <> g) by congruence.
pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; exact MSL).

rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1. clear CHh.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; exact MSp).

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
st1.
rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
st1. clear CH. st1.

rmeta_open (conc st hd) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSh | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
-
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (6576296, 6576296 + 928)]%Z m) as MU.

st1.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.

pose proof MRb as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives stB) sc (Z_to_bv 64 (6576296 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (RCTX + 80 + 8 * sc)) (le8 (pw stB (Some g))))
by (unfold RCTX, pw, wz; cbn [oconc]; f_equal; unfold wa; f_equal; lia);
pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
end.
assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3 SOK.

pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
pose proof (length_le8 (pw stB (Some g))) as L8;
apply (rw_cells_frame usegs mX _ _ A bs) in FR; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8, FRL; unfold RCTX; cbn; lia];
apply (stk_write usegs mX _ _ A bs) in ST; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia];
apply (munch_write _ _ mX A bs) in MU; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8; unfold RCTX; cbn [inside]; lia];
apply (wmono_write usegs _ mX (wa A) bs) in WM;
lazymatch goal with HI : mem_inv usegs mX |- _ =>
apply (mem_inv_store usegs mX (wa A) bs) in HI;
[| rewrite L8; destruct ACTS as [_ AW]; unfold RCTX; apply (wr_at_store_ok usegs mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
end;
remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
end.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
Qed.

End RC__1.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QLsg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn9M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation RMFACTS := (@MFACTS_g ref_reserved).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
(b + n <= 0x10000 \/ 0xe4000 <= b) /\ (b + n <= 0xe4000 \/ 0x647000 <= b).
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.

#[using="Type"] Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof.
intros Hf Hs.
assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
{ intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

#[using="Hr"] Lemma rconc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

#[using="b off B P0 K0 S16"] Lemma rsk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr8_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
0 <= v < 256 ->
rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr8; exact TKx].
apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr16_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 65536 ->
rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr16; exact TKx].
apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr32_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 2^32 ->
rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof.
intros Hf H0 H1. unfold wr16.
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof.
intros Hf H1. unfold wr32.
rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

#[using="r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16"] Lemma renframe_mrep :
let res := enframe_at st2 g k n off in
rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
/\ ticks_ok (fst res)
/\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof.
pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
unfold aadd. cbn [fst snd].

set (stC := if negb (off =? 0) then _ else _).
assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
/\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
/\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
/\ (forall q, conc (fst stC) q = conc st2 q)).
{ subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
- subst off. rewrite Z.mul_0_r, Z.add_0_r.
split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
-
rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
unfold UNIT in *.
replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
cbn [fst snd].
unfold renframe_tail_mem. cbv zeta.

set (po := snd b + (UNIT + stride * k) + UNIT * off).
assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
{ unfold po, P0, UNIT. f_equal; lia. }
rewrite Eq.
assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
{ unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
split; [apply Z.div_pos; lia| exact Q16]. }

rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.

unfold set_size, aadd. cbn [fst snd id].
set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
rewrite Ersv.
assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
set (stF := if negb (rsv =? 0) then _ else _).
set (mF := if rsv =? 0 then _ else _).
assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
{ subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
- split; [exact ME|]. split; [exact TE|]. split; assumption.
- destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
split; [exact MF|]. split; [exact TF|]. split; assumption. }
clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
set (stG := if 5 <=? rsv then _ else _).
set (mG := if 5 <=? rsv then _ else _).
assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
/\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
{ subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
-
rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
- split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
destruct PG as (MG & TG & -> & R2 & ERg & EGg).
assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
{ rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
split; [exact MH|]. split; [exact TH|].
split; [|split; [reflexivity| unfold po, UNIT; lia]].
rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

#[using="Type"] Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
rpres_except C m0 m4 ->
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
(forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof.
intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
{ unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
unfold renframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : rpres_except C m0 mE).
{ subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : rpres_except C m0 mF).
{ subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
- split; [exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

#[using="Type"] Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
rmrep st m1 -> unk_agree st o m1 ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
~ grp_hdr_cov st (fst q) (snd q) ->
bytes_at usegs m1 (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof.
intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read usegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rmeta_chunk_facts : forall st m g,
rmrep st m -> meta_slot st g ->
let G := conc st g in
rw_cells usegs m G (meta_cells st (get_meta_rec st g))
/\ 0 < G /\ G + 40 <= alloc_ceiling
/\ (G + 40 <= 0x10000 \/ 0xe4000 <= G) /\ (G + 40 <= 0xe4000 \/ 0x647000 <= G)
/\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
/\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
/\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof.
intros st m g MR MS G.
split; [apply rmrep_meta_chunk; assumption|].
pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
destruct MS as (a & ara & kk & Ha & Hkk & Eg).
destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
{ subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
- intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
- exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.

#[using="Type"] Lemma rregion_facts : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe4000 <= r_base r)
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0xe4000 \/ 0x647000 <= r_base r).
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.

Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

#[using="MR UA Hr Hk B0 IDX SPAN S16 B16 SMOD HDR0"] Lemma rslot_facts :
exists x3 x2 x1 : byte,
wr_at usegs m1 (P0 - 4) stride
/\ bytes_at usegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
/\ B = r_base r + snd b /\ 4096 <= r_base r
/\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe4000 <= r_base r).
Proof.
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC |- *.
assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
assert (WRs : wr_at usegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
assert (WR3 : wr_at usegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
exists x3, x2, x1.
assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
{ intros d Hd (b' & gh & Hb' & Hf & Hc).
pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
clear - Hd Hc AL' B16 SMOD IDX S16.
destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
pose proof Ybs as (_ & _ & YB).
assert (Y3 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
{ split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
assert (Y2 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
{ split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
assert (Y1 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
{ split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
split; [exact WRs|].
split.
{ rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y3| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y2| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y1| lia]. }
split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed.
End SLOT.

Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
\/ fresh_addr st a.

#[using="Type"] Lemma rmalloc_fp_mono st sta stb lo sp a :
(forall rid r, (s_regions sta) !! rid = Some r ->
exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof.
intros HR [H|[H|H]]; [| right; left | right; right; exact H].
- destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
- destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

#[using="Type"] Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

#[using="LB sc MF ACT AV K0 LBK N0 NFIT"] Lemma rfast_slot_ok : exists b r,
slot_ok st2 g b r k n
/\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
free_slot_addr st a)
/\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
unfold UNIT, IB in *.
assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
pose proof (AVAI k K0 TBk) as KAI.
assert (K32 : k < 32) by lia.
assert (P2k : 0 < 2 ^ k <= m_avail mr).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
rewrite LBK in E'. rewrite E'. exact LE'. }
assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
exists b, r. pose proof rget_meta_rec_st2 as E2.
split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
- pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
| (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
| (intros off O0 OF;
assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
apply Z.div_lt_upper_bound; lia)
| lia ].
- intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End FASTFACTS.

End RC__1.
