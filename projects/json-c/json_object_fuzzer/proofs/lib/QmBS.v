(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg QZAi QfYR QfcC Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y Qbf8 QSzV QvBB Qi8L QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import Qbf8 QSzV QvBB.Mq1.
Export Qi8L.Mq1.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
end.

Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 128) (q)
/\ rw_cells rsegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
rw_cells rsegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 128 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 128)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 UFLOW) fc None m (seg_rom rsegs)).

Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 160) q
/\ rw_cells rsegs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
rw_cells rsegs m Fp (rf_cells T p w f ssJ) ->
sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
rtext T txt pre post -> p = zlength pre -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 160 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 160)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHGETC) fc None m (seg_rom rsegs)).

End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 Ql2m QGeV QLsg QkQT QlkP QM7w QCwx QFqQ Q98Z QkLq QnOf QdZ1 Qv4L QQbX Qn9M QnkH Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QJE4.Mq3.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq8 Qi8L.Mq4 QdZ1.Mq2 QQbX.Mq2 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

#[using="Type"] Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono rsegs m0 m ->
evt rsegs (fun ms' => exists (a1' a2' : word) m',
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom rsegs)
/\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp) /\ rmrep st' m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf200) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR' MI FR ST LO LOLE MU WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RSSP_GUARD, rta_frame in *.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="MR MSL MASK CLO"] Lemma rfin_walk :
forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
bv_unsigned gw = G ->
rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk rsegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' a3' : word) m' k,
0 <= k < 32 /\ lowbit mask = 2 ^ k /\
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb40) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros HG FR ST LO MI.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
unfold meta_cells in CH. rewrite <- HG in CH.
destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
assert (P2 : 0 < 2 ^ k <= mask).
{ destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
unfold alloc_ceiling, rta_frame, RSSP_GUARD in *.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.

step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).

pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl rsegs m) as WMg.
step.
lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- _ =>
apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
(meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
[| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
| reflexivity | cbn; tauto ];
rewrite HG in H;
pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
end.

step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. step. step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.
step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.

step.
rewrite ?LB in MR1.
eapply evt_mono.
{ eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
[exact MR1 | assumption | exact FR | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM]. }
cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.

End RC__1.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE QYTG QXxF QBeb Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import QWTl.Mq5.
Import Qbf8.
Import Q2qa.Mq1 QytA QlQE QFkE Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq2 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.

Import QJE4.Mq0 QJE4.Mq1 QDUx.Mq3 QWTl.Mq1 QWTl.Mq2 QWTl.Mq3 QDUx.Mq2 Q9Ay.Mq9 QXxF QBeb Q6y7.Mq1.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 Qv4L.Mqa QdZ1.Mq2.
Import QQbX.Mq1 QdZ1.Mq0 QnkH.Mq5 Qv4L.Mq1 Qv4L.Mq2 Qv4L.Mq3 QnkH.Mq3 QnkH.Mq4 Qi8L.Mq2 Qi8L.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := QWTl.Mq5.
Module RA2 := Qv4L.Mqa.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
#[using="Type"] Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.

#[using="Type"] Lemma rrw_cells_magree C m m' A cs :
rw_cells rsegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells rsegs m' A cs.
Proof.
intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply RA2.rrw_cells_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
#[using="Type"] Lemma rbytes_at_magree C m m' A bs :
bytes_at rsegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at rsegs m' A bs.
Proof.
intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply RA2.rbytes_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
#[using="Type"] Lemma rwr_at_magree C m m' A n :
wr_at rsegs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at rsegs m' A n.
Proof. intros H AG HC H0 H1. eapply RA2.rwr_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha]. Qed.

#[using="Type"] Lemma rauxv_ok_magree C m m' B :
rauxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8)) -> rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 0x622e60.
Hypothesis KH : forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms'.

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

#[using="Type"] Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. intros H. left. apply ram_fp_alloc_fp. exact H. Qed.

#[using="RC__ TP"] Lemma rETP : errno_addr tp = 0x622e60 - 164.
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

#[using="TK KH"] Lemma rfinish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
am_rel st st1 mo -> rmrep st1 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
rw_cells rsegs m' (errno_addr tp) [C4 e] -> rauxv_ok m' (bv_unsigned sp) -> magree (rFP st1) m m' ->
brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rv = pw st1 mo -> (mo = None -> e = Z_to_bv 64 12) ->
rimplT o (k st1 mo) sX Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)).
Proof.
intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv REL MR1 MI1 ST1 ERR1 AUX1 AG BL1 P1 P2 P3 -> E12.
apply KH; [| exact BL1]. unfold ram_post. do 16 eexists. split; [reflexivity|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact AUX1|]. split.
{ apply rpres_of_magree. exact AG. }
split; [exact MR1|]. split.
{ destruct TK as [T1 T2]. split; intros; rewrite (amr_shadow _ _ _ REL) in *; rewrite (amr_tick _ _ _ REL); eauto. }
repeat (split; [auto|]). exact E12.
Qed.

#[using="Type"] Lemma rFP_mono stX stY a :
(forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rFP stX a -> rFP stY a.
Proof.
intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
{ unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
unfold lr_lo in *. rewrite K', B'. lia.
Qed.

#[using="Type"] Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof. intros E. apply rFP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

#[using="AMP LO LOLE"] Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8).
Proof.
intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold RAUXV_CELL, RLIBC, RCTX, RAM_STACK, alloc_ceiling in *;
rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
- destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
- pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold alloc_ceiling in C. lia.
Qed.

#[using="LO TP"] Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. intros WF X. rewrite TP. eapply ram_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

#[using="Type"] Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.

#[using="Type"] Lemma ram_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> QUZl.M RR) (bl : QUZl.M RR) :
am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
= kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
#[using="Type"] Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

#[using="AMP TK LO LOLE TP KH"] Lemma rcarve_K : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv rsegs mX -> bytes_at rsegs mX (conc stY p) (zeros 4096) -> wr_at rsegs mX (conc stY p) 4096 ->
rw_cells rsegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs mX lo (bv_unsigned sp + -64) ->
rw_cells rsegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (k (am_took (carve_st stY p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR))) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce570) fc None mX (seg_rom rsegs)).
Proof.
intros until t6. intros AI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX ZB ZW FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MRX as (WFX & _).
eapply rimplT_evt.
{ eapply (ram_carve_walk sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc mX junk lo stY p r);
first [exact MRX | exact MIX | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
| exact (ami_secretr _ _ AI) | exact ZB | exact ZW | exact FRX | exact STX | exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
pose proof (carve_st_regions stY p) as RC.
eapply rfinish_K.
- eapply (ram_rel_carve st stY p r AI); assumption.
- exact MR2.
- exact MI2.
- exact ST2.
- eapply rrw_cells_magree; [exact ERRX| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X.
apply (rerrno_not_amfp stY a WFX); [exact (proj1 (ram_fp_same stY _ lo _ a RC) X) | lia].
- eapply rauxv_ok_magree; [exact AUXX| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stY _ WFX). apply rFP_am. exact (proj1 (ram_fp_same stY _ lo _ a RC) X).
- assert (RA : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY) by (cbn; exact RC).
eapply magree_trans; [exact AGX| apply rmagree_of_pres; exact PE2| intros a X; exact (rFP_same stY _ a RA X) | intros a X; apply rFP_am; refine (proj2 (ram_fp_same (carve_st stY p) _ lo _ a _) X); reflexivity].
- unfold brk_link_ps in *. rewrite rbrk_am_took, rbrk_carve. destruct (c_brk (ctx stY)) as [| |rid off]; auto.
rewrite rconc_am_took, rconc_carve. exact BLX.
- exact P1.
- exact P2.
- exact P3.
- unfold pw, oconc, wz. rewrite rconc_am_took, rconc_carve. rewrite (conc_aadd stY p AREA_HDR) by (rewrite Hr; eauto). reflexivity.
- intros X; discriminate X.
Qed.

#[using="TP"] Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof.
intros WF H. rewrite rETP. pose proof WF as (_ & WR & _ & WA & WG). unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
Qed.

Lemma rfinish_path : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> c_avail_meta_areas (ctx stY) = Some p ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv rsegs mX ->
rw_cells rsegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs mX lo (bv_unsigned sp + -64) ->
rw_cells rsegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_finish stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce600) fc None mX (seg_rom rsegs)).
Proof using AMP KH LO LOLE TK TP.
intros until t6. intros AI AMA Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'.
pose proof MRX as (WFX & _ & (_ & _ & PGX & _) & _). pose proof WFX as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (conc_region' stY p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU. pose proof (lr_lo_ge r) as LRG.
assert (PAL : conc stY p mod 4096 = 0) by (rewrite Cp; unfold pgal in SAL; clear - RBAL SAL; Z.div_mod_to_equations; lia).
assert (IMG : conc stY p + 4096 <= 0x10000 \/ 0x645000 <= conc stY p) by (pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)); lia).
pose proof rETP as rETP'. pose proof TP as TPv. unfold wz in PGX.

unfold am_finish. rewrite AMA. unfold pgal in SAL. unfold PGSZ at 1. rewrite (proj2 (Z.eqb_eq _ _) SAL). cbn [negb].

eapply rimplT_evt.
{ apply (ram_to_mprotect (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX (conc stY p)). }
intros ms2 ->.
eapply (rimplT_mprotect o (conc stY p) PGSZ PROT_RW _ sX).
{ eapply rimpl_enode_dec_weaken; [| intros rsp a Hd; exact (dec_mprotect_rw_weaken _ _ rsp a Hd)].
unfold PGSZ, PROT_RW.
eapply rmprotect_spec with (lo := lo) (errv := e);
[ rewrite unsigned_lit by lia; exact STX | exact ERRX | exact PGX | exact MIX | reflexivity | reflexivity | reflexivity
| exact PAL | reflexivity | lia | lia | lia | lia | ..]; rewrite ?rETP', ?TPv, ?unsigned_lit by lia; unfold RPAGE_SIZE; try lia. }
intros ans ms3 [MP G]. unfold rmprotect_post in MP.
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & PG3 & CASE).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0xce610)) with (Z_to_bv 64 0xce610 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [exact FRX| exact MU3| exact WM3|]. rewrite rETP'. cbn. unfold alloc_ceiling in LO. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [exact MRX| exact MU3| exact WM3|].
intros lo' hi' y [E|[E|[E|[]]]] Hy; inversion E; subst lo' hi'.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). unfold alloc_ceiling in *. lia.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). lia.
- eapply (rfresh_page_avoids stY mX p r y MRX); try assumption; lia. }
assert (M23 : magree (rFP stY) mX m3).
{ eapply magree_of_munch; [exact MU3|].
cbn. split; [| split; [| split; [| exact I]]]; intros x Hx.
- left. left. lia.
- left. right. left. rewrite TPv in Hx. exact Hx.
- left. right. right. right. exists (fst p), r. split; [exact Hr|]. split; [exact NK|]. lia. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AGX| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUXX| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clear MU3 WM3.
destruct ans as [e'|b]; cbn in G.
-
cbn [range_val Q9A7.Mq0.munmap_ret Q9A7.Mq0.rg_errno] in *.
unfold mprotect_answer_ok, is_errno_form, neg_errno, TWO64, ENOSYS.
replace ((2 ^ 64 - e' =? 0) || ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64))) with true by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
replace ((2 ^ 64 - e' =? 0) || (2 ^ 64 - e' =? 2 ^ 64 - 38)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
cbn [negb].
eapply rimplT_evt.
{ eapply (ram_mp_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo e' stY);
first [exact MR3 | exact MI3 | exact TPv | exact ERR3 | exact G | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
intros ms4 [RP ERR4]. unfold ram_ret_post in RP. cbn [ms_mem] in ERR4.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & EQ & PE4 & WM4 & MI4 & ST4 & MR4).
rewrite EQ in ERR4 |- *. cbn [ms_mem] in ERR4.
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ exact MR4.
+ exact MI4.
+ exact ST4.
+ exact ERR4.
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
+ exact BLX.
+ exact P1.
+ exact P2.
+ exact P3.
+ reflexivity.
+ intros _. cbn in CASE. rewrite CASE. reflexivity.
-
subst b. cbn [range_val] in *.
unfold mprotect_answer_ok. cbn [Z.eqb orb negb].
rewrite (am_carve_eq stY p k bail), (ram_take_took (carve_st stY p) p k bail).
destruct CASE as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
eapply rimplT_evt.
{ apply (ram_mp_ok0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 (Z_to_bv 64 0xce610) F fc m3). }
intros ms4 ->.
eapply (rcarve_K stY p r m3 sX junk); first [exact AI | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
| exact MR3 | exact MI3 | exact ZB | exact ZW | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | exact BLX | exact P1 | exact P2 | exact P3 | idtac].
unfold pgal. exact SAL.
Qed.

#[using="Type"] Lemma rlive_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

#[using="Type"] Lemma rfresh_of_ranges_free stY x L a :
s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof.
intros E1 E2 RF XC Ha. split; [lia|]. rewrite (rlive_ranges_same st stY E1 E2) in RF.
eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.

#[using="Type"] Lemma rrepfoot_clear stY mY x L a :
rmrep stY mY -> ranges_free (live_ranges stY) x L = true -> rrepfoot stY a \/ rgrp_region_addr stY a -> ~ (x <= a < x + L).
Proof.
intros MRY RF H. pose proof MRY as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (clear_range_of_ranges_free stY x L RF) as CR.
assert (IMG : forall y, 0x10000 <= y < 0x645000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y RS RF Hy)).
destruct H as [[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (rra & Hra & _).
eapply (CR (fst ak) rra a Hra). eapply rarea_in_live; eauto.
- destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (rb & Hrb & _).
eapply (CR (fst b) rb a Hrb). eapply rgroup_in_live; eauto.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
- apply IMG. lia.
- apply IMG. lia.
- destruct C as (rid & rg & Hrg & Krg & Hin). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed.

#[using="AMP TK LO LOLE TP KH"] Lemma rmmap_path : forall (stY : mstate) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> s_regions stY = s_regions st -> c_avail_meta_area_count (ctx stY) = 0 ->
0 <= c_meta_alloc_shift (ctx stY) <= 38 ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
(forall q mr, (s_metas stY) !! q = Some mr -> meta_slot stY q) ->
ptrs_in (fun rid => (rid < s_next_rid stY)%N) stY ->
rmrep stY mX -> mem_inv rsegs mX ->
rw_cells rsegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs mX lo (bv_unsigned sp + -64) ->
rw_cells rsegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_after_brk stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce510) fc None mX (seg_rom rsegs)).
Proof.
intros until t6. intros AI RGY ACNT SHR TL MK PTR MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MRX as (WFX & _). pose proof WFX as (RS & WR & DJ & WA & WG).
set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx stY))).
assert (NR : 2 <= n <= 2^39).
{ unfold n. rewrite Z.shiftl_mul_pow2 by lia. split.
- rewrite <- (Z.mul_1_r 2) at 1. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r with (b := 0); lia || (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
- change (2^39) with (2 * 2^38). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
unfold am_after_brk. rewrite ACNT. cbn [Z.eqb]. fold n.

eapply rimplT_evt.
{ apply (ram_to_mmap (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX stY MRX ltac:(lia)). }
intros ms2 ->. fold n.
pose proof MRX as MR2. pose proof MIX as MI2. pose proof FRX as FR2. pose proof STX as ST2. pose proof ERRX as ERR2. pose proof AGX as AG2. pose proof AUXX as AUX2.
set (m2 := mX) in MR2, MI2, FR2, ST2, ERR2, AG2, AUX2 |- *.
clear MRX MIX FRX STX ERRX AUXX AGX.
eapply (rimplT_mmap_none o (n * PGSZ) _ sX).
{ unfold PGSZ. replace (Z_to_bv 64 (n * 4096)) with (Z_to_bv 64 (n * 4096)%Z) by reflexivity.
eapply (rmmap_anon_spec true) with (lo := lo) (errv := e) (avoid := []);
[ rewrite unsigned_lit by lia; exact ST2 | exact ERR2 | exact MI2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?rETP', ?TPv, ?unsigned_lit by lia; try lia. all: first [rewrite Q9A7.Mq0.alloc_ceiling_val; lia | unfold alloc_ceiling in *; lia]. }
intros ans ms3 MP. unfold rmmap_anon_post in MP.
destruct ans as [e'|x].
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & ER).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0xce53c)) with (Z_to_bv 64 0xce53c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
cbn [mmap_val]. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64.
replace ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [orb negb]. replace (2 ^ 64 - 4096 <? 2 ^ 64 - e') with true by (symmetry; apply Z.ltb_lt; lia).
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. rewrite rETP'. cbn. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
intros lo' hi' y [E|[E|[]]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
assert (M23 : magree (rFP stY) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| split; [| exact I]]; intros y Hy; [left; left; lia|]. left. right. left. rewrite TPv in Hy. exact Hy. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
eapply rimplT_evt.
{ eapply (ram_mm_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 n) u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo stY);
first [exact MR3 | exact MI3 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
intros ms4 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & -> & PE4 & WM4 & MI4 & ST4 & MR4).
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ exact MR4.
+ exact MI4.
+ exact ST4.
+ eapply rrw_cells_magree; [exact ERR3| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp stY a WFX); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
+ exact BLX.
+ exact P1.
+ exact P2.
+ exact P3.
+ reflexivity.
+ intros _. rewrite ER. reflexivity.
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2' & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & AOK).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0xce53c)) with (Z_to_bv 64 0xce53c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
cbn [mmap_val].
destruct (mmap_answer_ok (live_ranges stY) (n * PGSZ) x) eqn:VOK; cbn [negb]; [| apply rimplT_undef].

unfold mmap_addr_ok in AOK. apply andb_prop in AOK. destruct AOK as [AOK _]. apply andb_prop in AOK. destruct AOK as [AOK XC].
apply andb_prop in AOK. destruct AOK as [XA X0]. apply Z.eqb_eq in XA. apply Z.ltb_lt in X0. apply Z.leb_le in XC.
rewrite A2.mmap_len_round_up in XC. first [rewrite Q9A7.Mq0.alloc_ceiling_val in XC | unfold alloc_ceiling in XC]. change page_size with 4096 in XA.
assert (LAL : round_up_pg (n * PGSZ) = n * PGSZ) by (apply round_up_pg_aligned; unfold PGSZ; apply Z.mod_mul; lia).
rewrite LAL in XC.
unfold mmap_answer_ok in VOK. rewrite LAL in VOK. apply orb_prop in VOK.
assert (RF : ranges_free (live_ranges stY) x (n * PGSZ) = true).
{ destruct VOK as [V|V]; [| apply andb_prop in V; destruct V as [_ V]; exact V].
unfold is_errno_form, TWO64 in V. apply andb_prop in V. destruct V as [V _]. apply Z.leb_le in V. unfold PGSZ in XC. exfalso. lia. }
unfold is_err, TWO64. replace (2 ^ 64 - 4096 <? x) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ in XC; lia).
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stY).
pose proof (rAMI_new_region st stY RKMeta x (n * PGSZ) AI ltac:(discriminate) ltac:(unfold PGSZ; lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
set (st2 := upd_ctx _ st1).
assert (E2 : st2 = mm_ok_st st1 rid n) by reflexivity.

unfold Q9A7.Mq0.mmap_raw in ST3 |- *. rewrite A2.mmap_len_round_up, LAL in ST3 |- *.
set (m3 := apply_unmaps m2' [(wa x, Z_to_bv 64 (n * PGSZ))]) in *.
assert (Hx1 : 0 <= x < 2^64) by (unfold PGSZ in XC; lia). assert (Hn1 : 0 <= n * PGSZ < 2^64) by (unfold PGSZ in *; lia). assert (Hxn : x + n * PGSZ <= 2^64) by (unfold PGSZ in *; lia).
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ apply (rw_cells_unmaps_other rsegs m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. lia.
- cbn. unfold PGSZ in *. lia. }
assert (ERR4 : rw_cells rsegs m3 (errno_addr tp) [C4 e]).
{ apply (rw_cells_unmaps_other rsegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); [exact ERR3|]. cbn. rewrite rETP'.
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x622e60 - 164) RS RF ltac:(lia)).
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x622e60 - 161) RS RF ltac:(lia)). unfold PGSZ in *. lia. }
assert (MI4 : mem_inv rsegs m3) by (apply (mem_inv_unmaps rsegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); exact MI3).
assert (MR2' : rmrep stY m2').
{ eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_agree'; [exact MR2'|]. intros y Hy HF. unfold m3. apply (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
rewrite wa_unsigned by lia. pose proof (rrepfoot_clear stY m2' x (n * PGSZ) y MR2' RF HF). lia. }
assert (MRn : rmrep st1 m3).
{ unfold st1. apply (RA2.rmrep_new_region stY m3 m3 x (n * PGSZ) RKMeta);
first [ exact MR3
| eapply ptrs_in_mono; [| exact PTR]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| apply (ami_fresh _ _ AI); unfold rid; lia
| unfold alloc_ceiling; rewrite LAL; exact XC
| rewrite LAL; exact RF
| intros; reflexivity
| intros; discriminate
| unfold PGSZ in *; lia ]. }
assert (M23 : magree (rFP stY) m2 m3).
{ intros y Hy Hc. unfold m3. rewrite (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact I]. intros X. apply Hc. left. left. lia.
- rewrite wa_unsigned by lia. destruct (Z.lt_ge_cases y x); [lia|]. destruct (Z.lt_ge_cases y (x + n * PGSZ)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stY x (n * PGSZ)); [exact RGY| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; exact XC| lia]. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clearbody m3. clear MU3 WM3 MR2 MR2' MI3 ERR3.

eapply rimplT_evt.
{ eapply (ram_mm_ok sp gp tp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo x n st1 st1 rid (mkRegion RKMeta x (n * PGSZ)));
first [exact MRn | exact MI4 | intros a X; exact X | exact RG1 | reflexivity | exact XA | exact X0 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | idtac];
try (unfold alloc_ceiling, PGSZ in *; lia).
change (ctx st1) with (ctx stY). lia. }
intros ms4 (m4 & -> & PE4 & WM4 & MI5 & FR4 & ST4 & MR4).
pose proof MRn as (WFn & _).
assert (RG2 : forall q, (s_regions st2) !! q = if decide (q = rid) then Some (mkRegion RKMeta x (n * PGSZ)) else (s_regions stY) !! q).
{ intros q. change (s_regions st2) with (<[rid := mkRegion RKMeta x (n * PGSZ)]> (s_regions stY)).
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
replace (Z_to_bv 64 (x + 4096)) with (Z_to_bv 64 (conc st2 (rid, 4096))) by (change (conc st2 (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rfinish_path st2 (rid, 4096) (mkRegion RKMeta x (n * PGSZ)) m4 sX junk e).
+ unfold st2. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* right. exists (rid, PGSZ), (mkRegion RKMeta x (n * PGSZ)). cbn [fst]. split; [reflexivity|]. split; [exact RG1| cbn; discriminate].
* left. reflexivity.
+ reflexivity.
+ cbn [fst]. rewrite RG2. destruct (decide (rid = rid)); [reflexivity| congruence].
+ cbn. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite LAL. unfold PGSZ. lia.
+ unfold pgal. reflexivity.
+ cbn. lia.
+ change (s_areas st2) with (s_areas stY). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas st2) with (s_metas stY). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MK _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas st2) with (s_areas stY). apply TL. exact Htl.
+ cbn. lia.
+ exact MR4.
+ exact MI5.
+ exact FR4.
+ exact ST4.
+ eapply rrw_cells_magree; [exact ERR4| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp st1 a WFn); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below st1 a WFn (rFP_am st1 a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| |].
* intros a X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq. rewrite RG2.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate|]. repeat split; auto; lia.
* intros a X. eapply rFP_same; [| exact (rFP_am st1 a X)]. reflexivity.
+ unfold brk_link_ps in *. change (c_brk (ctx st2)) with (c_brk (ctx stY)).
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _).
destruct (c_brk (ctx stY)) as [| |rb ob]; auto. change (conc st2 (rb, ob)) with (conc st1 (rb, ob)). rewrite CQ1; [exact BLX|]. cbn [fst]. unfold rid. lia.
+ exact P1.
+ exact P2.
+ exact P3.
Qed.

#[using="RC__"] Lemma rimage_range_clear stY x L : s_reserved stY = ref_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
x + L <= 0x10000 \/ 0x645000 <= x.
Proof.
intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs m1 lo (bv_unsigned sp + -64) ->
rw_cells rsegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (let old := conc stI (brid, boff) in
let new := old + PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok old new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI old PGSZ) then bad_answer bail
else
let st1 := upd_region brid (fun rg => mkRegion (r_kind rg) (r_base rg) (boff + PGSZ)) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (brid, boff)) (set_brk (BrkLive brid (boff + PGSZ)) c))) st1 in
am_after_brk st2 false k bail)) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce460) fc None m1 (seg_rom rsegs)).
Proof.
intros until t6. intros AMPI AI RGI BLI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6 & HX7) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
pose proof (amp_brk stI AMPI) as HB. rewrite BRK in HB. destruct HB as (r & Hr & Kr & Lr & OAL & O4 & FRA & UNQ).
pose proof (conc_region' stI (brid, boff) r Hr) as OLD. cbn [snd] in OLD.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr). unfold alloc_ceiling in RBC. rewrite Lr in RBC.
assert (RUB : round_up_pg boff = boff) by (apply round_up_pg_aligned; unfold PGSZ in OAL; exact OAL). rewrite RUB in RBC.
set (old := conc stI (brid, boff)) in *.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold brk_link_ps in BLI. rewrite BRK in BLI. fold old in BLI.
cbv zeta.

eapply rimplT_evt.
{ eapply (ram_disp_live _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI brid boff); [exact MR1| exact ACNT| exact BRK| fold old; lia| fold old; unfold PGSZ; lia]. }
intros ms2 ->. fold old.
eapply (rimplT_brk o (old + PGSZ) _ s).
{ unfold PGSZ; lia. }
{ rewrite BLI. unfold PGSZ.
exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 0xce484 (or_introl eq_refl) old (old + 4096) ltac:(lia)). }
intros a ms3 ->. rewrite BLI. unfold brk_res, brk_mem, rbrk_regs.
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI old PGSZ) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
unfold alloc_ceiling, PGSZ in OC. unfold PGSZ in RF.
assert (OALD : old mod 4096 = 0) by (rewrite OLD; rewrite Z.add_mod, RBAL by lia; unfold PGSZ in OAL; rewrite OAL; reflexivity).
rewrite (brk_new_pages_aligned old 4096) by (first [lia | exact OALD | reflexivity]).
rewrite (rgr_eq stI brid r boff Hr).
set (stG := set_regions _ stI).
unfold PGSZ. rewrite (am_after_brk_false_eq stG _ (brid, boff) k bail) by (cbn; first [lia | reflexivity | unfold PGSZ in OAL; exact OAL]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ stG).

assert (Ho1 : 0 <= old < 2^64) by lia. assert (Hn1 : 0 <= 4096 < 2^64) by lia. assert (Hon : old + 4096 <= 2^64) by lia.
pose proof (rimage_range_clear stI old 4096 RS RF ltac:(lia)) as IMG.
set (m2 := apply_zeros m1 [(wa old, Z_to_bv 64 4096)]).
unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6. fold old in HX6.
assert (HC2 : rw_cells rsegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact HX1| cbn; unfold RCTX; lia]).
assert (TC2 : rw_cells rsegs m2 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (wz old)])
by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact HX6| cbn; unfold RCTX; lia]).
assert (MI2 : mem_inv rsegs m2).
{ apply (mem_inv_zeros rsegs m1 old 4096 Ho1 Hn1 Hon MI1). intros y Hy. apply ref_ro_addr_false. lia. }
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra))
by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact FR1| cbn; lia]).
assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -64)) by (apply (stk_zeros rsegs m1 old 4096 Ho1 Hn1 Hon); exact ST1).
assert (ERR2 : rw_cells rsegs m2 (errno_addr tp) [C4 e1])
by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact ERR1| cbn; rewrite rETP'; lia]).
pose proof (rw_cells_zeros_new rsegs m1 old 4096 Ho1 Hn1 Hon) as ZN. fold m2 in ZN.
assert (MU12 : munch [(old, old + 4096)]%Z m1 m2) by (apply (munch_zeros m1 old 4096 Ho1 Hn1 Hon); [apply munch_refl| cbn; lia]).
assert (WM12 : wmono rsegs m1 m2) by (apply (wmono_zeros rsegs m1 old 4096 Ho1 Hn1 Hon); apply wmono_refl).
assert (MR2 : rmrep stI m2).
{ eapply rmrep_transport_unowned; [exact MR1| exact MU12| exact WM12|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'. intros RFt. apply (rrepfoot_clear stI m1 old 4096 y MR1 RF (or_introl RFt)). lia. }
assert (M12 : magree (rFP stI) m1 m2).
{ intros y Hy Hc. unfold m2. apply (zeros_outside m1 old 4096 Ho1 Hn1 Hon). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y old); [lia|]. destruct (Z.lt_ge_cases y (old + 4096)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI old 4096); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| lia]. }
clearbody m2.

eapply rimplT_evt.
{ eapply (ram_bl_ok _ gp tp t0 t1 t2 (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 _ s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (old + 4096)); [lia | | | exact MI2].
- unfold pw in HC2. cbn [oconc] in HC2. exact HC2.
- unfold wz in TC2. exact TC2. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & HC3 & TC3). replace (old + 4096 - 4096) with old by lia.

pose proof (rAMI_grow st stI brid r boff AI Hr ltac:(rewrite Kr; discriminate) Lr) as (AIG & CQG & RG'). fold stG in AIG, CQG, RG'.
assert (MRG : rmrep stG m2).
{ unfold stG. apply (rmrep_grow_region stI m2 brid r boff MR2 Hr);
first [ rewrite Kr; discriminate
| exact Lr
| unfold PGSZ in OAL; exact OAL
| rewrite <- OLD; exact RF
| exact (amp_rpos stI AMPI)
| intros q rq Hq NE KB; apply NE; exact (UNQ q rq Hq KB)
| unfold alloc_ceiling, PGSZ in *; lia ]. }
assert (PWX : forall q, pw stX q = pw stI q) by (intros [q|]; unfold pw, oconc; [change (conc stX q) with (conc stG q); rewrite CQG|]; reflexivity).
assert (PWG : forall q, pw stG q = pw stI q) by (intros [q|]; unfold pw, oconc; [rewrite CQG|]; reflexivity).
assert (CQX : forall q, conc stX q = conc stI q) by (intros q; change (conc stX q) with (conc stG q); apply CQG).
assert (MRX : rmrep stX m3).
{ eapply (rmrep_ctx_frameW stG stX m2 m3 _ MRG MU3 WM3); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells. rewrite !PWX.
cbn [ctx stX stG upd_ctx s_ctx set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold wz at 5. exact HC3.
- right. split; [| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
unfold actives. apply map_ext. intros i. rewrite PWX, PWG. reflexivity.
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- left. unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (brid, boff + 4096)) with (conc stG (brid, boff + 4096)).
rewrite CQG. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold wz.
replace (r_base r + (boff + 4096)) with (old + 4096) by lia. change (s_ctx stI) with (ctx stI). exact TC3. }

assert (M23 : magree (rFP stX) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. unfold RCTX. split; [| split; [| exact I]]; intros y Hy; left; right; right; left; unfold RCTX; lia. }
assert (ZN3 : rw_cells rsegs m3 old [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]).
{ eapply rw_cells_transport; [exact ZN| exact MU3| exact WM3|]. cbn. unfold RCTX. lia. }
destruct ZN3 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (AGX1 : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. destruct (ami_regions _ _ AI q rq) as (r0 & H0 & _); [rewrite <- RGI; exact Hq|].
destruct (decide (q = brid)) as [->|NE].
- eexists. split; [exact RG'|]. rewrite Hr in Hq. inversion Hq; subst. cbn. repeat split; lia.
- exists rq. change (s_regions stX) with (<[brid := mkRegion (r_kind r) (r_base r) (boff + 4096)]> (s_regions stI)). rewrite lookup_insert_ne by congruence. repeat split; auto; lia. }
assert (AG3 : magree (rFP stX) m m3).
{ eapply magree_trans; [| exact M23| exact AGX1| intros y X; exact X]. eapply magree_trans; [exact AG1| exact M12| intros y X; exact X| intros y X; exact X]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_magree; [exact AUX1| |intros y X; exact (rFP_below stX y (proj1 MRX) X)].
eapply magree_trans; [exact M12| exact M23| exact AGX1| intros y X; exact X]. }
replace (Z_to_bv 64 old) with (Z_to_bv 64 (conc stX (brid, boff))) by (change (conc stX (brid, boff)) with (conc stG (brid, boff)); rewrite CQG; reflexivity).
eapply (rcarve_K stX (brid, boff) (mkRegion (r_kind r) (r_base r) (boff + 4096)) m3 _ junk e1);
first [exact RG' | exact MRX | exact MI3 | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | reflexivity | idtac].
+ unfold stX. apply (rAMI_ctx st stG _ AIG).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AIG).
* left. reflexivity.
* right. right. exists brid, (boff + 4096), (mkRegion (r_kind r) (r_base r) (boff + 4096)). split; [reflexivity|]. split; [exact RG'|]. cbn. rewrite Kr. discriminate.
+ cbn. rewrite Kr. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite round_up_pg_aligned; [lia|]. rewrite Z.add_mod, OAL by lia. reflexivity.
+ unfold pgal. unfold PGSZ in OAL. exact OAL.
+ cbn [snd r_base]. unfold lr_lo. cbn [r_kind r_base]. rewrite Kr. unfold PGSZ in O4. lia.
+ change (s_areas stX) with (s_areas stI). apply (proj1 (FRA (brid, boff) eq_refl ltac:(cbn; lia))).
+ intros j Hj. change (s_metas stX) with (s_metas stI). apply (proj2 (FRA (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
+ cbn. lia.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZB.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZW.
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
rewrite CQX. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold PGSZ. lia.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (old =? old + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [orb negb].
eapply rimplT_evt.
{ unfold PGSZ. eapply (ram_bl_fail _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI old); [exact MR1| exact ACNT| lia| lia| exact MI1]. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M13 : magree (rFP stI) m1 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 s junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ exact RGI.
+ exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ exact TLI.
+ exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply rw_cells_transport; [exact ERR1| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
+ eapply rauxv_ok_magree; [exact AUX1| exact M13| intros y X; exact (rFP_below stI y WF1 X)].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1 M13); intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.

Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs m1 lo (bv_unsigned sp + -64) ->
rw_cells rsegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
ps_m s = ps_m s ->
rimplT o (SVis (EBrk 0) (fun cur =>
if negb (brk0_answer_ok cur) then bad_answer bail else
let base := round_up_pg cur in
let new := base + 2 * PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok cur new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI base (2 * PGSZ)) then bad_answer bail
else
SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
let '(st1, rid) := new_region RKBrk base (2 * PGSZ) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
(set_avail_meta_areas (Some (rid, PGSZ))
(set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
am_after_brk st2 false k bail)))) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce460) fc None m1 (seg_rom rsegs)).
Proof using AMP ERR KH LO LOLE TK TP.
intros until t6. intros AMPI AI RGI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1 _.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6 & HX7) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6.

eapply rimplT_evt.
{ eapply (ram_disp_untried _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
intros ms2 ->.
eapply (rimplT_brk0 o _ s).
{ exact (ram_brk0_node x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1). }
intros cur ms3 [-> CR]. unfold rbrk_regs.
destruct (brk0_answer_ok cur) eqn:B0; cbn [negb]; [| apply rimplT_undef].
unfold brk0_answer_ok, TWO64, PGSZ in B0. apply andb_prop in B0. destruct B0 as [B0 _]. apply andb_prop in B0. destruct B0 as [C0 CAL].
apply Z.ltb_lt in C0. apply Z.eqb_eq in CAL.
rewrite (round_up_pg_aligned cur CAL). cbv zeta. unfold PGSZ.
replace (2 * 4096) with 8192 by reflexivity.

eapply rimplT_evt.
{ eapply (ram_bu_mid _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m1 cur); [lia| exact CAL| unfold wz in HX6; exact HX6| exact MI1]. }
intros ms4 (a2' & m2 & -> & MU2 & WM2 & MI2 & TC2).
eapply (rimplT_brk o (cur + 8192) _ (set_brk_ps cur s)).
{ lia. }
{ exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 0xce4c0 (or_intror eq_refl) cur (cur + 8192) ltac:(lia)). }
intros a ms5 ->. cbn [ps_brk set_brk_ps]. unfold brk_res, brk_mem, rbrk_regs.

assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (ERR2 : rw_cells rsegs m2 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (HC2 : rw_cells rsegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (eapply rw_cells_transport; [exact HX1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (M12 : magree (rFP stI) m1 m2).
{ eapply magree_of_munch; [exact MU2|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI cur 8192) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
unfold alloc_ceiling in OC.
rewrite (brk_new_pages_aligned cur 8192) by (first [lia | exact CAL | reflexivity]).
pose proof (rimage_range_clear stI cur 8192 RS RF ltac:(lia)) as IMG.
assert (Hc1 : 0 <= cur < 2^64) by lia. assert (Hn1 : 0 <= 8192 < 2^64) by lia. assert (Hcn : cur + 8192 <= 2^64) by lia.
set (m3 := apply_zeros m2 [(wa cur, Z_to_bv 64 8192)]).
assert (HC3 : rw_cells rsegs m3 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [exact HC2| cbn; unfold RCTX; lia]).
assert (TC3 : rw_cells rsegs m3 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)])
by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [unfold RCTX in TC2 |- *; exact TC2| cbn; unfold RCTX; lia]).
assert (MI3 : mem_inv rsegs m3) by (apply (mem_inv_zeros rsegs m2 cur 8192 Hc1 Hn1 Hcn MI2); intros y Hy; apply ref_ro_addr_false; lia).
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [exact FR2| cbn; lia]).
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -64)) by (apply (stk_zeros rsegs m2 cur 8192 Hc1 Hn1 Hcn); exact ST2).
assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 e1]) by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [exact ERR2| cbn; rewrite rETP'; lia]).
assert (VML4 : rw_cells rsegs m3 RVMLOCK [C4 (Z_to_bv 64 0)]).
{ pose proof MR1 as (_ & _ & (_ & _ & _ & _ & _ & VML1) & _).
apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [eapply rw_cells_transport; [exact VML1| exact MU2| exact WM2|]; cbn; unfold RCTX, RVMLOCK; lia| cbn; unfold RVMLOCK; lia]. }
pose proof (rw_cells_zeros_new rsegs m2 cur 8192 Hc1 Hn1 Hcn) as ZN. fold m3 in ZN.
assert (M23 : magree (rFP stI) m2 m3).
{ intros y Hy Hc. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y cur); [lia|]. destruct (Z.lt_ge_cases y (cur + 8192)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| lia]. }

assert (E23 : forall y, 0 <= y < 2^64 -> ~ (cur <= y < cur + 8192) -> m3 (wa y) = m2 (wa y)).
{ intros y Hy Hn. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia. lia. }
clearbody m3.

eapply rimplT_evt.
{ eapply (ram_bu_ok _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m3 cur);
first [exact TC3 | lia]. }
intros ms6 ->.
pose proof MI3 as MI4. pose proof FR3 as FR4. pose proof ST3 as ST4. pose proof TC3 as TC4. pose proof HC3 as HC4. pose proof ERR3 as ERR4.
eapply (rimplT_mmap_fixed o cur PGSZ _ (set_brk_ps (cur + 8192) (set_brk_ps cur s))).
{ unfold PGSZ. eapply (rmmap_fixed_spec (dec_mmap_fixed cur 4096) (fx_rel cur)) with (lo := lo) (errv := e1);
[ intros rsp fa Hd; exact (dec_mmap_fixed_shape cur 4096 rsp fa Hd)
| rewrite unsigned_lit by lia; exact ST4 | exact ERR4 | exact MI4 | exact VML4 | unfold RVMLOCK; lia
| unfold RVMLOCK; rewrite ?A2.mmap_len_round_up by lia; try (change (round_up_pg 4096) with 4096); lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?A2.mmap_len_round_up, ?rETP', ?TPv, ?unsigned_lit by lia; try (change (round_up_pg 4096) with 4096); try lia. }
intros fa ms7 MP. unfold rmmap_fixed_post in MP.
destruct MP as (rr & u & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5 & REL & -> & MU5 & WM5 & MI5 & ST5 & ERR5).
rewrite A2.mmap_len_round_up in MU5. change (round_up_pg 4096) with 4096 in MU5. rewrite unsigned_lit in MU5, ST5 by lia.
replace (ret_pc (Z_to_bv 64 0xce4e4)) with (Z_to_bv 64 0xce4e4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

replace (mmap_fixed_answer_ok cur (fixed_val cur fa)) with true.
2:{ symmetry. unfold mmap_fixed_answer_ok, is_errno_form, fixed_val, neg_errno, TWO64.
destruct fa as [e|  |e]; cbn in REL.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply Z.eqb_refl.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
cbn [negb].
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stI).
pose proof (rAMI_new_region st stI RKBrk cur 8192 AI ltac:(discriminate) ltac:(lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
rewrite (am_after_brk_false_eq st1 _ (rid, 4096) k bail) by (cbn; first [lia | reflexivity]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ st1).

assert (E45 : forall y, 0 <= y < 2^64 -> ~ (bv_unsigned sp - 64 - 112 <= y < bv_unsigned sp - 64) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 4096) -> m5 (wa y) = m3 (wa y)).
{ intros y Hy N1 N2 N3. apply MU5. rewrite wa_unsigned by lia. cbn. rewrite ?rETP' in *. repeat split; lia. }
assert (HC5 : rw_cells rsegs m5 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end)).
{ eapply RA2.rrw_cells_agree; [exact HC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
assert (TC5 : rw_cells rsegs m5 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
{ eapply RA2.rrw_cells_agree; [exact TC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply RA2.rrw_cells_agree; [exact FR4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
eapply rimplT_evt.
{ eapply (ram_b_store _ gp tp u0 u1 u2 _ u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (cur + 8192));
first [exact HC5 | exact TC5 | exact MI5 | lia]. }
intros ms8 (m6 & -> & MU6 & WM6 & MI6 & HC6 & TC6). replace (cur + 8192 - 4096) with (cur + 4096) by lia.
assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].

assert (E16 : forall y, 0 <= y < 2^64 ->
~ (RCTX + 40 <= y < RCTX + 48) -> ~ (RCTX + 920 <= y < RCTX + 928) -> ~ (lo <= y < bv_unsigned sp) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 8192) ->
m6 (wa y) = m1 (wa y)).
{ intros y Hy N0 N1 N2 N3 N4.
rewrite (MU6 (wa y)) by (rewrite wa_unsigned by lia; cbn; unfold RCTX in *; lia).
rewrite (E45 y Hy) by (rewrite ?rETP' in *; lia).
rewrite (E23 y Hy) by lia.
apply MU2. rewrite wa_unsigned by lia. cbn. unfold RCTX in *. lia. }
assert (MRn1 : rmrep st1 m1).
{ unfold st1. apply (RA2.rmrep_new_region stI m1 m1 cur 8192 RKBrk);
first [ exact MR1
| eapply ptrs_in_mono; [| exact PTRI]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| exact FRr | exact FRs
| unfold alloc_ceiling; change (round_up_pg 8192) with 8192; lia
| change (round_up_pg 8192) with 8192; exact RF
| intros; reflexivity
| intros; discriminate
| lia ]. }
assert (CQX : forall q, fst q <> rid -> conc stX q = conc stI q) by (intros q Hq; change (conc stX q) with (conc st1 q); apply CQ1; exact Hq).
pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
assert (PWX : forall q, optr_in (fun r => (r < s_next_rid stI)%N) q -> pw stX q = pw stI q).
{ intros [q|] Hq; unfold pw, oconc; [rewrite CQX; [reflexivity|]|reflexivity]. cbn in Hq. unfold rid. lia. }
assert (MRX : rmrep stX m6).
{ apply (rmrep_agree_but_ctx st1 stX m1 m6 MRn1); try reflexivity.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RMLOCK, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RLIBC, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RGOT_SSP, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RSSP_GUARD, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RVMLOCK, RCTX in *; lia.
- intros a ar Ha y Hy. change (s_areas st1) with (s_areas stI) in Ha.
destruct (rarea_conc stI a ar WF1 Ha) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RBa & RBAa & RBCa).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as (Da1 & _ & Da23 & Da2). unfold alloc_ceiling in RBCa.
rewrite (CQ1 a) in Hy by (intros E; rewrite E, FRr in Hra; discriminate).
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. eapply rrepfoot_area; [exact Ha| lia].
- intros b gh Hb y Hy. change (s_groups st1) with (s_groups stI) in Hb.
destruct (rgroup_conc stI b gh WF1 Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Alb & RBb & RBCb).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). destruct (rreserved_disjoint _ _ RFb) as (Db1 & _ & Db23 & Db2). unfold alloc_ceiling in RBCb.
pose proof (round_up_pg_ge (r_len rb)).
rewrite (CQ1 b) in Hy by (intros E; rewrite E, FRr in Hrb; discriminate).
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. do 5 right. left. exists b, gh. split; [exact Hb| lia].
- intros q rq Hq Kq y Hy.
assert (Hq' : (s_regions stI) !! q = Some rq).
{ change (s_regions st1) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)) in Hq.
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; discriminate| rewrite lookup_insert_ne in Hq by congruence; exact Hq]. }
destruct (WR _ _ Hq') as (RB0 & _ & _ & RBC & RFq). destruct (rreserved_disjoint _ _ RFq) as (Dq1 & _ & Dq23 & Dq2). unfold alloc_ceiling in RBC.
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). right. exists q, rq. auto.
-
destruct (rmrep_ctx_mid_agree st1 stX m1 m6 MRn1 ltac:(right; repeat split; reflexivity) eq_refl) as (X2 & X3 & X4 & X5).
{ intros y Hy. apply E16; rewrite ?rETP'; unfold RCTX in *; lia. }
split; [| split; [exact X2| split; [exact X3| split; [exact X4| split; [exact X5| split; [| exact (rmrep_init1 _ _ MRn1)]]]]]].
+ unfold ctx_head_cells. rewrite !PWX by assumption.
cbn [ctx stX st1 upd_ctx s_ctx set_next_rid set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold pw in HC6 |- *. cbn [oconc] in HC6 |- *. unfold wz. exact HC6.
+ unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. change (s_ctx st1) with (ctx stI). unfold wz. exact TC6. }

assert (ZP3 : rw_cells rsegs m3 (cur + 4096) [CB 4096 (zeros 4096)]).
{ destruct ZN as [[_ ZB0] ZW0]. cbn [cells_bytes cbytes cells_size csize app] in ZB0, ZW0. rewrite app_nil_r in ZB0. rewrite Nat.add_0_r in ZW0.
eapply (rrw_cells_of_zeros m3 cur 8192 4096); [exact ZB0| exact ZW0| split; [exact (zeros_length 4096)| exact I]| cbn [cells_bytes cbytes cells_size csize]; rewrite app_nil_r, Nat.add_0_r; reflexivity| lia| cbv; discriminate]. }
assert (ZP6 : rw_cells rsegs m6 (cur + 4096) [CB 4096 (zeros 4096)]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| cbn [cells_size csize]; rewrite ?Nat.add_0_r; cbn; unfold RCTX; lia].
eapply RA2.rrw_cells_agree; [exact ZP3|].
cbn [cells_size csize]. rewrite ?Nat.add_0_r. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
destruct ZP6 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize app] in ZB, ZW. rewrite app_nil_r in ZB. rewrite Nat.add_0_r in ZW.
assert (ST6 : stk rsegs m6 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
assert (ERR6 : rw_cells rsegs m6 (errno_addr tp) [C4 (sysret_errno rr e1)]) by (eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (FPX : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq.
change (s_regions stX) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)).
rewrite lookup_insert_ne by (intros ->; rewrite FRr in Hq; discriminate). repeat split; auto; lia. }
assert (M16 : magree (rFP stX) m1 m6).
{ intros y Hy Hc.
assert (~ (RCTX + 40 <= y < RCTX + 48)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
assert (~ (RCTX + 920 <= y < RCTX + 928)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
assert (~ (lo <= y < bv_unsigned sp)) by (intros X; apply Hc; left; left; exact X).
assert (~ (errno_addr tp <= y < errno_addr tp + 4)) by (intros X; apply Hc; left; right; left; rewrite <- TPv; exact X).
assert (~ (cur <= y < cur + 8192)).
{ intros X. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| exact X]. }
apply E16; assumption. }
replace (Z_to_bv 64 (cur + 4096)) with (Z_to_bv 64 (conc stX (rid, 4096))) by (change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rcarve_K stX (rid, 4096) (mkRegion RKBrk cur 8192) m6 _ _ (sysret_errno rr e1));
first [exact RG1 | exact MRX | exact MI6 | exact FR6 | exact ST6 | exact ERR6 | reflexivity | idtac].
all: try (cbn [snd fst r_len r_base r_kind]; unfold pgal, lr_lo; cbn [r_kind r_base]; change (round_up_pg 8192) with 8192; first [discriminate | lia]).
+ unfold stX. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* left. reflexivity.
* right. right. exists rid, 8192, (mkRegion RKBrk cur 8192). split; [reflexivity|]. split; [exact RG1|]. cbn. discriminate.
+ change (s_areas stX) with (s_areas stI). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr0 & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas stX) with (s_metas stI). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MKI _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr0 & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
+ cbn. lia.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZB.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZW.
+ eapply rauxv_ok_magree; [exact AUX1| exact M16| intros y X; exact (rFP_below stX y (proj1 MRX) X)].
+ eapply magree_trans; [exact AG1| exact M16| exact FPX| intros y X; exact X].
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. reflexivity.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (cur =? cur + 8192) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb negb].
eapply rimplT_evt.
{ eapply (ram_bu_fail _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m1 m2 stI cur);
first [exact MR1 | exact MU2 | exact WM2 | exact ACNT | exact MI2 | reflexivity | exact TC2 | lia]. }
intros ms6 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M23 : magree (rFP stI) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 (set_brk_ps cur s) junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ exact RGI.
+ exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ exact TLI.
+ exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
+ eapply rauxv_ok_magree; [exact AUX1| | intros y X; exact (rFP_below stI y WF1 X)].
eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1); [eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X] | |];
intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.

#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbody_spec : forall (stI : mstate) (x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (junk : list byte) (e1 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
rmrep stI m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs m1 lo (bv_unsigned sp + -64) ->
rw_cells rsegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (am_body stI k bail) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce40c) fc None m1 (seg_rom rsegs)).
Proof.
intros until e1. intros AMPI AI RGI BLI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MR1 as (WF1 & _).
unfold am_body.
destruct (c_free_meta_head (ctx stI)) as [h|] eqn:FMH.
-
pose proof (amp_fmh stI AMPI h FMH) as [HN0 HM0].
pose proof (amp_links stI AMPI) as [CLn CLp CLno CLs].
pose proof (CLs h HN0) as MSh.
pose proof (amp_fml stI AMPI h HM0 HN0) as (CL0 & FMn & FMp).
destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:HN; [| exfalso; apply HN0; reflexivity].
destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:HP.
2:{ exfalso. pose proof (proj2 (CLno h) HP) as X. rewrite HN in X. discriminate. }
destruct (CLn h nx HN) as [PVn MSn]. destruct (CLp h pv HP) as [NXp MSp].
assert (SELF : nx = h <-> pv = h).
{ split; intros ->; [rewrite HP in PVn| rewrite HN in NXp]; congruence. }
eapply rimplT_evt.
{ eapply (ram_deq sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI h nx pv);
first [exact MR1 | exact MI1 | exact FMH | exact MSh | exact HN | exact HP | exact MSn | exact MSp | exact SELF | exact FR1 | exact ST1 | exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
+ eapply (ram_rel_deq st stI h nx pv AI); try assumption.
* rewrite <- FMH. symmetry. exact (proj1 (proj2 (ami_ctx _ _ AI))).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HN.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HP.
* eapply meta_slot_same_areas; [| exact MSh]. symmetry. exact (ami_areas _ _ AI).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact CL0.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMn nx eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). intros X. apply (proj1 (CLno nx)) in X. rewrite PVn in X. discriminate.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMp pv eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). rewrite NXp. discriminate.
+ exact MR2.
+ exact MI2.
+ exact ST2.
+ eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
+ pose proof (sbl_regions _ _ (sbl_dequeue stI LFree h)) as RD.
eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [exact RD| exact X] | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a RD)); exact X].
+ unfold brk_link_ps in *. rewrite (sbl_brk _ _ (sbl_dequeue stI LFree h)). destruct (c_brk (ctx stI)) as [| |rid off]; auto.
unfold conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). exact BLI.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ unfold pw, oconc, wz, conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). reflexivity.
+ intros X; discriminate X.
-
destruct (Z.eqb_spec (c_avail_meta_count (ctx stI)) 0) as [CNT|CNT]; cbn [negb].
+
eapply rimplT_evt.
{ eapply (ram_disp0 _ gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact FMH| exact CNT]. }
intros ms2 ->.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
assert (PTRI : ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI).
{ apply (ami_ptrs _ _ AI); [| eapply ptrs_in_mono; [| exact (proj1 (amp_ptrs st AMP))]; intros q Hq; cbn in Hq; pose proof (ami_next _ _ AI); lia]. intros rid r Hr _.
destruct (N.lt_ge_cases rid (s_next_rid stI)) as [L|G]; [exact L|]. destruct (ami_fresh _ _ AI rid G) as [X _]. rewrite X in Hr. discriminate. }
destruct (Z.eqb_spec (c_avail_meta_area_count (ctx stI)) 0) as [ACNT|ACNT]; cbn [andb].
*
destruct (c_brk (ctx stI)) as [| |brid boff] eqn:BRK; cbn [negb].
--
eapply (rbrk_untried_path stI m1 junk e1); first [exact AMPI | exact AI | exact RGI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | reflexivity].
--
eapply rimplT_evt.
{ eapply (ram_disp_dead _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
intros ms3 ->.
eapply (rmmap_path stI m1 s junk e1); first [exact AI | exact RGI | exact ACNT | exact TLI | exact MKI | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
pose proof (amp_shift stI AMPI). lia.
--
eapply (rbrk_live_path stI brid boff m1 junk e1); first [exact AMPI | exact AI | exact RGI | exact BLI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1].
*
destruct (amp_avail_areas stI AMPI ACNT) as (p & r & AMA & Hr & NK & PAL & P0 & PLR & PHI & FRA).
pose proof (amp_acount stI AMPI) as ACR.
unfold am_after_brk. rewrite (proj2 (Z.eqb_neq _ _) ACNT).
eapply rimplT_evt.
{ eapply (ram_disp_fin _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI p r);
first [exact MR1 | exact ACNT | exact AMA | exact Hr | unfold pgal, PGSZ in *; exact PAL | lia | idtac]. unfold PGSZ in *. lia. }
intros ms3 ->.
eapply (rfinish_path stI p r m1 s junk e1); first [exact AI | exact AMA | exact Hr | exact NK | exact P0 | exact PLR | exact TLI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
-- unfold PGSZ in PHI. lia.
-- unfold pgal. unfold PGSZ in PAL. exact PAL.
-- apply (proj1 (FRA p eq_refl ltac:(lia))).
-- intros j Hj. apply (proj2 (FRA (aadd p (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
-- lia.
+
destruct (amp_avail stI AMPI CNT) as (aa & ar & kk & Haa & AVM & K0 & K1 & MQ).
pose proof (amp_count stI AMPI) as CR.
assert (MSq : meta_slot stI (aadd aa (AREA_HDR + META_SIZE * kk))) by (exists aa, ar, kk; repeat split; auto; unfold NSLOTS in *; lia).
rewrite (am_take_eq stI k bail _ AVM).
eapply rimplT_evt.
{ eapply (ram_take_walk sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI _);
first [exact MR1 | exact MI1 | exact FMH | exact CNT | exact AVM | exact MSq | exact FR1 | exact ST1 | exact LO | unfold NSLOTS in CR; lia | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
* eapply (ram_rel_take st stI _ AI).
-- rewrite <- AVM. symmetry. exact (proj1 (proj2 (proj2 (ami_ctx _ _ AI)))).
-- rewrite <- (ami_metas _ _ AI). exact MQ.
-- eapply meta_slot_same_areas; [| exact MSq]. symmetry. exact (ami_areas _ _ AI).
* exact MR2.
* exact MI2.
* exact ST2.
* eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
* eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
* eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [| exact X]; reflexivity | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a ltac:(reflexivity))); exact X].
* unfold brk_link_ps in *. unfold ctx in BLI. cbn. destruct (c_brk (s_ctx stI)) as [| |rid off]; auto.
* reflexivity.
* reflexivity.
* reflexivity.
* unfold pw, oconc, wz. reflexivity.
* intros X; discriminate X.
Qed.

#[using="lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH"] Lemma ralloc_meta_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs)).
Proof.
intros. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR as (WF0 & _).
rewrite alloc_meta_eq. unfold ralloc_meta_entry.
eapply rimplT_evt.
{ eapply (ram_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st);
first [exact MR | exact MI | exact AUX | exact ST | exact LO | exact (rmrep_init1 st m MR) | exact (amp_s_secret st AMP) | exact (amp_secret st AMP) | lia]. }
intros ms1 (x1 & u0 & u1 & u2 & s1x & s4x & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u9' & u10 & u11 & u12 & u13 & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & MR1).
assert (M01 : magree (rFP (am_init_st st)) m m1).
{ eapply magree_of_munch; [exact MU1|]. cbn. split; [| split; [| exact I]]; intros y Hy.
- left. left. lia.
- left. right. right. left. unfold RCTX in *. lia. }
eapply (rbody_spec (am_init_st st) x1 u0 u1 u2 s1x s4x u3 u4 u5 u6 u7 u8 u9 u9' u10 u11 u12 u13 m1 junk errv).
- exact (rAMpre_init st AMP).
- exact (rAMI_init st AMP).
- exact (ram_init_regions st).
- unfold brk_link_ps in *. rewrite ram_init_brk. destruct (c_brk (ctx st)) as [| |rid off]; auto. rewrite ram_init_conc. exact BL.
- exact MR1.
- exact MI1.
- exact FR1.
- exact ST1.
- eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite rETP'. cbn. unfold RCTX. lia.
- eapply rauxv_ok_magree; [exact AUX| exact M01| intros a X; exact (rFP_below (am_init_st st) a (proj1 MR1) X)].
- exact M01.
Qed.
End ASM.

#[using="Type"] Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof.
unfold ralloc_meta_stmt. intros.
eapply ralloc_meta_main; eassumption.
Qed.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QdZ1.Mq3 QQbX.Mq3 Qv4L.Mq7 Qv4L.Mq0 Qv4L.Mq8 QnkH.Mq7 Qi8L.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
match res with
| (st2, Some (g, idx)) =>
exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce954) fc None m1 (seg_rom rsegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a)
/\ 0 <= c_mmap_counter (ctx st2) < 2^32
/\ slot_ok st2 g b r idx n
/\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
| (st2, None) =>
exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp)
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ errv = Z_to_bv 64 12
end.

#[using="Type"] Lemma renf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
renf_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof.
intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

#[using="Type"] Lemma rfail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
rfail_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof.
intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rbig_stmt : Prop :=
forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
(m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
let st1 := set_tick t st in
RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^63 - 4097 -> brk_link_ps st s ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce6a4) fc None m1 (seg_rom rsegs)).

#[using="Type"] Lemma rrepfoot_low_core stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (6434236 <= a < 6434240).
Proof.
intros WF H. pose proof WF as (_ & WR & _ & WA & WG). unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
Qed.

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

#[using="as_pre as_inv RAS AS_PRE RBIG"] Lemma rmalloc_core_implT :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 -> (s_tick st < t)%N ->
rimplT m (malloc_core full_lay (set_tick t st) n) s
(rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge 0) as ASG.
assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
pose proof MR as (WF0 & CX0 & GL0 & _). destruct GL0 as (_ & NL & _).
assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
{ intros m1 MU WM. unfold alloc_ceiling in CLO.
split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split. { eapply unk_agree_munch; [| exact MU| |].
- eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
- intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
- intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
assert (ETP : bv_unsigned tp + -164 = 6434236) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
destruct (Z.le_gt_cases (2^63 - 4097) n) as [OV|NOV].
{
unfold malloc_core.
replace (size_overflows n) with true by (symmetry; unfold size_overflows; apply Z.leb_le; lia).
riprefixT. eapply evt_cut.
{ eapply (rentry_ovf_walk ra sp gp tp); [exact HA| lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI| exact ERR| exact TP]. }
intros ms' (a1' & m1 & -> & ST1 & MU & WM & MI1 & ERR1).
apply evt_done. apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, (Z_to_bv 64 12). do 14 eexists. split; [reflexivity|].
split. { apply rmrep_set_tick. eapply (rmrep_transport_unowned st m m1 _ MR MU WM).
intros lo' hi' a Hin Ha RF. destruct (rrepfoot_low_core st a WF0 RF) as [A1 A2].
rewrite ETP in Hin. unfold alloc_ceiling in *. destruct Hin as [E|[E|[]]]; inversion E; subst; lia. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|].
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. rewrite ETP. constructor; [cbn; unfold alloc_ceiling in CLO; lia|]. constructor; [cbn; unfold alloc_ceiling in CLO; lia| constructor]. }
split. { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. rewrite ETP. unfold alloc_ceiling in CLO. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia. }
split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity. }
destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
-
riprefixT. eapply evt_cut.
{ eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI]. }
intros ms' (a1' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
apply evt_done.
eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
+ unfold RAM_STACK. lia.
+ lia.
-
assert (N32 : 0 <= n < 2^32) by (unfold MMAP_THRESHOLD in TH; lia). clear N. rename N32 into N.
unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
riprefixT. eapply evt_cut.
{ eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI| exact NL]. }
intros ms' (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
apply evt_done.
eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
all: try eassumption.
+ apply renf_hyp_ret.
+ apply rfail_hyp_ret.
+ unfold RAS_STACK. lia.
+ reflexivity.
+ intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.

End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4vs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 Qy5Y.Mq4 QlQE.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3.
Import QPjm.Mq3 QWTl.Mq4 QDUx.Mqa Q9Ay.Mqb QXxF.Mq4 Q4vs Q6y7.
Import QFkE.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1.
Import Q98Z.Mq1 QdZ1.Mq2 QQbX.Mq2 QnkH.Mq8 Qv4L.Mq9 QnkH.Mq9 QnkH.Mqa Qi8L.Mq5.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
(st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rmrep st' m'
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
/\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

#[using="Type"] Lemma rpres_except_entry st lo (sp : word) m m1 :
munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 -> lo <= bv_unsigned sp - 96 ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof.
intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

#[using="Type"] Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
oracle_ok o m st -> rmrep st mw -> alloc_ceiling <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof.
intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
rewrite (OK rid r q h Hr Hk Hq M8 Hc).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
unfold alloc_ceiling in *.
symmetry. apply (PE (r_base r + q)); [lia|].
intros [[A|[A|A]]|[A|A]].
- lia.
- unfold RCTX in A. lia.
- destruct A as (rid' & r' & Hr' & Hk' & Hin).
destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
- destruct A as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
Z.div_mod_to_equations. lia.
- destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
destruct (N.eq_dec rid' rid) as [->|NE].
+ rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

#[using="Type"] Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof.
intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

#[using="Type"] Lemma rfree_fp_same st st' lo (sp : Z) a :
s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof. intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

#[using="Type"] Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof.
intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
unfold alloc_ceiling in *.
destruct H as [[A|[A|A]]|[A|A]].
- lia.
- unfold RCTX in A. lia.
- destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold alloc_ceiling in RC. lia.
- destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
Qed.

#[using="Type"] Lemma rknown_byte st m (q : aptr) r v :
rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
cell_read (get_shadow st (fst q)) (snd q) = Known v ->
bytes_at rsegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof.
intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

#[using="Type"] Lemma rimplT_queue {R} o h g st0 (k : mstate -> QUZl.M R) bail s Q ms :
(m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
rimplT o (queue h g st0 k bail) s Q ms.
Proof.
intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

#[using="Type"] Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof. reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

#[using="LO"] Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
(forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
(exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof.
intros RP PE FP KI ZI FR RES OOK MRX ER ES.
destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
unfold rntf_q. do 16 eexists. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

#[using="LO"] Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> QUZl.M R) (bail : QUZl.M R)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
(st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
rmrep st m -> mem_inv rsegs m -> oracle_ok o m st ->
stk rsegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
(forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdf80) fc None m (seg_rom rsegs)).
Proof.
induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
{ cbn [nontrivial_free]. apply rimplT_undef. }
rewrite ntf_unfold. cbv zeta.
pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
pose proof (go_slot _ _ _ GO) as MSL.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
set (ms0 := MS _ _ _ _ _ _ _).

assert (ENTRY : entry_hyps st g i ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
{ intros EH. subst ms0. eapply rntf_entry; eauto. }

assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
(G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
(G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
entry_hyps st g i).
{ intros. constructor; auto.
- exact (go_avail _ _ _ GO).
- exact (go_freed _ _ _ GO).
- pose proof (go_sc _ _ _ GO). lia.
- intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
- intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
- split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
destruct (ntf_cond st g i) eqn:HC.
-

assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
(m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
(forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
wmono rsegs m m2 -> oracle_ok o m2 stX ->
data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
{ intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
set (stU := fg_usage_st stX g) in *.
assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).

assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
{ destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
try lia; try exact HALL.
- exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
- destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
- destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
[ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
| pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
rewrite RU in FC; exact FC ])).
fold stG in GD. destruct GD as (KIG & NGM & NSL).
assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).

pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
-
assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
rewrite free_meta_eq.
eapply rimplT_evt.
{ eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
| apply munch_refl | apply wmono_refl | idtac].
- pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
- intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
intros ms3 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
+ destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
(eapply rpres_except_mono; [exact PE3| exact FPX]).
+ intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
+ eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
* unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* intros [b Hb]. apply NGM. exists b. unfold hosts in *.
replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
+ apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
+
pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
set (stS := record_seq _ (step_seq stG)) in *.
assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
unfold fm_st. apply frame_queue.
* apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
* apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
* cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
* right; exact (hosts_is_gm _ _ _ HOSTS).
+
pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
* unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
* exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
* intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
+ eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
+ exact MRG.
+ pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
+ pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
-
assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).

pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
clear NEST.
pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
assert (B1LT : snd b1 + 16 <= snd p).
{ rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
pose proof (go_stride _ _ _ GO1) as [S16 _].
assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).

pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
{ split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
unfold UNIT, IB in *. lia. }
destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].

unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
{ intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
rewrite !ESH.
rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
cbn [Z.eqb negb].
set (off16 := lo8 + 256 * hi8).
assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
{ unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
rewrite EB. unfold get_group.
replace (s_groups stG !! b1) with (s_groups stX !! b1).
2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.

assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.

assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
bytes_at rsegs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
{ intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
assert (HDR : bytes_at rsegs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
{ change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }

destruct HOSTSX as [aig Hghp].
eapply rimplT_evt.
{ eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
| exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | apply rntf_frame_size | idtac].
all: try reflexivity.
all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
all: rewrite ?EU1.
all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
all: try (symmetry; exact EB).
all: match goal with
| |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
| |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
| |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
fold off16 in G17; unfold UNIT in G17;
replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
rewrite Z.div_mul in G17 by lia; lia
| |- ?G => idtac "NCGOAL" G; fail
end. }
intros ms3 NC. unfold rnest_call_post in NC.
destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
fold stG in MR4.

pose proof (bv_unsigned_in_range _ sp) as SPR'.
assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (unfold alloc_ceiling in LO; rewrite unsigned_lit; lia).
rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
eapply (IH R _ bail s Q (Z_to_bv 64 0xce208) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
+ exact KIG.
+ constructor.
* exact HB1G.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
+ unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
+ exact MR4.
+ exact MI4.
+ apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
+ rewrite SPU. exact ST4.
+ rewrite SPU. lia.
+
intros st3 mi ms5 NQ. rewrite free_meta_eq.
unfold rntf_q in NQ. rewrite SPU in NQ.
destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
replace (ret_pc (Z_to_bv 64 0xce208)) with (Z_to_bv 64 0xce208) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
{ apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
assert (NGM3 : ~ is_gm st3 g).
{ intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
eapply rimplT_evt.
{ eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
- unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
- intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
- unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
- eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
- exact ST5. }
intros ms6 RP. apply KH.
pose proof (frame_trans _ _ _ FRG FR35) as FR03.
pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
* destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
(eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
(eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
(eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
* intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
* exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
* apply ZINV_fm. exact ZI3.
* unfold fm_st. apply frame_queue.
-- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
-- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
-- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
-- right; exact (hosts_is_gm _ _ _ HOSTS).
* destruct mi as [[bb len]|]; [| exact RES5].
destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
* exact OOK5.
* exact MR5.
* exact FS1.
* exact FS2. }

assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
(m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 ->
stk rsegs m4 lo (bv_unsigned sp + -96) -> rw_cells rsegs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0xce1a8) fc None m4 (seg_rom rsegs) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
{ intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
eapply rimplT_evt.
{ eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
intros ms5 FGP.
eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
- intros a Ha. eapply (rfree_fp_same st stX); eauto.
- apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
+
apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
set (sc := m_sizeclass (get_meta_rec st g)) in *.
set (an := optr_eqb (active st sc) (Some g)).
set (stm := deq_mid (LActive sc) g st).
set (st1 := dequeue (LActive sc) g st).
assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
assert (FR1' : ntf_frame st st1).
{ unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
destruct DS as (DSdata & GN1 & GP1 & _).

assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono rsegs m m2 ->
rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
(rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
rimplT o (match an, active st1 sc with
| true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
| _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
end) s Q ms2).
{ intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
{ destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }

assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
{ pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). unfold alloc_ceiling in B1.
rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
- destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). unfold alloc_ceiling in C1.
unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
- unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
evt rsegs (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0xce144) fc None m3 (seg_rom rsegs))).
{ intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
- eapply meta_slot_sbl; [exact SBLm| exact MSL].
- pose proof (go_sc _ _ _ GO). subst sc. lia.
- rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
assert (AVK : forall a, an = true -> active st1 sc = Some a ->
rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0xce144) fc None m3 (seg_rom rsegs))).
{ intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
set (stA := act_st st1 a (act_of st1 a)).
destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
rewrite (conc_sbl _ _ g SBLm).
eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
- unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
- unfold stA. apply ZINV_act. exact ZI1.
- unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
- unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
- unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
- unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
- unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
- unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
- unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
- unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
- eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
- eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
assert (NOACT : (an = false \/ active st1 sc = None) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0xce144) fc None m3 (seg_rom rsegs))).
{ intros NA.
eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
rewrite EP in MR4.
rewrite (conc_sbl _ _ g SBLm).
eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
- apply DSdata.
- apply (sbl_regions _ _ SBL1).
- apply (sbl_shadow _ _ SBL1).
- apply (sbl_groups _ _ SBL1).
- intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
- eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
- eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]];
try (exfalso; destruct D as (D1 & D2 & D3); congruence).
*
destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
assert (Enx : nx = g) by congruence.
eapply rimplT_evt.
{ eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- rewrite NX, Enx. reflexivity. }
intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
*
destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
assert (Enx : nx' = nx) by congruence. subst nx'.
eapply rimplT_evt.
{ eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- apply NEpv. exact NE.
- destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
+
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]];
try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
| | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
- destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
+
apply Z.eqb_eq in HM.
apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.

assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
(active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
rimplT o (k (aor_st stq g i) None) s Q ms2).
{ intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
assert (KIq : KINV stq LB c).
{ rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
- apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
- apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
- intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
assert (FRq : ntf_frame st stq).
{ rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
unfold rqpath_post in QP. cbv beta in QP.
destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
rewrite <- (conc_sbl st stq g SBL).
eapply rimplT_evt.
{ eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
- eapply meta_slot_sbl; [exact SBL| exact MSL].
- pose proof (go_li _ _ _ GO). lia.
- destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
intros ms3 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
* eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
* intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
* exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
* apply ZINV_aor. exact ZIq.
* apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
* exact eq_refl.
* apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
* exact MR2.
* reflexivity.
* reflexivity. }
destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
*
assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
{ destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia | exact HAct]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- right. exists g. split; [exact HAct| exact MSL].
- intros NE. exfalso. exact (NE HAct).
- intros hd Hhd NE. exfalso. apply NE. congruence. }
intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
*
assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
{ intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
apply rimplT_queue. intros GN GPV.
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
- intros _. split; assumption.
- intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
+
apply Z.eqb_neq in HM.
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_li _ _ _ GO). lia.
- exact (go_freed _ _ _ GO). }
intros ms2 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
* eapply rpres_except_entry; eauto.
* auto.
* exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
* apply ZINV_aor. exact ZI.
* apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
* exact eq_refl.
* eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
* exact MR1.
* reflexivity.
* reflexivity.
Qed.
End NTF.

End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QeTw Q1BE QvBB.Mq2.
Export Qi8L.Mq7.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
end.

Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - 128) (q)
/\ rw_cells usegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
/\ bytes_at usegs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
rw_cells usegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk usegs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 128 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 128)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv usegs m ->
evt usegs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 UFLOW) fc None m (seg_rom usegs)).

Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - 160) q
/\ rw_cells usegs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
/\ bytes_at usegs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
rw_cells usegs m Fp (rf_cells T p w f ssJ) ->
sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
rtext T txt pre post -> p = zlength pre -> bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk usegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 160 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 160)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv usegs m ->
evt usegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHGETC) fc None m (seg_rom usegs)).

End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QJE4.Mq3.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QnOf QdZ1 Qv4L.Mqk QQbX Qn9M Qv4L Qi8L.Mq9 QdZ1.Mq7 QQbX.Mq6 Qv4L.Mqb QnkH QnkH.Mqm.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

#[using="Type"] Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk usegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono usegs m0 m ->
evt usegs (fun ms' => exists (a1' a2' : word) m',
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom usegs)
/\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp) /\ rmrep st' m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd18c4) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR' MI FR ST LO LOLE MU WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RSSP_GUARD, rta_frame in *.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WMs.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="MR MSL MASK CLO"] Lemma rfin_walk :
forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
bv_unsigned gw = G ->
rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk usegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a1' a2' a3' : word) m' k,
0 <= k < 32 /\ lowbit mask = 2 ^ k /\
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1204) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros HG FR ST LO MI.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
unfold meta_cells in CH. rewrite <- HG in CH.
destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
assert (P2 : 0 < 2 ^ k <= mask).
{ destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
unfold alloc_ceiling, rta_frame, RSSP_GUARD in *.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.

step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).

pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl usegs m) as WMg.
step.
lazymatch goal with H : rw_cells usegs ?mc (bv_unsigned gw) ?cs |- _ =>
apply (rw_cells_congr usegs mc (bv_unsigned gw) cs
(meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
[| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
| reflexivity | cbn; tauto ];
rewrite HG in H;
pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
end.

step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. step. step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.
step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.

step.
rewrite ?LB in MR1.
eapply evt_mono.
{ eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
[exact MR1 | assumption | exact FR | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM]. }
cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.

End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import QWTl.Mq5.
Import QeTw.
Import Q2qa.Mq1 QytA QlQE QFkE Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq2 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.

Import QJE4.Mq0 QJE4.Mq1 QDUx.Mq3 QWTl.Mq1 QWTl.Mq2 QWTl.Mq3 QDUx.Mq2 Q9Ay.Mq9 QXxF QBeb Q6y7.Mq1.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq QkLq.Mq3 QnOf Qv4L.Mqk QdZ1.Mq7.
Import QQbX.Mq5 QdZ1.Mq5 QnkH.Mqg Qv4L.Mqc Qv4L.Mqd Qv4L.Mqe QnkH.Mqe QnkH.Mqf Qi8L.Mq8 Qi8L.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := QWTl.Mq5.
Module RA2 := Qv4L.Mqk.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
#[using="Type"] Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.

#[using="Type"] Lemma rrw_cells_magree C m m' A cs :
rw_cells usegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells usegs m' A cs.
Proof.
intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply RA2.rrw_cells_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
#[using="Type"] Lemma rbytes_at_magree C m m' A bs :
bytes_at usegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at usegs m' A bs.
Proof.
intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply RA2.rbytes_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
#[using="Type"] Lemma rwr_at_magree C m m' A n :
wr_at usegs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at usegs m' A n.
Proof. intros H AG HC H0 H1. eapply RA2.rwr_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha]. Qed.

#[using="Type"] Lemma rauxv_ok_magree C m m' B :
rauxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8)) -> rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 0x625520.
Hypothesis KH : forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms'.

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

#[using="Type"] Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. intros H. left. apply ram_fp_alloc_fp. exact H. Qed.

#[using="RC__ TP"] Lemma rETP : errno_addr tp = 0x625520 - 164.
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

#[using="TK KH"] Lemma rfinish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
am_rel st st1 mo -> rmrep st1 m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
rw_cells usegs m' (errno_addr tp) [C4 e] -> rauxv_ok m' (bv_unsigned sp) -> magree (rFP st1) m m' ->
brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rv = pw st1 mo -> (mo = None -> e = Z_to_bv 64 12) ->
rimplT o (k st1 mo) sX Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)).
Proof.
intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv REL MR1 MI1 ST1 ERR1 AUX1 AG BL1 P1 P2 P3 -> E12.
apply KH; [| exact BL1]. unfold ram_post. do 16 eexists. split; [reflexivity|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact AUX1|]. split.
{ apply rpres_of_magree. exact AG. }
split; [exact MR1|]. split.
{ destruct TK as [T1 T2]. split; intros; rewrite (amr_shadow _ _ _ REL) in *; rewrite (amr_tick _ _ _ REL); eauto. }
repeat (split; [auto|]). exact E12.
Qed.

#[using="Type"] Lemma rFP_mono stX stY a :
(forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rFP stX a -> rFP stY a.
Proof.
intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
{ unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
unfold lr_lo in *. rewrite K', B'. lia.
Qed.

#[using="Type"] Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof. intros E. apply rFP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

#[using="AMP LO LOLE"] Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8).
Proof.
intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold RAUXV_CELL, RLIBC, RCTX, RAM_STACK, alloc_ceiling in *;
rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
- destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
- pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold alloc_ceiling in C. lia.
Qed.

#[using="LO TP"] Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. intros WF X. rewrite TP. eapply ram_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

#[using="Type"] Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.

#[using="Type"] Lemma ram_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> QUZl.M RR) (bl : QUZl.M RR) :
am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
= kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
#[using="Type"] Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

#[using="AMP TK LO LOLE TP KH"] Lemma rcarve_K : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv usegs mX -> bytes_at usegs mX (conc stY p) (zeros 4096) -> wr_at usegs mX (conc stY p) 4096 ->
rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (k (am_took (carve_st stY p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR))) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c34) fc None mX (seg_rom usegs)).
Proof.
intros until t6. intros AI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX ZB ZW FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MRX as (WFX & _).
eapply rimplT_evt.
{ eapply (ram_carve_walk sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc mX junk lo stY p r);
first [exact MRX | exact MIX | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
| exact (ami_secretr _ _ AI) | exact ZB | exact ZW | exact FRX | exact STX | exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
pose proof (carve_st_regions stY p) as RC.
eapply rfinish_K.
- eapply (ram_rel_carve st stY p r AI); assumption.
- exact MR2.
- exact MI2.
- exact ST2.
- eapply rrw_cells_magree; [exact ERRX| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X.
apply (rerrno_not_amfp stY a WFX); [exact (proj1 (ram_fp_same stY _ lo _ a RC) X) | lia].
- eapply rauxv_ok_magree; [exact AUXX| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stY _ WFX). apply rFP_am. exact (proj1 (ram_fp_same stY _ lo _ a RC) X).
- assert (RA : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY) by (cbn; exact RC).
eapply magree_trans; [exact AGX| apply rmagree_of_pres; exact PE2| intros a X; exact (rFP_same stY _ a RA X) | intros a X; apply rFP_am; refine (proj2 (ram_fp_same (carve_st stY p) _ lo _ a _) X); reflexivity].
- unfold brk_link_ps in *. rewrite rbrk_am_took, rbrk_carve. destruct (c_brk (ctx stY)) as [| |rid off]; auto.
rewrite rconc_am_took, rconc_carve. exact BLX.
- exact P1.
- exact P2.
- exact P3.
- unfold pw, oconc, wz. rewrite rconc_am_took, rconc_carve. rewrite (conc_aadd stY p AREA_HDR) by (rewrite Hr; eauto). reflexivity.
- intros X; discriminate X.
Qed.

#[using="TP"] Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof.
intros WF H. rewrite rETP. pose proof WF as (_ & WR & _ & WA & WG). unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
Qed.

Lemma rfinish_path : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> c_avail_meta_areas (ctx stY) = Some p ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv usegs mX ->
rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_finish stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0cc4) fc None mX (seg_rom usegs)).
Proof using AMP KH LO LOLE TK TP.
intros until t6. intros AI AMA Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'.
pose proof MRX as (WFX & _ & (_ & _ & PGX & _) & _). pose proof WFX as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (conc_region' stY p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU. pose proof (lr_lo_ge r) as LRG.
assert (PAL : conc stY p mod 4096 = 0) by (rewrite Cp; unfold pgal in SAL; clear - RBAL SAL; Z.div_mod_to_equations; lia).
assert (IMG : conc stY p + 4096 <= 0x10000 \/ 0x647000 <= conc stY p) by (pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)); lia).
pose proof rETP as rETP'. pose proof TP as TPv. unfold wz in PGX.

unfold am_finish. rewrite AMA. unfold pgal in SAL. unfold PGSZ at 1. rewrite (proj2 (Z.eqb_eq _ _) SAL). cbn [negb].

eapply rimplT_evt.
{ apply (ram_to_mprotect (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX (conc stY p)). }
intros ms2 ->.
eapply (rimplT_mprotect o (conc stY p) PGSZ PROT_RW _ sX).
{ eapply rimpl_enode_dec_weaken; [| intros rsp a Hd; exact (dec_mprotect_rw_weaken _ _ rsp a Hd)].
unfold PGSZ, PROT_RW.
eapply rmprotect_spec with (lo := lo) (errv := e);
[ rewrite unsigned_lit by lia; exact STX | exact ERRX | exact PGX | exact MIX | reflexivity | reflexivity | reflexivity
| exact PAL | reflexivity | lia | lia | lia | lia | ..]; rewrite ?rETP', ?TPv, ?unsigned_lit by lia; unfold RPAGE_SIZE; try lia. }
intros ans ms3 [MP G]. unfold rmprotect_post in MP.
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & PG3 & CASE).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0xd0cd4)) with (Z_to_bv 64 0xd0cd4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [exact FRX| exact MU3| exact WM3|]. rewrite rETP'. cbn. unfold alloc_ceiling in LO. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [exact MRX| exact MU3| exact WM3|].
intros lo' hi' y [E|[E|[E|[]]]] Hy; inversion E; subst lo' hi'.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). unfold alloc_ceiling in *. lia.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). lia.
- eapply (rfresh_page_avoids stY mX p r y MRX); try assumption; lia. }
assert (M23 : magree (rFP stY) mX m3).
{ eapply magree_of_munch; [exact MU3|].
cbn. split; [| split; [| split; [| exact I]]]; intros x Hx.
- left. left. lia.
- left. right. left. rewrite TPv in Hx. exact Hx.
- left. right. right. right. exists (fst p), r. split; [exact Hr|]. split; [exact NK|]. lia. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AGX| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUXX| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clear MU3 WM3.
destruct ans as [e'|b]; cbn in G.
-
cbn [range_val Q9A7.Mq0.munmap_ret Q9A7.Mq0.rg_errno] in *.
unfold mprotect_answer_ok, is_errno_form, neg_errno, TWO64, ENOSYS.
replace ((2 ^ 64 - e' =? 0) || ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64))) with true by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
replace ((2 ^ 64 - e' =? 0) || (2 ^ 64 - e' =? 2 ^ 64 - 38)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
cbn [negb].
eapply rimplT_evt.
{ eapply (ram_mp_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo e' stY);
first [exact MR3 | exact MI3 | exact TPv | exact ERR3 | exact G | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
intros ms4 [RP ERR4]. unfold ram_ret_post in RP. cbn [ms_mem] in ERR4.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & EQ & PE4 & WM4 & MI4 & ST4 & MR4).
rewrite EQ in ERR4 |- *. cbn [ms_mem] in ERR4.
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ exact MR4.
+ exact MI4.
+ exact ST4.
+ exact ERR4.
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
+ exact BLX.
+ exact P1.
+ exact P2.
+ exact P3.
+ reflexivity.
+ intros _. cbn in CASE. rewrite CASE. reflexivity.
-
subst b. cbn [range_val] in *.
unfold mprotect_answer_ok. cbn [Z.eqb orb negb].
rewrite (am_carve_eq stY p k bail), (ram_take_took (carve_st stY p) p k bail).
destruct CASE as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
eapply rimplT_evt.
{ apply (ram_mp_ok0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 (Z_to_bv 64 0xd0cd4) F fc m3). }
intros ms4 ->.
eapply (rcarve_K stY p r m3 sX junk); first [exact AI | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
| exact MR3 | exact MI3 | exact ZB | exact ZW | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | exact BLX | exact P1 | exact P2 | exact P3 | idtac].
unfold pgal. exact SAL.
Qed.

#[using="Type"] Lemma rlive_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

#[using="Type"] Lemma rfresh_of_ranges_free stY x L a :
s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof.
intros E1 E2 RF XC Ha. split; [lia|]. rewrite (rlive_ranges_same st stY E1 E2) in RF.
eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.

#[using="Type"] Lemma rrepfoot_clear stY mY x L a :
rmrep stY mY -> ranges_free (live_ranges stY) x L = true -> rrepfoot stY a \/ rgrp_region_addr stY a -> ~ (x <= a < x + L).
Proof.
intros MRY RF H. pose proof MRY as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (clear_range_of_ranges_free stY x L RF) as CR.
assert (IMG : forall y, 0x10000 <= y < 0x647000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y RS RF Hy)).
destruct H as [[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (rra & Hra & _).
eapply (CR (fst ak) rra a Hra). eapply rarea_in_live; eauto.
- destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (rb & Hrb & _).
eapply (CR (fst b) rb a Hrb). eapply rgroup_in_live; eauto.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
- apply IMG. lia.
- apply IMG. lia.
- destruct C as (rid & rg & Hrg & Krg & Hin). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed.

#[using="AMP TK LO LOLE TP KH"] Lemma rmmap_path : forall (stY : mstate) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> s_regions stY = s_regions st -> c_avail_meta_area_count (ctx stY) = 0 ->
0 <= c_meta_alloc_shift (ctx stY) <= 38 ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
(forall q mr, (s_metas stY) !! q = Some mr -> meta_slot stY q) ->
ptrs_in (fun rid => (rid < s_next_rid stY)%N) stY ->
rmrep stY mX -> mem_inv usegs mX ->
rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_after_brk stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0bd4) fc None mX (seg_rom usegs)).
Proof.
intros until t6. intros AI RGY ACNT SHR TL MK PTR MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MRX as (WFX & _). pose proof WFX as (RS & WR & DJ & WA & WG).
set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx stY))).
assert (NR : 2 <= n <= 2^39).
{ unfold n. rewrite Z.shiftl_mul_pow2 by lia. split.
- rewrite <- (Z.mul_1_r 2) at 1. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r with (b := 0); lia || (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
- change (2^39) with (2 * 2^38). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
unfold am_after_brk. rewrite ACNT. cbn [Z.eqb]. fold n.

eapply rimplT_evt.
{ apply (ram_to_mmap (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX stY MRX ltac:(lia)). }
intros ms2 ->. fold n.
pose proof MRX as MR2. pose proof MIX as MI2. pose proof FRX as FR2. pose proof STX as ST2. pose proof ERRX as ERR2. pose proof AGX as AG2. pose proof AUXX as AUX2.
set (m2 := mX) in MR2, MI2, FR2, ST2, ERR2, AG2, AUX2 |- *.
clear MRX MIX FRX STX ERRX AUXX AGX.
eapply (rimplT_mmap_none o (n * PGSZ) _ sX).
{ unfold PGSZ. replace (Z_to_bv 64 (n * 4096)) with (Z_to_bv 64 (n * 4096)%Z) by reflexivity.
eapply (rmmap_anon_spec true) with (lo := lo) (errv := e) (avoid := []);
[ rewrite unsigned_lit by lia; exact ST2 | exact ERR2 | exact MI2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?rETP', ?TPv, ?unsigned_lit by lia; try lia. all: first [rewrite Q9A7.Mq0.alloc_ceiling_val; lia | unfold alloc_ceiling in *; lia]. }
intros ans ms3 MP. unfold rmmap_anon_post in MP.
destruct ans as [e'|x].
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & ER).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0xd0c00)) with (Z_to_bv 64 0xd0c00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
cbn [mmap_val]. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64.
replace ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [orb negb]. replace (2 ^ 64 - 4096 <? 2 ^ 64 - e') with true by (symmetry; apply Z.ltb_lt; lia).
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. rewrite rETP'. cbn. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
intros lo' hi' y [E|[E|[]]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
assert (M23 : magree (rFP stY) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| split; [| exact I]]; intros y Hy; [left; left; lia|]. left. right. left. rewrite TPv in Hy. exact Hy. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
eapply rimplT_evt.
{ eapply (ram_mm_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 n) u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo stY);
first [exact MR3 | exact MI3 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
intros ms4 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & -> & PE4 & WM4 & MI4 & ST4 & MR4).
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ exact MR4.
+ exact MI4.
+ exact ST4.
+ eapply rrw_cells_magree; [exact ERR3| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp stY a WFX); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
+ exact BLX.
+ exact P1.
+ exact P2.
+ exact P3.
+ reflexivity.
+ intros _. rewrite ER. reflexivity.
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2' & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & AOK).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0xd0c00)) with (Z_to_bv 64 0xd0c00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
cbn [mmap_val].
destruct (mmap_answer_ok (live_ranges stY) (n * PGSZ) x) eqn:VOK; cbn [negb]; [| apply rimplT_undef].

unfold mmap_addr_ok in AOK. apply andb_prop in AOK. destruct AOK as [AOK _]. apply andb_prop in AOK. destruct AOK as [AOK XC].
apply andb_prop in AOK. destruct AOK as [XA X0]. apply Z.eqb_eq in XA. apply Z.ltb_lt in X0. apply Z.leb_le in XC.
rewrite A2.mmap_len_round_up in XC. first [rewrite Q9A7.Mq0.alloc_ceiling_val in XC | unfold alloc_ceiling in XC]. change page_size with 4096 in XA.
assert (LAL : round_up_pg (n * PGSZ) = n * PGSZ) by (apply round_up_pg_aligned; unfold PGSZ; apply Z.mod_mul; lia).
rewrite LAL in XC.
unfold mmap_answer_ok in VOK. rewrite LAL in VOK. apply orb_prop in VOK.
assert (RF : ranges_free (live_ranges stY) x (n * PGSZ) = true).
{ destruct VOK as [V|V]; [| apply andb_prop in V; destruct V as [_ V]; exact V].
unfold is_errno_form, TWO64 in V. apply andb_prop in V. destruct V as [V _]. apply Z.leb_le in V. unfold PGSZ in XC. exfalso. lia. }
unfold is_err, TWO64. replace (2 ^ 64 - 4096 <? x) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ in XC; lia).
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stY).
pose proof (rAMI_new_region st stY RKMeta x (n * PGSZ) AI ltac:(discriminate) ltac:(unfold PGSZ; lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
set (st2 := upd_ctx _ st1).
assert (E2 : st2 = mm_ok_st st1 rid n) by reflexivity.

unfold Q9A7.Mq0.mmap_raw in ST3 |- *. rewrite A2.mmap_len_round_up, LAL in ST3 |- *.
set (m3 := apply_unmaps m2' [(wa x, Z_to_bv 64 (n * PGSZ))]) in *.
assert (Hx1 : 0 <= x < 2^64) by (unfold PGSZ in XC; lia). assert (Hn1 : 0 <= n * PGSZ < 2^64) by (unfold PGSZ in *; lia). assert (Hxn : x + n * PGSZ <= 2^64) by (unfold PGSZ in *; lia).
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ apply (rw_cells_unmaps_other usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. lia.
- cbn. unfold PGSZ in *. lia. }
assert (ERR4 : rw_cells usegs m3 (errno_addr tp) [C4 e]).
{ apply (rw_cells_unmaps_other usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); [exact ERR3|]. cbn. rewrite rETP'.
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x625520 - 164) RS RF ltac:(lia)).
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x625520 - 161) RS RF ltac:(lia)). unfold PGSZ in *. lia. }
assert (MI4 : mem_inv usegs m3) by (apply (mem_inv_unmaps usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); exact MI3).
assert (MR2' : rmrep stY m2').
{ eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_agree'; [exact MR2'|]. intros y Hy HF. unfold m3. apply (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
rewrite wa_unsigned by lia. pose proof (rrepfoot_clear stY m2' x (n * PGSZ) y MR2' RF HF). lia. }
assert (MRn : rmrep st1 m3).
{ unfold st1. apply (RA2.rmrep_new_region stY m3 m3 x (n * PGSZ) RKMeta);
first [ exact MR3
| eapply ptrs_in_mono; [| exact PTR]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| apply (ami_fresh _ _ AI); unfold rid; lia
| unfold alloc_ceiling; rewrite LAL; exact XC
| rewrite LAL; exact RF
| intros; reflexivity
| intros; discriminate
| unfold PGSZ in *; lia ]. }
assert (M23 : magree (rFP stY) m2 m3).
{ intros y Hy Hc. unfold m3. rewrite (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact I]. intros X. apply Hc. left. left. lia.
- rewrite wa_unsigned by lia. destruct (Z.lt_ge_cases y x); [lia|]. destruct (Z.lt_ge_cases y (x + n * PGSZ)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stY x (n * PGSZ)); [exact RGY| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; exact XC| lia]. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clearbody m3. clear MU3 WM3 MR2 MR2' MI3 ERR3.

eapply rimplT_evt.
{ eapply (ram_mm_ok sp gp tp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo x n st1 st1 rid (mkRegion RKMeta x (n * PGSZ)));
first [exact MRn | exact MI4 | intros a X; exact X | exact RG1 | reflexivity | exact XA | exact X0 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | idtac];
try (unfold alloc_ceiling, PGSZ in *; lia).
change (ctx st1) with (ctx stY). lia. }
intros ms4 (m4 & -> & PE4 & WM4 & MI5 & FR4 & ST4 & MR4).
pose proof MRn as (WFn & _).
assert (RG2 : forall q, (s_regions st2) !! q = if decide (q = rid) then Some (mkRegion RKMeta x (n * PGSZ)) else (s_regions stY) !! q).
{ intros q. change (s_regions st2) with (<[rid := mkRegion RKMeta x (n * PGSZ)]> (s_regions stY)).
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
replace (Z_to_bv 64 (x + 4096)) with (Z_to_bv 64 (conc st2 (rid, 4096))) by (change (conc st2 (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rfinish_path st2 (rid, 4096) (mkRegion RKMeta x (n * PGSZ)) m4 sX junk e).
+ unfold st2. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* right. exists (rid, PGSZ), (mkRegion RKMeta x (n * PGSZ)). cbn [fst]. split; [reflexivity|]. split; [exact RG1| cbn; discriminate].
* left. reflexivity.
+ reflexivity.
+ cbn [fst]. rewrite RG2. destruct (decide (rid = rid)); [reflexivity| congruence].
+ cbn. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite LAL. unfold PGSZ. lia.
+ unfold pgal. reflexivity.
+ cbn. lia.
+ change (s_areas st2) with (s_areas stY). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas st2) with (s_metas stY). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MK _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas st2) with (s_areas stY). apply TL. exact Htl.
+ cbn. lia.
+ exact MR4.
+ exact MI5.
+ exact FR4.
+ exact ST4.
+ eapply rrw_cells_magree; [exact ERR4| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp st1 a WFn); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below st1 a WFn (rFP_am st1 a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| |].
* intros a X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq. rewrite RG2.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate|]. repeat split; auto; lia.
* intros a X. eapply rFP_same; [| exact (rFP_am st1 a X)]. reflexivity.
+ unfold brk_link_ps in *. change (c_brk (ctx st2)) with (c_brk (ctx stY)).
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _).
destruct (c_brk (ctx stY)) as [| |rb ob]; auto. change (conc st2 (rb, ob)) with (conc st1 (rb, ob)). rewrite CQ1; [exact BLX|]. cbn [fst]. unfold rid. lia.
+ exact P1.
+ exact P2.
+ exact P3.
Qed.

#[using="RC__"] Lemma rimage_range_clear stY x L : s_reserved stY = ref_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
x + L <= 0x10000 \/ 0x647000 <= x.
Proof.
intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv usegs m1 ->
rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (let old := conc stI (brid, boff) in
let new := old + PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok old new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI old PGSZ) then bad_answer bail
else
let st1 := upd_region brid (fun rg => mkRegion (r_kind rg) (r_base rg) (boff + PGSZ)) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (brid, boff)) (set_brk (BrkLive brid (boff + PGSZ)) c))) st1 in
am_after_brk st2 false k bail)) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b24) fc None m1 (seg_rom usegs)).
Proof.
intros until t6. intros AMPI AI RGI BLI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6 & HX7) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
pose proof (amp_brk stI AMPI) as HB. rewrite BRK in HB. destruct HB as (r & Hr & Kr & Lr & OAL & O4 & FRA & UNQ).
pose proof (conc_region' stI (brid, boff) r Hr) as OLD. cbn [snd] in OLD.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr). unfold alloc_ceiling in RBC. rewrite Lr in RBC.
assert (RUB : round_up_pg boff = boff) by (apply round_up_pg_aligned; unfold PGSZ in OAL; exact OAL). rewrite RUB in RBC.
set (old := conc stI (brid, boff)) in *.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold brk_link_ps in BLI. rewrite BRK in BLI. fold old in BLI.
cbv zeta.

eapply rimplT_evt.
{ eapply (ram_disp_live _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI brid boff); [exact MR1| exact ACNT| exact BRK| fold old; lia| fold old; unfold PGSZ; lia]. }
intros ms2 ->. fold old.
eapply (rimplT_brk o (old + PGSZ) _ s).
{ unfold PGSZ; lia. }
{ rewrite BLI. unfold PGSZ.
exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 0xd0b48 (or_introl eq_refl) old (old + 4096) ltac:(lia)). }
intros a ms3 ->. rewrite BLI. unfold brk_res, brk_mem, rbrk_regs.
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI old PGSZ) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
unfold alloc_ceiling, PGSZ in OC. unfold PGSZ in RF.
assert (OALD : old mod 4096 = 0) by (rewrite OLD; rewrite Z.add_mod, RBAL by lia; unfold PGSZ in OAL; rewrite OAL; reflexivity).
rewrite (brk_new_pages_aligned old 4096) by (first [lia | exact OALD | reflexivity]).
rewrite (rgr_eq stI brid r boff Hr).
set (stG := set_regions _ stI).
unfold PGSZ. rewrite (am_after_brk_false_eq stG _ (brid, boff) k bail) by (cbn; first [lia | reflexivity | unfold PGSZ in OAL; exact OAL]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ stG).

assert (Ho1 : 0 <= old < 2^64) by lia. assert (Hn1 : 0 <= 4096 < 2^64) by lia. assert (Hon : old + 4096 <= 2^64) by lia.
pose proof (rimage_range_clear stI old 4096 RS RF ltac:(lia)) as IMG.
set (m2 := apply_zeros m1 [(wa old, Z_to_bv 64 4096)]).
unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6. fold old in HX6.
assert (HC2 : rw_cells usegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact HX1| cbn; unfold RCTX; lia]).
assert (TC2 : rw_cells usegs m2 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (wz old)])
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact HX6| cbn; unfold RCTX; lia]).
assert (MI2 : mem_inv usegs m2).
{ apply (mem_inv_zeros usegs m1 old 4096 Ho1 Hn1 Hon MI1). intros y Hy. apply ref_ro_addr_false. lia. }
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra))
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact FR1| cbn; lia]).
assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)) by (apply (stk_zeros usegs m1 old 4096 Ho1 Hn1 Hon); exact ST1).
assert (ERR2 : rw_cells usegs m2 (errno_addr tp) [C4 e1])
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact ERR1| cbn; rewrite rETP'; lia]).
pose proof (rw_cells_zeros_new usegs m1 old 4096 Ho1 Hn1 Hon) as ZN. fold m2 in ZN.
assert (MU12 : munch [(old, old + 4096)]%Z m1 m2) by (apply (munch_zeros m1 old 4096 Ho1 Hn1 Hon); [apply munch_refl| cbn; lia]).
assert (WM12 : wmono usegs m1 m2) by (apply (wmono_zeros usegs m1 old 4096 Ho1 Hn1 Hon); apply wmono_refl).
assert (MR2 : rmrep stI m2).
{ eapply rmrep_transport_unowned; [exact MR1| exact MU12| exact WM12|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'. intros RFt. apply (rrepfoot_clear stI m1 old 4096 y MR1 RF (or_introl RFt)). lia. }
assert (M12 : magree (rFP stI) m1 m2).
{ intros y Hy Hc. unfold m2. apply (zeros_outside m1 old 4096 Ho1 Hn1 Hon). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y old); [lia|]. destruct (Z.lt_ge_cases y (old + 4096)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI old 4096); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| lia]. }
clearbody m2.

eapply rimplT_evt.
{ eapply (ram_bl_ok _ gp tp t0 t1 t2 (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 _ s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (old + 4096)); [lia | | | exact MI2].
- unfold pw in HC2. cbn [oconc] in HC2. exact HC2.
- unfold wz in TC2. exact TC2. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & HC3 & TC3). replace (old + 4096 - 4096) with old by lia.

pose proof (rAMI_grow st stI brid r boff AI Hr ltac:(rewrite Kr; discriminate) Lr) as (AIG & CQG & RG'). fold stG in AIG, CQG, RG'.
assert (MRG : rmrep stG m2).
{ unfold stG. apply (rmrep_grow_region stI m2 brid r boff MR2 Hr);
first [ rewrite Kr; discriminate
| exact Lr
| unfold PGSZ in OAL; exact OAL
| rewrite <- OLD; exact RF
| exact (amp_rpos stI AMPI)
| intros q rq Hq NE KB; apply NE; exact (UNQ q rq Hq KB)
| unfold alloc_ceiling, PGSZ in *; lia ]. }
assert (PWX : forall q, pw stX q = pw stI q) by (intros [q|]; unfold pw, oconc; [change (conc stX q) with (conc stG q); rewrite CQG|]; reflexivity).
assert (PWG : forall q, pw stG q = pw stI q) by (intros [q|]; unfold pw, oconc; [rewrite CQG|]; reflexivity).
assert (CQX : forall q, conc stX q = conc stI q) by (intros q; change (conc stX q) with (conc stG q); apply CQG).
assert (MRX : rmrep stX m3).
{ eapply (rmrep_ctx_frameW stG stX m2 m3 _ MRG MU3 WM3); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells. rewrite !PWX.
cbn [ctx stX stG upd_ctx s_ctx set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold wz at 5. exact HC3.
- right. split; [| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
unfold actives. apply map_ext. intros i. rewrite PWX, PWG. reflexivity.
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- left. unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (brid, boff + 4096)) with (conc stG (brid, boff + 4096)).
rewrite CQG. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold wz.
replace (r_base r + (boff + 4096)) with (old + 4096) by lia. change (s_ctx stI) with (ctx stI). exact TC3. }

assert (M23 : magree (rFP stX) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. unfold RCTX. split; [| split; [| exact I]]; intros y Hy; left; right; right; left; unfold RCTX; lia. }
assert (ZN3 : rw_cells usegs m3 old [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]).
{ eapply rw_cells_transport; [exact ZN| exact MU3| exact WM3|]. cbn. unfold RCTX. lia. }
destruct ZN3 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (AGX1 : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. destruct (ami_regions _ _ AI q rq) as (r0 & H0 & _); [rewrite <- RGI; exact Hq|].
destruct (decide (q = brid)) as [->|NE].
- eexists. split; [exact RG'|]. rewrite Hr in Hq. inversion Hq; subst. cbn. repeat split; lia.
- exists rq. change (s_regions stX) with (<[brid := mkRegion (r_kind r) (r_base r) (boff + 4096)]> (s_regions stI)). rewrite lookup_insert_ne by congruence. repeat split; auto; lia. }
assert (AG3 : magree (rFP stX) m m3).
{ eapply magree_trans; [| exact M23| exact AGX1| intros y X; exact X]. eapply magree_trans; [exact AG1| exact M12| intros y X; exact X| intros y X; exact X]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_magree; [exact AUX1| |intros y X; exact (rFP_below stX y (proj1 MRX) X)].
eapply magree_trans; [exact M12| exact M23| exact AGX1| intros y X; exact X]. }
replace (Z_to_bv 64 old) with (Z_to_bv 64 (conc stX (brid, boff))) by (change (conc stX (brid, boff)) with (conc stG (brid, boff)); rewrite CQG; reflexivity).
eapply (rcarve_K stX (brid, boff) (mkRegion (r_kind r) (r_base r) (boff + 4096)) m3 _ junk e1);
first [exact RG' | exact MRX | exact MI3 | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | reflexivity | idtac].
+ unfold stX. apply (rAMI_ctx st stG _ AIG).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AIG).
* left. reflexivity.
* right. right. exists brid, (boff + 4096), (mkRegion (r_kind r) (r_base r) (boff + 4096)). split; [reflexivity|]. split; [exact RG'|]. cbn. rewrite Kr. discriminate.
+ cbn. rewrite Kr. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite round_up_pg_aligned; [lia|]. rewrite Z.add_mod, OAL by lia. reflexivity.
+ unfold pgal. unfold PGSZ in OAL. exact OAL.
+ cbn [snd r_base]. unfold lr_lo. cbn [r_kind r_base]. rewrite Kr. unfold PGSZ in O4. lia.
+ change (s_areas stX) with (s_areas stI). apply (proj1 (FRA (brid, boff) eq_refl ltac:(cbn; lia))).
+ intros j Hj. change (s_metas stX) with (s_metas stI). apply (proj2 (FRA (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
+ cbn. lia.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZB.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZW.
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
rewrite CQX. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold PGSZ. lia.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (old =? old + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [orb negb].
eapply rimplT_evt.
{ unfold PGSZ. eapply (ram_bl_fail _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI old); [exact MR1| exact ACNT| lia| lia| exact MI1]. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M13 : magree (rFP stI) m1 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 s junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ exact RGI.
+ exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ exact TLI.
+ exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply rw_cells_transport; [exact ERR1| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
+ eapply rauxv_ok_magree; [exact AUX1| exact M13| intros y X; exact (rFP_below stI y WF1 X)].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1 M13); intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.

Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv usegs m1 ->
rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
ps_m s = ps_m s ->
rimplT o (SVis (EBrk 0) (fun cur =>
if negb (brk0_answer_ok cur) then bad_answer bail else
let base := round_up_pg cur in
let new := base + 2 * PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok cur new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI base (2 * PGSZ)) then bad_answer bail
else
SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
let '(st1, rid) := new_region RKBrk base (2 * PGSZ) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
(set_avail_meta_areas (Some (rid, PGSZ))
(set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
am_after_brk st2 false k bail)))) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b24) fc None m1 (seg_rom usegs)).
Proof using AMP ERR KH LO LOLE TK TP.
intros until t6. intros AMPI AI RGI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1 _.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6 & HX7) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6.

eapply rimplT_evt.
{ eapply (ram_disp_untried _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
intros ms2 ->.
eapply (rimplT_brk0 o _ s).
{ exact (ram_brk0_node x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1). }
intros cur ms3 [-> CR]. unfold rbrk_regs.
destruct (brk0_answer_ok cur) eqn:B0; cbn [negb]; [| apply rimplT_undef].
unfold brk0_answer_ok, TWO64, PGSZ in B0. apply andb_prop in B0. destruct B0 as [B0 _]. apply andb_prop in B0. destruct B0 as [C0 CAL].
apply Z.ltb_lt in C0. apply Z.eqb_eq in CAL.
rewrite (round_up_pg_aligned cur CAL). cbv zeta. unfold PGSZ.
replace (2 * 4096) with 8192 by reflexivity.

eapply rimplT_evt.
{ eapply (ram_bu_mid _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m1 cur); [lia| exact CAL| unfold wz in HX6; exact HX6| exact MI1]. }
intros ms4 (a2' & m2 & -> & MU2 & WM2 & MI2 & TC2).
eapply (rimplT_brk o (cur + 8192) _ (set_brk_ps cur s)).
{ lia. }
{ exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 0xd0b84 (or_intror eq_refl) cur (cur + 8192) ltac:(lia)). }
intros a ms5 ->. cbn [ps_brk set_brk_ps]. unfold brk_res, brk_mem, rbrk_regs.

assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (ERR2 : rw_cells usegs m2 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (HC2 : rw_cells usegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (eapply rw_cells_transport; [exact HX1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (M12 : magree (rFP stI) m1 m2).
{ eapply magree_of_munch; [exact MU2|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI cur 8192) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
unfold alloc_ceiling in OC.
rewrite (brk_new_pages_aligned cur 8192) by (first [lia | exact CAL | reflexivity]).
pose proof (rimage_range_clear stI cur 8192 RS RF ltac:(lia)) as IMG.
assert (Hc1 : 0 <= cur < 2^64) by lia. assert (Hn1 : 0 <= 8192 < 2^64) by lia. assert (Hcn : cur + 8192 <= 2^64) by lia.
set (m3 := apply_zeros m2 [(wa cur, Z_to_bv 64 8192)]).
assert (HC3 : rw_cells usegs m3 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact HC2| cbn; unfold RCTX; lia]).
assert (TC3 : rw_cells usegs m3 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)])
by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [unfold RCTX in TC2 |- *; exact TC2| cbn; unfold RCTX; lia]).
assert (MI3 : mem_inv usegs m3) by (apply (mem_inv_zeros usegs m2 cur 8192 Hc1 Hn1 Hcn MI2); intros y Hy; apply ref_ro_addr_false; lia).
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact FR2| cbn; lia]).
assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)) by (apply (stk_zeros usegs m2 cur 8192 Hc1 Hn1 Hcn); exact ST2).
assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 e1]) by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact ERR2| cbn; rewrite rETP'; lia]).
assert (VML4 : rw_cells usegs m3 RVMLOCK [C4 (Z_to_bv 64 0)]).
{ pose proof MR1 as (_ & _ & (_ & _ & _ & _ & _ & VML1) & _).
apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [eapply rw_cells_transport; [exact VML1| exact MU2| exact WM2|]; cbn; unfold RCTX, RVMLOCK; lia| cbn; unfold RVMLOCK; lia]. }
pose proof (rw_cells_zeros_new usegs m2 cur 8192 Hc1 Hn1 Hcn) as ZN. fold m3 in ZN.
assert (M23 : magree (rFP stI) m2 m3).
{ intros y Hy Hc. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y cur); [lia|]. destruct (Z.lt_ge_cases y (cur + 8192)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| lia]. }

assert (E23 : forall y, 0 <= y < 2^64 -> ~ (cur <= y < cur + 8192) -> m3 (wa y) = m2 (wa y)).
{ intros y Hy Hn. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia. lia. }
clearbody m3.

eapply rimplT_evt.
{ eapply (ram_bu_ok _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m3 cur);
first [exact TC3 | lia]. }
intros ms6 ->.
pose proof MI3 as MI4. pose proof FR3 as FR4. pose proof ST3 as ST4. pose proof TC3 as TC4. pose proof HC3 as HC4. pose proof ERR3 as ERR4.
eapply (rimplT_mmap_fixed o cur PGSZ _ (set_brk_ps (cur + 8192) (set_brk_ps cur s))).
{ unfold PGSZ. eapply (rmmap_fixed_spec (dec_mmap_fixed cur 4096) (fx_rel cur)) with (lo := lo) (errv := e1);
[ intros rsp fa Hd; exact (dec_mmap_fixed_shape cur 4096 rsp fa Hd)
| rewrite unsigned_lit by lia; exact ST4 | exact ERR4 | exact MI4 | exact VML4 | unfold RVMLOCK; lia
| unfold RVMLOCK; rewrite ?A2.mmap_len_round_up by lia; try (change (round_up_pg 4096) with 4096); lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?A2.mmap_len_round_up, ?rETP', ?TPv, ?unsigned_lit by lia; try (change (round_up_pg 4096) with 4096); try lia. }
intros fa ms7 MP. unfold rmmap_fixed_post in MP.
destruct MP as (rr & u & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5 & REL & -> & MU5 & WM5 & MI5 & ST5 & ERR5).
rewrite A2.mmap_len_round_up in MU5. change (round_up_pg 4096) with 4096 in MU5. rewrite unsigned_lit in MU5, ST5 by lia.
replace (ret_pc (Z_to_bv 64 0xd0ba8)) with (Z_to_bv 64 0xd0ba8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

replace (mmap_fixed_answer_ok cur (fixed_val cur fa)) with true.
2:{ symmetry. unfold mmap_fixed_answer_ok, is_errno_form, fixed_val, neg_errno, TWO64.
destruct fa as [e|  |e]; cbn in REL.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply Z.eqb_refl.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
cbn [negb].
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stI).
pose proof (rAMI_new_region st stI RKBrk cur 8192 AI ltac:(discriminate) ltac:(lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
rewrite (am_after_brk_false_eq st1 _ (rid, 4096) k bail) by (cbn; first [lia | reflexivity]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ st1).

assert (E45 : forall y, 0 <= y < 2^64 -> ~ (bv_unsigned sp - 64 - 112 <= y < bv_unsigned sp - 64) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 4096) -> m5 (wa y) = m3 (wa y)).
{ intros y Hy N1 N2 N3. apply MU5. rewrite wa_unsigned by lia. cbn. rewrite ?rETP' in *. repeat split; lia. }
assert (HC5 : rw_cells usegs m5 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end)).
{ eapply RA2.rrw_cells_agree; [exact HC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
assert (TC5 : rw_cells usegs m5 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
{ eapply RA2.rrw_cells_agree; [exact TC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply RA2.rrw_cells_agree; [exact FR4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
eapply rimplT_evt.
{ eapply (ram_b_store _ gp tp u0 u1 u2 _ u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (cur + 8192));
first [exact HC5 | exact TC5 | exact MI5 | lia]. }
intros ms8 (m6 & -> & MU6 & WM6 & MI6 & HC6 & TC6). replace (cur + 8192 - 4096) with (cur + 4096) by lia.
assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].

assert (E16 : forall y, 0 <= y < 2^64 ->
~ (RCTX + 40 <= y < RCTX + 48) -> ~ (RCTX + 920 <= y < RCTX + 928) -> ~ (lo <= y < bv_unsigned sp) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 8192) ->
m6 (wa y) = m1 (wa y)).
{ intros y Hy N0 N1 N2 N3 N4.
rewrite (MU6 (wa y)) by (rewrite wa_unsigned by lia; cbn; unfold RCTX in *; lia).
rewrite (E45 y Hy) by (rewrite ?rETP' in *; lia).
rewrite (E23 y Hy) by lia.
apply MU2. rewrite wa_unsigned by lia. cbn. unfold RCTX in *. lia. }
assert (MRn1 : rmrep st1 m1).
{ unfold st1. apply (RA2.rmrep_new_region stI m1 m1 cur 8192 RKBrk);
first [ exact MR1
| eapply ptrs_in_mono; [| exact PTRI]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| exact FRr | exact FRs
| unfold alloc_ceiling; change (round_up_pg 8192) with 8192; lia
| change (round_up_pg 8192) with 8192; exact RF
| intros; reflexivity
| intros; discriminate
| lia ]. }
assert (CQX : forall q, fst q <> rid -> conc stX q = conc stI q) by (intros q Hq; change (conc stX q) with (conc st1 q); apply CQ1; exact Hq).
pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
assert (PWX : forall q, optr_in (fun r => (r < s_next_rid stI)%N) q -> pw stX q = pw stI q).
{ intros [q|] Hq; unfold pw, oconc; [rewrite CQX; [reflexivity|]|reflexivity]. cbn in Hq. unfold rid. lia. }
assert (MRX : rmrep stX m6).
{ apply (rmrep_agree_but_ctx st1 stX m1 m6 MRn1); try reflexivity.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RMLOCK, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RLIBC, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RGOT_SSP, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RSSP_GUARD, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RVMLOCK, RCTX in *; lia.
- intros a ar Ha y Hy. change (s_areas st1) with (s_areas stI) in Ha.
destruct (rarea_conc stI a ar WF1 Ha) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RBa & RBAa & RBCa).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as (Da1 & _ & Da23 & Da2). unfold alloc_ceiling in RBCa.
rewrite (CQ1 a) in Hy by (intros E; rewrite E, FRr in Hra; discriminate).
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. eapply rrepfoot_area; [exact Ha| lia].
- intros b gh Hb y Hy. change (s_groups st1) with (s_groups stI) in Hb.
destruct (rgroup_conc stI b gh WF1 Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Alb & RBb & RBCb).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). destruct (rreserved_disjoint _ _ RFb) as (Db1 & _ & Db23 & Db2). unfold alloc_ceiling in RBCb.
pose proof (round_up_pg_ge (r_len rb)).
rewrite (CQ1 b) in Hy by (intros E; rewrite E, FRr in Hrb; discriminate).
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. do 5 right. left. exists b, gh. split; [exact Hb| lia].
- intros q rq Hq Kq y Hy.
assert (Hq' : (s_regions stI) !! q = Some rq).
{ change (s_regions st1) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)) in Hq.
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; discriminate| rewrite lookup_insert_ne in Hq by congruence; exact Hq]. }
destruct (WR _ _ Hq') as (RB0 & _ & _ & RBC & RFq). destruct (rreserved_disjoint _ _ RFq) as (Dq1 & _ & Dq23 & Dq2). unfold alloc_ceiling in RBC.
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). right. exists q, rq. auto.
-
destruct (rmrep_ctx_mid_agree st1 stX m1 m6 MRn1 ltac:(right; repeat split; reflexivity) eq_refl) as (X2 & X3 & X4 & X5).
{ intros y Hy. apply E16; rewrite ?rETP'; unfold RCTX in *; lia. }
split; [| split; [exact X2| split; [exact X3| split; [exact X4| split; [exact X5| split; [| exact (rmrep_init1 _ _ MRn1)]]]]]].
+ unfold ctx_head_cells. rewrite !PWX by assumption.
cbn [ctx stX st1 upd_ctx s_ctx set_next_rid set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold pw in HC6 |- *. cbn [oconc] in HC6 |- *. unfold wz. exact HC6.
+ unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. change (s_ctx st1) with (ctx stI). unfold wz. exact TC6. }

assert (ZP3 : rw_cells usegs m3 (cur + 4096) [CB 4096 (zeros 4096)]).
{ destruct ZN as [[_ ZB0] ZW0]. cbn [cells_bytes cbytes cells_size csize app] in ZB0, ZW0. rewrite app_nil_r in ZB0. rewrite Nat.add_0_r in ZW0.
eapply (rrw_cells_of_zeros m3 cur 8192 4096); [exact ZB0| exact ZW0| split; [exact (zeros_length 4096)| exact I]| cbn [cells_bytes cbytes cells_size csize]; rewrite app_nil_r, Nat.add_0_r; reflexivity| lia| cbv; discriminate]. }
assert (ZP6 : rw_cells usegs m6 (cur + 4096) [CB 4096 (zeros 4096)]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| cbn [cells_size csize]; rewrite ?Nat.add_0_r; cbn; unfold RCTX; lia].
eapply RA2.rrw_cells_agree; [exact ZP3|].
cbn [cells_size csize]. rewrite ?Nat.add_0_r. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
destruct ZP6 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize app] in ZB, ZW. rewrite app_nil_r in ZB. rewrite Nat.add_0_r in ZW.
assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
assert (ERR6 : rw_cells usegs m6 (errno_addr tp) [C4 (sysret_errno rr e1)]) by (eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (FPX : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq.
change (s_regions stX) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)).
rewrite lookup_insert_ne by (intros ->; rewrite FRr in Hq; discriminate). repeat split; auto; lia. }
assert (M16 : magree (rFP stX) m1 m6).
{ intros y Hy Hc.
assert (~ (RCTX + 40 <= y < RCTX + 48)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
assert (~ (RCTX + 920 <= y < RCTX + 928)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
assert (~ (lo <= y < bv_unsigned sp)) by (intros X; apply Hc; left; left; exact X).
assert (~ (errno_addr tp <= y < errno_addr tp + 4)) by (intros X; apply Hc; left; right; left; rewrite <- TPv; exact X).
assert (~ (cur <= y < cur + 8192)).
{ intros X. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| exact X]. }
apply E16; assumption. }
replace (Z_to_bv 64 (cur + 4096)) with (Z_to_bv 64 (conc stX (rid, 4096))) by (change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rcarve_K stX (rid, 4096) (mkRegion RKBrk cur 8192) m6 _ _ (sysret_errno rr e1));
first [exact RG1 | exact MRX | exact MI6 | exact FR6 | exact ST6 | exact ERR6 | reflexivity | idtac].
all: try (cbn [snd fst r_len r_base r_kind]; unfold pgal, lr_lo; cbn [r_kind r_base]; change (round_up_pg 8192) with 8192; first [discriminate | lia]).
+ unfold stX. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* left. reflexivity.
* right. right. exists rid, 8192, (mkRegion RKBrk cur 8192). split; [reflexivity|]. split; [exact RG1|]. cbn. discriminate.
+ change (s_areas stX) with (s_areas stI). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr0 & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas stX) with (s_metas stI). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MKI _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr0 & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
+ cbn. lia.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZB.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZW.
+ eapply rauxv_ok_magree; [exact AUX1| exact M16| intros y X; exact (rFP_below stX y (proj1 MRX) X)].
+ eapply magree_trans; [exact AG1| exact M16| exact FPX| intros y X; exact X].
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. reflexivity.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (cur =? cur + 8192) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb negb].
eapply rimplT_evt.
{ eapply (ram_bu_fail _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m1 m2 stI cur);
first [exact MR1 | exact MU2 | exact WM2 | exact ACNT | exact MI2 | reflexivity | exact TC2 | lia]. }
intros ms6 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M23 : magree (rFP stI) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 (set_brk_ps cur s) junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ exact RGI.
+ exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ exact TLI.
+ exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
+ eapply rauxv_ok_magree; [exact AUX1| | intros y X; exact (rFP_below stI y WF1 X)].
eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1); [eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X] | |];
intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.

#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbody_spec : forall (stI : mstate) (x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (junk : list byte) (e1 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
rmrep stI m1 -> mem_inv usegs m1 ->
rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (am_body stI k bail) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0ad0) fc None m1 (seg_rom usegs)).
Proof.
intros until e1. intros AMPI AI RGI BLI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MR1 as (WF1 & _).
unfold am_body.
destruct (c_free_meta_head (ctx stI)) as [h|] eqn:FMH.
-
pose proof (amp_fmh stI AMPI h FMH) as [HN0 HM0].
pose proof (amp_links stI AMPI) as [CLn CLp CLno CLs].
pose proof (CLs h HN0) as MSh.
pose proof (amp_fml stI AMPI h HM0 HN0) as (CL0 & FMn & FMp).
destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:HN; [| exfalso; apply HN0; reflexivity].
destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:HP.
2:{ exfalso. pose proof (proj2 (CLno h) HP) as X. rewrite HN in X. discriminate. }
destruct (CLn h nx HN) as [PVn MSn]. destruct (CLp h pv HP) as [NXp MSp].
assert (SELF : nx = h <-> pv = h).
{ split; intros ->; [rewrite HP in PVn| rewrite HN in NXp]; congruence. }
eapply rimplT_evt.
{ eapply (ram_deq sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI h nx pv);
first [exact MR1 | exact MI1 | exact FMH | exact MSh | exact HN | exact HP | exact MSn | exact MSp | exact SELF | exact FR1 | exact ST1 | exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
+ eapply (ram_rel_deq st stI h nx pv AI); try assumption.
* rewrite <- FMH. symmetry. exact (proj1 (proj2 (ami_ctx _ _ AI))).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HN.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HP.
* eapply meta_slot_same_areas; [| exact MSh]. symmetry. exact (ami_areas _ _ AI).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact CL0.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMn nx eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). intros X. apply (proj1 (CLno nx)) in X. rewrite PVn in X. discriminate.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMp pv eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). rewrite NXp. discriminate.
+ exact MR2.
+ exact MI2.
+ exact ST2.
+ eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
+ pose proof (sbl_regions _ _ (sbl_dequeue stI LFree h)) as RD.
eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [exact RD| exact X] | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a RD)); exact X].
+ unfold brk_link_ps in *. rewrite (sbl_brk _ _ (sbl_dequeue stI LFree h)). destruct (c_brk (ctx stI)) as [| |rid off]; auto.
unfold conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). exact BLI.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ unfold pw, oconc, wz, conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). reflexivity.
+ intros X; discriminate X.
-
destruct (Z.eqb_spec (c_avail_meta_count (ctx stI)) 0) as [CNT|CNT]; cbn [negb].
+
eapply rimplT_evt.
{ eapply (ram_disp0 _ gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact FMH| exact CNT]. }
intros ms2 ->.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
assert (PTRI : ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI).
{ apply (ami_ptrs _ _ AI); [| eapply ptrs_in_mono; [| exact (proj1 (amp_ptrs st AMP))]; intros q Hq; cbn in Hq; pose proof (ami_next _ _ AI); lia]. intros rid r Hr _.
destruct (N.lt_ge_cases rid (s_next_rid stI)) as [L|G]; [exact L|]. destruct (ami_fresh _ _ AI rid G) as [X _]. rewrite X in Hr. discriminate. }
destruct (Z.eqb_spec (c_avail_meta_area_count (ctx stI)) 0) as [ACNT|ACNT]; cbn [andb].
*
destruct (c_brk (ctx stI)) as [| |brid boff] eqn:BRK; cbn [negb].
--
eapply (rbrk_untried_path stI m1 junk e1); first [exact AMPI | exact AI | exact RGI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | reflexivity].
--
eapply rimplT_evt.
{ eapply (ram_disp_dead _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
intros ms3 ->.
eapply (rmmap_path stI m1 s junk e1); first [exact AI | exact RGI | exact ACNT | exact TLI | exact MKI | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
pose proof (amp_shift stI AMPI). lia.
--
eapply (rbrk_live_path stI brid boff m1 junk e1); first [exact AMPI | exact AI | exact RGI | exact BLI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1].
*
destruct (amp_avail_areas stI AMPI ACNT) as (p & r & AMA & Hr & NK & PAL & P0 & PLR & PHI & FRA).
pose proof (amp_acount stI AMPI) as ACR.
unfold am_after_brk. rewrite (proj2 (Z.eqb_neq _ _) ACNT).
eapply rimplT_evt.
{ eapply (ram_disp_fin _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI p r);
first [exact MR1 | exact ACNT | exact AMA | exact Hr | unfold pgal, PGSZ in *; exact PAL | lia | idtac]. unfold PGSZ in *. lia. }
intros ms3 ->.
eapply (rfinish_path stI p r m1 s junk e1); first [exact AI | exact AMA | exact Hr | exact NK | exact P0 | exact PLR | exact TLI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
-- unfold PGSZ in PHI. lia.
-- unfold pgal. unfold PGSZ in PAL. exact PAL.
-- apply (proj1 (FRA p eq_refl ltac:(lia))).
-- intros j Hj. apply (proj2 (FRA (aadd p (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
-- lia.
+
destruct (amp_avail stI AMPI CNT) as (aa & ar & kk & Haa & AVM & K0 & K1 & MQ).
pose proof (amp_count stI AMPI) as CR.
assert (MSq : meta_slot stI (aadd aa (AREA_HDR + META_SIZE * kk))) by (exists aa, ar, kk; repeat split; auto; unfold NSLOTS in *; lia).
rewrite (am_take_eq stI k bail _ AVM).
eapply rimplT_evt.
{ eapply (ram_take_walk sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI _);
first [exact MR1 | exact MI1 | exact FMH | exact CNT | exact AVM | exact MSq | exact FR1 | exact ST1 | exact LO | unfold NSLOTS in CR; lia | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
* eapply (ram_rel_take st stI _ AI).
-- rewrite <- AVM. symmetry. exact (proj1 (proj2 (proj2 (ami_ctx _ _ AI)))).
-- rewrite <- (ami_metas _ _ AI). exact MQ.
-- eapply meta_slot_same_areas; [| exact MSq]. symmetry. exact (ami_areas _ _ AI).
* exact MR2.
* exact MI2.
* exact ST2.
* eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
* eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
* eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [| exact X]; reflexivity | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a ltac:(reflexivity))); exact X].
* unfold brk_link_ps in *. unfold ctx in BLI. cbn. destruct (c_brk (s_ctx stI)) as [| |rid off]; auto.
* reflexivity.
* reflexivity.
* reflexivity.
* unfold pw, oconc, wz. reflexivity.
* intros X; discriminate X.
Qed.

#[using="lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH"] Lemma ralloc_meta_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs)).
Proof.
intros. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR as (WF0 & _).
rewrite alloc_meta_eq. unfold ralloc_meta_entry.
eapply rimplT_evt.
{ eapply (ram_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st);
first [exact MR | exact MI | exact AUX | exact ST | exact LO | exact (rmrep_init1 st m MR) | exact (amp_s_secret st AMP) | exact (amp_secret st AMP) | lia]. }
intros ms1 (x1 & u0 & u1 & u2 & s1x & s4x & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u9' & u10 & u11 & u12 & u13 & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & MR1).
assert (M01 : magree (rFP (am_init_st st)) m m1).
{ eapply magree_of_munch; [exact MU1|]. cbn. split; [| split; [| exact I]]; intros y Hy.
- left. left. lia.
- left. right. right. left. unfold RCTX in *. lia. }
eapply (rbody_spec (am_init_st st) x1 u0 u1 u2 s1x s4x u3 u4 u5 u6 u7 u8 u9 u9' u10 u11 u12 u13 m1 junk errv).
- exact (rAMpre_init st AMP).
- exact (rAMI_init st AMP).
- exact (ram_init_regions st).
- unfold brk_link_ps in *. rewrite ram_init_brk. destruct (c_brk (ctx st)) as [| |rid off]; auto. rewrite ram_init_conc. exact BL.
- exact MR1.
- exact MI1.
- exact FR1.
- exact ST1.
- eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite rETP'. cbn. unfold RCTX. lia.
- eapply rauxv_ok_magree; [exact AUX| exact M01| intros a X; exact (rFP_below (am_init_st st) a (proj1 MR1) X)].
- exact M01.
Qed.
End ASM.

#[using="Type"] Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof.
unfold ralloc_meta_stmt. intros.
eapply ralloc_meta_main; eassumption.
Qed.

End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 Qy5Y.Mq4 QlQE.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3.
Import QPjm.Mq3 QWTl.Mq4 QDUx.Mqa Q9Ay.Mqb QXxF.Mq4 Q4vs Q6y7.
Import QFkE.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq QkLq.Mq3.
Import Q98Z.Mq4 QdZ1.Mq7 QQbX.Mq6 QnkH.Mqj Qv4L.Mqj QnkH.Mqk QnkH.Mql Qi8L.Mqa.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
(st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ rmrep st' m'
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
/\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

#[using="Type"] Lemma rpres_except_entry st lo (sp : word) m m1 :
munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono usegs m m1 -> lo <= bv_unsigned sp - 96 ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof.
intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

#[using="Type"] Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
oracle_ok o m st -> rmrep st mw -> alloc_ceiling <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof.
intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
rewrite (OK rid r q h Hr Hk Hq M8 Hc).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
unfold alloc_ceiling in *.
symmetry. apply (PE (r_base r + q)); [lia|].
intros [[A|[A|A]]|[A|A]].
- lia.
- unfold RCTX in A. lia.
- destruct A as (rid' & r' & Hr' & Hk' & Hin).
destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
- destruct A as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
Z.div_mod_to_equations. lia.
- destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
destruct (N.eq_dec rid' rid) as [->|NE].
+ rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

#[using="Type"] Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof.
intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

#[using="Type"] Lemma rfree_fp_same st st' lo (sp : Z) a :
s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof. intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

#[using="Type"] Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof.
intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
unfold alloc_ceiling in *.
destruct H as [[A|[A|A]]|[A|A]].
- lia.
- unfold RCTX in A. lia.
- destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold alloc_ceiling in RC. lia.
- destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
Qed.

#[using="Type"] Lemma rknown_byte st m (q : aptr) r v :
rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
cell_read (get_shadow st (fst q)) (snd q) = Known v ->
bytes_at usegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof.
intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

#[using="Type"] Lemma rimplT_queue {R} o h g st0 (k : mstate -> QUZl.M R) bail s Q ms :
(m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
rimplT o (queue h g st0 k bail) s Q ms.
Proof.
intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

#[using="Type"] Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof. reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

#[using="LO"] Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
(forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
(exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof.
intros RP PE FP KI ZI FR RES OOK MRX ER ES.
destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
unfold rntf_q. do 16 eexists. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

#[using="LO"] Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> QUZl.M R) (bail : QUZl.M R)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
(st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
rmrep st m -> mem_inv usegs m -> oracle_ok o m st ->
stk usegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
(forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0644) fc None m (seg_rom usegs)).
Proof.
induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
{ cbn [nontrivial_free]. apply rimplT_undef. }
rewrite ntf_unfold. cbv zeta.
pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
pose proof (go_slot _ _ _ GO) as MSL.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
set (ms0 := MS _ _ _ _ _ _ _).

assert (ENTRY : entry_hyps st g i ->
evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
{ intros EH. subst ms0. eapply rntf_entry; eauto. }

assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
(G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
(G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
entry_hyps st g i).
{ intros. constructor; auto.
- exact (go_avail _ _ _ GO).
- exact (go_freed _ _ _ GO).
- pose proof (go_sc _ _ _ GO). lia.
- intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
- intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
- split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
destruct (ntf_cond st g i) eqn:HC.
-

assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
(m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
(forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
wmono usegs m m2 -> oracle_ok o m2 stX ->
data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
{ intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
set (stU := fg_usage_st stX g) in *.
assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).

assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
{ destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
try lia; try exact HALL.
- exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
- destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
- destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
[ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
| pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
rewrite RU in FC; exact FC ])).
fold stG in GD. destruct GD as (KIG & NGM & NSL).
assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).

pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
-
assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
rewrite free_meta_eq.
eapply rimplT_evt.
{ eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
| apply munch_refl | apply wmono_refl | idtac].
- pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
- intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
intros ms3 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
+ destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
(eapply rpres_except_mono; [exact PE3| exact FPX]).
+ intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
+ eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
* unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* intros [b Hb]. apply NGM. exists b. unfold hosts in *.
replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
+ apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
+
pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
set (stS := record_seq _ (step_seq stG)) in *.
assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
unfold fm_st. apply frame_queue.
* apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
* apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
* cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
* right; exact (hosts_is_gm _ _ _ HOSTS).
+
pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
* unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
* exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
* intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
+ eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
+ exact MRG.
+ pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
+ pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
-
assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).

pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
clear NEST.
pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
assert (B1LT : snd b1 + 16 <= snd p).
{ rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
pose proof (go_stride _ _ _ GO1) as [S16 _].
assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).

pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
{ split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
unfold UNIT, IB in *. lia. }
destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].

unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
{ intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
rewrite !ESH.
rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
cbn [Z.eqb negb].
set (off16 := lo8 + 256 * hi8).
assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
{ unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
rewrite EB. unfold get_group.
replace (s_groups stG !! b1) with (s_groups stX !! b1).
2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.

assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.

assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
bytes_at usegs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
{ intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
assert (HDR : bytes_at usegs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
{ change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }

destruct HOSTSX as [aig Hghp].
eapply rimplT_evt.
{ eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
| exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | apply rntf_frame_size | idtac].
all: try reflexivity.
all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
all: rewrite ?EU1.
all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
all: try (symmetry; exact EB).
all: match goal with
| |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
| |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
| |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
fold off16 in G17; unfold UNIT in G17;
replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
rewrite Z.div_mul in G17 by lia; lia
| |- ?G => idtac "NCGOAL" G; fail
end. }
intros ms3 NC. unfold rnest_call_post in NC.
destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
fold stG in MR4.

pose proof (bv_unsigned_in_range _ sp) as SPR'.
assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (unfold alloc_ceiling in LO; rewrite unsigned_lit; lia).
rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
eapply (IH R _ bail s Q (Z_to_bv 64 0xd08cc) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
+ exact KIG.
+ constructor.
* exact HB1G.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
+ unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
+ exact MR4.
+ exact MI4.
+ apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
+ rewrite SPU. exact ST4.
+ rewrite SPU. lia.
+
intros st3 mi ms5 NQ. rewrite free_meta_eq.
unfold rntf_q in NQ. rewrite SPU in NQ.
destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
replace (ret_pc (Z_to_bv 64 0xd08cc)) with (Z_to_bv 64 0xd08cc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
{ apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
assert (NGM3 : ~ is_gm st3 g).
{ intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
eapply rimplT_evt.
{ eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
- unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
- intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
- unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
- eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
- exact ST5. }
intros ms6 RP. apply KH.
pose proof (frame_trans _ _ _ FRG FR35) as FR03.
pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
* destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
(eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
(eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
(eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
* intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
* exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
* apply ZINV_fm. exact ZI3.
* unfold fm_st. apply frame_queue.
-- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
-- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
-- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
-- right; exact (hosts_is_gm _ _ _ HOSTS).
* destruct mi as [[bb len]|]; [| exact RES5].
destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
* exact OOK5.
* exact MR5.
* exact FS1.
* exact FS2. }

assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
(m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono usegs m m4 -> mem_inv usegs m4 ->
stk usegs m4 lo (bv_unsigned sp + -96) -> rw_cells usegs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0xd086c) fc None m4 (seg_rom usegs) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
{ intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
eapply rimplT_evt.
{ eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
intros ms5 FGP.
eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
- intros a Ha. eapply (rfree_fp_same st stX); eauto.
- apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
+
apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
set (sc := m_sizeclass (get_meta_rec st g)) in *.
set (an := optr_eqb (active st sc) (Some g)).
set (stm := deq_mid (LActive sc) g st).
set (st1 := dequeue (LActive sc) g st).
assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
assert (FR1' : ntf_frame st st1).
{ unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
destruct DS as (DSdata & GN1 & GP1 & _).

assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono usegs m m2 ->
rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
(rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
rimplT o (match an, active st1 sc with
| true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
| _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
end) s Q ms2).
{ intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
{ destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }

assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
{ pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). unfold alloc_ceiling in B1.
rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
- destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). unfold alloc_ceiling in C1.
unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
- unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
evt usegs (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0xd0808) fc None m3 (seg_rom usegs))).
{ intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
- eapply meta_slot_sbl; [exact SBLm| exact MSL].
- pose proof (go_sc _ _ _ GO). subst sc. lia.
- rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
assert (AVK : forall a, an = true -> active st1 sc = Some a ->
rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0xd0808) fc None m3 (seg_rom usegs))).
{ intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
set (stA := act_st st1 a (act_of st1 a)).
destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
rewrite (conc_sbl _ _ g SBLm).
eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
- unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
- unfold stA. apply ZINV_act. exact ZI1.
- unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
- unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
- unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
- unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
- unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
- unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
- unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
- unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
- eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
- eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
assert (NOACT : (an = false \/ active st1 sc = None) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0xd0808) fc None m3 (seg_rom usegs))).
{ intros NA.
eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
rewrite EP in MR4.
rewrite (conc_sbl _ _ g SBLm).
eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
- apply DSdata.
- apply (sbl_regions _ _ SBL1).
- apply (sbl_shadow _ _ SBL1).
- apply (sbl_groups _ _ SBL1).
- intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
- eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
- eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]];
try (exfalso; destruct D as (D1 & D2 & D3); congruence).
*
destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
assert (Enx : nx = g) by congruence.
eapply rimplT_evt.
{ eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- rewrite NX, Enx. reflexivity. }
intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
*
destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
assert (Enx : nx' = nx) by congruence. subst nx'.
eapply rimplT_evt.
{ eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- apply NEpv. exact NE.
- destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
+
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]];
try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
| | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
- destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
+
apply Z.eqb_eq in HM.
apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.

assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
(active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
rimplT o (k (aor_st stq g i) None) s Q ms2).
{ intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
assert (KIq : KINV stq LB c).
{ rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
- apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
- apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
- intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
assert (FRq : ntf_frame st stq).
{ rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
unfold rqpath_post in QP. cbv beta in QP.
destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
rewrite <- (conc_sbl st stq g SBL).
eapply rimplT_evt.
{ eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
- eapply meta_slot_sbl; [exact SBL| exact MSL].
- pose proof (go_li _ _ _ GO). lia.
- destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
intros ms3 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
* eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
* intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
* exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
* apply ZINV_aor. exact ZIq.
* apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
* exact eq_refl.
* apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
* exact MR2.
* reflexivity.
* reflexivity. }
destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
*
assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
{ destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia | exact HAct]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- right. exists g. split; [exact HAct| exact MSL].
- intros NE. exfalso. exact (NE HAct).
- intros hd Hhd NE. exfalso. apply NE. congruence. }
intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
*
assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
{ intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
apply rimplT_queue. intros GN GPV.
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
- intros _. split; assumption.
- intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
+
apply Z.eqb_neq in HM.
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
- pose proof (go_li _ _ _ GO). lia.
- exact (go_freed _ _ _ GO). }
intros ms2 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
* eapply rpres_except_entry; eauto.
* auto.
* exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
* apply ZINV_aor. exact ZI.
* apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
* exact eq_refl.
* eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
* exact MR1.
* reflexivity.
* reflexivity.
Qed.
End NTF.

End RC__1.
End Mq8.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi8L.Mq9.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
match res with
| (st2, Some (g, idx)) =>
exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1018) fc None m1 (seg_rom usegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv usegs m1
/\ stk usegs m1 lo (bv_unsigned sp + -48)
/\ rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
/\ rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a)
/\ 0 <= c_mmap_counter (ctx st2) < 2^32
/\ slot_ok st2 g b r idx n
/\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
| (st2, None) =>
exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom usegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp)
/\ rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ errv = Z_to_bv 64 12
end.

#[using="Type"] Lemma renf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
renf_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof.
intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

#[using="Type"] Lemma rfail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
rfail_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof.
intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rbig_stmt : Prop :=
forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
(m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
let st1 := set_tick t st in
RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^63 - 4097 -> brk_link_ps st s ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0d68) fc None m1 (seg_rom usegs)).

#[using="Type"] Lemma rrepfoot_low_core stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (6444156 <= a < 6444160).
Proof.
intros WF H. pose proof WF as (_ & WR & _ & WA & WG). unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
Qed.

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

#[using="as_pre as_inv RAS AS_PRE RBIG"] Lemma rmalloc_core_implT :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 -> (s_tick st < t)%N ->
rimplT m (malloc_core full_lay (set_tick t st) n) s
(rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge 0) as ASG.
assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
pose proof MR as (WF0 & CX0 & GL0 & _). destruct GL0 as (_ & NL & _).
assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono usegs m m1 ->
rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
/\ rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
{ intros m1 MU WM. unfold alloc_ceiling in CLO.
split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split. { eapply unk_agree_munch; [| exact MU| |].
- eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
- intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
- intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
assert (ETP : bv_unsigned tp + -164 = 6444156) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
destruct (Z.le_gt_cases (2^63 - 4097) n) as [OV|NOV].
{
unfold malloc_core.
replace (size_overflows n) with true by (symmetry; unfold size_overflows; apply Z.leb_le; lia).
riprefixT. eapply evt_cut.
{ eapply (rentry_ovf_walk ra sp gp tp); [exact HA| lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI| exact ERR| exact TP]. }
intros ms' (a1' & m1 & -> & ST1 & MU & WM & MI1 & ERR1).
apply evt_done. apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, (Z_to_bv 64 12). do 14 eexists. split; [reflexivity|].
split. { apply rmrep_set_tick. eapply (rmrep_transport_unowned st m m1 _ MR MU WM).
intros lo' hi' a Hin Ha RF. destruct (rrepfoot_low_core st a WF0 RF) as [A1 A2].
rewrite ETP in Hin. unfold alloc_ceiling in *. destruct Hin as [E|[E|[]]]; inversion E; subst; lia. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|].
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. rewrite ETP. constructor; [cbn; unfold alloc_ceiling in CLO; lia|]. constructor; [cbn; unfold alloc_ceiling in CLO; lia| constructor]. }
split. { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. rewrite ETP. unfold alloc_ceiling in CLO. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia. }
split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity. }
destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
-
riprefixT. eapply evt_cut.
{ eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI]. }
intros ms' (a1' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
apply evt_done.
eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
+ unfold RAM_STACK. lia.
+ lia.
-
assert (N32 : 0 <= n < 2^32) by (unfold MMAP_THRESHOLD in TH; lia). clear N. rename N32 into N.
unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
riprefixT. eapply evt_cut.
{ eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI| exact NL]. }
intros ms' (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
apply evt_done.
eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
all: try eassumption.
+ apply renf_hyp_ret.
+ apply rfail_hyp_ret.
+ unfold RAS_STACK. lia.
+ reflexivity.
+ intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.

End RC__1.
