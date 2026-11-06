(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Qpj5 Q6sh QQwg QKTr QvDJ QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QqLk QmP7 QpY2 Q9Ho QYyZ QnRU QOJv Qu3b QnaW QEEn QQ8H QteI Qx6U QsDw QcYs QEyY QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq2 QqLk QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QnaW.Mq1 QYyZ.Mq5 QYyZ.Mq3 QEEn.Mq0 QQ8H.Mq2 QteI.Mq0 Qx6U.Mq2.
Import QsDw.Mq0 QcYs.Mq3 QEyY.Mq0.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma calloc_no_overflow : forall cnt sz, 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> calloc_overflows cnt sz = false.
Proof.
intros cnt sz Hc Hs. unfold calloc_overflows. destruct (Z.eqb_spec sz 0) as [->|NZ]; [reflexivity|]. cbn [negb andb].
apply Z.ltb_ge. apply Z.div_le_lower_bound; [lia|]. nia.
Qed.

Lemma mz_mono {BAND : Band} : forall G RE X SP SP' x, SP <= SP' -> mz G RE X SP x -> mz G RE X SP' x.
Proof. intros G RE X SP SP' x LE [H|[H|[H|H]]]; unfold mz; [tauto| tauto| tauto| do 3 right; lia]. Qed.

Lemma calloc_W_mz0 {BAND : Band} : forall a LB FS G RE X c bp lo hi x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - CALLOC_STACK ->
In (lo, hi) (calloc_W RE X bp c (c_alloc_user (cls a c))) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx. unfold CALLOC_STACK, ALLOC_STACK in CSP.
unfold calloc_W in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. do 3 right. unfold CALLOC_STACK, ALLOC_STACK in Hx. lia.
- apply (mz_mono _ _ _ (bp - 48)); [lia|].
eapply (malloc_W_mz0 a LB FS G RE X c (bp - 48) lo hi x GC Hc); [unfold MALLOC_STACK; lia| | exact Hx].
unfold malloc_W. right. replace (bp - 48 - 2144) with (bp - 2192) by lia. exact Hin.
Qed.

Lemma calloc_W_mz {BAND : Band} : forall a a1 LB FS G G1 RE X c i bp lo hi x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - CALLOC_STACK ->
In (lo, hi) (calloc_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a a1 LB FS G G1 RE X c i bp lo hi x GC GS TI Hc CSP Hin Hx.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (calloc_W_mz0 a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx)|].
unfold slot_W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; left;
apply (slot_fpP a a1 LB FS G G1 RE X c i GC GS TI); [left| right]; split; cbn [fst snd]; lia.
Qed.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRD : ac_RDepot C = RDepot.

Lemma calloc_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (cnt sz lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_calloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 ->
from_primary (cnt * sz) = true ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (if calloc_overflows cnt sz then @Qpj5.Mq1.mret PStateA _ None else raw_malloc_A L (cnt * sz)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (cnt * sz) /\ aptr_req p = cnt * sz
/\ ARUN C s' ((p, A, cnt * sz) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ blk_shadow asegs m' A (cnt * sz)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_calloc a_alayout)) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR ST CEIL LO MI -> -> UNW DNH DCAP -> -> Hcnt Hsz Hle HP.
cbn [ala_calloc_stack ala_tp ala_gp ala_calloc a_alayout] in LO |- *.
rewrite (calloc_no_overflow cnt sz Hcnt Hsz).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
set (n := cnt * sz) in *. assert (Hn : 0 <= n <= 2^26) by (subst n; nia).
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (calloc_icpt_spec LV RE X ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo cnt sz dn GC R1 R2 R3 R7 MI ST CEIL' ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP Hcnt Hsz HP) as M.
rewrite Z_to_bv_bv_unsigned in M. fold n in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold calloc_post in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & G1 & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
set (c := class_of n) in *.
destruct r as [p|].
- destruct REST as (aa1 & i & -> & -> & QF & GS & TI & I0 & -> & MU & RPF & CM & UC).
destruct (lift_some C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl Hn HP ltac:(idtac; lia) QF GS TI I0 MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (calloc_W_mz (ps_a s) aa1 LB0 FS0 G G1 RE X c i); try eassumption; [lia| idtac; unfold CALLOC_STACK, ALLOC_STACK; lia])
RT' RS' RD' RPF CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (slot_beg RE c i + rz_size n). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UC| exact HP4].
- destruct REST as (-> & MU & QF & GS & RP').
destruct (lift_none C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa G1 c n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(idtac; lia) QF GS MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (calloc_W_mz0 (ps_a s) LB0 FS0 G RE X c); try eassumption; [lia| idtac; unfold CALLOC_STACK, ALLOC_STACK; lia])
RT' RS' RD' RP') as (HP1 & HP3).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM QpME QmvA QkZz QcfN Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QpY2.Mq3 QqLk QnRU.Mqa Q9Ho.Mq2 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1.
Import QpY2.Mq2.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QnRU.Mq8 QmvA.Mq3 QkZz.Mq1 QteI.Mq9 QQ8H.Mq3 Qx6U.Mq4.
Import QcfN.Mq1.
Import QlES.
Import QnRU.Mq6.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition asan_free_entry : Z := 0x3ed2c.

Definition DEALLOC_STACK : Z := 64 + QCHUNK_STACK.

Lemma land_mask4 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551612 = x - x mod 4.
Proof.
intros x Hx.
assert (E : 18446744073709551612 = Z.ldiff (Z.ones 64) (Z.ones 2)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^2) with 4. pose proof (Z.div_mod x 4). lia.
Qed.

Lemma cas_free_hdr {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (hdr b1 n' : Z) (id : word),
mem_inv asegs m -> (b1 = 0x11 \/ b1 = 0x91) -> hdr mod 16 = 0 -> 0x645000 <= hdr -> hdr + 16 <= band_lo ->
rw_cells asegs m hdr [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz n'); C8 id] ->
evt asegs (fun ms' => exists (a0' a2' a4' a5' a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz 3) a2' (wz hdr) a4' a5' a6' (wz 0) (wz hdr) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3ee1c) fc None m' (seg_rom asegs)
/\ munch [(hdr, hdr + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' hdr [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz n'); C8 id])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz hdr) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3eddc) fc None m (seg_rom asegs)).
Proof.
intros until id; intros MI Hb1 AL HK HC HDR. rewrite ?KHI_eq in HK. idtac.
pose proof (munch_refl [(hdr, hdr + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (proj1 (rw_cells_app asegs m hdr [C1 (b8 2); C1 (b8 b1); C2 (wz 0)] _)) in HDR as [HW HDR]. cbn [cells_size csize Nat.add] in HDR.

do 8 step.
rewrite !(unsigned_lit hdr) by lia. rewrite land_mask4 by lia. replace (hdr - hdr mod 4) with hdr by (Z.div_mod_to_equations; lia).
rewrite (Z.shiftl_mul_pow2 hdr 3) by lia. change (2^3) with 8. rewrite !(unsigned_lit (hdr * 8)) by lia.
replace ((hdr * 8) mod 32) with 0 by (Z.div_mod_to_equations; lia). rewrite !Z.shiftl_0_r.
replace (bv_swrap 32 255) with 255 by reflexivity. replace (bv_swrap 32 2) with 2 by reflexivity. replace (bv_swrap 32 3) with 3 by reflexivity.
destruct Hb1 as [-> | ->].
- recast HW [C4 (wz 0x1102)].
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
change (sx32 (wz 4354)) with (wz 4354).
step. lits. step. if_lit.
step. step. step. lits.
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
step. if_lit.
recast HW [C1 (b8 3); C1 (b8 17); C2 (wz 0)].
apply evt_done. do 5 eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
apply (proj2 (rw_cells_app asegs _ hdr [C1 (b8 3); C1 (b8 17); C2 (wz 0)] _)). split; [exact HW| exact HDR].
- recast HW [C4 (wz 0x9102)].
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
change (sx32 (wz 37122)) with (wz 37122).
step. lits. step. if_lit.
step. step. step. lits.
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
step. if_lit.
recast HW [C1 (b8 3); C1 (b8 145); C2 (wz 0)].
apply evt_done. do 5 eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
apply (proj2 (rw_cells_app asegs _ hdr [C1 (b8 3); C1 (b8 145); C2 (wz 0)] _)). split; [exact HW| exact HDR].
Qed.

Lemma wr_at_hjunk : forall m A k, wr_at asegs m A k -> 0x645000 <= A -> hjunk m A (A + k).
Proof.
intros m A k (H0 & H1 & H) HA. split; [lia|]. split; [lia|]. intros x Hx.
specialize (H (x - A) ltac:(lia)). replace (A + (x - A)) with x in H by lia.
rewrite a_wview_overlay in H by (rewrite wa_unsigned by lia; lia).
destruct (m (wa x)) as [b|]; [exists b; reflexivity| exfalso; apply H; reflexivity].
Qed.

Lemma RStats_free_words : forall RE X m, RStats RE X m -> exists w1 w2 : word, rw_cells asegs m (rl_T X + 2824) [C8 w1; C8 w2].
Proof.
intros RE X m (HJ & _). apply hjunk_C8x2.
destruct (hjunk_split m _ (rl_T X + 2824) _ HJ ltac:(lia)) as [_ H2].
destruct (hjunk_split m _ (rl_T X + 2824 + 16) _ H2 ltac:(lia)) as [H3 _]. exact H3.
Qed.

Lemma free_switch {BAND : Band} : forall a LB FS G RE X m p A n lo hi,
gcons a LB FS G RE X -> In (p, A, n) LB -> chunk_rep a G RE m p A n -> (lo, hi) = chunk_cont p A n ->
exists G',
gcons a (alb_remove p LB) FS G' RE X
/\ (forall mm, RPrim a G RE X mm -> RPrim a G' RE X mm)
/\ (RChunks a LB G RE X m -> RChunks a (alb_remove p LB) G' RE X m)
/\ (forall x, (lo <= x < hi \/ in_sh (lo, hi - lo) x) -> fp_RChunks a (alb_remove p LB) G' RE X x -> False)
/\ (forall rb bt bg m', RQuarM rb bt bg [] a LB G RE X m -> agree_on asegs (fp_RQuar a LB G RE X) m m' ->
qchunk_mem m' lo hi A n -> RQuarM rb bt bg [(p, A)] a (alb_remove p LB) G' RE X m')
/\ (forall x, (lo <= x < hi \/ in_sh (lo, hi - lo) x) -> fp_RQuar a (alb_remove p LB) G' RE X x).
Proof.
intros a LB FS G RE X m p A n lo hi GC INB CR EC. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (gc_nodup a LB FS G RE X GC) as NDL.
destruct (gc_blocks a LB FS G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
-
subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB FS G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
cbn [chunk_cont] in EC. rewrite HA in EC. replace (slot_beg RE (class_of n) i0 + rz_size n - rz_size n) with (slot_beg RE (class_of n) i0) in EC by lia.
injection EC as Elo Ehi. subst lo hi.
set (G' := set_tag (class_of n) i0 (TQuar (APrim id0 n)) G).
pose proof (retag_at G (class_of n) i0 (TLive (APrim id0 n)) (TQuar (APrim id0 n)) Ht) as RT. fold G' in RT.
pose proof (slot_prim a LB FS G RE X GC _ _ _ Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
exists G'. split; [| split; [| split; [| split; [| split]]]].
+ eapply gcons_free_prim; [exact GC| exact INB| reflexivity| exact Ht].
+ intros mm RP. eapply RPrim_retag; [exact RP| exact Ht| reflexivity| reflexivity].
+ intros RC. eapply RChunks_drop; [exact RC| exact INB| exact NDL| intros e He; exact He|].
intros c' i' q NE Hq. subst G'. eapply drop_tags_retag; [exact Ht| exact NE| exact Hq].
+ intros x Hx FC. pose proof (rl_prim a LB FS G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. rewrite ?KHI_eq in PK. idtac.
assert (XB : (slot_beg RE (class_of n) i0 <= x < slot_beg RE (class_of n) i0 + class_size (class_of n)) \/ 0x2008fff7000 <= x < SH band_lo).
{ destruct Hx as [Hx|Hx]; [left; lia| right].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia.
exact (slot_band a LB FS G RE X GC _ _ _ x Ht Hx). }

assert (LIVE' : forall c' i' q, tag_at G' c' i' = Some (TLive q) -> tag_at G c' i' = Some (TLive q) /\ (class_of n <> c' \/ i0 <> i')).
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? class_of n) && (i' =? i0)) eqn:E; [discriminate|].
split; [exact Hq|]. destruct (Z.eqb_spec c' (class_of n)); [destruct (Z.eqb_spec i' i0); [discriminate| lia]| lia]. }

assert (SECB : forall e y, In e (as_reg a) -> (se_beg e + kPage <= y < se_beg e + se_size e \/ in_sh (se_beg e + kPage, se_size e - kPage) y) ->
(al_space_beg (ae_L RE) <= y < al_space_beg (ae_L RE) + 2^37 + 4096 -> False)
/\ (in_sh (slot_beg RE (class_of n) i0, class_size (class_of n)) y -> False)).
{ intros e y He Hy. pose proof (sec_facts a LB FS G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & _). unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
destruct Hy as [Hy|Hy].
- split; [lia|]. intros Hs. pose proof SH_band as ?SHBDx; pose proof (slot_band a LB FS G RE X GC _ _ _ y Ht Hs). rewrite ?KHI_eq in E2. lia.
- pose proof (sec_band a LB FS G RE X GC e y He Hy). split; [lia|]. intros Hs.
exact (in_sh_disjoint (slot_beg RE (class_of n) i0) (class_size (class_of n)) (se_beg e + kPage) (se_size e - kPage) y P3 ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q M1 E6 E2 E1 r1 e PK RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - M2 M1 D1 E6 E4 E2 E1 e PK P3 P2 P1 KP i0 n RE BAND; lia | lia ])) Hs Hy). }
destruct FC as [[[F|F] _]|[F|F]].
* destruct F as (c' & i' & t' & Ht' & Hl & F). destruct t' as [| |q|q|]; try discriminate. destruct (LIVE' _ _ _ Ht') as [HtG NE].
pose proof (slots_disjoint a LB FS G RE X GC _ _ _ _ _ _ Ht HtG NE) as D.
pose proof (slot_prim a LB FS G RE X GC _ _ _ HtG) as (P1' & P2' & P3' & _). unfold prim_hi, prim_lo in *. destruct F; cbn [fst snd] in *.
pose proof SH_band as ?SHBDx. destruct XB as [XB|XB]; [lia|]. lia.
* destruct F as (e & He & _ & F). destruct (SECB e x He (or_introl F)) as [S1 S2]. destruct XB as [XB|XB]; [exact (S1 ltac:(lia))|].
pose proof (sec_facts a LB FS G RE X GC e He) as (E1 & E2 & E3 & _). rewrite ?KHI_eq in E2. pose proof SH_band as ?SHBDx. lia.
* destruct F as (c' & i' & t' & Ht' & Hl & F). destruct t' as [| |q|q|]; try discriminate. destruct (LIVE' _ _ _ Ht') as [HtG NE].
pose proof (slots_disjoint a LB FS G RE X GC _ _ _ _ _ _ Ht HtG NE) as D.
pose proof (slot_prim a LB FS G RE X GC _ _ _ HtG) as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
pose proof SH_band as ?SHBDx; pose proof (slot_band a LB FS G RE X GC _ _ _ x HtG F).
destruct Hx as [Hx|Hx]; [lia|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia.
exact (in_sh_disjoint (slot_beg RE (class_of n) i0) (class_size (class_of n)) (slot_beg RE c' i') (class_size c') x P3 P3' ltac:(lia) ltac:(lia) D Hx F).
* destruct F as (e & He & _ & F). destruct (SECB e x He (or_intror F)) as [S1 S2]. destruct Hx as [Hx|Hx]; [exact (S1 ltac:(lia))|].
apply S2. replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros rb bt bg m' RQ AG QM'. eapply (RQuarM_free_prim a LB FS G RE X GC rb bt bg m m' _ A n RQ INB AG id0 (class_of n) i0 eq_refl eq_refl Ht HA QM').
+ intros x Hx. assert (TQ' : tag_at G' (class_of n) i0 = Some (TQuar (APrim id0 n))) by (rewrite RT, !Z.eqb_refl; reflexivity).
destruct Hx as [Hx|Hx].
* do 5 right; left. exists (class_of n), i0, (TQuar (APrim id0 n)). split; [exact TQ'|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
* do 6 right; left. exists (class_of n), i0, (TQuar (APrim id0 n)). split; [exact TQ'|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
-
subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
cbn [chunk_cont] in EC. injection EC as Elo Ehi. subst lo hi.
pose proof (sec_facts a LB FS G RE X GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5) as [M1 M2]. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
exists G. split; [| split; [| split; [| split; [| split]]]].
+ eapply gcons_free_sec; [exact GC| exact INB| reflexivity].
+ intros mm RP; exact RP.
+ intros RC. eapply RChunks_drop; [exact RC| exact INB| exact NDL| intros e' He'; exact He'| intros c' i' q NE Hq; exact Hq].
+ intros x Hx FC. pose proof (rl_prim a LB FS G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. unfold KHI in PK, E2. idtac.
assert (XB : (mb0 + kPage <= x < mb0 + sec_map_size n) \/ 2147446784 <= x < 17594333495296).
{ destruct Hx as [Hx|Hx]; [left; lia| right]. replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia.
exact (sec_band a LB FS G RE X GC _ x He Hx). }

assert (OTHER : forall e, In e (as_reg a) -> sec_live (alb_remove (ASec mb0 n) LB) e -> e <> mkSec mb0 (sec_map_size n) n /\ (se_beg e + se_size e <= mb0 \/ mb0 + sec_map_size n <= se_beg e)).
{ intros e He' (A2 & HL). apply In_alb_remove in HL as [HL NE]. cbn [ablk_id fst] in NE.
assert (NEe : e <> mkSec mb0 (sec_map_size n) n) by (intros ->; apply NE; reflexivity). split; [exact NEe|].
destruct (decide (se_beg e = mb0)) as [EQ|NEb].
- exfalso. apply NEe. exact (NoDup_map_In_inj se_beg (as_reg a) e (mkSec mb0 (sec_map_size n) n) (gc_sec_nodup a LB FS G RE X GC) He' He EQ).
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e (mkSec mb0 (sec_map_size n) n) (gc_sec_disj a LB FS G RE X GC) He' He
ltac:(cbn; intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd se_beg se_size] in D. lia. }
destruct FC as [[[F|F] _]|[F|F]].
* destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_prim a LB FS G RE X GC _ _ _ Ht') as (P1' & P2' & P3' & _). unfold prim_hi, prim_lo in *.
destruct F; cbn [fst snd] in *. pose proof SH_band as ?SHBDx. destruct XB as [XB|XB]; lia.
* destruct F as (e & He' & HL & F). destruct (OTHER e He' HL) as [_ D]. pose proof (sec_facts a LB FS G RE X GC e He') as (E1' & E2' & E3' & _). rewrite ?KHI_eq in E2'.
pose proof SH_band as ?SHBDx. destruct XB as [XB|XB]; (first [ clear - E2' D XB F e x M2 E1 KP mb0 n BAND M1 E6; lia | lia ]).
* destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_prim a LB FS G RE X GC _ _ _ Ht') as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
pose proof SH_band as ?SHBDx; pose proof (slot_band a LB FS G RE X GC _ _ _ x Ht' F). destruct Hx as [Hx|Hx]; [(first [ clear - H SHBDx P3' P1' PK i' c' Hx x M1 E6 E2 KP mb0 n RE BAND; lia | lia ])|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia.
exact (in_sh_disjoint (mb0 + kPage) (sec_map_size n - kPage) (slot_beg RE c' i') (class_size c') x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H15 q2 H1 H0 r q H SHBDx PK x M1 E6 E2 E1 r2 KP mb0 n RE BAND; lia | lia ])) P3' ltac:(lia) ltac:(lia) ltac:((first [ clear - H SHBDx P3' P2' P1' PK i' c' x M2 M1 D1 E6 E2 E1 KP mb0 n RE BAND; lia | lia ])) Hx F).
* destruct F as (e & He' & HL & F). destruct (OTHER e He' HL) as [_ D]. pose proof (sec_facts a LB FS G RE X GC e He') as (E1' & E2' & E3' & E4' & E5' & E6' & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5') as [M1' M2']. rewrite <- E4' in M1'.
pose proof (sec_band a LB FS G RE X GC e x He' F). destruct Hx as [Hx|Hx]; [(first [ clear - H M2' M1' E6' E4' E2' D PK e Hx x M2 M1 E6 E2 KP mb0 n RE BAND; lia | lia ])|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia.
exact (in_sh_disjoint (mb0 + kPage) (sec_map_size n - kPage) (se_beg e + kPage) (se_size e - kPage) x
ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H20 q3 H1 H0 r q H PK x M1 E6 E2 E1 r3 KP mb0 n RE BAND; lia | lia ])) ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q M1' E6' E1' r1 e BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - H M2' M1' E6' E4' E2' E1' D PK e x M2 M1 E6 E2 E1 KP mb0 n RE BAND; lia | lia ])) Hx F).
+ intros rb bt bg m' RQ AG QM'. eapply (RQuarM_free_sec a LB FS G RE X GC rb bt bg m m' _ A n RQ INB AG mb0 eq_refl He HA QM').
+ assert (NL : ~ sec_live (alb_remove (ASec mb0 n) LB) (mkSec mb0 (sec_map_size n) n)).
{ intros (A' & HL). cbn [se_beg se_req] in HL. apply In_alb_remove in HL as [_ NE]. apply NE. reflexivity. }
intros x [Hx|Hx].
* do 7 right; left. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size se_req]. split; [exact He|]. split; [exact NL|]. lia.
* do 8 right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size se_req]. split; [exact He|]. split; [exact NL|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
Qed.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis recycle_spec : recycle_stmt C RE X L.
Hypothesis HRD : ac_RDepot C = RDepot.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Lemma dealloc_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A n lo : Z)
(obj sz bp dn : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> In (p, A, n) LB0 -> qroom a p -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - DEALLOC_STACK ->
rw_cells asegs m obj (unw_obj obj sz [q0; q1; q2; q3; q4] rest bp) ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 2080 < 2^64 ->
aimplT atn (asan_free (ae_L RE) a p) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB0) FS0 lo m free_step)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A) (wz obj) (wz 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_free_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros QR INB QRM MI ST CEIL LO OBJ SZB DNH DCAP OLO OHI.
pose proof CEIL as CEIL'. idtac. unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
change (2^64) with 18446744073709551616 in OHI.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB) as HN2.

pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC INB) as CR.
assert (PC0 : exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & _ & _ & NPd & _). unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & _ & _ & BPd & _). unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [cbn [chunk_cont]; rewrite HA; f_equal; lia|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2.
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (APrim id0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [left; exists (class_of n), i0, (TLive (APrim id0 n)); split; [exact Ht|]; split; [reflexivity| split; cbn [fst snd]; lia]|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (APrim id0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; lia.
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; left. exists (class_of n), i0, (TLive (APrim id0 n)). split; [exact Ht|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
pose proof (sec_facts _ _ _ _ _ _ GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
assert (LIVE : sec_live LB0 (mkSec mb0 (sec_map_size n) n)) by (exists A; exact INB).
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (ASec mb0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [right; exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]; auto|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (ASec mb0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; (first [ clear - CT HA' i' c' Hbx nb Ab x E1 HA0 KU mb0 ks A RE BAND; lia | lia ]).
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]. split; [exact He|]. split; [exact LIVE|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. (first [ clear - Db Dn D Hx x E1 BPd NPd PK TD TK KP mb0 ks n X RE BAND; lia | lia ]). }
destruct PC0 as (plo & phi & CM & En & Hn0 & ECONT & PZ & PZS & PT3).
assert (PTT : phi <= rl_T X \/ rl_T X + 4096 <= plo).
{ pose proof CM as CM0. destruct CM0 as (_ & _ & _ & _ & _ & PU). destruct PU as (_ & _ & _ & P4 & _ & P6 & _).
pose proof (used_size_pos n ltac:(lia)) as [U1 _]. pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as RU0.
destruct (Z.le_gt_cases phi (rl_T X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_T X + 4096) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj1 (PT3 (Z.max plo (rl_T X)) ltac:(lia))). lia. }
destruct (free_switch a LB0 FS0 G RE X m p A n plo phi GC INB CR ECONT) as (G' & GC' & RPG & RCG & NFC & RQG & QZ').
pose proof (qchunk_geom m plo phi A n) as QG.
clear QG.
destruct CM as (LEFT & (b1 & idw & Hb1 & HDR) & WR & JUNK & SHD & PURE). unfold hdr_cells in HDR. hide SHD.
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). rewrite ?KHI_eq in M8. idtac.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2]. set (u := used_size n) in *.
pose proof (round_up_ge u 8 ltac:(lia)) as RU.
pose proof (ngran_eq u ltac:(lia)) as (NG1 & NG2 & NG3).
assert (AH : 0x645000 <= A).
{ destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn' & HP' & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn' & HP' & He0 & HA0)].
- pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht0) as (P1 & _). pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKx & _).
pose proof (rz_size_range n) as [RZx _]. unfold prim_user in HA0. unfold prim_lo, KHI in *. clear - P1 PKx HA0 RZx. lia.
- pose proof (sec_facts _ _ _ _ _ _ GC _ He0) as (_ & E2x & _ & _ & E5x & _). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5x) as [G1x _]. pose proof (sec_req_facts n ltac:(lia) E5x) as [_ RQx].
unfold kSecUserOff in HA0. clear - E2x G1x RQx HA0. lia. }

assert (JALL : hjunk m A phi).
{ pose proof (wr_at_hjunk _ _ _ WR ltac:(lia)) as (_ & _ & W1). destruct JUNK as (_ & J2 & J3).
split; [lia|]. split; [lia|]. intros x Hx. destruct (Z.lt_ge_cases x (A + u)); [apply W1; lia| apply J3; lia]. }
destruct (hjunk_split _ A (A + 8) phi JALL ltac:(lia)) as [J8 _]. destruct (hjunk_C8 _ A J8) as [w0 JC]. hide JALL.
destruct (RStats_free_words _ _ _ RS) as (f1 & f2 & STC).
unfold unw_obj in OBJ. cbn [map app] in OBJ.
replace (A - 16) with (A + -16) in HDR by lia.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] m) as MU.
pose proof (wmono_refl asegs m) as WM.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] -> lo' <= x < hi' ->
(band_lo <= x < bv_unsigned sp) \/ (plo <= x < phi) \/ (rl_T X + 2824 <= x < rl_T X + 2840)).
{ intros lo' hi' x Hin Hx. cbn in Hin. pose proof (qchunk_geom m plo phi A n) as XX || idtac.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; [left; lia| left; lia| right; left; lia| right; left; (first [ clear - Hx x AH NG3 NG1 RU U1 M6 M4 u phi plo ks n A BAND; lia | lia ])| right; right; lia]. }
assert (RTW : Forall (rt_avoid RE X) [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ apply List.Forall_forall. intros [lo' hi'] Hin x Hx FT. cbn [fst snd] in Hx.
destruct (WCASE lo' hi' x Hin Hx) as [Z|[Z|Z]].
- pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(left; exact FT)). lia.
- destruct (PZ x Z) as [LU|FC]; [exact (fp_RTconst_cz a LB0 FS0 G RE X GC x FT ltac:(do 2 right; left; exact LU))| exact (fpC_excl a LB0 FS0 G RE X GC x FC (or_introl FT))].
- exact (rt_avoid_Thigh RE X (rl_T X + 2824) (rl_T X + 2840) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT). }
assert (STW : Forall st_avoid [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ repeat apply Forall_cons; try apply Forall_nil; st_avoid_solve. }

assert (QO1 : QOTH C a (alb_remove p LB0) FS0 G' RE X m).
{ apply QOTH_split. split; [exact RT|]. split; [exact RS|]. split; [exact (RPG m RP)|].
split; [exact (RCG RC)|]. split; [| split; [rewrite HRD; exact RD| exact RF]].
eapply HRSx; [exact RSE| reflexivity| reflexivity| reflexivity|].
intros e He (A' & HA'). exists A'. apply In_alb_remove in HA' as [HA' _]. exact HA'. }
unfold asan_free_entry, A_INSTANCE in *.
apply aimplT_from_evt.
do 10 step.
carve_frame 64%nat ST.
do 9 step.
step. unfold_cond; cond_unsig; if_false.
do 7 step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (run_free_hooks_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT2.
step. if_true.

assert (AL16 : (A + -16) mod 16 = 0) by (Z.div_mod_to_equations; (first [ clear - H29 q10 H0 H r q AH U1 RU r0 M6 M4 M2 r5 u phi plo ks A p BAND; lia | lia ])).
assert (HK16 : 0x645000 <= A + -16) by (rewrite ?KHI_eq; (first [ clear - AH U1 RU NG1 NG3 M6 M5 M4 M2 PURE u phi plo ks A p BAND; lia | lia ])).
assert (HC16 : A + -16 + 16 <= band_lo) by (idtac; lia).
call_ch (cas_free_hdr) ltac:(fun PO => idtac); try eassumption; try lia.
rename POST into HDR3.
assert (LB1 : Z.land b1 3 = 1) by (destruct Hb1 as [-> | ->]; reflexivity).
assert (B1R : 0 <= b1 < 256) by (first [ clear - HK16 AH U1 RU M6 M5 M4 u Hb1 b1 phi plo ks A p BAND; lia | lia ]).
step. step.
stf.
step.
rewrite zxb_b8, (Z.mod_small b1 256) by lia.
step.
rewrite (unsigned_lit b1), LB1 by lia.
step. if_false.
step. lits.
step.
step. if_true.

step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (get_thread_stats_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT4.
assert (UB : u <= 2^26 + 1) by (subst u; unfold used_size; lia).
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step. step.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
step. step.
do 4 step.
do 8 step.
step. step.
lazymatch goal with ST' : stk _ _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp); rename ST' into STF end.
apply evt_done.

unfold asan_free. rewrite (proj2 (Z.ltb_ge kQMaxSize (aptr_used p))) by (unfold aptr_used; lia).
replace (wz (A + -16)) with (wz (A - 16)) by (f_equal; lia).
unhide SHD. unhide JALL.
lazymatch type of MU with munch ?W m ?mf =>

assert (WZ' : forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> wzone a (alb_remove p LB0) G' RE X (bv_unsigned sp) z);
[ intros lo' hi' z Hin Hx; unfold wzone; destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]];
[ do 3 right; exact Z
| left; apply QZ'; left; exact Z
| right; right; left; left; split; cbn [fst snd]; lia ]
| ];
assert (QO2 : QOTH C a (alb_remove p LB0) FS0 G' RE X mf);
[ apply QOTH_split in QO1 as (_ & _ & RP1 & QRE1); apply QOTH_split;
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]|];
split; [eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]|];
split;
[ eapply RPrim_frame; [exact RP1| exact WM|]; eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx); lia
| exact (fpQ_RPrim a (alb_remove p LB0) FS0 G' RE X GC' z (QZ' z (or_introl Z)) Fx)
| refine (fpP_RStats a (alb_remove p LB0) FS0 G' RE X GC' z Fx _); left; split; cbn [fst snd]; lia ]
| eapply QREST_munch; [exact GC'| exact QRE1| exact MU| exact WM|]; intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy) ]
| ];

assert (AGQ : agree_on asegs (fp_RQuar a LB0 G RE X) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia))
| destruct (PZ z Z) as [LU|FC]; [exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(do 2 right; left; exact LU))| exact (fpQ_RChunks a LB0 FS0 G RE X GC z Fx FC)]
| refine (fpQ_RStats a LB0 FS0 G RE X GC z Fx _); left; split; cbn [fst snd]; lia ]
| ];
assert (AGlow : agree_on asegs (fun z => 2147446784 <= z < 17594333495296) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| (first [ clear - Z Hz z AH U1 RU NG1 NG3 M8 M6 M5 M4 PURE phi plo u ks A p BAND; lia | lia ])| (first [ clear - Z Hz z HK16 AH U1 RU M6 M5 M4 M1 phi plo PK TK u ks A p X RE BAND; lia | lia ])]
| ];
assert (AGlr : agree_on asegs (fun z => plo <= z < A + -16) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| | (first [ clear - Z Hz z HK16 AH U1 RU M8 M6 M5 M4 PTT PURE phi plo PK TK u ks A p X RE BAND; lia | lia ])];
cbn in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Hy Hz z HC16 AH U1 RU M6 M4 phi plo CEIL' u LO ks lo A p sp BAND Z HK16 M8 M5 PTT PURE PK TK X RE; lia | lia ])
| ];
assert (QM : qchunk_mem mf plo phi A (aptr_req p));
[ split; [| split; [| split; [| split]]];
[ intros Hrz; destruct (LEFT Hrz) as [LC LJ]; split; [| eapply hjunk_wmono; [exact LJ| exact WM]];
eapply rw_cells_agree; [exact AGlr| exact LC|]; intros z Hz; cbn [cells_size csize Nat.add] in Hz; (first [ clear - Hz z Hrz HK16 AH U1 RU NG1 NG3 M6 M5 M4 M2 M1 phi plo u ks A p BAND; lia | lia ])
| exists b1, idw; split; [exact Hb1| exact HDR3]
| eapply hjunk_wmono; [exact JALL| exact WM]
| exists (ush u); eapply rw_cells_agree; [exact AGlow| exact SHD|]; intros z Hz; cbn [cells_size csize] in Hz; change (used_size (aptr_req p)) with u in Hz;
rewrite !Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id in Hz by (Z.div_mod_to_equations; (first [ clear - H34 q11 H29 q10 H0 H r Hz z HK16 U1 RU r1 M8 M6 M4 M2 M1 q5 q PURE r6 r5 r4 r3 phi plo u ks A p BAND NG2 H19 q8 NG1 q6 NG3 M5; lia | lia ])); unfold SH, A_SHADOW_OFS in Hz; cbn beta; Z.div_mod_to_equations; (first [ clear - H39 q12 H10 H9 r1 H5 H4 r0 H0 H r Hz q z HK16 U1 RU r2 NG3 M9 M8 M6 M4 M1 q6 q5 PURE r7 r6 r5 r4 phi plo TB u ks A p X BAND; lia | lia ])
| exact PURE ]
| ];
pose proof (RQG 0 QB QB mf RQ AGQ QM) as RQ2;
assert (QR2 : QRUN C 0 QB QB [(p, A)] a (alb_remove p LB0) FS0 G' RE X mf) by (split; [exact GC'| split; [exact QO2| exact RQ2]])
end.
eapply aimplT_mono.
{ eapply (qchunk_spec C L RE X HRD); [exact QR2| eassumption| exact STF| exact CEIL'| unfold QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia| lia
| exact QRM| exact OBJ| exact SZB| eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); [intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)| exact DNH]
| exact DCAP| exact OLO| change (2^64) with 18446744073709551616; lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO |- *.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
do 15 eexists. exists m5, G5. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [| split; [| exact QR5]].
2:{
destruct DS5 as [DS5 ES5]. split; [eapply depot_keep_step; [| exact DS5]; eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)|].
eapply errno_keep_trans; [| exact ES5]. eapply (errno_keep_of_ezone _ _ _ _ RE X m _ _ GC' MU WM). intros lo' hi' z Hin Hy. unfold ezone.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [do 5 right; lia| left; apply QZ'; left; exact Z| right; right; left; unfold in_iv; cbn [fst snd]; lia]. }
eapply aheap_presA_trans; [| exact AP5].
eapply aheap_presA_of_munch_w; [exact GC'| apply Permutation_refl| apply Permutation_refl| lia| exact MU| exact WM| exact WZ'].
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD QVo2 QRfV QEYd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq2 QqLk QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 Qu3b.Mq2 QYyZ.Mq5 QkfD QYyZ.Mq3 QEEn.Mq0 QQ8H.Mq2 Qx6U.Mq2 QmvA.Mq1 QpME.Mq6.
Import QVo2.Mq1.
Import QRfV.Mq0 QnRU.Mq9 QnRU.Mq1 QEYd Qx6U.Mq3.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma wr_at_hjunk : forall m A n, wr_at asegs m A n -> 0x645000 <= A -> hjunk m A (A + n).
Proof.
intros m A n (H1 & H2 & H) HA. split; [right; exact HA|]. split; [exact H2|]. intros a Ha.
specialize (H (a - A) ltac:(lia)). replace (A + (a - A)) with a in H by lia.
rewrite a_wview_overlay in H by (rewrite wa_unsigned by lia; lia).
destruct (m (wa a)) as [b|]; [exists b; reflexivity| exfalso; exact (H eq_refl)].
Qed.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRSE : ac_RSec C = RSec.
Hypothesis HRD : ac_RDepot C = RDepot.
Hypothesis large_alloc_spec : forall RE X, large_alloc_stmt RE X LV.
Hypothesis poison_zero_spec : forall RE X, poison_zero_stmt_lh RE X LV.

Definition lz (a : AState) (RE : aentry) (X : rlay) (SP mb msz x : Z) : Prop :=
fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < SP \/ nmap mb msz x.

Lemma malloc_W_sec_lz : forall a LB FS G RE X bp mb msz lo hi x,
gcons a LB FS G RE X -> band_lo <= bp - MALLOC_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo, hi) (malloc_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo <= x < hi -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo hi x GC CSP MSZ MB8 Hin Hx. pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold malloc_W_sec, alloc_W_sec, MALLOC_STACK, ALLOC_STACK, SS_BASE, DP_END in Hin. unfold MALLOC_STACK in CSP. cbn [tl app In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <-.
- do 3 right; left. idtac. lia.
- right; left. do 3 right. lia.
- left. right; left. split; cbn [fst snd]; lia.
- left. do 2 right. lia.
- left. left. split; cbn [fst snd]; lia.
- do 2 right; left. left. split; cbn [fst snd]; lia.
- do 2 right; left. right; left. split; cbn [fst snd]; lia.
- right; left. left. split; cbn [fst snd]; lia.
- right; left. right; left. split; cbn [fst snd]; lia.
- right; left. do 2 right; left. split; cbn [fst snd]; lia.
- do 4 right. left. lia.
- do 4 right. right. split; cbn [fst snd]; [lia|]. assert (E : SH (mb + msz) <= SH mb + msz / 8) by (rewrite !SH_eq; clear - MB8 MSZ; Z.div_mod_to_equations; lia). lia.
Qed.

Lemma lift_sec_some : forall s LB FS RE X G LB0 FS0 aa n mb m m' SP W,
let msz := sec_map_size n in let A := mb + kSecUserOff in
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RPrim (ps_a s) G RE X m -> RChunks (ps_a s) LB0 G RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m ->
0 <= n <= 2^26 -> from_primary n = false -> band_lo <= SP ->
as_reg aa = as_reg (ps_a s) ++ [mkSec mb msz n] ->
as_tq aa = as_tq (ps_a s) -> as_gq aa = as_gq (ps_a s) -> (forall c, cls aa c = cls (ps_a s) c) ->
as_cache_inited aa = as_cache_inited (ps_a s) -> as_next aa = as_next (ps_a s) ->
mb mod kPage = 0 -> appr mb msz -> mb + msz <= band_lo -> zavoids mb msz (avoid_of (ae_L RE) (ps_a s)) = true ->
munch W m m' -> wmono asegs m m' -> (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> lz (ps_a s) RE X SP mb msz x) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' -> RSec aa LB0 RE X m' ->
chunk_mem m' (mb + kPage) (mb + msz) A n ->
aheap_presA asegs a_alayout LB FS SP m m'
/\ ablock_rangeA A n
/\ ARUN C (set_a aa s) ((ASec mb n, A, n) :: LB) FS RE m'
/\ blk_shadow asegs m' A n.
Proof.
intros s LB FS RE X G LB0 FS0 aa n mb m m' SP W msz A PB PF GC R3 R4 R6 R8 Hn HP CSP REG TQ GQ CLS CI NX MBP MBK MBC ZA MU WM ZN RT' RS' RD' RSE' CM.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (sec_geom_facts n Hn HP) as (GN & Grz & _ & _ & Gnd1 & Gssz & _ & GM1 & _). fold msz in GM1.
pose proof MBP as MBP'. rewrite KP in MBP'.
pose proof MBK as MBKr. apply appr_to_lia in MBK; [| lia| lia].
destruct (zavoid_facts RE X (ps_a s) mb msz (rlay_avoid RE X RL) ltac:(lia) ZA) as (AVO & AVP & AVQ & AVR).
assert (SOK : sec_ok RE X (mkSec mb msz n)).
{ unfold sec_ok. cbn [se_beg se_size se_req]. split; [exact MBP'|]. split; [exact MBKr|]. split; [exact MBC|]. split; [reflexivity|]. split; [exact HP|]. split; [lia|].
split; [unfold iv_disjoint; cbn [fst snd]; lia|]. split; [unfold iv_disjoint; cbn [fst snd]; lia|].
apply List.Forall_forall. intros o Ho. unfold iv_disjoint. cbn [fst snd]. destruct (AVO o Ho); lia. }
pose proof (gcons_reg_add (ps_a s) aa LB0 FS0 G RE X mb msz n GC REG CLS NX SOK AVR ltac:(lia)) as GC1.
assert (NI : ~ In mb (map se_beg (as_reg (ps_a s)))).
{ intros Hin. apply in_map_iff in Hin. destruct Hin as (e & E & He).
pose proof (AVR e He) as D. pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. rewrite E in D. (first [ clear - M1 E6 D e MBKr GM1 Gssz Gnd1 GN MBK MBP NX msz mb n aa s BAND; lia | lia ]). }
pose proof (gcons_alloc_sec aa LB0 FS0 G RE X mb n GC1 ltac:(rewrite REG; apply in_or_app; right; left; reflexivity) (sec_id_fresh _ _ _ _ _ _ mb n GC NI) Hn HP) as GC2.
fold A in GC2.

pose proof (conj MBP' (conj MBK (conj MBC (conj AVO (conj AVP (conj AVQ AVR)))))) as NMF.
assert (ZP : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RPrim G RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpP_RStats _ _ _ _ _ _ GC x F Z).
- exact (fpP_RDepot _ _ _ _ _ _ GC x F Z).
- exact (fpP_RSec _ _ _ _ _ _ GC x F Z).
- pose proof (fp_RPrim_lt_ceil G RE X x RL F). lia.
- exact (nmap_RPrim _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (ZQ : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RQuar (ps_a s) LB0 G RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpQ_RStats _ _ _ _ _ _ GC x F Z).
- exact (fpQ_RDepot _ _ _ _ _ _ GC x F Z).
- exact (fpQ_RSec _ _ _ _ _ _ GC x F Z).
- apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x F). left. lia.
- exact (nmap_RQuar _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (ZC : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RChunks (ps_a s) LB0 G RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F)).
- exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F)).
- exact (fpC_excl _ _ _ _ _ _ GC x F ltac:(right; left; exact Z)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 3 right; left; exact F)). lia.
- exact (nmap_RChunks _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (ZF : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RFake FS0 RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(do 3 right; left; exact F)).
- exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(do 2 right; left; exact F)).
- exact (fpSec_RFake _ _ _ _ _ _ GC x Z F).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 6 right; exact F)). lia.
- exact (nmap_RFake _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (AG : forall P : Z -> Prop, (forall x, lz (ps_a s) RE X SP mb msz x -> P x -> False) -> agree_on asegs P m m').
{ intros P HP0. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx. exact (HP0 x (ZN lo hi x Hin Hx) Px). }
split.
{ unfold aheap_presA. apply AG. intros x Z CA. destruct Z as [Z|[Z|[Z|[Z|Z]]]].
- exact (pzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA Z).
- exact (ssec_client _ _ _ _ _ _ GC LB FS SP x PB PF CSP CA Z).
- exact (qzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (nmap_client _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR LB FS SP x PB PF CSP CA Z). }
split. { unfold ablock_rangeA. subst A. rewrite KU. rewrite ?KHI_eq in *. repeat split; first [lia| clear - MBP'; Z.div_mod_to_equations; lia]. }
assert (RC2 : RChunks aa ((ASec mb n, A, n) :: LB0) G RE X m').
{ apply RChunks_cons.
- eapply RChunks_ext; [eapply RChunks_frame; [exact R4| exact WM| apply AG; exact ZC]| intros e He; rewrite REG; apply in_or_app; left; exact He| apply same_tags_refl].
- cbn [chunk_rep]. split; [reflexivity|]. split; [rewrite REG; apply in_or_app; right; left; reflexivity|]. split; [reflexivity|]. exact CM.
- intros q B k z Hin NE Z1 Z2. cbn [chunk_cont fst snd] in Z1.
assert (NMz : nmap mb msz z) by (left; destruct Z1 as [X1 X2]; cbn [fst snd] in X1, X2; rewrite KP in X1; lia).
pose proof (RChunks_open _ _ _ _ _ _ _ _ _ R4 Hin) as CRq.
destruct q as [idq nq|mb' nq]; cbn [chunk_rep chunk_cont fst snd] in CRq, Z2.
+ destruct CRq as (-> & i' & Hti' & HB & _).
replace (B - rz_size k + class_size (class_of k) - (B - rz_size k)) with (class_size (class_of k)) in Z2 by lia.
rewrite HB in Z2. replace (slot_beg RE (class_of k) i' + rz_size k - rz_size k) with (slot_beg RE (class_of k) i') in Z2 by lia.
exact (nmap_slot _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR _ _ _ z Hti' ltac:(left; exact Z2) NMz).
+ destruct CRq as (-> & Hr & HB & _).
pose proof (sec_facts _ _ _ _ _ _ GC _ Hr) as (_ & _ & _ & E4 & _). cbn [se_size se_req] in E4.
exact (nmap_sec _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR _ z Hr ltac:(left; cbn [se_beg se_size]; destruct Z2 as [Y1 Y2]; cbn [fst snd] in Y1, Y2; rewrite KP in Y1; lia) NMz). }
split.
{ eapply (ARUN_close C _ _ _ _ _ X G ((ASec mb n, A, n) :: LB0) FS0); [apply perm_skip; exact PB| exact PF|]. cbn [ps_a set_a].
split; [exact GC2|]. rewrite HRT, HRS, HRP, HRC, HRSE, HRD.
split; [exact RT'|]. split; [exact RS'|].
split. { eapply RPrim_ext; [eapply RPrim_frame; [exact R3| exact WM| apply AG; exact ZP]| exact CLS| exact CI| apply same_len_refl| apply same_tags_refl]. }
split; [exact RC2|].
split. { eapply RSec_ext; [exact RSE'| reflexivity| reflexivity]. }
split. { eapply (ac_RQuar_alloc_sec C); [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; exact ZQ]| exact TQ| exact GQ| exact REG| exact NI]. }
split; [exact RD'|]. eapply (ac_RFake_frame C); [exact R8| exact WM| apply AG; exact ZF]. }
exact (RChunks_shadow _ _ FS0 _ _ X _ (ASec mb n) A n GC2 RC2 ltac:(left; reflexivity)).
Qed.

Lemma lift_sec_none : forall s LB FS RE X G LB0 FS0 m m' SP W,
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RPrim (ps_a s) G RE X m -> RChunks (ps_a s) LB0 G RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec (ps_a s) RE X x \/ band_lo <= x < SP) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' -> RSec (ps_a s) LB0 RE X m' ->
aheap_presA asegs a_alayout LB FS SP m m' /\ ARUN C s LB FS RE m'.
Proof.
intros s LB FS RE X G LB0 FS0 m m' SP W PB PF GC R3 R4 R6 R8 CSP MU WM ZN RT' RS' RD' RSE'.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
assert (AG : forall P : Z -> Prop, (forall x, (fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec (ps_a s) RE X x \/ band_lo <= x < SP) -> P x -> False) -> agree_on asegs P m m').
{ intros P HP0. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx. exact (HP0 x (ZN lo hi x Hin Hx) Px). }
split.
{ unfold aheap_presA. apply AG. intros x Z CA. destruct Z as [Z|[Z|[Z|Z]]].
- exact (pzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA Z).
- exact (ssec_client _ _ _ _ _ _ GC LB FS SP x PB PF CSP CA Z).
- exact (qzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)). }
eapply (ARUN_close C _ _ _ _ _ X G LB0 FS0); [exact PB| exact PF|].
split; [exact GC|]. rewrite HRT, HRS, HRP, HRC, HRSE, HRD.
split; [exact RT'|]. split; [exact RS'|].
split. { eapply RPrim_frame; [exact R3| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpP_RStats _ _ _ _ _ _ GC x F Z)| exact (fpP_RDepot _ _ _ _ _ _ GC x F Z)| exact (fpP_RSec _ _ _ _ _ _ GC x F Z)| pose proof (fp_RPrim_lt_ceil G RE X x RL F); lia]. }
split. { eapply RChunks_frame; [exact R4| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F))| exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F))| exact (fpC_excl _ _ _ _ _ _ GC x F ltac:(right; left; exact Z))
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 3 right; left; exact F)); lia]. }
split; [exact RSE'|].
split. { eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpQ_RStats _ _ _ _ _ _ GC x F Z)| exact (fpQ_RDepot _ _ _ _ _ _ GC x F Z)| exact (fpQ_RSec _ _ _ _ _ _ GC x F Z)| apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x F); left; lia]. }
split; [exact RD'|].
eapply (ac_RFake_frame C); [exact R8| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(do 3 right; left; exact F))| exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(do 2 right; left; exact F))| exact (fpSec_RFake _ _ _ _ _ _ GC x Z F)
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 6 right; exact F)); lia].
Qed.

Lemma malloc_W_sec_z : forall a LB FS G RE X bp lo hi x,
gcons a LB FS G RE X -> band_lo <= bp - MALLOC_STACK ->
In (lo, hi) (malloc_W_sec RE X bp) -> lo <= x < hi -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < bp.
Proof.
intros a LB FS G RE X bp lo hi x GC CSP Hin Hx.
destruct (malloc_W_sec_lz a LB FS G RE X bp 0 0 lo hi x GC CSP ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto|].
exfalso. destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia|]. change (0 / 8) with 0 in Z2. lia.
Qed.

Lemma malloc_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (n lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_malloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 n -> 0 <= n <= 2^26 ->
from_primary n = false ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req p = n
/\ ARUN C s' ((p, A, n) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
/\ blk_shadow asegs m' A n
/\ (forall mb k, p = ASec mb k -> A = mb + kSecUserOff)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_malloc a_alayout)) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR ST CEIL LO MI -> -> UNW DNH DCAP -> Hn HP.
cbn [ala_malloc_stack ala_tp ala_gp ala_malloc a_alayout] in LO |- *.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (malloc_icpt_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo n dn GC R1 R2 R5 R7 MI ST CEIL' ltac:(unfold MALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP Hn HP) as M.
rewrite Z_to_bv_bv_unsigned in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold malloc_post_sec in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
destruct r as [p|].
- destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MU & RSE' & CM).
pose proof (sec_geom_facts n Hn HP) as (GN & _ & _ & _ & Gnd1 & Gssz & _ & GM1 & _).
destruct (lift_sec_some s LB FS RE X G LB0 FS0 aa n mb m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 Hn HP ltac:(idtac; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_sec_lz (ps_a s) LB0 FS0 G RE X); [exact GC| idtac; unfold MALLOC_STACK; lia| lia| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT' RS' RD' RSE' CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
pose proof CM as (_ & _ & WR & _). pose proof (sec_geom_facts n Hn HP) as (_ & _ & Gn' & _). rewrite Gn' in WR.
pose proof (wr_at_hjunk _ _ _ WR ltac:(rewrite ?KHI_eq in MBK; (first [ clear - GM1 Gssz Gnd1 GN MBK MBP NX mb aa KU KP n s BAND; lia | lia ]))) as HJ.
replace (mb + kSecUserOff + n) with (mb + kSecUserOff + Z.of_nat (Z.to_nat n)) in HJ by lia. destruct (hjunk_cells _ _ _ HJ) as [junk UC].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (mb + kSecUserOff), junk. split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UC|]. split; [exact HP4|]. intros mb' k E. injection E as <- <-. reflexivity.
- destruct REST as (-> & -> & MU & RSE').
destruct (lift_sec_none s LB FS RE X G LB0 FS0 m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 ltac:(idtac; lia) MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_sec_z (ps_a s) LB0 FS0 G RE X); [exact GC| idtac; unfold MALLOC_STACK; lia| exact Hin| exact Hx])
RT' RS' RD' RSE') as [HP1 HP3].
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QV3O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk QV3O QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QOJv.Mqc Qu3b QnaW.Mq3 QYyZ.Mqc QYyZ.Mqa QEEn QQ8H.Mq5 QteI.Mqa Qx6U.Mq6.
Import QsDw.Mq1 QcYs.Mq7 QEyY.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma calloc_no_overflow : forall cnt sz, 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> calloc_overflows cnt sz = false.
Proof.
intros cnt sz Hc Hs. unfold calloc_overflows. destruct (Z.eqb_spec sz 0) as [->|NZ]; [reflexivity|]. cbn [negb andb].
apply Z.ltb_ge. apply Z.div_le_lower_bound; [lia|]. nia.
Qed.

Lemma mz_mono {BAND : Band} : forall G RE X SP SP' x, SP <= SP' -> mz G RE X SP x -> mz G RE X SP' x.
Proof. intros G RE X SP SP' x LE [H|[H|[H|H]]]; unfold mz; [tauto| tauto| tauto| do 3 right; lia]. Qed.

Lemma calloc_W_mz0 {BAND : Band} : forall a LB FS G RE X c bp lo hi x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - CALLOC_STACK ->
In (lo, hi) (calloc_W RE X bp c (c_alloc_user (cls a c))) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx. unfold CALLOC_STACK, ALLOC_STACK in CSP.
unfold calloc_W in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. do 3 right. unfold CALLOC_STACK, ALLOC_STACK in Hx. lia.
- apply (mz_mono _ _ _ (bp - 48)); [lia|].
eapply (malloc_W_mz0 a LB FS G RE X c (bp - 48) lo hi x GC Hc); [unfold MALLOC_STACK; lia| | exact Hx].
unfold malloc_W. right. replace (bp - 48 - 2144) with (bp - 2192) by lia. exact Hin.
Qed.

Lemma calloc_W_mz {BAND : Band} : forall a a1 LB FS G G1 RE X c i bp lo hi x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - CALLOC_STACK ->
In (lo, hi) (calloc_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a a1 LB FS G G1 RE X c i bp lo hi x GC GS TI Hc CSP Hin Hx.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (calloc_W_mz0 a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx)|].
unfold slot_W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; left;
apply (slot_fpP a a1 LB FS G G1 RE X c i GC GS TI); [left| right]; split; cbn [fst snd]; lia.
Qed.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRD : ac_RDepot C = RDepot.

Lemma calloc_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (cnt sz lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_calloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 ->
from_primary (cnt * sz) = true ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (if calloc_overflows cnt sz then @Qpj5.Mq1.mret PStateA _ None else raw_malloc_A L (cnt * sz)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (cnt * sz) /\ aptr_req p = cnt * sz
/\ ARUN C s' ((p, A, cnt * sz) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ blk_shadow asegs m' A (cnt * sz)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_calloc a_alayout)) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR ST CEIL LO MI -> -> UNW DNH DCAP -> -> Hcnt Hsz Hle HP.
cbn [ala_calloc_stack ala_tp ala_gp ala_calloc a_alayout] in LO |- *.
rewrite (calloc_no_overflow cnt sz Hcnt Hsz).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
set (n := cnt * sz) in *. assert (Hn : 0 <= n <= 2^26) by (subst n; nia).
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (calloc_icpt_spec LV RE X ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo cnt sz dn GC R1 R2 R3 R7 MI ST CEIL' ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP Hcnt Hsz HP) as M.
rewrite Z_to_bv_bv_unsigned in M. fold n in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold calloc_post in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & G1 & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
set (c := class_of n) in *.
destruct r as [p|].
- destruct REST as (aa1 & i & -> & -> & QF & GS & TI & I0 & -> & MU & RPF & CM & UC).
destruct (lift_some C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl Hn HP ltac:(idtac; lia) QF GS TI I0 MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (calloc_W_mz (ps_a s) aa1 LB0 FS0 G G1 RE X c i); try eassumption; [lia| idtac; unfold CALLOC_STACK, ALLOC_STACK; lia])
RT' RS' RD' RPF CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (slot_beg RE c i + rz_size n). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UC| exact HP4].
- destruct REST as (-> & MU & QF & GS & RP').
destruct (lift_none C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa G1 c n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(idtac; lia) QF GS MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (calloc_W_mz0 (ps_a s) LB0 FS0 G RE X c); try eassumption; [lia| idtac; unfold CALLOC_STACK, ALLOC_STACK; lia])
RT' RS' RD' RP') as (HP1 & HP3).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjgW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk QV3O QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 Qu3b QYyZ.Mqc QjgW QYyZ.Mqa QEEn QQ8H.Mq5 Qx6U.Mq6 QmvA.Mq5 QpME.Mqc.
Import QVo2.Mq4.
Import QRfV.Mq3 QnRU.Mqk QnRU.Mqd QEYd.Mq0 Qx6U.Mq7.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma wr_at_hjunk : forall m A n, wr_at asegs m A n -> 0x647000 <= A -> hjunk m A (A + n).
Proof.
intros m A n (H1 & H2 & H) HA. split; [right; exact HA|]. split; [exact H2|]. intros a Ha.
specialize (H (a - A) ltac:(lia)). replace (A + (a - A)) with a in H by lia.
rewrite a_wview_overlay in H by (rewrite wa_unsigned by lia; lia).
destruct (m (wa a)) as [b|]; [exists b; reflexivity| exfalso; exact (H eq_refl)].
Qed.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRSE : ac_RSec C = RSec.
Hypothesis HRD : ac_RDepot C = RDepot.
Hypothesis large_alloc_spec : forall RE X, large_alloc_stmt RE X LV.
Hypothesis poison_zero_spec : forall RE X, poison_zero_stmt_lh RE X LV.

Definition lz (a : AState) (RE : aentry) (X : rlay) (SP mb msz x : Z) : Prop :=
fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < SP \/ nmap mb msz x.

Lemma malloc_W_sec_lz : forall a LB FS G RE X bp mb msz lo hi x,
gcons a LB FS G RE X -> band_lo <= bp - MALLOC_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo, hi) (malloc_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo <= x < hi -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo hi x GC CSP MSZ MB8 Hin Hx. pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold malloc_W_sec, alloc_W_sec, MALLOC_STACK, ALLOC_STACK, SS_BASE, DP_END in Hin. unfold MALLOC_STACK in CSP. cbn [tl app In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <-.
- do 3 right; left. idtac. lia.
- right; left. do 3 right. lia.
- left. right; left. split; cbn [fst snd]; lia.
- left. do 2 right. lia.
- left. left. split; cbn [fst snd]; lia.
- do 2 right; left. left. split; cbn [fst snd]; lia.
- do 2 right; left. right; left. split; cbn [fst snd]; lia.
- right; left. left. split; cbn [fst snd]; lia.
- right; left. right; left. split; cbn [fst snd]; lia.
- right; left. do 2 right; left. split; cbn [fst snd]; lia.
- do 4 right. left. lia.
- do 4 right. right. split; cbn [fst snd]; [lia|]. assert (E : SH (mb + msz) <= SH mb + msz / 8) by (rewrite !SH_eq; clear - MB8 MSZ; Z.div_mod_to_equations; lia). lia.
Qed.

Lemma lift_sec_some : forall s LB FS RE X G LB0 FS0 aa n mb m m' SP W,
let msz := sec_map_size n in let A := mb + kSecUserOff in
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RPrim (ps_a s) G RE X m -> RChunks (ps_a s) LB0 G RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m ->
0 <= n <= 2^26 -> from_primary n = false -> band_lo <= SP ->
as_reg aa = as_reg (ps_a s) ++ [mkSec mb msz n] ->
as_tq aa = as_tq (ps_a s) -> as_gq aa = as_gq (ps_a s) -> (forall c, cls aa c = cls (ps_a s) c) ->
as_cache_inited aa = as_cache_inited (ps_a s) -> as_next aa = as_next (ps_a s) ->
mb mod kPage = 0 -> appr mb msz -> mb + msz <= band_lo -> zavoids mb msz (avoid_of (ae_L RE) (ps_a s)) = true ->
munch W m m' -> wmono asegs m m' -> (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> lz (ps_a s) RE X SP mb msz x) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' -> RSec aa LB0 RE X m' ->
chunk_mem m' (mb + kPage) (mb + msz) A n ->
aheap_presA asegs a_alayout LB FS SP m m'
/\ ablock_rangeA A n
/\ ARUN C (set_a aa s) ((ASec mb n, A, n) :: LB) FS RE m'
/\ blk_shadow asegs m' A n.
Proof.
intros s LB FS RE X G LB0 FS0 aa n mb m m' SP W msz A PB PF GC R3 R4 R6 R8 Hn HP CSP REG TQ GQ CLS CI NX MBP MBK MBC ZA MU WM ZN RT' RS' RD' RSE' CM.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (sec_geom_facts n Hn HP) as (GN & Grz & _ & _ & Gnd1 & Gssz & _ & GM1 & _). fold msz in GM1.
pose proof MBP as MBP'. rewrite KP in MBP'.
pose proof MBK as MBKr. apply appr_to_lia in MBK; [| lia| lia].
destruct (zavoid_facts RE X (ps_a s) mb msz (rlay_avoid RE X RL) ltac:(lia) ZA) as (AVO & AVP & AVQ & AVR).
assert (SOK : sec_ok RE X (mkSec mb msz n)).
{ unfold sec_ok. cbn [se_beg se_size se_req]. split; [exact MBP'|]. split; [exact MBKr|]. split; [exact MBC|]. split; [reflexivity|]. split; [exact HP|]. split; [lia|].
split; [unfold iv_disjoint; cbn [fst snd]; lia|]. split; [unfold iv_disjoint; cbn [fst snd]; lia|].
apply List.Forall_forall. intros o Ho. unfold iv_disjoint. cbn [fst snd]. destruct (AVO o Ho); lia. }
pose proof (gcons_reg_add (ps_a s) aa LB0 FS0 G RE X mb msz n GC REG CLS NX SOK AVR ltac:(lia)) as GC1.
assert (NI : ~ In mb (map se_beg (as_reg (ps_a s)))).
{ intros Hin. apply in_map_iff in Hin. destruct Hin as (e & E & He).
pose proof (AVR e He) as D. pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. rewrite E in D. (first [ clear - M1 E6 D e MBKr GM1 Gssz Gnd1 GN MBK MBP NX msz mb n aa s BAND; lia | lia ]). }
pose proof (gcons_alloc_sec aa LB0 FS0 G RE X mb n GC1 ltac:(rewrite REG; apply in_or_app; right; left; reflexivity) (sec_id_fresh _ _ _ _ _ _ mb n GC NI) Hn HP) as GC2.
fold A in GC2.

pose proof (conj MBP' (conj MBK (conj MBC (conj AVO (conj AVP (conj AVQ AVR)))))) as NMF.
assert (ZP : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RPrim G RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpP_RStats _ _ _ _ _ _ GC x F Z).
- exact (fpP_RDepot _ _ _ _ _ _ GC x F Z).
- exact (fpP_RSec _ _ _ _ _ _ GC x F Z).
- pose proof (fp_RPrim_lt_ceil G RE X x RL F). lia.
- exact (nmap_RPrim _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (ZQ : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RQuar (ps_a s) LB0 G RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpQ_RStats _ _ _ _ _ _ GC x F Z).
- exact (fpQ_RDepot _ _ _ _ _ _ GC x F Z).
- exact (fpQ_RSec _ _ _ _ _ _ GC x F Z).
- apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x F). left. lia.
- exact (nmap_RQuar _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (ZC : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RChunks (ps_a s) LB0 G RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F)).
- exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F)).
- exact (fpC_excl _ _ _ _ _ _ GC x F ltac:(right; left; exact Z)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 3 right; left; exact F)). lia.
- exact (nmap_RChunks _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (ZF : forall x, lz (ps_a s) RE X SP mb msz x -> fp_RFake FS0 RE X x -> False).
{ intros x [Z|[Z|[Z|[Z|Z]]]] F.
- exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(do 3 right; left; exact F)).
- exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(do 2 right; left; exact F)).
- exact (fpSec_RFake _ _ _ _ _ _ GC x Z F).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 6 right; exact F)). lia.
- exact (nmap_RFake _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR x Z F). }
assert (AG : forall P : Z -> Prop, (forall x, lz (ps_a s) RE X SP mb msz x -> P x -> False) -> agree_on asegs P m m').
{ intros P HP0. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx. exact (HP0 x (ZN lo hi x Hin Hx) Px). }
split.
{ unfold aheap_presA. apply AG. intros x Z CA. destruct Z as [Z|[Z|[Z|[Z|Z]]]].
- exact (pzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA Z).
- exact (ssec_client _ _ _ _ _ _ GC LB FS SP x PB PF CSP CA Z).
- exact (qzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (nmap_client _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR LB FS SP x PB PF CSP CA Z). }
split. { unfold ablock_rangeA. subst A. rewrite KU. rewrite ?KHI_eq in *. repeat split; first [lia| clear - MBP'; Z.div_mod_to_equations; lia]. }
assert (RC2 : RChunks aa ((ASec mb n, A, n) :: LB0) G RE X m').
{ apply RChunks_cons.
- eapply RChunks_ext; [eapply RChunks_frame; [exact R4| exact WM| apply AG; exact ZC]| intros e He; rewrite REG; apply in_or_app; left; exact He| apply same_tags_refl].
- cbn [chunk_rep]. split; [reflexivity|]. split; [rewrite REG; apply in_or_app; right; left; reflexivity|]. split; [reflexivity|]. exact CM.
- intros q B k z Hin NE Z1 Z2. cbn [chunk_cont fst snd] in Z1.
assert (NMz : nmap mb msz z) by (left; destruct Z1 as [X1 X2]; cbn [fst snd] in X1, X2; rewrite KP in X1; lia).
pose proof (RChunks_open _ _ _ _ _ _ _ _ _ R4 Hin) as CRq.
destruct q as [idq nq|mb' nq]; cbn [chunk_rep chunk_cont fst snd] in CRq, Z2.
+ destruct CRq as (-> & i' & Hti' & HB & _).
replace (B - rz_size k + class_size (class_of k) - (B - rz_size k)) with (class_size (class_of k)) in Z2 by lia.
rewrite HB in Z2. replace (slot_beg RE (class_of k) i' + rz_size k - rz_size k) with (slot_beg RE (class_of k) i') in Z2 by lia.
exact (nmap_slot _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR _ _ _ z Hti' ltac:(left; exact Z2) NMz).
+ destruct CRq as (-> & Hr & HB & _).
pose proof (sec_facts _ _ _ _ _ _ GC _ Hr) as (_ & _ & _ & E4 & _). cbn [se_size se_req] in E4.
exact (nmap_sec _ _ _ _ _ _ GC mb msz MBP' MBK MBC ltac:(lia) AVO AVP AVQ AVR _ z Hr ltac:(left; cbn [se_beg se_size]; destruct Z2 as [Y1 Y2]; cbn [fst snd] in Y1, Y2; rewrite KP in Y1; lia) NMz). }
split.
{ eapply (ARUN_close C _ _ _ _ _ X G ((ASec mb n, A, n) :: LB0) FS0); [apply perm_skip; exact PB| exact PF|]. cbn [ps_a set_a].
split; [exact GC2|]. rewrite HRT, HRS, HRP, HRC, HRSE, HRD.
split; [exact RT'|]. split; [exact RS'|].
split. { eapply RPrim_ext; [eapply RPrim_frame; [exact R3| exact WM| apply AG; exact ZP]| exact CLS| exact CI| apply same_len_refl| apply same_tags_refl]. }
split; [exact RC2|].
split. { eapply RSec_ext; [exact RSE'| reflexivity| reflexivity]. }
split. { eapply (ac_RQuar_alloc_sec C); [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; exact ZQ]| exact TQ| exact GQ| exact REG| exact NI]. }
split; [exact RD'|]. eapply (ac_RFake_frame C); [exact R8| exact WM| apply AG; exact ZF]. }
exact (RChunks_shadow _ _ FS0 _ _ X _ (ASec mb n) A n GC2 RC2 ltac:(left; reflexivity)).
Qed.

Lemma lift_sec_none : forall s LB FS RE X G LB0 FS0 m m' SP W,
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RPrim (ps_a s) G RE X m -> RChunks (ps_a s) LB0 G RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec (ps_a s) RE X x \/ band_lo <= x < SP) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' -> RSec (ps_a s) LB0 RE X m' ->
aheap_presA asegs a_alayout LB FS SP m m' /\ ARUN C s LB FS RE m'.
Proof.
intros s LB FS RE X G LB0 FS0 m m' SP W PB PF GC R3 R4 R6 R8 CSP MU WM ZN RT' RS' RD' RSE'.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
assert (AG : forall P : Z -> Prop, (forall x, (fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec (ps_a s) RE X x \/ band_lo <= x < SP) -> P x -> False) -> agree_on asegs P m m').
{ intros P HP0. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx. exact (HP0 x (ZN lo hi x Hin Hx) Px). }
split.
{ unfold aheap_presA. apply AG. intros x Z CA. destruct Z as [Z|[Z|[Z|Z]]].
- exact (pzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA Z).
- exact (ssec_client _ _ _ _ _ _ GC LB FS SP x PB PF CSP CA Z).
- exact (qzone_client _ _ _ _ _ _ LB FS SP x GC PB PF CSP CA (or_intror Z)). }
eapply (ARUN_close C _ _ _ _ _ X G LB0 FS0); [exact PB| exact PF|].
split; [exact GC|]. rewrite HRT, HRS, HRP, HRC, HRSE, HRD.
split; [exact RT'|]. split; [exact RS'|].
split. { eapply RPrim_frame; [exact R3| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpP_RStats _ _ _ _ _ _ GC x F Z)| exact (fpP_RDepot _ _ _ _ _ _ GC x F Z)| exact (fpP_RSec _ _ _ _ _ _ GC x F Z)| pose proof (fp_RPrim_lt_ceil G RE X x RL F); lia]. }
split. { eapply RChunks_frame; [exact R4| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F))| exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(left; exact F))| exact (fpC_excl _ _ _ _ _ _ GC x F ltac:(right; left; exact Z))
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 3 right; left; exact F)); lia]. }
split; [exact RSE'|].
split. { eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpQ_RStats _ _ _ _ _ _ GC x F Z)| exact (fpQ_RDepot _ _ _ _ _ _ GC x F Z)| exact (fpQ_RSec _ _ _ _ _ _ GC x F Z)| apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x F); left; lia]. }
split; [exact RD'|].
eapply (ac_RFake_frame C); [exact R8| exact WM| apply AG]. intros x [Z|[Z|[Z|Z]]] F;
[exact (fpS_excl _ _ _ _ _ _ GC x Z ltac:(do 3 right; left; exact F))| exact (fpD_excl _ _ _ _ _ _ GC x Z ltac:(do 2 right; left; exact F))| exact (fpSec_RFake _ _ _ _ _ _ GC x Z F)
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC x ltac:(do 6 right; exact F)); lia].
Qed.

Lemma malloc_W_sec_z : forall a LB FS G RE X bp lo hi x,
gcons a LB FS G RE X -> band_lo <= bp - MALLOC_STACK ->
In (lo, hi) (malloc_W_sec RE X bp) -> lo <= x < hi -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < bp.
Proof.
intros a LB FS G RE X bp lo hi x GC CSP Hin Hx.
destruct (malloc_W_sec_lz a LB FS G RE X bp 0 0 lo hi x GC CSP ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto|].
exfalso. destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia|]. change (0 / 8) with 0 in Z2. lia.
Qed.

Lemma malloc_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (n lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_malloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 n -> 0 <= n <= 2^26 ->
from_primary n = false ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req p = n
/\ ARUN C s' ((p, A, n) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
/\ blk_shadow asegs m' A n
/\ (forall mb k, p = ASec mb k -> A = mb + kSecUserOff)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_malloc a_alayout)) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR ST CEIL LO MI -> -> UNW DNH DCAP -> Hn HP.
cbn [ala_malloc_stack ala_tp ala_gp ala_malloc a_alayout] in LO |- *.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (malloc_icpt_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo n dn GC R1 R2 R5 R7 MI ST CEIL' ltac:(unfold MALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP Hn HP) as M.
rewrite Z_to_bv_bv_unsigned in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold malloc_post_sec in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
destruct r as [p|].
- destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MU & RSE' & CM).
pose proof (sec_geom_facts n Hn HP) as (GN & _ & _ & _ & Gnd1 & Gssz & _ & GM1 & _).
destruct (lift_sec_some s LB FS RE X G LB0 FS0 aa n mb m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 Hn HP ltac:(idtac; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_sec_lz (ps_a s) LB0 FS0 G RE X); [exact GC| idtac; unfold MALLOC_STACK; lia| lia| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT' RS' RD' RSE' CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
pose proof CM as (_ & _ & WR & _). pose proof (sec_geom_facts n Hn HP) as (_ & _ & Gn' & _). rewrite Gn' in WR.
pose proof (wr_at_hjunk _ _ _ WR ltac:(rewrite ?KHI_eq in MBK; (first [ clear - GM1 Gssz Gnd1 GN MBK MBP NX mb aa KU KP n s BAND; lia | lia ]))) as HJ.
replace (mb + kSecUserOff + n) with (mb + kSecUserOff + Z.of_nat (Z.to_nat n)) in HJ by lia. destruct (hjunk_cells _ _ _ HJ) as [junk UC].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (mb + kSecUserOff), junk. split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UC|]. split; [exact HP4|]. intros mb' k E. injection E as <- <-. reflexivity.
- destruct REST as (-> & -> & MU & RSE').
destruct (lift_sec_none s LB FS RE X G LB0 FS0 m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 ltac:(idtac; lia) MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_sec_z (ps_a s) LB0 FS0 G RE X); [exact GC| idtac; unfold MALLOC_STACK; lia| exact Hin| exact Hx])
RT' RS' RD' RSE') as [HP1 HP3].
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV3O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mql. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXcn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkZz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkZz.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ8H.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqh.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition asan_free_entry : Z := 0x3ef58.

Definition DEALLOC_STACK : Z := 64 + QCHUNK_STACK.

Lemma land_mask4 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551612 = x - x mod 4.
Proof.
intros x Hx.
assert (E : 18446744073709551612 = Z.ldiff (Z.ones 64) (Z.ones 2)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^2) with 4. pose proof (Z.div_mod x 4). lia.
Qed.

Lemma cas_free_hdr {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (hdr b1 n' : Z) (id : word),
mem_inv asegs m -> (b1 = 0x11 \/ b1 = 0x91) -> hdr mod 16 = 0 -> 0x647000 <= hdr -> hdr + 16 <= band_lo ->
rw_cells asegs m hdr [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz n'); C8 id] ->
evt asegs (fun ms' => exists (a0' a2' a4' a5' a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz 3) a2' (wz hdr) a4' a5' a6' (wz 0) (wz hdr) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f048) fc None m' (seg_rom asegs)
/\ munch [(hdr, hdr + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' hdr [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz n'); C8 id])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz hdr) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f008) fc None m (seg_rom asegs)).
Proof.
intros until id; intros MI Hb1 AL HK HC HDR. rewrite ?KHI_eq in HK. idtac.
pose proof (munch_refl [(hdr, hdr + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (proj1 (rw_cells_app asegs m hdr [C1 (b8 2); C1 (b8 b1); C2 (wz 0)] _)) in HDR as [HW HDR]. cbn [cells_size csize Nat.add] in HDR.

do 8 step.
rewrite !(unsigned_lit hdr) by lia. rewrite land_mask4 by lia. replace (hdr - hdr mod 4) with hdr by (Z.div_mod_to_equations; lia).
rewrite (Z.shiftl_mul_pow2 hdr 3) by lia. change (2^3) with 8. rewrite !(unsigned_lit (hdr * 8)) by lia.
replace ((hdr * 8) mod 32) with 0 by (Z.div_mod_to_equations; lia). rewrite !Z.shiftl_0_r.
replace (bv_swrap 32 255) with 255 by reflexivity. replace (bv_swrap 32 2) with 2 by reflexivity. replace (bv_swrap 32 3) with 3 by reflexivity.
destruct Hb1 as [-> | ->].
- recast HW [C4 (wz 0x1102)].
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
change (sx32 (wz 4354)) with (wz 4354).
step. lits. step. if_lit.
step. step. step. lits.
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
step. if_lit.
recast HW [C1 (b8 3); C1 (b8 17); C2 (wz 0)].
apply evt_done. do 5 eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
apply (proj2 (rw_cells_app asegs _ hdr [C1 (b8 3); C1 (b8 17); C2 (wz 0)] _)). split; [exact HW| exact HDR].
- recast HW [C4 (wz 0x9102)].
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
change (sx32 (wz 37122)) with (wz 37122).
step. lits. step. if_lit.
step. step. step. lits.
amo_step (amo_aligned_intro4 hdr ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
step. if_lit.
recast HW [C1 (b8 3); C1 (b8 145); C2 (wz 0)].
apply evt_done. do 5 eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
apply (proj2 (rw_cells_app asegs _ hdr [C1 (b8 3); C1 (b8 145); C2 (wz 0)] _)). split; [exact HW| exact HDR].
Qed.

Lemma wr_at_hjunk : forall m A k, wr_at asegs m A k -> 0x647000 <= A -> hjunk m A (A + k).
Proof.
intros m A k (H0 & H1 & H) HA. split; [lia|]. split; [lia|]. intros x Hx.
specialize (H (x - A) ltac:(lia)). replace (A + (x - A)) with x in H by lia.
rewrite a_wview_overlay in H by (rewrite wa_unsigned by lia; lia).
destruct (m (wa x)) as [b|]; [exists b; reflexivity| exfalso; apply H; reflexivity].
Qed.

Lemma RStats_free_words : forall RE X m, RStats RE X m -> exists w1 w2 : word, rw_cells asegs m (rl_T X + 2824) [C8 w1; C8 w2].
Proof.
intros RE X m (HJ & _). apply hjunk_C8x2.
destruct (hjunk_split m _ (rl_T X + 2824) _ HJ ltac:(lia)) as [_ H2].
destruct (hjunk_split m _ (rl_T X + 2824 + 16) _ H2 ltac:(lia)) as [H3 _]. exact H3.
Qed.

Lemma free_switch {BAND : Band} : forall a LB FS G RE X m p A n lo hi,
gcons a LB FS G RE X -> In (p, A, n) LB -> chunk_rep a G RE m p A n -> (lo, hi) = chunk_cont p A n ->
exists G',
gcons a (alb_remove p LB) FS G' RE X
/\ (forall mm, RPrim a G RE X mm -> RPrim a G' RE X mm)
/\ (RChunks a LB G RE X m -> RChunks a (alb_remove p LB) G' RE X m)
/\ (forall x, (lo <= x < hi \/ in_sh (lo, hi - lo) x) -> fp_RChunks a (alb_remove p LB) G' RE X x -> False)
/\ (forall rb bt bg m', RQuarM rb bt bg [] a LB G RE X m -> agree_on asegs (fp_RQuar a LB G RE X) m m' ->
qchunk_mem m' lo hi A n -> RQuarM rb bt bg [(p, A)] a (alb_remove p LB) G' RE X m')
/\ (forall x, (lo <= x < hi \/ in_sh (lo, hi - lo) x) -> fp_RQuar a (alb_remove p LB) G' RE X x).
Proof.
intros a LB FS G RE X m p A n lo hi GC INB CR EC. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (gc_nodup a LB FS G RE X GC) as NDL.
destruct (gc_blocks a LB FS G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
-
subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB FS G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
cbn [chunk_cont] in EC. rewrite HA in EC. replace (slot_beg RE (class_of n) i0 + rz_size n - rz_size n) with (slot_beg RE (class_of n) i0) in EC by lia.
injection EC as Elo Ehi. subst lo hi.
set (G' := set_tag (class_of n) i0 (TQuar (APrim id0 n)) G).
pose proof (retag_at G (class_of n) i0 (TLive (APrim id0 n)) (TQuar (APrim id0 n)) Ht) as RT. fold G' in RT.
pose proof (slot_prim a LB FS G RE X GC _ _ _ Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
exists G'. split; [| split; [| split; [| split; [| split]]]].
+ eapply gcons_free_prim; [exact GC| exact INB| reflexivity| exact Ht].
+ intros mm RP. eapply RPrim_retag; [exact RP| exact Ht| reflexivity| reflexivity].
+ intros RC. eapply RChunks_drop; [exact RC| exact INB| exact NDL| intros e He; exact He|].
intros c' i' q NE Hq. subst G'. eapply drop_tags_retag; [exact Ht| exact NE| exact Hq].
+ intros x Hx FC. pose proof (rl_prim a LB FS G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. rewrite ?KHI_eq in PK. idtac.
assert (XB : (slot_beg RE (class_of n) i0 <= x < slot_beg RE (class_of n) i0 + class_size (class_of n)) \/ 0x2008fff7000 <= x < SH band_lo).
{ destruct Hx as [Hx|Hx]; [left; lia| right].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia.
exact (slot_band a LB FS G RE X GC _ _ _ x Ht Hx). }

assert (LIVE' : forall c' i' q, tag_at G' c' i' = Some (TLive q) -> tag_at G c' i' = Some (TLive q) /\ (class_of n <> c' \/ i0 <> i')).
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? class_of n) && (i' =? i0)) eqn:E; [discriminate|].
split; [exact Hq|]. destruct (Z.eqb_spec c' (class_of n)); [destruct (Z.eqb_spec i' i0); [discriminate| lia]| lia]. }

assert (SECB : forall e y, In e (as_reg a) -> (se_beg e + kPage <= y < se_beg e + se_size e \/ in_sh (se_beg e + kPage, se_size e - kPage) y) ->
(al_space_beg (ae_L RE) <= y < al_space_beg (ae_L RE) + 2^37 + 4096 -> False)
/\ (in_sh (slot_beg RE (class_of n) i0, class_size (class_of n)) y -> False)).
{ intros e y He Hy. pose proof (sec_facts a LB FS G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & _). unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
destruct Hy as [Hy|Hy].
- split; [lia|]. intros Hs. pose proof SH_band as ?SHBDx; pose proof (slot_band a LB FS G RE X GC _ _ _ y Ht Hs). rewrite ?KHI_eq in E2. lia.
- pose proof (sec_band a LB FS G RE X GC e y He Hy). split; [lia|]. intros Hs.
exact (in_sh_disjoint (slot_beg RE (class_of n) i0) (class_size (class_of n)) (se_beg e + kPage) (se_size e - kPage) y P3 ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q M1 E6 E2 E1 r1 e PK RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - M2 M1 D1 E6 E4 E2 E1 e PK P3 P2 P1 KP i0 n RE BAND; lia | lia ])) Hs Hy). }
destruct FC as [[[F|F] _]|[F|F]].
* destruct F as (c' & i' & t' & Ht' & Hl & F). destruct t' as [| |q|q|]; try discriminate. destruct (LIVE' _ _ _ Ht') as [HtG NE].
pose proof (slots_disjoint a LB FS G RE X GC _ _ _ _ _ _ Ht HtG NE) as D.
pose proof (slot_prim a LB FS G RE X GC _ _ _ HtG) as (P1' & P2' & P3' & _). unfold prim_hi, prim_lo in *. destruct F; cbn [fst snd] in *.
pose proof SH_band as ?SHBDx. destruct XB as [XB|XB]; [lia|]. lia.
* destruct F as (e & He & _ & F). destruct (SECB e x He (or_introl F)) as [S1 S2]. destruct XB as [XB|XB]; [exact (S1 ltac:(lia))|].
pose proof (sec_facts a LB FS G RE X GC e He) as (E1 & E2 & E3 & _). rewrite ?KHI_eq in E2. pose proof SH_band as ?SHBDx. lia.
* destruct F as (c' & i' & t' & Ht' & Hl & F). destruct t' as [| |q|q|]; try discriminate. destruct (LIVE' _ _ _ Ht') as [HtG NE].
pose proof (slots_disjoint a LB FS G RE X GC _ _ _ _ _ _ Ht HtG NE) as D.
pose proof (slot_prim a LB FS G RE X GC _ _ _ HtG) as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
pose proof SH_band as ?SHBDx; pose proof (slot_band a LB FS G RE X GC _ _ _ x HtG F).
destruct Hx as [Hx|Hx]; [lia|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia.
exact (in_sh_disjoint (slot_beg RE (class_of n) i0) (class_size (class_of n)) (slot_beg RE c' i') (class_size c') x P3 P3' ltac:(lia) ltac:(lia) D Hx F).
* destruct F as (e & He & _ & F). destruct (SECB e x He (or_intror F)) as [S1 S2]. destruct Hx as [Hx|Hx]; [exact (S1 ltac:(lia))|].
apply S2. replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros rb bt bg m' RQ AG QM'. eapply (RQuarM_free_prim a LB FS G RE X GC rb bt bg m m' _ A n RQ INB AG id0 (class_of n) i0 eq_refl eq_refl Ht HA QM').
+ intros x Hx. assert (TQ' : tag_at G' (class_of n) i0 = Some (TQuar (APrim id0 n))) by (rewrite RT, !Z.eqb_refl; reflexivity).
destruct Hx as [Hx|Hx].
* do 5 right; left. exists (class_of n), i0, (TQuar (APrim id0 n)). split; [exact TQ'|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
* do 6 right; left. exists (class_of n), i0, (TQuar (APrim id0 n)). split; [exact TQ'|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
-
subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
cbn [chunk_cont] in EC. injection EC as Elo Ehi. subst lo hi.
pose proof (sec_facts a LB FS G RE X GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5) as [M1 M2]. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
exists G. split; [| split; [| split; [| split; [| split]]]].
+ eapply gcons_free_sec; [exact GC| exact INB| reflexivity].
+ intros mm RP; exact RP.
+ intros RC. eapply RChunks_drop; [exact RC| exact INB| exact NDL| intros e' He'; exact He'| intros c' i' q NE Hq; exact Hq].
+ intros x Hx FC. pose proof (rl_prim a LB FS G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. unfold KHI in PK, E2. idtac.
assert (XB : (mb0 + kPage <= x < mb0 + sec_map_size n) \/ 2147446784 <= x < 17594333495296).
{ destruct Hx as [Hx|Hx]; [left; lia| right]. replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia.
exact (sec_band a LB FS G RE X GC _ x He Hx). }

assert (OTHER : forall e, In e (as_reg a) -> sec_live (alb_remove (ASec mb0 n) LB) e -> e <> mkSec mb0 (sec_map_size n) n /\ (se_beg e + se_size e <= mb0 \/ mb0 + sec_map_size n <= se_beg e)).
{ intros e He' (A2 & HL). apply In_alb_remove in HL as [HL NE]. cbn [ablk_id fst] in NE.
assert (NEe : e <> mkSec mb0 (sec_map_size n) n) by (intros ->; apply NE; reflexivity). split; [exact NEe|].
destruct (decide (se_beg e = mb0)) as [EQ|NEb].
- exfalso. apply NEe. exact (NoDup_map_In_inj se_beg (as_reg a) e (mkSec mb0 (sec_map_size n) n) (gc_sec_nodup a LB FS G RE X GC) He' He EQ).
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e (mkSec mb0 (sec_map_size n) n) (gc_sec_disj a LB FS G RE X GC) He' He
ltac:(cbn; intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd se_beg se_size] in D. lia. }
destruct FC as [[[F|F] _]|[F|F]].
* destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_prim a LB FS G RE X GC _ _ _ Ht') as (P1' & P2' & P3' & _). unfold prim_hi, prim_lo in *.
destruct F; cbn [fst snd] in *. pose proof SH_band as ?SHBDx. destruct XB as [XB|XB]; lia.
* destruct F as (e & He' & HL & F). destruct (OTHER e He' HL) as [_ D]. pose proof (sec_facts a LB FS G RE X GC e He') as (E1' & E2' & E3' & _). rewrite ?KHI_eq in E2'.
pose proof SH_band as ?SHBDx. destruct XB as [XB|XB]; (first [ clear - E2' D XB F e x M2 E1 KP mb0 n BAND M1 E6; lia | lia ]).
* destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_prim a LB FS G RE X GC _ _ _ Ht') as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
pose proof SH_band as ?SHBDx; pose proof (slot_band a LB FS G RE X GC _ _ _ x Ht' F). destruct Hx as [Hx|Hx]; [(first [ clear - H SHBDx P3' P1' PK i' c' Hx x M1 E6 E2 KP mb0 n RE BAND; lia | lia ])|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia.
exact (in_sh_disjoint (mb0 + kPage) (sec_map_size n - kPage) (slot_beg RE c' i') (class_size c') x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H15 q2 H1 H0 r q H SHBDx PK x M1 E6 E2 E1 r2 KP mb0 n RE BAND; lia | lia ])) P3' ltac:(lia) ltac:(lia) ltac:((first [ clear - H SHBDx P3' P2' P1' PK i' c' x M2 M1 D1 E6 E2 E1 KP mb0 n RE BAND; lia | lia ])) Hx F).
* destruct F as (e & He' & HL & F). destruct (OTHER e He' HL) as [_ D]. pose proof (sec_facts a LB FS G RE X GC e He') as (E1' & E2' & E3' & E4' & E5' & E6' & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5') as [M1' M2']. rewrite <- E4' in M1'.
pose proof (sec_band a LB FS G RE X GC e x He' F). destruct Hx as [Hx|Hx]; [(first [ clear - H M2' M1' E6' E4' E2' D PK e Hx x M2 M1 E6 E2 KP mb0 n RE BAND; lia | lia ])|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia.
exact (in_sh_disjoint (mb0 + kPage) (sec_map_size n - kPage) (se_beg e + kPage) (se_size e - kPage) x
ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H20 q3 H1 H0 r q H PK x M1 E6 E2 E1 r3 KP mb0 n RE BAND; lia | lia ])) ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q M1' E6' E1' r1 e BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - H M2' M1' E6' E4' E2' E1' D PK e x M2 M1 E6 E2 E1 KP mb0 n RE BAND; lia | lia ])) Hx F).
+ intros rb bt bg m' RQ AG QM'. eapply (RQuarM_free_sec a LB FS G RE X GC rb bt bg m m' _ A n RQ INB AG mb0 eq_refl He HA QM').
+ assert (NL : ~ sec_live (alb_remove (ASec mb0 n) LB) (mkSec mb0 (sec_map_size n) n)).
{ intros (A' & HL). cbn [se_beg se_req] in HL. apply In_alb_remove in HL as [_ NE]. apply NE. reflexivity. }
intros x [Hx|Hx].
* do 7 right; left. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size se_req]. split; [exact He|]. split; [exact NL|]. lia.
* do 8 right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size se_req]. split; [exact He|]. split; [exact NL|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
Qed.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis recycle_spec : recycle_stmt C RE X L.
Hypothesis HRD : ac_RDepot C = RDepot.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Lemma dealloc_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A n lo : Z)
(obj sz bp dn : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> In (p, A, n) LB0 -> qroom a p -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - DEALLOC_STACK ->
rw_cells asegs m obj (unw_obj obj sz [q0; q1; q2; q3; q4] rest bp) ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 2080 < 2^64 ->
aimplT atn (asan_free (ae_L RE) a p) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB0) FS0 lo m free_step)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A) (wz obj) (wz 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_free_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros QR INB QRM MI ST CEIL LO OBJ SZB DNH DCAP OLO OHI.
pose proof CEIL as CEIL'. idtac. unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
change (2^64) with 18446744073709551616 in OHI.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB) as HN2.

pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC INB) as CR.
assert (PC0 : exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & _ & _ & NPd & _). unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & _ & _ & BPd & _). unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [cbn [chunk_cont]; rewrite HA; f_equal; lia|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2.
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (APrim id0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [left; exists (class_of n), i0, (TLive (APrim id0 n)); split; [exact Ht|]; split; [reflexivity| split; cbn [fst snd]; lia]|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (APrim id0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; lia.
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; left. exists (class_of n), i0, (TLive (APrim id0 n)). split; [exact Ht|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
pose proof (sec_facts _ _ _ _ _ _ GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
assert (LIVE : sec_live LB0 (mkSec mb0 (sec_map_size n) n)) by (exists A; exact INB).
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (ASec mb0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [right; exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]; auto|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (ASec mb0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; (first [ clear - CT HA' i' c' Hbx nb Ab x E1 HA0 KU mb0 ks A RE BAND; lia | lia ]).
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]. split; [exact He|]. split; [exact LIVE|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. (first [ clear - Db Dn D Hx x E1 BPd NPd PK TD TK KP mb0 ks n X RE BAND; lia | lia ]). }
destruct PC0 as (plo & phi & CM & En & Hn0 & ECONT & PZ & PZS & PT3).
assert (PTT : phi <= rl_T X \/ rl_T X + 4096 <= plo).
{ pose proof CM as CM0. destruct CM0 as (_ & _ & _ & _ & _ & PU). destruct PU as (_ & _ & _ & P4 & _ & P6 & _).
pose proof (used_size_pos n ltac:(lia)) as [U1 _]. pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as RU0.
destruct (Z.le_gt_cases phi (rl_T X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_T X + 4096) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj1 (PT3 (Z.max plo (rl_T X)) ltac:(lia))). lia. }
destruct (free_switch a LB0 FS0 G RE X m p A n plo phi GC INB CR ECONT) as (G' & GC' & RPG & RCG & NFC & RQG & QZ').
pose proof (qchunk_geom m plo phi A n) as QG.
clear QG.
destruct CM as (LEFT & (b1 & idw & Hb1 & HDR) & WR & JUNK & SHD & PURE). unfold hdr_cells in HDR. hide SHD.
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). rewrite ?KHI_eq in M8. idtac.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2]. set (u := used_size n) in *.
pose proof (round_up_ge u 8 ltac:(lia)) as RU.
pose proof (ngran_eq u ltac:(lia)) as (NG1 & NG2 & NG3).
assert (AH : 0x647000 <= A).
{ destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn' & HP' & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn' & HP' & He0 & HA0)].
- pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht0) as (P1 & _). pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKx & _).
pose proof (rz_size_range n) as [RZx _]. unfold prim_user in HA0. unfold prim_lo, KHI in *. clear - P1 PKx HA0 RZx. lia.
- pose proof (sec_facts _ _ _ _ _ _ GC _ He0) as (_ & E2x & _ & _ & E5x & _). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5x) as [G1x _]. pose proof (sec_req_facts n ltac:(lia) E5x) as [_ RQx].
unfold kSecUserOff in HA0. clear - E2x G1x RQx HA0. lia. }

assert (JALL : hjunk m A phi).
{ pose proof (wr_at_hjunk _ _ _ WR ltac:(lia)) as (_ & _ & W1). destruct JUNK as (_ & J2 & J3).
split; [lia|]. split; [lia|]. intros x Hx. destruct (Z.lt_ge_cases x (A + u)); [apply W1; lia| apply J3; lia]. }
destruct (hjunk_split _ A (A + 8) phi JALL ltac:(lia)) as [J8 _]. destruct (hjunk_C8 _ A J8) as [w0 JC]. hide JALL.
destruct (RStats_free_words _ _ _ RS) as (f1 & f2 & STC).
unfold unw_obj in OBJ. cbn [map app] in OBJ.
replace (A - 16) with (A + -16) in HDR by lia.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] m) as MU.
pose proof (wmono_refl asegs m) as WM.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] -> lo' <= x < hi' ->
(band_lo <= x < bv_unsigned sp) \/ (plo <= x < phi) \/ (rl_T X + 2824 <= x < rl_T X + 2840)).
{ intros lo' hi' x Hin Hx. cbn in Hin. pose proof (qchunk_geom m plo phi A n) as XX || idtac.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; [left; lia| left; lia| right; left; lia| right; left; (first [ clear - Hx x AH NG3 NG1 RU U1 M6 M4 u phi plo ks n A BAND; lia | lia ])| right; right; lia]. }
assert (RTW : Forall (rt_avoid RE X) [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ apply List.Forall_forall. intros [lo' hi'] Hin x Hx FT. cbn [fst snd] in Hx.
destruct (WCASE lo' hi' x Hin Hx) as [Z|[Z|Z]].
- pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(left; exact FT)). lia.
- destruct (PZ x Z) as [LU|FC]; [exact (fp_RTconst_cz a LB0 FS0 G RE X GC x FT ltac:(do 2 right; left; exact LU))| exact (fpC_excl a LB0 FS0 G RE X GC x FC (or_introl FT))].
- exact (rt_avoid_Thigh RE X (rl_T X + 2824) (rl_T X + 2840) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT). }
assert (STW : Forall st_avoid [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ repeat apply Forall_cons; try apply Forall_nil; st_avoid_solve. }

assert (QO1 : QOTH C a (alb_remove p LB0) FS0 G' RE X m).
{ apply QOTH_split. split; [exact RT|]. split; [exact RS|]. split; [exact (RPG m RP)|].
split; [exact (RCG RC)|]. split; [| split; [rewrite HRD; exact RD| exact RF]].
eapply HRSx; [exact RSE| reflexivity| reflexivity| reflexivity|].
intros e He (A' & HA'). exists A'. apply In_alb_remove in HA' as [HA' _]. exact HA'. }
unfold asan_free_entry, A_INSTANCE in *.
apply aimplT_from_evt.
do 10 step.
carve_frame 64%nat ST.
do 9 step.
step. unfold_cond; cond_unsig; if_false.
do 7 step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (run_free_hooks_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT2.
step. if_true.

assert (AL16 : (A + -16) mod 16 = 0) by (Z.div_mod_to_equations; (first [ clear - H29 q10 H0 H r q AH U1 RU r0 M6 M4 M2 r5 u phi plo ks A p BAND; lia | lia ])).
assert (HK16 : 0x647000 <= A + -16) by (rewrite ?KHI_eq; (first [ clear - AH U1 RU NG1 NG3 M6 M5 M4 M2 PURE u phi plo ks A p BAND; lia | lia ])).
assert (HC16 : A + -16 + 16 <= band_lo) by (idtac; lia).
call_ch (cas_free_hdr) ltac:(fun PO => idtac); try eassumption; try lia.
rename POST into HDR3.
assert (LB1 : Z.land b1 3 = 1) by (destruct Hb1 as [-> | ->]; reflexivity).
assert (B1R : 0 <= b1 < 256) by (first [ clear - HK16 AH U1 RU M6 M5 M4 u Hb1 b1 phi plo ks A p BAND; lia | lia ]).
step. step.
stf.
step.
rewrite zxb_b8, (Z.mod_small b1 256) by lia.
step.
rewrite (unsigned_lit b1), LB1 by lia.
step. if_false.
step. lits.
step.
step. if_true.

step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (get_thread_stats_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT4.
assert (UB : u <= 2^26 + 1) by (subst u; unfold used_size; lia).
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step. step.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
step. step.
do 4 step.
do 8 step.
step. step.
lazymatch goal with ST' : stk _ _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp); rename ST' into STF end.
apply evt_done.

unfold asan_free. rewrite (proj2 (Z.ltb_ge kQMaxSize (aptr_used p))) by (unfold aptr_used; lia).
replace (wz (A + -16)) with (wz (A - 16)) by (f_equal; lia).
unhide SHD. unhide JALL.
lazymatch type of MU with munch ?W m ?mf =>

assert (WZ' : forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> wzone a (alb_remove p LB0) G' RE X (bv_unsigned sp) z);
[ intros lo' hi' z Hin Hx; unfold wzone; destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]];
[ do 3 right; exact Z
| left; apply QZ'; left; exact Z
| right; right; left; left; split; cbn [fst snd]; lia ]
| ];
assert (QO2 : QOTH C a (alb_remove p LB0) FS0 G' RE X mf);
[ apply QOTH_split in QO1 as (_ & _ & RP1 & QRE1); apply QOTH_split;
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]|];
split; [eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]|];
split;
[ eapply RPrim_frame; [exact RP1| exact WM|]; eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx); lia
| exact (fpQ_RPrim a (alb_remove p LB0) FS0 G' RE X GC' z (QZ' z (or_introl Z)) Fx)
| refine (fpP_RStats a (alb_remove p LB0) FS0 G' RE X GC' z Fx _); left; split; cbn [fst snd]; lia ]
| eapply QREST_munch; [exact GC'| exact QRE1| exact MU| exact WM|]; intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy) ]
| ];

assert (AGQ : agree_on asegs (fp_RQuar a LB0 G RE X) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia))
| destruct (PZ z Z) as [LU|FC]; [exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(do 2 right; left; exact LU))| exact (fpQ_RChunks a LB0 FS0 G RE X GC z Fx FC)]
| refine (fpQ_RStats a LB0 FS0 G RE X GC z Fx _); left; split; cbn [fst snd]; lia ]
| ];
assert (AGlow : agree_on asegs (fun z => 2147446784 <= z < 17594333495296) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| (first [ clear - Z Hz z AH U1 RU NG1 NG3 M8 M6 M5 M4 PURE phi plo u ks A p BAND; lia | lia ])| (first [ clear - Z Hz z HK16 AH U1 RU M6 M5 M4 M1 phi plo PK TK u ks A p X RE BAND; lia | lia ])]
| ];
assert (AGlr : agree_on asegs (fun z => plo <= z < A + -16) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| | (first [ clear - Z Hz z HK16 AH U1 RU M8 M6 M5 M4 PTT PURE phi plo PK TK u ks A p X RE BAND; lia | lia ])];
cbn in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Hy Hz z HC16 AH U1 RU M6 M4 phi plo CEIL' u LO ks lo A p sp BAND Z HK16 M8 M5 PTT PURE PK TK X RE; lia | lia ])
| ];
assert (QM : qchunk_mem mf plo phi A (aptr_req p));
[ split; [| split; [| split; [| split]]];
[ intros Hrz; destruct (LEFT Hrz) as [LC LJ]; split; [| eapply hjunk_wmono; [exact LJ| exact WM]];
eapply rw_cells_agree; [exact AGlr| exact LC|]; intros z Hz; cbn [cells_size csize Nat.add] in Hz; (first [ clear - Hz z Hrz HK16 AH U1 RU NG1 NG3 M6 M5 M4 M2 M1 phi plo u ks A p BAND; lia | lia ])
| exists b1, idw; split; [exact Hb1| exact HDR3]
| eapply hjunk_wmono; [exact JALL| exact WM]
| exists (ush u); eapply rw_cells_agree; [exact AGlow| exact SHD|]; intros z Hz; cbn [cells_size csize] in Hz; change (used_size (aptr_req p)) with u in Hz;
rewrite !Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id in Hz by (Z.div_mod_to_equations; (first [ clear - H34 q11 H29 q10 H0 H r Hz z HK16 U1 RU r1 M8 M6 M4 M2 M1 q5 q PURE r6 r5 r4 r3 phi plo u ks A p BAND NG2 H19 q8 NG1 q6 NG3 M5; lia | lia ])); unfold SH, A_SHADOW_OFS in Hz; cbn beta; Z.div_mod_to_equations; (first [ clear - H39 q12 H10 H9 r1 H5 H4 r0 H0 H r Hz q z HK16 U1 RU r2 NG3 M9 M8 M6 M4 M1 q6 q5 PURE r7 r6 r5 r4 phi plo TB u ks A p X BAND; lia | lia ])
| exact PURE ]
| ];
pose proof (RQG 0 QB QB mf RQ AGQ QM) as RQ2;
assert (QR2 : QRUN C 0 QB QB [(p, A)] a (alb_remove p LB0) FS0 G' RE X mf) by (split; [exact GC'| split; [exact QO2| exact RQ2]])
end.
eapply aimplT_mono.
{ eapply (qchunk_spec C L RE X HRD); [exact QR2| eassumption| exact STF| exact CEIL'| unfold QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia| lia
| exact QRM| exact OBJ| exact SZB| eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); [intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)| exact DNH]
| exact DCAP| exact OLO| change (2^64) with 18446744073709551616; lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO |- *.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
do 15 eexists. exists m5, G5. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [| split; [| exact QR5]].
2:{
destruct DS5 as [DS5 ES5]. split; [eapply depot_keep_step; [| exact DS5]; eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)|].
eapply errno_keep_trans; [| exact ES5]. eapply (errno_keep_of_ezone _ _ _ _ RE X m _ _ GC' MU WM). intros lo' hi' z Hin Hy. unfold ezone.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [do 5 right; lia| left; apply QZ'; left; exact Z| right; right; left; unfold in_iv; cbn [fst snd]; lia]. }
eapply aheap_presA_trans; [| exact AP5].
eapply aheap_presA_of_munch_w; [exact GC'| apply Permutation_refl| apply Permutation_refl| lia| exact MU| exact WM| exact WZ'].
Qed.
End S.
