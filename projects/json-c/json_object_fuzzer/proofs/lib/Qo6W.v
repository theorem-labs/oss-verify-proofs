(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QvDJ QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QqLk QmP7 QpY2 Q9Ho QYyZ Qu3b QkfD QEEn QQ8H Qx6U QsDw QcA6 QmvA QpME QVo2 QRfV QnRU QEYd QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq2 QqLk QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 Qu3b.Mq2 QYyZ.Mq5 QkfD QYyZ.Mq3 QEEn.Mq0 QQ8H.Mq2 Qx6U.Mq2 QsDw.Mq0 QcA6.Mq0 QmvA.Mq1 QpME.Mq6.
Import QVo2.Mq1.
Import QRfV.Mq0 QnRU.Mq9 QnRU.Mq1 QEYd Qx6U.Mq3 QcA6.Mq2 Qx6U.Mq1.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma calloc_W_sec_lz {BAND : Band} : forall a LB FS G RE X bp mb msz lo hi x,
gcons a LB FS G RE X -> band_lo <= bp - CALLOC_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo, hi) (calloc_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo <= x < hi -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo hi x GC CSP MSZ MB8 Hin Hx. unfold CALLOC_STACK, ALLOC_STACK in CSP.
unfold calloc_W_sec, CALLOC_STACK, ALLOC_STACK in Hin. cbn [app In] in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. do 3 right; left. lia.
- destruct (malloc_W_sec_lz a LB FS G RE X (bp - 48) mb msz lo hi x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8
ltac:(unfold malloc_W_sec, MALLOC_STACK; cbn [app In]; right; replace (bp - 48 - 2144) with (bp - 2192) by lia; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]];
unfold lz; [tauto| tauto| tauto| do 3 right; left; lia| tauto].
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

Lemma calloc_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (cnt sz lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_calloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 ->
from_primary (cnt * sz) = false ->
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
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
set (n := cnt * sz) in *. assert (Hn : 0 <= n <= 2^26) by (subst n; nia).
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (calloc_icpt_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo cnt sz dn GC R1 R2 R5 R7 MI ST CEIL' ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP Hcnt Hsz Hle HP) as M.
rewrite Z_to_bv_bv_unsigned in M. fold n in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold calloc_post_sec in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
destruct r as [p|].
- destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MU & RSE' & CM & UZ).
pose proof (sec_geom_facts n Hn HP) as (GN & _ & _ & _ & Gnd1 & Gssz & _ & GM1 & _).
destruct (lift_sec_some C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 aa n mb m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 Hn HP ltac:(idtac; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (calloc_W_sec_lz (ps_a s) LB0 FS0 G RE X); [exact GC| idtac; unfold CALLOC_STACK, ALLOC_STACK; lia| lia| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT' RS' RD' RSE' CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (mb + kSecUserOff). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UZ| exact HP4].
- destruct REST as (-> & -> & MU & RSE').
destruct (lift_sec_none C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 ltac:(idtac; lia) MU WM
ltac:(intros lo' hi' x Hin Hx; destruct (calloc_W_sec_lz (ps_a s) LB0 FS0 G RE X (bv_unsigned sp) 0 0 lo' hi' x GC ltac:(idtac; unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]];
[first [clear - Z; tauto| tauto]| first [clear - Z; tauto| tauto]| first [clear - Z; tauto| tauto]| first [clear - Z; tauto| tauto]| exfalso; destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia| change (0 / 8) with 0 in Z2; lia]])
RT' RS' RD' RSE') as [HP1 HP3].
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5 QUnM QkZz QteI QcfN Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QNQk.Mq2 QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QpY2.Mq3 QqLk QnRU.Mqa Q9Ho.Mq2 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1 QmvA.Mq0 QYyZ.Mq3.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QnRU.Mq8 QmvA.Mq3 QkZz.Mq1 QteI.Mq9 QQ8H.Mq3 Qx6U.Mq4 QcA6.Mq1.
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
Local Notation mem := (word -> option byte) (only parsing).

Definition free_icpt_entry : Z := 0x632d8.

Definition FREE_STACK : Z := 2128 + DEALLOC_STACK.

Lemma raw_free_A_intro atn L p s (Q : unit -> PStateA -> machine_state -> Prop) ms :
aimplT atn (asan_free L (ps_a s) p) s (fun a' s1 ms' => Q tt (set_a a' s1) ms') ms ->
@implMG PStateA asegs atn unit (raw_free_A L p) s Q ms.
Proof.
intros H. unfold raw_free_A.
eapply implMG_bind with (Q1 := fun x s' ms' => x = s /\ s' = s /\ ms' = ms).
{ apply implMG_get. apply evt_done. repeat split; reflexivity. }
intros x s' ms' (-> & -> & ->).
eapply implMG_bind. { apply aimplT_state in H. exact H. }
intros a' s1 ms1 [-> HQ]. cbn in HQ.
apply implMG_upd. apply evt_done. exact HQ.
Qed.

Definition ia_zone (x : Z) : Prop := IA <= x < 0x171d38 \/ IA_FLAG <= x < IA_FLAG + 4.

Lemma RQuarM_refresh_ia {BAND : Band} : forall a LB0 FS0 G RE X rb bt bg m m',
gcons a LB0 FS0 G RE X -> RQuarM rb bt bg [] a LB0 G RE X m ->
agree_on asegs (fun x => fp_RQuar a LB0 G RE X x /\ ~ ia_zone x) m m' -> ia_inv m' ->
RQuarM rb bt bg [] a LB0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X rb bt bg m m' GC (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND) AG HI'.
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC. rewrite ?KHI_eq in PK.
pose proof (rlay_obj_facts RE X _ (gc_rlay _ _ _ _ _ _ GC) (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK. rewrite ?KHI_eq in TK.
exists JT, JG, QA. unfold ia_zone, IA, IA_FLAG in AG.
assert (SLOT : forall c j t x, tag_at G c j = Some t -> tag_quar t = true -> in_iv (slot_beg RE c j, class_size c) x ->
fp_RQuar a LB0 G RE X x /\ ~ (986368 <= x < 1514808 \/ 1570184 <= x < 1570184 + 4)).
{ intros c j t x Ht Hq Hx. pose proof (qslot_facts a LB0 FS0 G RE X GC c j t Ht) as (P1 & _). unfold prim_lo in P1. destruct Hx as [Hx1 Hx2]; cbn [fst snd] in Hx1, Hx2.
split; [do 5 right; left; exists c, j, t; split; [exact Ht| split; [exact Hq| split; cbn [fst snd]; lia]]| lia]. }
assert (SLOTS : forall c j t x, tag_at G c j = Some t -> tag_quar t = true -> in_sh (slot_beg RE c j, class_size c) x ->
fp_RQuar a LB0 G RE X x /\ ~ (986368 <= x < 1514808 \/ 1570184 <= x < 1570184 + 4)).
{ intros c j t x Ht Hq Hx. pose proof SH_band as ?SHBDx; pose proof (slot_band a LB0 FS0 G RE X GC c j t x Ht Hx).
split; [do 6 right; left; exists c, j, t; auto| lia]. }
assert (QREP : forall C q J, (forall x, C <= x < C + 32 -> fp_RQuar a LB0 G RE X x /\ ~ (986368 <= x < 1514808 \/ 1570184 <= x < 1570184 + 4)) ->
qrep RE G m QA C q J -> qrep RE G m' QA C q J).
{ intros C q J HC R. pose proof R as (_ & _ & R3 & _). eapply qrep_agree; [exact AG| exact R| exact HC| |].
- intros j x Hj Hx. eapply SLOT; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)| reflexivity| exact Hx].
- intros j x Hj Hx. eapply SLOTS; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)| reflexivity| exact Hx]. }
split; [apply QREP; [| exact HT]; intros x Hx; unfold TQ in Hx; split; [left; split; cbn [fst snd]; lia| lia]|].
split; [apply QREP; [| exact HG]; intros x Hx; unfold GQ, A_INSTANCE in Hx; split; [right; right; left; unfold A_INSTANCE; split; cbn [fst snd]; lia| lia]|].
split; [eapply rw_cells_agree; [exact AG| exact HM|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold QMUT, A_INSTANCE in Hx;
split; [right; right; left; unfold A_INSTANCE; split; cbn [fst snd]; lia| lia]|].
split; [exact HI'|].
split; [exact ND|]. split; [exact TQO|]. split; [exact C24|]. split; [exact NDP|]. split; [| split; [exact TQP| split; [exact PQA| exact BND]]].
intros p Hp. pose proof (REP p Hp) as R. destruct p as [id n|mb n]; cbn [qptr_rep] in R |- *.
- destruct R as (i & Ht & Hpr & HQA & QM). exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|].
eapply qchunk_mem_agree; [exact AG| exact QM| |].
+ intros x Hx. eapply SLOT; [exact Ht| reflexivity|]. split; cbn [fst snd]; lia.
+ intros x Hx. eapply SLOTS; [exact Ht| reflexivity|]. split; cbn [fst snd]; [lia|].
replace (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) with (class_size (class_of n)) in Hx by lia. lia.
- destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|].
pose proof (qsec_facts a LB0 FS0 G RE X GC _ Hin) as (_ & E2 & _). cbn [se_beg se_size] in E2. rewrite ?KHI_eq in E2.
eapply qchunk_mem_agree; [exact AG| exact QM| |].
+ intros x Hx. split; [| pose proof kconsts as (_ & _ & _ & _ & KP & _); lia]. do 7 right; left. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. auto.
+ intros x Hx. pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin) as SB. cbn [se_beg se_size] in SB.
split; [| specialize (SB ltac:(replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia; exact Hx)); lia].
do 8 right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. split; [exact Hin|]. split; [exact Hnl|].
replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
Qed.

Definition free_pre_W (bp T : Z) : list (Z * Z) :=
[(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (IA_FLAG, IA_FLAG + 4); (IA, IA + 8); (IA_MAP1, IA_MAP1 + 262144); (0x0130d40, 0x171d30); (T + 3168, T + 3169)].

Definition free_pre_post {BAND : Band} (RE : aentry) (X : rlay) (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo A : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 : word) (m' : mem) (sz : Z) (q0 q1 q2 q3 q4 : word) (rest junk8 : list byte),
ms' = MS (mkR (wz 0x63480) (wz (bp + -2128)) gp (wz A_TP) t0 t1 t2 (wz bp) (wz A) (wz A) (wz (bp + -2128)) (wz 1) a3 a4 a5 a6 a7
s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz asan_free_entry) fc None m' (seg_rom asegs)
/\ munch (free_pre_W bp (rl_T X)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bp + -2128)
/\ rw_cells asegs m' (bp + -2128) (unw_obj (bp + -2128) sz [q0; q1; q2; q3; q4] rest bp)
/\ 1 <= sz <= 30
/\ rw_cells asegs m' (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ RTconst RE X m' /\ ia_inv m' /\ rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)].

Lemma rw_cells_join : forall m A B cs1 cs2,
rw_cells asegs m A cs1 -> rw_cells asegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app asegs m A cs1 cs2)). split; assumption. Qed.

Ltac zofn H := repeat match type of H with context [Z.of_nat ?n] =>
lazymatch n with S _ => idtac | O => idtac end; let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end.

Section Pre.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma free_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z),
RTconst RE X m -> rlay_ok RE X -> ia_inv m -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - 2128 - 144 -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= A < 2^47 ->
evt asegs (free_pre_post RE X ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x632c4) fc None m (seg_rom asegs)).
Proof.
intros until A; intros RT RL IAI TU MI ST CEIL LO BPR UNW HA.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in BPR. change (2^47) with 140737488355328 in HA.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (free_pre_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1 in MU.
pose proof (munch_refl [(bp - 2128, bp)] m) as MU2.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128);
(1570184, 1570184 + 4); (986368, 986368 + 8); (986376, 986376 + 262144); (0x0130d40, 0x171d30); (rl_T X + 3168, rl_T X + 3169)]).
{ pose proof (@ia_W_rt BAND RE X (bp - 2128) ltac:(unfold INTALLOC_STACK; lia) RL) as FW. unfold ia_W, IA_FLAG, IA, IA_MAP1, INTALLOC_STACK in FW.
inversion FW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; subst.
constructor; [exact (rt_avoid_stack RE X RL (bp - 2128) bp ltac:(lia))|]. constructor; [exact (rt_avoid_stack RE X RL (bp - 2128 - 144) (bp - 2128) ltac:(lia))|].
constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R4|]. constructor; [exact R5|].
constructor; [exact (rt_avoid_Thigh RE X (rl_T X + 3168) (rl_T X + 3169) RL ltac:(lia) ltac:(lia))| constructor]. }
unfold A_INSTANCE in *.
step.
carve_frame 2032%nat ST.
do 8 step.
step.
step.
carve_frame 96%nat ST.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]);
assert (IA1 : ia_inv mc) by (eapply (ia_inv_agree (fun x => 0x10000 <= x < 0x645000)); [| exact IAI| intros x Hx; unfold IA, IA_FLAG in Hx; cbn beta; lia];
eapply agree_on_of_munch; [exact MU2| exact WM|]; intros x Hx _; cbn [outside]; lia)
end.
clear MU2.
call_ch (intalloc_spec RE X) ltac:(fun PO => unfold ia_W, INTALLOC_STACK, IA_FLAG, IA, IA_MAP1 in PO; rewrite !(unsigned_lit (bp + -2128)) in PO by lia);
try eassumption; try (rewrite ?unsigned_lit by lia; first [eassumption| unfold INTALLOC_STACK; lia]).
subst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with H : RTconst RE X mc |- _ => rename H into RT2 end;
lazymatch goal with H : ia_inv mc |- _ => rename H into IA2 end;
pose proof (munch_refl [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (rl_T X + 3168, rl_T X + 3169)] mc) as MU3;
pose proof (wmono_refl asegs mc) as WM3 end.

step.
rewrite (unsigned_lit A) by lia. rewrite (Z.shiftr_div_pow2 A 47) by lia. rewrite (Z.div_small A (2^47)) by (change (2^47) with 140737488355328; lia).
step. if_lit.
step.
rewrite (unsigned_lit A) by lia. rewrite (Z.shiftr_div_pow2 A 32) by lia. change (2^32) with 4294967296.
assert (QH : 0 <= A / 4294967296 < 32768) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
step.
rewrite (unsigned_lit (A / 4294967296)) by lia. rewrite (Z.shiftl_mul_pow2 (A / 4294967296) 3) by lia. change (2^3) with 8.
step.
pose proof IA2 as (b0 & FL & B01 & ZMAP & ZR). unfold IA_MAP1 in ZMAP.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (wa (986376 + (A / 4294967296 * 8))) 8 = Some (le8 (wz 0)))
by (eapply zbytes_load8; [exact ZMAP| lia| lia]) end.
step.
clear HR b0 FL B01 ZMAP ZR.
step.
step. if_lit.

do 5 step.
stf.
step.
stf.
step.
call0 (malloc_ctx_size_spec RE X). { eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]. } { assumption. }
subst.
step. step. if_lit.
step.
call0 (get_current_pc_spec). subst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
step. lits.
clear K19 K15.
step.
step.
call0 (malloc_ctx_size_spec RE X). { exact RT3. } { assumption. }
subst.
step.
step. lits.
step. lits.
step.
rewrite (unsigned_lit bp), land_ones64 by lia.
step.
step.
step. if_lit.
do 6 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (proj1 (rw_cells_app asegs mc (bp + -2128) [C8 (wz (bp + -2112))] _)) in FR0 as [OBT FR0];
apply (proj1 (rw_cells_app asegs mc _ [C8 (wz 0)] _)) in FR0 as [OBZ OB80];
cbn [cells_size csize Nat.add] in OBZ, OB80; zofn OBZ; zofn OB80;
apply (proj1 (rw_cells_app asegs mc (bp + -2032) [CB 1960 _] _)) in FR as [OB1960 FR];
apply (proj1 (rw_cells_app asegs mc _ [C8 (wz bp)] _)) in FR as [OBP FRS];
cbn [cells_size csize Nat.add] in OBP, FRS; zofn OBP; zofn FRS;
replace (bp + -2032 + 1960 + 8) with (bp + -64) in FRS by lia;
pose proof (cells_hjunk _ _ _ OB80 ltac:(lia)) as J1; pose proof (cells_hjunk _ _ _ OB1960 ltac:(lia)) as J2;
cbn [cells_size csize Nat.add] in J1, J2; zofn J1; zofn J2;
replace (bp + -2128 + 8 + 8) with (bp + -2112) in J1, OB80 by lia; replace (bp + -2112 + 80) with (bp + -2032) in J1 by lia;
pose proof (hjunk_merge _ _ _ _ J1 J2) as J; clear J1 J2 OB80 OB1960;
destruct (hjunk_split _ _ (bp + -2072) _ J ltac:(lia)) as [JQ JR]; clear J;
replace (bp + -2072) with (bp + -2112 + 40) in JQ by lia;
destruct (hjunk_C8x5 _ _ JQ) as (q0 & q1 & q2 & q3 & q4 & OBQ); clear JQ;
destruct (hjunk_cells _ (bp + -2072) 2000%nat ltac:(replace (bp + -2072 + Z.of_nat 2000) with (bp + -2032 + 1960) by (change (Z.of_nat 2000) with 2000; lia); exact JR))
as (rest & OBR); clear JR;
recast OBZ [C4 (wz 0); C4 (wz 0)];
pose proof (rw_cells_join _ _ _ _ _ OBR OBP ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as O4;
pose proof (rw_cells_join _ _ _ _ _ OBQ O4 ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as O3;
pose proof (rw_cells_join _ _ _ _ _ OBZ O3 ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as O2;
pose proof (rw_cells_join _ _ _ _ _ OBT O2 ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as OBJ;
cbn [app] in OBJ; clear O4 O3 O2 OBR OBP OBQ OBZ OBT;
replace (bp + -2112) with (bp + -2128 + 16) in OBJ by lia;
change (rw_cells asegs mc (bp + -2128) (unw_obj (bp + -2128) 0 [q0; q1; q2; q3; q4] rest bp)) in OBJ;

pose proof FRS as FRS';
apply (proj1 (rw_cells_app asegs mc (bp + -64) [CB 8 _; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])) in FRS' as [_ REC];
cbn [cells_size csize Nat.add] in REC; zofn REC; replace (bp + -64 + 48) with (bp - 16) in REC by lia;

assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]);
assert (URD : unw_readable asegs RE mc (bp - 16))
by (eapply (unw_readable_prologue RE _ m mc bp s0 ra); [exact MU| intros y Hy; cbn [outside]; lia| exact REC| exact UNW]);
clear REC
end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ST' : stk asegs mc lo (bv_unsigned (wz (bp + -2128)))) by (rewrite unsigned_lit by lia; exact PC);
assert (LO' : lo <= bv_unsigned (wz (bp + -2128)) - unwind_stack) by (rewrite unsigned_lit by lia; unfold unwind_stack; lia);
assert (OLO' : bv_unsigned (wz (bp + -2128)) <= bp + -2128) by (rewrite unsigned_lit by lia; lia);
assert (MI' : mem_inv asegs mc) by assumption
end.
eapply evt_cut.
{ eapply (unwind_impl_spec RE X);
[exact RT4| exact RL| exact MI'| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact TU| exact URD| lia
| exact OLO'| lia| lia]. }
clear ST' LO' OLO' MI'.
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MUd & WMd & MId & STd
& sz & q & rest' & OBJ3 & LQ & TU3 & SZB & RT5).
unfold unwind_stack in MUd. rewrite !(unsigned_lit (bp + -2128)) in MUd, STd by lia.
clear OBJ TU URD RT4.
lazymatch type of MUd with munch _ ?mx _ =>
apply (munch_chain' _ mx m3 _ m MUd) in MU; [| sub_fp_solve];
apply (munch_chain' _ mx m3 _ _ MUd) in MU3; [| sub_fp_solve];
transport_after_call asegs mx m3 MUd WMd; clear MUd WMd end.
replace (ret_pc (wz 406636)) with (wz 406636) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

step. step.
step.
step.
step.
apply evt_done. unfold free_pre_post.
destruct q as [|q0' [|q1' [|q2' [|q3' [|q4' [|? ?]]]]]]; try discriminate LQ.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
assert (IA3 : ia_inv mf)
by (eapply (ia_inv_agree (fun x => 0x10000 <= x < 0x645000)); [| exact IA2| intros y Hy; unfold IA, IA_FLAG in Hy; cbn beta; lia];
eapply agree_on_of_munch; [exact MU3| exact WM3|]; intros y Hy _; cbn [outside]; lia) end.
do 16 eexists. exists m3, sz, q0', q1', q2', q3', q4', rest'. eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|].
split; [exact OBJ3|]. split; [exact SZB|].
split; [exact FRS|]. split; [exact RT5|]. split; [exact IA3| exact TU3].
Qed.

Lemma free_icpt_epi : forall (ra : word) (bp : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s0' s1' s2' s3' s4' s5' : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (junk8 : list byte),
mem_inv asegs m -> 0 <= bp < 2^64 -> 2128 <= bp ->
rw_cells asegs m (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (fun ms' => ms' = MS (mkR ra (wz bp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR (wz 0x63480) (wz (bp + -2128)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x63480) fc None m (seg_rom asegs)).
Proof.
intros until junk8; intros MI BPR BLO FRS. change (2^64) with 18446744073709551616 in BPR.
do 10 step.
apply evt_done. reflexivity.
Qed.

Lemma dealloc_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 64, bv_unsigned sp)] lo m (fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_free_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST LO. pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (proj1 ST) as LO0.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold asan_free_entry.
do 10 step.
carve_frame 64%nat ST.
do 9 step.
step. if_lit.
do 10 step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact I.
Qed.
End Pre.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (LV : lvp).
Local Notation atn := (at_nodeA LV asegs).
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Hypothesis recycle_spec : forall RE X, recycle_stmt C RE X LV.

Lemma QRUN_pre : forall a LB0 FS0 G RE X m m' bp,
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> band_lo <= bp - 2128 - 144 ->
munch (free_pre_W bp (rl_T X)) m m' -> wmono asegs m m' ->
RTconst RE X m' -> ia_inv m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
QRUN C 0 QB QB [] a LB0 FS0 G RE X m'
/\ (forall LB FS, Permutation LB LB0 -> Permutation FS FS0 -> aheap_presA asegs a_alayout LB FS bp m m').
Proof.
intros a LB0 FS0 G RE X m m' bp QR CEIL MU WM RT' IA' TU'. pose proof CEIL as CEIL'. idtac.
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1 in MU.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (1570184, 1570184 + 4); (986368, 986368 + 8);
(986376, 986376 + 262144); (1248576, 1514800); (rl_T X + 3168, rl_T X + 3169)] -> lo' <= x < hi' ->
(band_lo <= x < bp) \/ (fp_RQuar a LB0 G RE X x /\ ia_zone x) \/ x = rl_T X + 3168).
{ intros lo' hi' x Hin Hx. cbn in Hin. unfold ia_zone, IA, IA_FLAG.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-; [left; lia| left; lia| right; left| right; left| right; left| right; left| right; right; lia].
- split; [| lia]. do 4 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia. }
assert (STW : Forall st_avoid [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (1570184, 1570184 + 4); (986368, 986368 + 8);
(986376, 986376 + 262144); (1248576, 1514800); (rl_T X + 3168, rl_T X + 3169)]).
{ unfold A_ERRNO in *. repeat apply Forall_cons; try apply Forall_nil.
all: intros x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. }
split.
- split; [exact GC|]. split.
+ apply QOTH_split. split; [exact RT'|]. split; [eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]|]. split.
* eapply RPrim_frame; [exact RP| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]].
-- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
-- exact (fpQ_RPrim a LB0 FS0 G RE X GC z Z Fx).
-- refine (fpP_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
* apply QREST_split. split.
-- eapply QR3_munch; [exact GC| split; [exact RC| split; [exact RSE| exact RF]]| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]]; [do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z].
-- rewrite HRD. eapply RDepot_frame_unw; [exact RL| exact RD| exact WM| | exact TU'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NE] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]].
++ pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)). lia.
++ exact (fpQ_RDepot a LB0 FS0 G RE X GC z Z Fx).
++ exact (NE Z).
+ eapply RQuarM_refresh_ia; [exact GC| exact RQ| | exact IA'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NZ] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[_ Z]|Z]].
* exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia)).
* exact (NZ Z).
* refine (fpQ_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
- intros LB FS PB PF. eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| lia| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]]; [do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z].
Qed.

Lemma free_icpt_spec : forall L, afreeA_stmt asegs atn a_alayout (ARUN C) L.
Proof.
intros L. unfold afreeA_stmt.
intros until dn; intros EL AR INB QRM ST CEIL LO MI TP GP UNW DNH DCAP A0. subst tp gp a0 L.
cbn [ala_free_stack ala_tp ala_gp ala_free a_alayout].
pose proof CEIL as CEIL'. idtac. cbn [ala_free_stack a_alayout] in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & QR).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
assert (INB0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact INB]).
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB0) as HN2.
pose proof (gc_blocks _ _ _ _ _ _ GC _ _ _ INB0) as BLK.
assert (HN0 : 0 <= n /\ aptr_req p = n).
{ destruct BLK as [(id0 & i0 & E0 & Hn & _)|(mb0 & E0 & Hn & _)]; subst p; cbn [aptr_req]; split; lia || reflexivity. }
pose proof (ARUN_block_range C _ _ _ _ _ _ AR INB) as BR. cbn [ablk_addr ablk_size fst snd] in BR. unfold ablock_rangeA in BR.
rewrite ?KHI_eq in BR.
pose proof RQ as (JT & JG & QA & _ & _ & _ & IAI & _).
pose proof (RDepot_unw _ _ _ RD) as TU.
apply raw_free_A_intro.
rewrite <- (Z_to_bv_bv_unsigned sp).
eapply aimplT_evt.
{ eapply (free_icpt_pre RE X); [exact RT| exact RL| exact IAI| exact TU| exact MI| exact ST| exact CEIL'| lia| lia| exact UNW| lia]. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m2 & sz & q0 & q1 & q2 & q3 & q4 & rest & junk8
& -> & MU & WM & MI2 & ST2 & OBJ & SZB & FRS & RT2 & IA2 & TU2).
destruct (QRUN_pre _ _ _ _ _ _ _ _ (bv_unsigned sp) QR ltac:(lia) MU WM RT2 IA2 TU2) as [QR2 AP2].
assert (DK2 : depot_keep asegs m m2).
{ eapply depot_keep_of_munch; [exact MU| exact WM|]. pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKl & TBl & _). cbn [fst snd] in TKl, TBl.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1, DP_N. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
assert (EK2 : errno_keep asegs m m2).
{ eapply errno_keep_of_munch; [exact MU| exact WM|]. pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKe & TBe & _). cbn [fst snd] in TKe, TBe.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }

assert (ST' : stk asegs m2 lo (bv_unsigned (wz (bv_unsigned sp + -2128)))) by (rewrite unsigned_lit by lia; exact ST2).
assert (LO' : lo <= bv_unsigned (wz (bv_unsigned sp + -2128)) - DEALLOC_STACK) by (rewrite unsigned_lit by lia; unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia).
assert (OLO' : bv_unsigned (wz (bv_unsigned sp + -2128)) <= bv_unsigned sp + -2128) by (rewrite unsigned_lit by lia; lia).
eapply aimplT_then.
{ eapply (dealloc_spec C LV RE X HRD HRSx);
[exact QR2| exact INB0| exact QRM| exact MI2| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact SZB| exact (DK2 dn DNH)| exact DCAP| exact OLO'| lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
replace (ret_pc (wz 406656)) with (wz 406656) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite (unsigned_lit (bv_unsigned sp + -2128)) in ST5, AP5 by lia.

assert (FRS5 : rw_cells asegs m5 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FRS| left; lia]. }
assert (OBJ5 : rw_cells asegs m5 (bv_unsigned sp + -2128) (unw_obj (bv_unsigned sp + -2128) sz [q0; q1; q2; q3; q4] rest (bv_unsigned sp))).
{ eapply aheap_presA_rw_cells; [exact AP5| exact OBJ| left; lia]. }
eapply evt_cut; [eapply (free_icpt_epi ra (bv_unsigned sp)); [exact MI5| lia| lia| exact FRS5]|].
cbv beta. intros ms2 ->.
apply evt_done. unfold std_postA. do 15 eexists. exists m5. split; [reflexivity|].
split; [exact MI5|]. split.
{ rewrite Z_to_bv_bv_unsigned.
pose proof (stk_release asegs m5 lo _ _ ST5 OBJ5 ltac:(lia)) as ST6. unfold unw_obj in ST6. cbn [cells_size csize Nat.add app map length] in ST6. zofn ST6.
replace (bv_unsigned sp + -2128 + 2064) with (bv_unsigned sp + -64) in ST6 by lia.
pose proof (stk_release asegs m5 lo _ _ ST6 FRS5 ltac:(lia)) as ST7. cbn [cells_size csize Nat.add] in ST7. zofn ST7.
replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST7 by lia. exact ST7. }
split.
{ rewrite Z_to_bv_bv_unsigned. eapply aheap_presA_trans.
- eapply aheap_presA_weaken; [exact (AP2 LB FS PB PF)| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf].
- eapply aheap_presA_weaken; [exact AP5| lia| | intros f Hf; eapply Permutation_in; [exact PF| exact Hf]].
intros b Hb. eapply Permutation_in; [exact (alb_remove_perm p _ _ PB)| exact Hb]. }
split; [reflexivity|]. split; [reflexivity|].
split; [exact (proj1 DS5 dn (DK2 dn DNH) ltac:(unfold DEPOT_CAP in DCAP; lia))|].
split; [eapply errno_keep_trans; [exact EK2| exact (proj2 DS5)]|].
eapply (ARUN_of_QRUN C HRT HRS HRP HRC HRQ); [exact (alb_remove_perm p _ _ PB)| exact PF|]. cbn [ps_a set_a]. exact QR5.
Qed.

Definition afree_nullA_stmt6 (RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (lo : Z),
RUN s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_free_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) ->
a0 = Z_to_bv 64 0 ->
evt asegs (fun ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s ms'
(fun _ m' => depot_keep asegs m m' /\ errno_keep asegs m m' /\ RUN s LB FS RE m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_free a_alayout)) fc None m (seg_rom asegs)).

Lemma free_null_spec : afree_nullA_stmt6 (ARUN C).
Proof.
unfold afree_nullA_stmt6.
intros until lo; intros AR ST CEIL LO MI TP GP UNW A0. subst tp gp a0.
cbn [ala_free_stack ala_tp ala_gp ala_free a_alayout].
pose proof CEIL as CEIL'. idtac. cbn [ala_free_stack a_alayout] in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & QR).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof RQ as (JT & JG & QA & _ & _ & _ & IAI & _).
pose proof (RDepot_unw _ _ _ RD) as TU.
rewrite <- (Z_to_bv_bv_unsigned sp).
eapply evt_cut.
{ eapply (free_icpt_pre RE X); [exact RT| exact RL| exact IAI| exact TU| exact MI| exact ST| exact CEIL'| lia| lia| exact UNW| lia]. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m2 & sz & q0 & q1 & q2 & q3 & q4 & rest & junk8
& -> & MU & WM & MI2 & ST2 & OBJ & SZB & FRS & RT2 & IA2 & TU2).
destruct (QRUN_pre _ _ _ _ _ _ _ _ (bv_unsigned sp) QR ltac:(lia) MU WM RT2 IA2 TU2) as [QR2 AP2].

assert (ST' : stk asegs m2 lo (bv_unsigned (wz (bv_unsigned sp + -2128)))) by (rewrite unsigned_lit by lia; exact ST2).
assert (LO' : lo <= bv_unsigned (wz (bv_unsigned sp + -2128)) - 64) by (rewrite unsigned_lit by lia; lia).
eapply evt_cut.
{ eapply dealloc_null_spec; [exact MI2| exact ST'| exact LO']. }
cbv beta. intros ms2 PO. unfold leafw_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & -> & MU5 & WM5 & MI5 & ST5 & _).
replace (ret_pc (wz 406656)) with (wz 406656) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite !(unsigned_lit (bv_unsigned sp + -2128)) in ST5, MU5 by lia.
assert (FRS5 : rw_cells asegs m5 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (rw_cells_transport asegs _ m2 m5); [exact FRS| exact MU5| exact WM5| cbn [disjoint_from]; cbn [cells_size csize Nat.add]; lia]. }
assert (OBJ5 : rw_cells asegs m5 (bv_unsigned sp + -2128) (unw_obj (bv_unsigned sp + -2128) sz [q0; q1; q2; q3; q4] rest (bv_unsigned sp))).
{ eapply (rw_cells_transport asegs _ m2 m5); [exact OBJ| exact MU5| exact WM5| unfold unw_obj; cbn [disjoint_from map app]; cbn [cells_size csize Nat.add]; lia]. }
eapply evt_cut; [eapply (free_icpt_epi ra (bv_unsigned sp)); [exact MI5| lia| lia| exact FRS5]|].
cbv beta. intros ms3 ->.
apply evt_done. unfold std_postA. do 15 eexists. exists m5. split; [reflexivity|].
split; [exact MI5|]. split.
{ rewrite Z_to_bv_bv_unsigned.
pose proof (stk_release asegs m5 lo _ _ ST5 OBJ5 ltac:(lia)) as ST6. unfold unw_obj in ST6. cbn [cells_size csize Nat.add app map length] in ST6. zofn ST6.
replace (bv_unsigned sp + -2128 + 2064) with (bv_unsigned sp + -64) in ST6 by lia.
pose proof (stk_release asegs m5 lo _ _ ST6 FRS5 ltac:(lia)) as ST7. cbn [cells_size csize Nat.add] in ST7. zofn ST7.
replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST7 by lia. exact ST7. }

destruct (QRUN_pre _ _ _ _ _ _ _ _ (bv_unsigned sp) QR ltac:(lia)
ltac:(eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU5]]; unfold free_pre_W; intros z Hz; cbn [outside] in Hz |- *; lia)
(wmono_trans asegs _ _ _ WM WM5)
ltac:(eapply RTconst_stack; [exact RT2| exact RL| exact MU5| exact WM5| constructor; [cbn [fst]; lia| constructor]])
ltac:(eapply (ia_inv_agree (fun x => 0x10000 <= x < 0x645000)); [| exact IA2| intros y Hy; unfold IA, IA_FLAG in Hy; cbn beta; lia];
eapply agree_on_of_munch; [exact MU5| exact WM5|]; intros y Hy _; cbn [outside]; lia)
ltac:(eapply (rw_cells_transport asegs _ m2 m5); [exact TU2| exact MU5| exact WM5| cbn [disjoint_from]; cbn [cells_size csize Nat.add];
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _); cbn [fst snd] in TK, TB; idtac; lia]))
as [QR5 AP5].
split.
{ rewrite Z_to_bv_bv_unsigned. exact (AP5 LB FS PB PF). }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU5]]; unfold free_pre_W; intros z Hz; cbn [outside] in Hz |- *; lia| exact (wmono_trans asegs _ _ _ WM WM5)|].
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKl & TBl & _). cbn [fst snd] in TKl, TBl.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1, DP_N. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
split.
{
eapply errno_keep_of_munch; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU5]]; unfold free_pre_W; intros z Hz; cbn [outside] in Hz |- *; lia| exact (wmono_trans asegs _ _ _ WM WM5)|].
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKe & TBe & _). cbn [fst snd] in TKe, TBe.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
eapply (ARUN_of_QRUN C HRT HRS HRP HRC HRQ); [exact PB| exact PF| exact QR5].
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QV3O QjgW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk QV3O QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 Qu3b QYyZ.Mqc QjgW QYyZ.Mqa QEEn QQ8H.Mq5 Qx6U.Mq6 QsDw.Mq1 QcA6.Mq3 QmvA.Mq5 QpME.Mqc.
Import QVo2.Mq4.
Import QRfV.Mq3 QnRU.Mqk QnRU.Mqd QEYd.Mq0 Qx6U.Mq7 QcA6.Mq4 Qx6U.Mq5.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma calloc_W_sec_lz {BAND : Band} : forall a LB FS G RE X bp mb msz lo hi x,
gcons a LB FS G RE X -> band_lo <= bp - CALLOC_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo, hi) (calloc_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo <= x < hi -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo hi x GC CSP MSZ MB8 Hin Hx. unfold CALLOC_STACK, ALLOC_STACK in CSP.
unfold calloc_W_sec, CALLOC_STACK, ALLOC_STACK in Hin. cbn [app In] in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. do 3 right; left. lia.
- destruct (malloc_W_sec_lz a LB FS G RE X (bp - 48) mb msz lo hi x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8
ltac:(unfold malloc_W_sec, MALLOC_STACK; cbn [app In]; right; replace (bp - 48 - 2144) with (bp - 2192) by lia; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]];
unfold lz; [tauto| tauto| tauto| do 3 right; left; lia| tauto].
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

Lemma calloc_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (cnt sz lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_calloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 ->
from_primary (cnt * sz) = false ->
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
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
set (n := cnt * sz) in *. assert (Hn : 0 <= n <= 2^26) by (subst n; nia).
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (calloc_icpt_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo cnt sz dn GC R1 R2 R5 R7 MI ST CEIL' ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP Hcnt Hsz Hle HP) as M.
rewrite Z_to_bv_bv_unsigned in M. fold n in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold calloc_post_sec in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
destruct r as [p|].
- destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MU & RSE' & CM & UZ).
pose proof (sec_geom_facts n Hn HP) as (GN & _ & _ & _ & Gnd1 & Gssz & _ & GM1 & _).
destruct (lift_sec_some C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 aa n mb m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 Hn HP ltac:(idtac; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (calloc_W_sec_lz (ps_a s) LB0 FS0 G RE X); [exact GC| idtac; unfold CALLOC_STACK, ALLOC_STACK; lia| lia| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT' RS' RD' RSE' CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (mb + kSecUserOff). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UZ| exact HP4].
- destruct REST as (-> & -> & MU & RSE').
destruct (lift_sec_none C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 m m' (bv_unsigned sp) _ PB PF GC R3 R4 R6 R8 ltac:(idtac; lia) MU WM
ltac:(intros lo' hi' x Hin Hx; destruct (calloc_W_sec_lz (ps_a s) LB0 FS0 G RE X (bv_unsigned sp) 0 0 lo' hi' x GC ltac:(idtac; unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]];
[first [clear - Z; tauto| tauto]| first [clear - Z; tauto| tauto]| first [clear - Z; tauto| tauto]| first [clear - Z; tauto| tauto]| exfalso; destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia| change (0 / 8) with 0 in Z2; lia]])
RT' RS' RD' RSE') as [HP1 HP3].
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq2.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqa.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6.
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
Local Notation mem := (word -> option byte) (only parsing).

Definition free_icpt_entry : Z := 0x636b0.

Definition FREE_STACK : Z := 2128 + DEALLOC_STACK.

Lemma raw_free_A_intro atn L p s (Q : unit -> PStateA -> machine_state -> Prop) ms :
aimplT atn (asan_free L (ps_a s) p) s (fun a' s1 ms' => Q tt (set_a a' s1) ms') ms ->
@implMG PStateA asegs atn unit (raw_free_A L p) s Q ms.
Proof.
intros H. unfold raw_free_A.
eapply implMG_bind with (Q1 := fun x s' ms' => x = s /\ s' = s /\ ms' = ms).
{ apply implMG_get. apply evt_done. repeat split; reflexivity. }
intros x s' ms' (-> & -> & ->).
eapply implMG_bind. { apply aimplT_state in H. exact H. }
intros a' s1 ms1 [-> HQ]. cbn in HQ.
apply implMG_upd. apply evt_done. exact HQ.
Qed.

Definition ia_zone (x : Z) : Prop := IA <= x < 0x1743f8 \/ IA_FLAG <= x < IA_FLAG + 4.

Lemma RQuarM_refresh_ia {BAND : Band} : forall a LB0 FS0 G RE X rb bt bg m m',
gcons a LB0 FS0 G RE X -> RQuarM rb bt bg [] a LB0 G RE X m ->
agree_on asegs (fun x => fp_RQuar a LB0 G RE X x /\ ~ ia_zone x) m m' -> ia_inv m' ->
RQuarM rb bt bg [] a LB0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X rb bt bg m m' GC (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND) AG HI'.
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC. rewrite ?KHI_eq in PK.
pose proof (rlay_obj_facts RE X _ (gc_rlay _ _ _ _ _ _ GC) (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK. rewrite ?KHI_eq in TK.
exists JT, JG, QA. unfold ia_zone, IA, IA_FLAG in AG.
assert (SLOT : forall c j t x, tag_at G c j = Some t -> tag_quar t = true -> in_iv (slot_beg RE c j, class_size c) x ->
fp_RQuar a LB0 G RE X x /\ ~ (996288 <= x < 1524728 \/ 1580104 <= x < 1580104 + 4)).
{ intros c j t x Ht Hq Hx. pose proof (qslot_facts a LB0 FS0 G RE X GC c j t Ht) as (P1 & _). unfold prim_lo in P1. destruct Hx as [Hx1 Hx2]; cbn [fst snd] in Hx1, Hx2.
split; [do 5 right; left; exists c, j, t; split; [exact Ht| split; [exact Hq| split; cbn [fst snd]; lia]]| lia]. }
assert (SLOTS : forall c j t x, tag_at G c j = Some t -> tag_quar t = true -> in_sh (slot_beg RE c j, class_size c) x ->
fp_RQuar a LB0 G RE X x /\ ~ (996288 <= x < 1524728 \/ 1580104 <= x < 1580104 + 4)).
{ intros c j t x Ht Hq Hx. pose proof SH_band as ?SHBDx; pose proof (slot_band a LB0 FS0 G RE X GC c j t x Ht Hx).
split; [do 6 right; left; exists c, j, t; auto| lia]. }
assert (QREP : forall C q J, (forall x, C <= x < C + 32 -> fp_RQuar a LB0 G RE X x /\ ~ (996288 <= x < 1524728 \/ 1580104 <= x < 1580104 + 4)) ->
qrep RE G m QA C q J -> qrep RE G m' QA C q J).
{ intros C q J HC R. pose proof R as (_ & _ & R3 & _). eapply qrep_agree; [exact AG| exact R| exact HC| |].
- intros j x Hj Hx. eapply SLOT; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)| reflexivity| exact Hx].
- intros j x Hj Hx. eapply SLOTS; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)| reflexivity| exact Hx]. }
split; [apply QREP; [| exact HT]; intros x Hx; unfold TQ in Hx; split; [left; split; cbn [fst snd]; lia| lia]|].
split; [apply QREP; [| exact HG]; intros x Hx; unfold GQ, A_INSTANCE in Hx; split; [right; right; left; unfold A_INSTANCE; split; cbn [fst snd]; lia| lia]|].
split; [eapply rw_cells_agree; [exact AG| exact HM|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold QMUT, A_INSTANCE in Hx;
split; [right; right; left; unfold A_INSTANCE; split; cbn [fst snd]; lia| lia]|].
split; [exact HI'|].
split; [exact ND|]. split; [exact TQO|]. split; [exact C24|]. split; [exact NDP|]. split; [| split; [exact TQP| split; [exact PQA| exact BND]]].
intros p Hp. pose proof (REP p Hp) as R. destruct p as [id n|mb n]; cbn [qptr_rep] in R |- *.
- destruct R as (i & Ht & Hpr & HQA & QM). exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|].
eapply qchunk_mem_agree; [exact AG| exact QM| |].
+ intros x Hx. eapply SLOT; [exact Ht| reflexivity|]. split; cbn [fst snd]; lia.
+ intros x Hx. eapply SLOTS; [exact Ht| reflexivity|]. split; cbn [fst snd]; [lia|].
replace (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) with (class_size (class_of n)) in Hx by lia. lia.
- destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|].
pose proof (qsec_facts a LB0 FS0 G RE X GC _ Hin) as (_ & E2 & _). cbn [se_beg se_size] in E2. rewrite ?KHI_eq in E2.
eapply qchunk_mem_agree; [exact AG| exact QM| |].
+ intros x Hx. split; [| pose proof kconsts as (_ & _ & _ & _ & KP & _); lia]. do 7 right; left. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. auto.
+ intros x Hx. pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin) as SB. cbn [se_beg se_size] in SB.
split; [| specialize (SB ltac:(replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia; exact Hx)); lia].
do 8 right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. split; [exact Hin|]. split; [exact Hnl|].
replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
Qed.

Definition free_pre_W (bp T : Z) : list (Z * Z) :=
[(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (IA_FLAG, IA_FLAG + 4); (IA, IA + 8); (IA_MAP1, IA_MAP1 + 262144); (0x0133400, 0x1743f0); (T + 3168, T + 3169)].

Definition free_pre_post {BAND : Band} (RE : aentry) (X : rlay) (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo A : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 : word) (m' : mem) (sz : Z) (q0 q1 q2 q3 q4 : word) (rest junk8 : list byte),
ms' = MS (mkR (wz 0x63858) (wz (bp + -2128)) gp (wz A_TP) t0 t1 t2 (wz bp) (wz A) (wz A) (wz (bp + -2128)) (wz 1) a3 a4 a5 a6 a7
s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz asan_free_entry) fc None m' (seg_rom asegs)
/\ munch (free_pre_W bp (rl_T X)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bp + -2128)
/\ rw_cells asegs m' (bp + -2128) (unw_obj (bp + -2128) sz [q0; q1; q2; q3; q4] rest bp)
/\ 1 <= sz <= 30
/\ rw_cells asegs m' (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ RTconst RE X m' /\ ia_inv m' /\ rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)].

Lemma rw_cells_join : forall m A B cs1 cs2,
rw_cells asegs m A cs1 -> rw_cells asegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app asegs m A cs1 cs2)). split; assumption. Qed.

Ltac zofn H := repeat match type of H with context [Z.of_nat ?n] =>
lazymatch n with S _ => idtac | O => idtac end; let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end.

Section Pre.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma free_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z),
RTconst RE X m -> rlay_ok RE X -> ia_inv m -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - 2128 - 144 -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= A < 2^47 ->
evt asegs (free_pre_post RE X ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x6369c) fc None m (seg_rom asegs)).
Proof.
intros until A; intros RT RL IAI TU MI ST CEIL LO BPR UNW HA.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in BPR. change (2^47) with 140737488355328 in HA.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (free_pre_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1 in MU.
pose proof (munch_refl [(bp - 2128, bp)] m) as MU2.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128);
(1580104, 1580104 + 4); (996288, 996288 + 8); (996296, 996296 + 262144); (0x0133400, 0x1743f0); (rl_T X + 3168, rl_T X + 3169)]).
{ pose proof (@ia_W_rt BAND RE X (bp - 2128) ltac:(unfold INTALLOC_STACK; lia) RL) as FW. unfold ia_W, IA_FLAG, IA, IA_MAP1, INTALLOC_STACK in FW.
inversion FW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; subst.
constructor; [exact (rt_avoid_stack RE X RL (bp - 2128) bp ltac:(lia))|]. constructor; [exact (rt_avoid_stack RE X RL (bp - 2128 - 144) (bp - 2128) ltac:(lia))|].
constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R4|]. constructor; [exact R5|].
constructor; [exact (rt_avoid_Thigh RE X (rl_T X + 3168) (rl_T X + 3169) RL ltac:(lia) ltac:(lia))| constructor]. }
unfold A_INSTANCE in *.
step.
carve_frame 2032%nat ST.
do 8 step.
step.
step.
carve_frame 96%nat ST.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]);
assert (IA1 : ia_inv mc) by (eapply (ia_inv_agree (fun x => 0x10000 <= x < 0x647000)); [| exact IAI| intros x Hx; unfold IA, IA_FLAG in Hx; cbn beta; lia];
eapply agree_on_of_munch; [exact MU2| exact WM|]; intros x Hx _; cbn [outside]; lia)
end.
clear MU2.
call_ch (intalloc_spec RE X) ltac:(fun PO => unfold ia_W, INTALLOC_STACK, IA_FLAG, IA, IA_MAP1 in PO; rewrite !(unsigned_lit (bp + -2128)) in PO by lia);
try eassumption; try (rewrite ?unsigned_lit by lia; first [eassumption| unfold INTALLOC_STACK; lia]).
subst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with H : RTconst RE X mc |- _ => rename H into RT2 end;
lazymatch goal with H : ia_inv mc |- _ => rename H into IA2 end;
pose proof (munch_refl [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (rl_T X + 3168, rl_T X + 3169)] mc) as MU3;
pose proof (wmono_refl asegs mc) as WM3 end.

step.
rewrite (unsigned_lit A) by lia. rewrite (Z.shiftr_div_pow2 A 47) by lia. rewrite (Z.div_small A (2^47)) by (change (2^47) with 140737488355328; lia).
step. if_lit.
step.
rewrite (unsigned_lit A) by lia. rewrite (Z.shiftr_div_pow2 A 32) by lia. change (2^32) with 4294967296.
assert (QH : 0 <= A / 4294967296 < 32768) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
step.
rewrite (unsigned_lit (A / 4294967296)) by lia. rewrite (Z.shiftl_mul_pow2 (A / 4294967296) 3) by lia. change (2^3) with 8.
step.
pose proof IA2 as (b0 & FL & B01 & ZMAP & ZR). unfold IA_MAP1 in ZMAP.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (wa (996296 + (A / 4294967296 * 8))) 8 = Some (le8 (wz 0)))
by (eapply zbytes_load8; [exact ZMAP| lia| lia]) end.
step.
clear HR b0 FL B01 ZMAP ZR.
step.
step. if_lit.

do 5 step.
stf.
step.
stf.
step.
call0 (malloc_ctx_size_spec RE X). { eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]. } { assumption. }
subst.
step. step. if_lit.
step.
call0 (get_current_pc_spec). subst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
step. lits.
clear K19 K15.
step.
step.
call0 (malloc_ctx_size_spec RE X). { exact RT3. } { assumption. }
subst.
step.
step. lits.
step. lits.
step.
rewrite (unsigned_lit bp), land_ones64 by lia.
step.
step.
step. if_lit.
do 6 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (proj1 (rw_cells_app asegs mc (bp + -2128) [C8 (wz (bp + -2112))] _)) in FR0 as [OBT FR0];
apply (proj1 (rw_cells_app asegs mc _ [C8 (wz 0)] _)) in FR0 as [OBZ OB80];
cbn [cells_size csize Nat.add] in OBZ, OB80; zofn OBZ; zofn OB80;
apply (proj1 (rw_cells_app asegs mc (bp + -2032) [CB 1960 _] _)) in FR as [OB1960 FR];
apply (proj1 (rw_cells_app asegs mc _ [C8 (wz bp)] _)) in FR as [OBP FRS];
cbn [cells_size csize Nat.add] in OBP, FRS; zofn OBP; zofn FRS;
replace (bp + -2032 + 1960 + 8) with (bp + -64) in FRS by lia;
pose proof (cells_hjunk _ _ _ OB80 ltac:(lia)) as J1; pose proof (cells_hjunk _ _ _ OB1960 ltac:(lia)) as J2;
cbn [cells_size csize Nat.add] in J1, J2; zofn J1; zofn J2;
replace (bp + -2128 + 8 + 8) with (bp + -2112) in J1, OB80 by lia; replace (bp + -2112 + 80) with (bp + -2032) in J1 by lia;
pose proof (hjunk_merge _ _ _ _ J1 J2) as J; clear J1 J2 OB80 OB1960;
destruct (hjunk_split _ _ (bp + -2072) _ J ltac:(lia)) as [JQ JR]; clear J;
replace (bp + -2072) with (bp + -2112 + 40) in JQ by lia;
destruct (hjunk_C8x5 _ _ JQ) as (q0 & q1 & q2 & q3 & q4 & OBQ); clear JQ;
destruct (hjunk_cells _ (bp + -2072) 2000%nat ltac:(replace (bp + -2072 + Z.of_nat 2000) with (bp + -2032 + 1960) by (change (Z.of_nat 2000) with 2000; lia); exact JR))
as (rest & OBR); clear JR;
recast OBZ [C4 (wz 0); C4 (wz 0)];
pose proof (rw_cells_join _ _ _ _ _ OBR OBP ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as O4;
pose proof (rw_cells_join _ _ _ _ _ OBQ O4 ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as O3;
pose proof (rw_cells_join _ _ _ _ _ OBZ O3 ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as O2;
pose proof (rw_cells_join _ _ _ _ _ OBT O2 ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 2000) with 2000 || idtac; change (Z.of_nat 40) with 40 || idtac; change (Z.of_nat 8) with 8 || idtac; lia)) as OBJ;
cbn [app] in OBJ; clear O4 O3 O2 OBR OBP OBQ OBZ OBT;
replace (bp + -2112) with (bp + -2128 + 16) in OBJ by lia;
change (rw_cells asegs mc (bp + -2128) (unw_obj (bp + -2128) 0 [q0; q1; q2; q3; q4] rest bp)) in OBJ;

pose proof FRS as FRS';
apply (proj1 (rw_cells_app asegs mc (bp + -64) [CB 8 _; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])) in FRS' as [_ REC];
cbn [cells_size csize Nat.add] in REC; zofn REC; replace (bp + -64 + 48) with (bp - 16) in REC by lia;

assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]);
assert (URD : unw_readable asegs RE mc (bp - 16))
by (eapply (unw_readable_prologue RE _ m mc bp s0 ra); [exact MU| intros y Hy; cbn [outside]; lia| exact REC| exact UNW]);
clear REC
end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ST' : stk asegs mc lo (bv_unsigned (wz (bp + -2128)))) by (rewrite unsigned_lit by lia; exact PC);
assert (LO' : lo <= bv_unsigned (wz (bp + -2128)) - unwind_stack) by (rewrite unsigned_lit by lia; unfold unwind_stack; lia);
assert (OLO' : bv_unsigned (wz (bp + -2128)) <= bp + -2128) by (rewrite unsigned_lit by lia; lia);
assert (MI' : mem_inv asegs mc) by assumption
end.
eapply evt_cut.
{ eapply (unwind_impl_spec RE X);
[exact RT4| exact RL| exact MI'| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact TU| exact URD| lia
| exact OLO'| lia| lia]. }
clear ST' LO' OLO' MI'.
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MUd & WMd & MId & STd
& sz & q & rest' & OBJ3 & LQ & TU3 & SZB & RT5).
unfold unwind_stack in MUd. rewrite !(unsigned_lit (bp + -2128)) in MUd, STd by lia.
clear OBJ TU URD RT4.
lazymatch type of MUd with munch _ ?mx _ =>
apply (munch_chain' _ mx m3 _ m MUd) in MU; [| sub_fp_solve];
apply (munch_chain' _ mx m3 _ _ MUd) in MU3; [| sub_fp_solve];
transport_after_call asegs mx m3 MUd WMd; clear MUd WMd end.
replace (ret_pc (wz 407620)) with (wz 407620) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

step. step.
step.
step.
step.
apply evt_done. unfold free_pre_post.
destruct q as [|q0' [|q1' [|q2' [|q3' [|q4' [|? ?]]]]]]; try discriminate LQ.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
assert (IA3 : ia_inv mf)
by (eapply (ia_inv_agree (fun x => 0x10000 <= x < 0x647000)); [| exact IA2| intros y Hy; unfold IA, IA_FLAG in Hy; cbn beta; lia];
eapply agree_on_of_munch; [exact MU3| exact WM3|]; intros y Hy _; cbn [outside]; lia) end.
do 16 eexists. exists m3, sz, q0', q1', q2', q3', q4', rest'. eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|].
split; [exact OBJ3|]. split; [exact SZB|].
split; [exact FRS|]. split; [exact RT5|]. split; [exact IA3| exact TU3].
Qed.

Lemma free_icpt_epi : forall (ra : word) (bp : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s0' s1' s2' s3' s4' s5' : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (junk8 : list byte),
mem_inv asegs m -> 0 <= bp < 2^64 -> 2128 <= bp ->
rw_cells asegs m (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (fun ms' => ms' = MS (mkR ra (wz bp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR (wz 0x63858) (wz (bp + -2128)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x63858) fc None m (seg_rom asegs)).
Proof.
intros until junk8; intros MI BPR BLO FRS. change (2^64) with 18446744073709551616 in BPR.
do 10 step.
apply evt_done. reflexivity.
Qed.

Lemma dealloc_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 64, bv_unsigned sp)] lo m (fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_free_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST LO. pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (proj1 ST) as LO0.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold asan_free_entry.
do 10 step.
carve_frame 64%nat ST.
do 9 step.
step. if_lit.
do 10 step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact I.
Qed.
End Pre.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (LV : lvp).
Local Notation atn := (at_nodeA LV asegs).
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Hypothesis recycle_spec : forall RE X, recycle_stmt C RE X LV.

Lemma QRUN_pre : forall a LB0 FS0 G RE X m m' bp,
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> band_lo <= bp - 2128 - 144 ->
munch (free_pre_W bp (rl_T X)) m m' -> wmono asegs m m' ->
RTconst RE X m' -> ia_inv m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
QRUN C 0 QB QB [] a LB0 FS0 G RE X m'
/\ (forall LB FS, Permutation LB LB0 -> Permutation FS FS0 -> aheap_presA asegs a_alayout LB FS bp m m').
Proof.
intros a LB0 FS0 G RE X m m' bp QR CEIL MU WM RT' IA' TU'. pose proof CEIL as CEIL'. idtac.
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1 in MU.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (1580104, 1580104 + 4); (996288, 996288 + 8);
(996296, 996296 + 262144); (1258496, 1524720); (rl_T X + 3168, rl_T X + 3169)] -> lo' <= x < hi' ->
(band_lo <= x < bp) \/ (fp_RQuar a LB0 G RE X x /\ ia_zone x) \/ x = rl_T X + 3168).
{ intros lo' hi' x Hin Hx. cbn in Hin. unfold ia_zone, IA, IA_FLAG.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-; [left; lia| left; lia| right; left| right; left| right; left| right; left| right; right; lia].
- split; [| lia]. do 4 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia. }
assert (STW : Forall st_avoid [(bp - 2128, bp); (bp - 2128 - 144, bp - 2128); (1580104, 1580104 + 4); (996288, 996288 + 8);
(996296, 996296 + 262144); (1258496, 1524720); (rl_T X + 3168, rl_T X + 3169)]).
{ unfold A_ERRNO in *. repeat apply Forall_cons; try apply Forall_nil.
all: intros x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. }
split.
- split; [exact GC|]. split.
+ apply QOTH_split. split; [exact RT'|]. split; [eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]|]. split.
* eapply RPrim_frame; [exact RP| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]].
-- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
-- exact (fpQ_RPrim a LB0 FS0 G RE X GC z Z Fx).
-- refine (fpP_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
* apply QREST_split. split.
-- eapply QR3_munch; [exact GC| split; [exact RC| split; [exact RSE| exact RF]]| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]]; [do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z].
-- rewrite HRD. eapply RDepot_frame_unw; [exact RL| exact RD| exact WM| | exact TU'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NE] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]].
++ pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)). lia.
++ exact (fpQ_RDepot a LB0 FS0 G RE X GC z Z Fx).
++ exact (NE Z).
+ eapply RQuarM_refresh_ia; [exact GC| exact RQ| | exact IA'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NZ] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[_ Z]|Z]].
* exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia)).
* exact (NZ Z).
* refine (fpQ_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
- intros LB FS PB PF. eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| lia| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|Z]]; [do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z].
Qed.

Lemma free_icpt_spec : forall L, afreeA_stmt asegs atn a_alayout (ARUN C) L.
Proof.
intros L. unfold afreeA_stmt.
intros until dn; intros EL AR INB QRM ST CEIL LO MI TP GP UNW DNH DCAP A0. subst tp gp a0 L.
cbn [ala_free_stack ala_tp ala_gp ala_free a_alayout].
pose proof CEIL as CEIL'. idtac. cbn [ala_free_stack a_alayout] in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & QR).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
assert (INB0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact INB]).
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB0) as HN2.
pose proof (gc_blocks _ _ _ _ _ _ GC _ _ _ INB0) as BLK.
assert (HN0 : 0 <= n /\ aptr_req p = n).
{ destruct BLK as [(id0 & i0 & E0 & Hn & _)|(mb0 & E0 & Hn & _)]; subst p; cbn [aptr_req]; split; lia || reflexivity. }
pose proof (ARUN_block_range C _ _ _ _ _ _ AR INB) as BR. cbn [ablk_addr ablk_size fst snd] in BR. unfold ablock_rangeA in BR.
rewrite ?KHI_eq in BR.
pose proof RQ as (JT & JG & QA & _ & _ & _ & IAI & _).
pose proof (RDepot_unw _ _ _ RD) as TU.
apply raw_free_A_intro.
rewrite <- (Z_to_bv_bv_unsigned sp).
eapply aimplT_evt.
{ eapply (free_icpt_pre RE X); [exact RT| exact RL| exact IAI| exact TU| exact MI| exact ST| exact CEIL'| lia| lia| exact UNW| lia]. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m2 & sz & q0 & q1 & q2 & q3 & q4 & rest & junk8
& -> & MU & WM & MI2 & ST2 & OBJ & SZB & FRS & RT2 & IA2 & TU2).
destruct (QRUN_pre _ _ _ _ _ _ _ _ (bv_unsigned sp) QR ltac:(lia) MU WM RT2 IA2 TU2) as [QR2 AP2].
assert (DK2 : depot_keep asegs m m2).
{ eapply depot_keep_of_munch; [exact MU| exact WM|]. pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKl & TBl & _). cbn [fst snd] in TKl, TBl.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1, DP_N. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
assert (EK2 : errno_keep asegs m m2).
{ eapply errno_keep_of_munch; [exact MU| exact WM|]. pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKe & TBe & _). cbn [fst snd] in TKe, TBe.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }

assert (ST' : stk asegs m2 lo (bv_unsigned (wz (bv_unsigned sp + -2128)))) by (rewrite unsigned_lit by lia; exact ST2).
assert (LO' : lo <= bv_unsigned (wz (bv_unsigned sp + -2128)) - DEALLOC_STACK) by (rewrite unsigned_lit by lia; unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia).
assert (OLO' : bv_unsigned (wz (bv_unsigned sp + -2128)) <= bv_unsigned sp + -2128) by (rewrite unsigned_lit by lia; lia).
eapply aimplT_then.
{ eapply (dealloc_spec C LV RE X HRD HRSx);
[exact QR2| exact INB0| exact QRM| exact MI2| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact SZB| exact (DK2 dn DNH)| exact DCAP| exact OLO'| lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
replace (ret_pc (wz 407640)) with (wz 407640) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite (unsigned_lit (bv_unsigned sp + -2128)) in ST5, AP5 by lia.

assert (FRS5 : rw_cells asegs m5 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FRS| left; lia]. }
assert (OBJ5 : rw_cells asegs m5 (bv_unsigned sp + -2128) (unw_obj (bv_unsigned sp + -2128) sz [q0; q1; q2; q3; q4] rest (bv_unsigned sp))).
{ eapply aheap_presA_rw_cells; [exact AP5| exact OBJ| left; lia]. }
eapply evt_cut; [eapply (free_icpt_epi ra (bv_unsigned sp)); [exact MI5| lia| lia| exact FRS5]|].
cbv beta. intros ms2 ->.
apply evt_done. unfold std_postA. do 15 eexists. exists m5. split; [reflexivity|].
split; [exact MI5|]. split.
{ rewrite Z_to_bv_bv_unsigned.
pose proof (stk_release asegs m5 lo _ _ ST5 OBJ5 ltac:(lia)) as ST6. unfold unw_obj in ST6. cbn [cells_size csize Nat.add app map length] in ST6. zofn ST6.
replace (bv_unsigned sp + -2128 + 2064) with (bv_unsigned sp + -64) in ST6 by lia.
pose proof (stk_release asegs m5 lo _ _ ST6 FRS5 ltac:(lia)) as ST7. cbn [cells_size csize Nat.add] in ST7. zofn ST7.
replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST7 by lia. exact ST7. }
split.
{ rewrite Z_to_bv_bv_unsigned. eapply aheap_presA_trans.
- eapply aheap_presA_weaken; [exact (AP2 LB FS PB PF)| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf].
- eapply aheap_presA_weaken; [exact AP5| lia| | intros f Hf; eapply Permutation_in; [exact PF| exact Hf]].
intros b Hb. eapply Permutation_in; [exact (alb_remove_perm p _ _ PB)| exact Hb]. }
split; [reflexivity|]. split; [reflexivity|].
split; [exact (proj1 DS5 dn (DK2 dn DNH) ltac:(unfold DEPOT_CAP in DCAP; lia))|].
split; [eapply errno_keep_trans; [exact EK2| exact (proj2 DS5)]|].
eapply (ARUN_of_QRUN C HRT HRS HRP HRC HRQ); [exact (alb_remove_perm p _ _ PB)| exact PF|]. cbn [ps_a set_a]. exact QR5.
Qed.

Definition afree_nullA_stmt6 (RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (lo : Z),
RUN s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_free_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) ->
a0 = Z_to_bv 64 0 ->
evt asegs (fun ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s ms'
(fun _ m' => depot_keep asegs m m' /\ errno_keep asegs m m' /\ RUN s LB FS RE m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_free a_alayout)) fc None m (seg_rom asegs)).

Lemma free_null_spec : afree_nullA_stmt6 (ARUN C).
Proof.
unfold afree_nullA_stmt6.
intros until lo; intros AR ST CEIL LO MI TP GP UNW A0. subst tp gp a0.
cbn [ala_free_stack ala_tp ala_gp ala_free a_alayout].
pose proof CEIL as CEIL'. idtac. cbn [ala_free_stack a_alayout] in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & QR).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof RQ as (JT & JG & QA & _ & _ & _ & IAI & _).
pose proof (RDepot_unw _ _ _ RD) as TU.
rewrite <- (Z_to_bv_bv_unsigned sp).
eapply evt_cut.
{ eapply (free_icpt_pre RE X); [exact RT| exact RL| exact IAI| exact TU| exact MI| exact ST| exact CEIL'| lia| lia| exact UNW| lia]. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m2 & sz & q0 & q1 & q2 & q3 & q4 & rest & junk8
& -> & MU & WM & MI2 & ST2 & OBJ & SZB & FRS & RT2 & IA2 & TU2).
destruct (QRUN_pre _ _ _ _ _ _ _ _ (bv_unsigned sp) QR ltac:(lia) MU WM RT2 IA2 TU2) as [QR2 AP2].

assert (ST' : stk asegs m2 lo (bv_unsigned (wz (bv_unsigned sp + -2128)))) by (rewrite unsigned_lit by lia; exact ST2).
assert (LO' : lo <= bv_unsigned (wz (bv_unsigned sp + -2128)) - 64) by (rewrite unsigned_lit by lia; lia).
eapply evt_cut.
{ eapply dealloc_null_spec; [exact MI2| exact ST'| exact LO']. }
cbv beta. intros ms2 PO. unfold leafw_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & -> & MU5 & WM5 & MI5 & ST5 & _).
replace (ret_pc (wz 407640)) with (wz 407640) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite !(unsigned_lit (bv_unsigned sp + -2128)) in ST5, MU5 by lia.
assert (FRS5 : rw_cells asegs m5 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (rw_cells_transport asegs _ m2 m5); [exact FRS| exact MU5| exact WM5| cbn [disjoint_from]; cbn [cells_size csize Nat.add]; lia]. }
assert (OBJ5 : rw_cells asegs m5 (bv_unsigned sp + -2128) (unw_obj (bv_unsigned sp + -2128) sz [q0; q1; q2; q3; q4] rest (bv_unsigned sp))).
{ eapply (rw_cells_transport asegs _ m2 m5); [exact OBJ| exact MU5| exact WM5| unfold unw_obj; cbn [disjoint_from map app]; cbn [cells_size csize Nat.add]; lia]. }
eapply evt_cut; [eapply (free_icpt_epi ra (bv_unsigned sp)); [exact MI5| lia| lia| exact FRS5]|].
cbv beta. intros ms3 ->.
apply evt_done. unfold std_postA. do 15 eexists. exists m5. split; [reflexivity|].
split; [exact MI5|]. split.
{ rewrite Z_to_bv_bv_unsigned.
pose proof (stk_release asegs m5 lo _ _ ST5 OBJ5 ltac:(lia)) as ST6. unfold unw_obj in ST6. cbn [cells_size csize Nat.add app map length] in ST6. zofn ST6.
replace (bv_unsigned sp + -2128 + 2064) with (bv_unsigned sp + -64) in ST6 by lia.
pose proof (stk_release asegs m5 lo _ _ ST6 FRS5 ltac:(lia)) as ST7. cbn [cells_size csize Nat.add] in ST7. zofn ST7.
replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST7 by lia. exact ST7. }

destruct (QRUN_pre _ _ _ _ _ _ _ _ (bv_unsigned sp) QR ltac:(lia)
ltac:(eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU5]]; unfold free_pre_W; intros z Hz; cbn [outside] in Hz |- *; lia)
(wmono_trans asegs _ _ _ WM WM5)
ltac:(eapply RTconst_stack; [exact RT2| exact RL| exact MU5| exact WM5| constructor; [cbn [fst]; lia| constructor]])
ltac:(eapply (ia_inv_agree (fun x => 0x10000 <= x < 0x647000)); [| exact IA2| intros y Hy; unfold IA, IA_FLAG in Hy; cbn beta; lia];
eapply agree_on_of_munch; [exact MU5| exact WM5|]; intros y Hy _; cbn [outside]; lia)
ltac:(eapply (rw_cells_transport asegs _ m2 m5); [exact TU2| exact MU5| exact WM5| cbn [disjoint_from]; cbn [cells_size csize Nat.add];
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _); cbn [fst snd] in TK, TB; idtac; lia]))
as [QR5 AP5].
split.
{ rewrite Z_to_bv_bv_unsigned. exact (AP5 LB FS PB PF). }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU5]]; unfold free_pre_W; intros z Hz; cbn [outside] in Hz |- *; lia| exact (wmono_trans asegs _ _ _ WM WM5)|].
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKl & TBl & _). cbn [fst snd] in TKl, TBl.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1, DP_N. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
split.
{
eapply errno_keep_of_munch; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU5]]; unfold free_pre_W; intros z Hz; cbn [outside] in Hz |- *; lia| exact (wmono_trans asegs _ _ _ WM WM5)|].
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKe & TBe & _). cbn [fst snd] in TKe, TBe.
unfold free_pre_W, IA_FLAG, IA, IA_MAP1. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
eapply (ARUN_of_QRUN C HRT HRS HRP HRC HRQ); [exact PB| exact PF| exact QR5].
Qed.
End S.
