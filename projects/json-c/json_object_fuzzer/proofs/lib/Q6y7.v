(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QnDM_c1 Q2qa Qy5Y QDUx Q4J3 QytA QJE4 QZAi QUZl Q7S0 Ql2m QGeV QLsg QWTl Q9Ay QXxF Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5.
Import QDUx.Mqb QWTl.Mq0 Q9Ay.Mq0 QXxF.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.

Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

#[using="SO"] Lemma enf_facts : m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b mod 16 = 0
/\ 0 <= idx <= m_last_idx mr /\ m_last_idx mr < 32
/\ snd b + 16 + stride * (m_last_idx mr + 1) <= round_up_pg (r_len r) /\ 16 <= stride /\ stride mod 16 = 0
/\ (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b')
/\ cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0
/\ (forall off, 0 <= off -> 16 * off + N + 4 <= stride -> (stride * idx + 16 * off) / 16 < 65536).
Proof.
destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL' AVr FRr FBr MPL SCr].
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *.
repeat (split; [assumption|]). exact Q16.
Qed.

Definition enf0_st : mstate :=
wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
(wr8 (fst b, snd b + (16 + stride * idx) + -3) idx
(wr16 (fst b, snd b + (16 + stride * idx) + -2) ((snd b + (16 + stride * idx) - (snd b + 16)) / 16) st)).

#[using="r B P STR SO"] Lemma enf0_st_eq : fst (enframe_at st g idx N 0) = enf0_st /\ snd (enframe_at st g idx N 0) = (fst b, snd b + (16 + stride * idx)).
Proof.
pose proof enf_facts as (Hmem & _).
assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
unfold enframe_at. change (get_meta_rec st g) with mr. rewrite Hmem. cbn [default from_option id]. fold stride.
change (negb (0 =? 0)) with false. cbv iota beta. unfold aadd. cbn [fst snd].
unfold set_size. cbn [fst snd].
replace (snd b + (UNIT + stride * idx) + (stride - IB) - (snd b + (UNIT + stride * idx)) - N) with 0 by (unfold UNIT, IB; lia).
cbn [Z.eqb negb Z.leb]. unfold enf0_st, UNIT. split; reflexivity.
Qed.

#[using="st g b idx j mr stride B P N"] Lemma meta_word_mod4096 r0 : mw_ok r0 -> meta_word r0 mod 4096 = meta_word (m_set_maplen 0 r0).
Proof.
intros (LI & FB & SC & ML). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.

#[using="st g b idx j mr stride B P N"] Lemma le1_lor_m64 a : 0 <= a < 32 -> le1 (Z_to_bv 64 (Z.lor a 18446744073709551552)) = [b8 (Z.lor a 192)].
Proof.
intros Ha. unfold le1. cbn [Z_to_le_bytes]. f_equal. unfold b8. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
rewrite <- !(Z.land_ones _ 8) by lia. change (Z.ones 8) with 255.
rewrite <- (Z.land_ones (Z.lor a 18446744073709551552) 64) by lia.
change (Z.ones 64) with 18446744073709551615.
rewrite !Z.land_lor_distr_l. rewrite <- !Z.land_assoc.
change (Z.land 18446744073709551615 255) with 255. change (Z.land 18446744073709551552 255) with 192.
change (Z.land 192 255) with 192. reflexivity.
Qed.

Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).

End ENF.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE QPjm QBeb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import QnDM_c1.Mq0 Q2qa.Mq1 QytA QlQE QFkE.
Import Q9A7.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq2 QPjm.Mq3 Q4J3.Mq2.
Import QJE4.Mq0 QJE4.Mq1 QDUx.Mq3 QWTl.Mq1 QWTl.Mq2 QWTl.Mq3 QDUx.Mq2 Q9Ay.Mq9 QXxF QBeb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Module A2 := QWTl.Mq5.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

#[using="Type"] Lemma magree_refl C m : magree C m m. Proof. intros a _ _; reflexivity. Qed.
#[using="Type"] Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.

#[using="Type"] Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : AMpre st.

Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.

Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.

Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.

Definition FP (stX : mstate) (a : Z) : Prop := alloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

#[using="Type"] Lemma FP_am stX a : am_fp stX lo (bv_unsigned sp) a -> FP stX a.
Proof. intros H. left. apply am_fp_alloc_fp. exact H. Qed.

#[using="RC__ TP"] Lemma ETP : errno_addr tp = 0x1a620 - 164.
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

#[using="Type"] Lemma FP_mono stX stY a :
(forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
FP stX a -> FP stY a.
Proof.
intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
{ unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
unfold lr_lo in *. rewrite K', B'. lia.
Qed.

#[using="Type"] Lemma FP_same stX stY a : s_regions stY = s_regions stX -> FP stX a -> FP stY a.
Proof. intros E. apply FP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

#[using="AMP LO LOLE"] Lemma FP_below stX a : regions_wf stX -> FP stX a -> a < bv_unsigned sp /\ ~ (AUXV_CELL <= a < AUXV_CELL + 8).
Proof.
intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold AUXV_CELL, LIBC, CTX, AM_STACK, alloc_ceiling in *;
rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
- destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
- pose proof (fresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold alloc_ceiling in C. lia.
Qed.

#[using="LO TP"] Lemma errno_not_amfp stX a : regions_wf stX -> am_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. intros WF X. rewrite TP. eapply am_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

#[using="Type"] Lemma brk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.

#[using="Type"] Lemma am_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> QUZl.M RR) (bl : QUZl.M RR) :
am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
= kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
#[using="Type"] Lemma brk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
#[using="Type"] Lemma conc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

#[using="TP"] Lemma repfoot_low stY a : regions_wf stY -> repfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof.
intros WF H. rewrite ETP. pose proof WF as (_ & WR & _ & WA & WG). unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|C]]]]]]; unfold CTX, MLOCK, NEED_LOCKS, QnDM_c1.Mq0.PAGE_SIZE_A in *; try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (area_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. unfold alloc_ceiling in RBC. lia.
- destruct C as (b & gh & Hb & Hin). destruct (group_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. unfold alloc_ceiling in RBC. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. unfold alloc_ceiling in RBC. lia.
Qed.

#[using="Type"] Lemma live_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

#[using="Type"] Lemma fresh_of_ranges_free stY x L a :
s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof.
intros E1 E2 RF XC Ha. split; [lia|]. rewrite (live_ranges_same st stY E1 E2) in RF.
eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.

#[using="RC__"] Lemma image_range_clear stY x L : s_reserved stY = agent_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
x + L <= 0x10000 \/ 0x1b000 <= x.
Proof.
intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)). cbn in *. lia.
Qed.

End ASM.

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 QDUx.Mq1 QPjm.Mq4 Q4J3.Mq3 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).

Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.

End CORE.

End RC__1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4vs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4vs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma gmeta_mw st g p : gmeta_ok st g p -> mw_ok (get_meta_rec st g).
Proof.
intros GO. pose proof (go_li _ _ _ GO). pose proof (go_freeable _ _ _ GO). pose proof (go_sc _ _ _ GO). pose proof (go_maplen _ _ _ GO).
unfold mw_ok. repeat split; lia.
Qed.

#[using="Type"] Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> QUZl.M R) bail :
nontrivial_free dec (S f) st g i k bail =
let mr := get_meta_rec st g in
let sc := m_sizeclass mr in
if ntf_cond st g i then
match m_next mr with
| Some _ =>
guard 50 (sc <? 48) (
let activate_new := optr_eqb (active st sc) (Some g) in
let st1 := dequeue (LActive sc) g st in
match activate_new, active st1 sc with
| true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
| _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
end) bail
| None => free_group R dec (nontrivial_free dec f) st g k bail
end
else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
guard 51 (sc <? 48) (
if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
else k (aor_st st g i) None) bail
else k (aor_st st g i) None.
Proof. reflexivity. Qed.

#[using="Type"] Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> QUZl.M R) bail :
free_group R dec rec st g k bail =
let mr := get_meta_rec st g in
let st1 := fg_usage_st st g in
match m_mem mr with
| None => SVis (EUndef UBadPtr) (fun _ => bail)
| Some p =>
let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
if negb (m_maplen mr =? 0) then
free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
else
dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
end.
Proof. reflexivity. Qed.

Definition ntf_result (st' : mstate) (mi : mapinfo) (a0v a1v : word) : Prop :=
match mi with
| None => a1v = wz 0
| Some (b, len) =>
a0v = wz (conc st' b) /\ a1v = wz len /\ 0 < len < 2^64 /\ snd b = 0
/\ (exists r, (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup /\ len = round_up_pg (r_len r))
/\ (forall b' gh, (s_groups st') !! b' = Some gh -> fst b' <> fst b)
end.

Definition oracle_ok (o m : word -> option byte) (st : mstate) : Prop :=
forall rid r q h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= q < round_up_pg (r_len r) ->
8 <= (r_base r + q) mod 16 ->
cell_read (get_shadow st rid) q = Unknown h ->
o (wa (r_base r + q)) = m (wa (r_base r + q)).

#[using="Type"] Lemma oracle_ok_frame o m st st' : oracle_ok o m st -> s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> oracle_ok o m st'.
Proof.
intros OK ER ES rid r q h Hr Hk Hq M8 Hc. rewrite ER in Hr. unfold get_shadow in Hc. rewrite ES in Hc.
exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

#[using="Type"] Lemma free_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
intros FR HS H. eapply (free_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

#[using="Type"] Lemma free_fp_same st st' lo (sp : Z) a :
s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
free_fp st' lo sp a -> free_fp st lo sp a.
Proof. intros ER ES EG H. eapply (free_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

#[using="Type"] Lemma rdv_known o st q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rdv pans_mem o st q = v.
Proof. intros H. unfold rdv. rewrite H. reflexivity. Qed.

Section NTF.
Variables (ra0 : word) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.

End NTF.

End RC__1.
