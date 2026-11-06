(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0qe.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0pj X0qm X0pc X0qn X0q2 X0q4.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qk X0qi X0qj X0pm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0op X0ow X0ox X0oq X0or X0os X0ot X0ou X0ov X0oy.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Module A2 := X0qe.

Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

Lemma magree_refl C m : magree C m m. Proof. intros a _ _; reflexivity. Qed.
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_pres C m m' : pres_except C m m' -> magree C m m'.
Proof. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
Lemma pres_of_magree C m m' : magree C m m' -> pres_except C m m'.
Proof. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (wview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

Lemma rw_cells_magree C m m' A cs :
rw_cells asegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells asegs m' A cs.
Proof.
intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply A2.rw_cells_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma bytes_at_magree C m m' A bs :
bytes_at asegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at asegs m' A bs.
Proof.
intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply A2.bytes_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma wr_at_magree C m m' A n :
wr_at asegs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at asegs m' A n.
Proof. intros H AG HC H0 H1. eapply A2.wr_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha]. Qed.

Lemma auxv_ok_magree {RCEIL : RunCeiling} C m m' B :
auxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ (AUXV_CELL <= a < AUXV_CELL + 8)) -> auxv_ok m' B.
Proof.
intros sfH_; first [ sf_destruct 13%nat sfH_ as av x3 x4 x5 x6 x11 x12 x23 rnd AC AL RN H | sf_fb; destruct sfH_ as (av & x3 & x4 & x5 & x6 & x11 & x12 & x23 & rnd & AC & AL & RN & H) ]; intros AG HC.
first [ unshelve sf_eexists 9%nat; [ exact (av) | exact (x3) | exact (x4) | exact (x5) | exact (x6) | exact (x11) | exact (x12) | exact (x23) | exact (rnd) | ] | sf_fb; exists av, x3, x4, x5, x6, x11, x12, x23, rnd ]. split; [|split; [|split; [|exact H]]].
- eapply rw_cells_magree; [exact AC| exact AG|]. cbn. intros a Ha X. destruct (HC a X) as [_ Y]. apply Y. exact Ha.
- eapply bytes_at_magree; [exact AL| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _].
unfold auxv_list in Ha. rewrite u64s_length, map_length in Ha. cbn in Ha. lia.
- eapply bytes_at_magree; [exact RN| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _]. rewrite zeros_length in Ha. lia.
Qed.

Section ASM.
Context {RCEIL : RunCeiling}.
Variables (R : Type) (k : mstate -> optr -> X1qu.M R) (bail : X1qu.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : AMpre st.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis KH : forall st1 mo s' ms',
am_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
implT o (k st1 mo) s' Q ms'.

Definition FP (stX : mstate) (a : Z) : Prop := alloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

#[using="Type"] Lemma FP_am stX a : am_fp stX lo (bv_unsigned sp) a -> FP stX a.
Proof. intros H. left. apply am_fp_alloc_fp. exact H. Qed.

#[using="RCEIL TP"] Lemma ETP : errno_addr tp = 0x1a620 - 164.
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

#[using="TK KH"] Lemma finish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
am_rel st st1 mo -> mrep st1 m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (errno_addr tp) [C4 e] -> auxv_ok m' (bv_unsigned sp) -> magree (FP st1) m m' ->
brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rv = pw st1 mo ->
implT o (k st1 mo) sX Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)).
Proof.
intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv REL MR1 MI1 ST1 ERR1 AUX1 AG BL1 P1 P2 P3 ->.
apply KH; [| exact BL1]. unfold am_post. sf_eexists 16%nat. split; [reflexivity|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact AUX1|]. split.
{ apply pres_of_magree. exact AG. }
split; [exact MR1|]. split.
{ destruct TK as [T1 T2]. split; intros; rewrite (amr_shadow _ _ _ REL) in *; rewrite (amr_tick _ _ _ REL); eauto. }
auto.
Qed.

#[using="Type"] Lemma FP_mono stX stY a :
(forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
FP stX a -> FP stY a.
Proof.
intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
first [ pose proof (HR rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' K' B' L' | sf_fb; destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L') ]. left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
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
- first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RBC RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF) ]. destruct (reserved_disjoint _ _ RF) as [D1 D2]. pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
- pose proof (fresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold alloc_ceiling in C. lia.
Qed.

#[using="Type"] Lemma brk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.

#[using="Type"] Lemma am_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> X1qu.M RR) (bl : X1qu.M RR) :
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

#[using="TK KH"] Lemma finish_K' : forall (gpr : word) (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
gpr = gp ->
am_rel st st1 mo -> mrep st1 m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (errno_addr tp) [C4 e] -> auxv_ok m' (bv_unsigned sp) -> magree (FP st1) m m' ->
brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rv = pw st1 mo ->
implT o (k st1 mo) sX Q
(MS (mkR ra sp gpr tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)).
Proof. intros gpr. intros until rv. intros ->. apply finish_K. Qed.

#[using="TP"] Lemma repfoot_low stY a : regions_wf stY -> repfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof.
intros WF H. rewrite ETP. pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as _ WR _ WA WG | sf_fb; destruct sfP_ as (_ & WR & _ & WA & WG) ]. unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|C]]]]]]; unfold CTX, MLOCK, NEED_LOCKS, X0qm.PAGE_SIZE_A in *; try lia.
- first [ sf_destruct 4%nat C as ak ar Hak Hin | sf_fb; destruct C as (ak & ar & Hak & Hin) ]. first [ pose proof (area_conc stY ak ar WF Hak) as sfP_; sf_destruct 10%nat sfP_ as rra Hra Ca Sa0 Sa1 SaL NKa RB0 RBAL RBC | sf_fb; destruct (area_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC) ].
first [ pose proof (WR _ _ Hra) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF) as [D1 D2]. unfold alloc_ceiling in RBC. lia.
- first [ sf_destruct 4%nat C as b gh Hb Hin | sf_fb; destruct C as (b & gh & Hb & Hin) ]. first [ pose proof (group_conc stY b gh WF Hb) as sfP_; sf_destruct 9%nat sfP_ as rb Hrb Cb Krb Sb0 Sb1 Al RB0 RBC | sf_fb; destruct (group_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC) ].
first [ pose proof (WR _ _ Hrb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF) as [D1 D2]. unfold alloc_ceiling in RBC. lia.
- first [ sf_destruct 7%nat C as rid rg v Hrg Krg Hin _ | sf_fb; destruct C as (rid & rg & v & Hrg & Krg & Hin & _) ]. first [ pose proof (WR _ _ Hrg) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RBC RF | sf_fb; destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF) ]. destruct (reserved_disjoint _ _ RF) as [D1 D2]. unfold alloc_ceiling in RBC. lia.
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

#[using="Type"] Lemma repfoot_clear stY mY x L a :
mrep stY mY -> ranges_free (live_ranges stY) x L = true -> repfoot stY a \/ grp_region_addr stY a -> ~ (x <= a < x + L).
Proof.
intros MRY RF H. pose proof MRY as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as RS WR DJ WA WG | sf_fb; destruct sfP_ as (RS & WR & DJ & WA & WG) ].
pose proof (clear_range_of_ranges_free stY x L RF) as CR.
assert (IMG : forall y, 0x10000 <= y < 0x1b000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (image_clear_of_ranges_free stY x L y RS RF Hy)).
destruct H as [[C|[C|[C|[C|[C|[C|C]]]]]]|C]; unfold CTX, MLOCK, NEED_LOCKS, X0qm.PAGE_SIZE_A in *.
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- first [ sf_destruct 4%nat C as ak ar Hak Hin | sf_fb; destruct C as (ak & ar & Hak & Hin) ]. destruct (WA ak ar Hak) as (rra & Hra & _).
eapply (CR (fst ak) rra a Hra). eapply area_in_live; eauto.
- first [ sf_destruct 4%nat C as b gh Hb Hin | sf_fb; destruct C as (b & gh & Hb & Hin) ]. destruct (WG b gh Hb) as (rb & Hrb & _).
eapply (CR (fst b) rb a Hrb). eapply group_in_live; eauto.
- first [ sf_destruct 7%nat C as rid rg v Hrg Krg Hin _ | sf_fb; destruct C as (rid & rg & v & Hrg & Krg & Hin & _) ]. eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
- first [ sf_destruct 5%nat C as rid rg Hrg Krg Hin | sf_fb; destruct C as (rid & rg & Hrg & Krg & Hin) ]. eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed.

#[using="RCEIL"] Lemma image_range_clear stY x L : s_reserved stY = agent_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
x + L <= 0x10000 \/ 0x1b000 <= x.
Proof.
intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)). cbn in *. lia.
Qed.

End ASM.

