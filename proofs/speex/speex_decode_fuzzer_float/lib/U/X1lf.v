(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.

From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1po X1q6 X1qh X1qj X1qd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0q7 X0qb.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qn X0py X0qd X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0p8 X0pd X0pe X0pa X0p7 X0pf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1ky X1lz X1m0 X1lw X1m4 X1kr X1la X1k8 X1lb X1lc X1ld X1l9 X1m5 X1m6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0q8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rmembed_strel_follow {RCEIL : RunCeiling} {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : X1qu.M R1) (t2 : X1qu.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
implM rsegs (membed alloc_ceiling t1) s Q1 ms ->
implM rsegs (membed alloc_ceiling t2) s
(fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
exists r1, []. cbn. auto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
impl rsegs (at_node rsegs) (X1bs.bind _ (Ret Unr) f) Qx msx = impl rsegs (at_node rsegs) (f Unr) Qx msx) by reflexivity.
destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
5:{ cbn [ev_step] in *. unfold munr in *. cbn [X1bs.bind] in *. exact H. }
5:{ cbn [ev_step] in *. unfold munr in *. cbn [X1bs.bind] in *. exact H. }
all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
eapply impl_epost_mono; [eapply IH; exact H1|];
intros [r2' s2] ms2; cbn; intros sfH_; first [ sf_destruct 6%nat sfH_ as r1' ans F1 F2 HR HQ | sf_fb; destruct sfH_ as (r1' & ans & F1 & F2 & HR & HQ) ];
exists r1', (z :: ans); cbn; auto.
Qed.

Lemma rimplT_silent {RCEIL : RunCeiling} {R} o (t : X1qu.M R) o' (x : R) s Q ms :
mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt rsegs (Q x s) ms.
Proof. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

Lemma rheap_pres_of_fp {RCEIL : RunCeiling} st st' LB lo sp m m' :
RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
rheap_pres LB sp m m'.
Proof.
intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
- destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); unfold alloc_ceiling in *; lia.
- destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
- first [ pose proof (rblock_inside st LB m blk MF MR Hin) as sfP_; sf_destruct 12%nat sfP_ as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | sf_fb; destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ].
unfold alloc_ceiling in *.
pose proof MR' as (WF' & _). pose proof WF' as sfP_; first [ sf_destruct 4%nat sfP_ as _ WR' DISJ' _ | sf_fb; destruct sfP_ as (_ & WR' & DISJ' & _) ].
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 4%nat sfP_ as _ WR DISJ _ | sf_fb; destruct sfP_ as (_ & WR & DISJ & _) ].
destruct REL as [RREG _ _]. first [ pose proof (RREG _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as r1 Hr1 K1 B1 L1 | sf_fb; destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1) ].
pose proof (round_up_pg_mono _ _ L1) as RL1.
pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
+ lia.
+ rewrite unsigned_lit in H by lia. lia.
+ unfold RCTX in H. lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

Lemma ruser_chunk {RCEIL : RunCeiling} st' m' (p : aptr) r n :
rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
exists junk, rw_cells rsegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof.
intros MR Hr Hk P0 PN N0.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF _ _ _ _ SH | sf_fb; destruct sfP_ as (WF & _ & _ & _ & _ & SH) ]. destruct (SH (fst p) r Hr Hk) as [HW _].
pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as sfP_; first [ sf_destruct 4%nat sfP_ as R4 _ RC RI | sf_fb; destruct sfP_ as (R4 & _ & RC & RI) ]. unfold alloc_ceiling in RC.
rewrite (conc_region' st' p r Hr).
assert (W : wr_at rsegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
split; [exact L| exact I].
Qed.

Section TOPLEVEL.
Context {RCEIL : RunCeiling}.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
exists st2 r ans o1,
fst res = strip st2
/\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
/\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

#[using="as_pre as_inv RAS AS_PRE RBIG"] Theorem rlibc_malloc_spec_proof : rlibc_malloc_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR0.
assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
first [ sf_destruct 8%nat HEAP as st LB0 HPERM Hst MR [BLK AR] RPL GA | sf_fb; destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR] & RPL & GA) ]. rename LB into LBc. rename LB0 into LB.
pose proof (X0q8.areach_facts_proof _ _ AR) as MF.
assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
assert (RPLR : rclient_range LBc (bv_unsigned sp) RREPLACED (Z.of_nat (cells_size [C4 (wz 0)]))).
{ right; left. unfold RREPLACED, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }

assert (STEP : forall (b : bool) (f1 f2 : PState -> PState) (r1 r2 : option bptr) (sx : PState) Q (msx : machine_state),
evt rsegs (Q (if b then r1 else r2) ((if b then f1 else f2) sx)) msx ->
implM rsegs (if b then (mupd f1 ;;; mret r1) else (mupd f2 ;;; mret r2)) sx Q msx).
{ intros b f1 f2 r1 r2 sx Q msx H. destruct b.
- eapply (implM_bind rsegs _ _ _ (fun _ sy msy => sy = f1 sx /\ msy = msx)); [apply implM_upd; apply evt_done; split; reflexivity|].
intros [] sy msy [-> ->]. apply implM_ret. exact H.
- eapply (implM_bind rsegs _ _ _ (fun _ sy msy => sy = f2 sx /\ msy = msx)); [apply implM_upd; apply evt_done; split; reflexivity|].
intros [] sy msy [-> ->]. apply implM_ret. exact H. }
unfold raw_malloc.
eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0' s1' ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind rsegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
{ rewrite <- Hst. unfold cmalloc.

rewrite (s_ceil_strip st), (X0q7.areach_s_ceil _ _ _ AR).
eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
x = (strip st2, r)
/\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
- eapply implM_mono.
+ eapply (rmembed_strel_follow CREL).
* pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
* unfold rimplT in |- *.
pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
unfold rimplT in X. exact X.
+ intros [cst2 r'] s' ms'' sfH_; first [ sf_destruct 6%nat sfH_ as [o1 [st2 r]] ans F1 F2 HC CQ | sf_fb; destruct sfH_ as ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ) ]. unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
first [ unshelve sf_eexists 4%nat; [ exact (st2) | exact (r) | exact (ans) | exact (o1) | ] | sf_fb; exists st2, r, ans, o1 ]. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
- intros [cst2 r'] s' ms'' sfH_; first [ sf_destruct 8%nat sfH_ as st2 r ans o1 E F1 F2 CQ | sf_fb; destruct sfH_ as (st2 & r & ans & o1 & E & F1 & F2 & CQ) ]. inversion E; subst. clear E.
apply implM_ret. apply evt_done. unfold rmidQ. first [ unshelve sf_eexists 4%nat; [ exact (st2) | exact (r) | exact (ans) | exact (o1) | ] | sf_fb; exists st2, r, ans, o1 ]. cbn [fst snd].
split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
intros [cs c] s' ms'' MQ. cbv beta iota.
first [ sf_destruct 9%nat MQ as st2 r ans o1 Ecs Ec F1 F2 CQ | sf_fb; destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ) ]. cbn [fst snd] in Ecs, Ec. subst cs c.
pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.

assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
| Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
follow (cmalloc (strip st) n) ans = Some y).
{ intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
cbv zeta.
set (hdr1 := hdr_after (ps_m s) (strip st2) (ps_hdr s)).
destruct r as [[g idx]|].
-
cbn [rcoreQ] in CQ.
first [ sf_destruct 40%nat CQ as b rg m1 errv1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' u3 u4 u5 u6 ra' -> MR2 TK2 UA2 MI2 ST2 FR2 ERR2 AUX2 PE2 SPANFP CTR2 SO EXPO MREL BL2 PSM PSF PSO | sf_fb; destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> & MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO) ].
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as sfP_; first [ sf_destruct 4%nat sfP_ as R4 RAL RC RI1 | sf_fb; destruct sfP_ as (R4 & RAL & RC & RI1) ].
assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
set (stride := get_stride (get_meta_rec st2 g)) in *.
set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
unfold alloc_ceiling in RC, CLO. unfold RMALLOC_STACK in LO.

set (slot := slot_of st2 g idx) in *.
assert (Eslot : slot = (fst b, snd b + 16 + stride * idx)).
{ unfold slot, slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd]. f_equal. subst stride. unfold UNIT. lia. }
set (TOP := negb (m_maplen (get_meta_rec st2 g) =? 0)).
assert (TOPc : slot_top (strip st2) slot = TOP).
{ unfold slot_top. change (s_slots (strip st2) !! slot) with (s_slots st2 !! slot). rewrite Eslot. subst stride. rewrite SSL. reflexivity. }
rewrite TOPc.
set (tagm := if TOP then real_off hdr1 (strip st2) slot n else -1).
set (hdr2 := if TOP then <[slot := real_off hdr1 (strip st2) slot n]> hdr1 else hdr1).
apply STEP.
replace (if TOP then Some (slot, real_off hdr1 (strip st2) slot n) else Some (slot, -1)) with (Some (slot, tagm)) by (subst tagm; destruct TOP; reflexivity).
replace ((if TOP then fun s2 : PState => set_hdr_ps (<[slot:=real_off hdr1 (strip st2) slot n]> hdr1) (set_m (strip st2) s2)
else fun s2 : PState => set_hdr_ps hdr1 (set_m (strip st2) s2)) s')
with (set_hdr_ps hdr2 (set_m (strip st2) s')) by (subst hdr2; destruct TOP; reflexivity).

pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
eapply evt_mono; [exact EV|]. clear EV.
intros msf [_ EP]. unfold renf_post in EP.
first [ sf_destruct 25%nat EP as st' p w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' ER -> MI' ST' MR' TK' PE' LEAF | sf_fb; destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF) ].
first [ sf_destruct 7%nat LEAF as off OFF0 FIT Ep Est' Ep2 Eoff | sf_fb; destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff) ].
assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
pose proof (strip_eq_proj _ _ SE) as sfP_; first [ sf_destruct 8%nat sfP_ as Ec Er En Em _ _ Esl Es | sf_fb; destruct sfP_ as (Ec & Er & En & Em & _ & _ & Esl & Es) ].
assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
{ rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
assert (Epa : p = aadd slot (UNIT * off)) by (rewrite Ep, Eslot; unfold aadd, UNIT; cbn [fst snd]; f_equal; lia).
set (A := conc st' p) in *.

assert (OFF255 : off <= 255).
{ pose proof (fold_off_range (enf_off0 m st2 b stride idx) ((stride - 4 - n) / 16)) as FR.
assert (E0 : 0 <= enf_off0 m st2 b stride idx < 256) by (unfold enf_off0; cbv zeta; destruct (rdv pans_mem m st2 _ =? 0); apply land255_range).
assert (SL0 : 0 <= (stride - 4 - n) / 16) by (apply Z.div_pos; lia). specialize (FR E0 SL0). rewrite Eoff. fold stride. first [lia| subst stride; lia]. }

assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
{ unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
pose proof (FC (strip st2, Some slot) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.

set (tag := if TOP then off else -1).
pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) slot tag AR ltac:(lia) FF FC1) as AR'.
assert (Est2 : st' = havoc (aadd (fst b, sstart (X1po.MR st2 g) idx) (UNIT * off)) n (fst (enframe_at st2 g idx n off))).
{ rewrite Est', Epa, Eslot. unfold X1po.sstart, X1po.gbase, X1po.MR. rewrite Hmem. cbn [default from_option id fst snd]. subst stride. reflexivity. }
assert (Eslot2 : slot = (fst b, X1po.sstart (X1po.MR st2 g) idx)).
{ rewrite Eslot. unfold X1po.sstart, X1po.gbase, X1po.MR. rewrite Hmem. cbn [default from_option id fst snd]. subst stride. reflexivity. }
assert (SS3 : X1po.sstart (X1po.MR st2 g) idx - 3 = snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3).
{ unfold X1po.sstart, X1po.gbase, X1po.MR. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT. lia. }
assert (SS2 : X1po.sstart (X1po.MR st2 g) idx - 2 = snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -2).
{ unfold X1po.sstart, X1po.gbase, X1po.MR. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT. lia. }
assert (SS1 : X1po.sstart (X1po.MR st2 g) idx - 1 = snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -2 + 1).
{ unfold X1po.sstart, X1po.gbase, X1po.MR. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT. lia. }
assert (RGM : slot_top (strip st2) slot = TOP /\ (TOP = true -> real_off hdr1 (strip st2) slot n = off) /\ (X0qc.RBIG <= n -> TOP = true)
/\ RGA st' (if TOP then <[slot := off]> hdr1 else hdr1) (((slot, tag), A, n) :: LB)).
{ subst A hdr1 tag TOP. rewrite Epa. rewrite Eslot2. rewrite Est2. rewrite <- Hst. rewrite Epa, Eslot2, Est2 in AR'.
eapply (rga_malloc ref_reserved st LB (ps_hdr s) n m m ans st2 g b idx off AR GA ltac:(lia) F1 Hmem ltac:(lia)).
-   change (X1po.MR st2 g) with (get_meta_rec st2 g). fold stride. unfold UNIT, IB. lia.
-   intros K0. cbn [fst snd] in K0. rewrite SS3 in K0. rewrite Eoff. unfold enf_off0. cbv zeta. unfold rdv. cbn [fst snd]. rewrite K0. cbn [Z.eqb].
unfold IB, UNIT. reflexivity.
-   intros x3 xl xh K3 NZ3 K2 K1. cbn [fst snd] in K3, K2, K1. rewrite SS3 in K3. rewrite SS2 in K2. rewrite SS1 in K1.
rewrite Eoff. unfold enf_off0. cbv zeta. unfold rdv. cbn [fst snd]. rewrite K3, K2, K1.
replace (x3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ3). cbn [negb]. unfold IB, UNIT. reflexivity.
-   intros rid r0 Hr0. destruct MREL as [RR _ _]. first [ pose proof (RR rid r0 Hr0) as sfP_; sf_destruct 4%nat sfP_ as r1 Hr1 K1 _ | sf_fb; destruct (RR rid r0 Hr0) as (r1 & Hr1 & K1 & _) ]. exists r1. auto.
- exact AR'. }
first [ sf_destruct 4%nat RGM as _ RO BIG RG' | sf_fb; destruct RGM as (_ & RO & BIG & RG') ].
assert (Etag : tagm = tag) by (subst tagm tag; destruct TOP; [rewrite (RO eq_refl)|]; reflexivity).
assert (Ehdr2 : hdr2 = if TOP then <[slot := off]> hdr1 else hdr1) by (subst hdr2; destruct TOP; [rewrite (RO eq_refl)|]; reflexivity).
rewrite Etag. clearbody hdr2. subst hdr2 || rewrite Ehdr2.
destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
fold A in UCH.
unfold rmalloc_post. sf_eexists 15%nat. exists m', errv1.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
- lia.
- (clear - X Ha a En off p st' TOP slot SKL SK RI1 R4 S16 SPAN B0 hdr1 stride rg b idx g st2 n RCEIL; lia). }
assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
{ eapply rpres_except_mono.
+ eapply rpres_except_trans; [exact PE2|].
eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
+ intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
split; [exact PSF|]. split; [exact PSO|].
exists A, ujunk.
split; [reflexivity|].
split. { unfold rblock_range, alloc_ceiling. rewrite EA.
split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split; [split|].
- apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
- exact AR'.
- split.
+
eapply rheap_pres_rw_cells; [| exact RPL| exact RPLR].
eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN].
+   cbn [ps_hdr set_hdr_ps set_m]. exact RG'. }
split; [exact UCH|].
split.
2:{
intros SM.
first [ pose proof (X0q7.areach_inv _ _ _ AR) as sfP_; sf_destruct 5%nat sfP_ as Li LSi BLi INVi _ | sf_fb; destruct (X0q7.areach_inv _ _ _ AR) as (Li & LSi & BLi & INVi & _) ].
pose proof (INVL_set_tick x0 st Li BLi LSi (N.succ (s_tick st)) ltac:(cbn; lia) INVi) as INV0.
pose proof (TF0_tick_new st (N.succ (s_tick st)) (TKS_of _ _ _ _ _ INVi) ltac:(cbn; lia)) as TF0'.
unfold mrun in F1.
pose proof (malloc_core_small (set_tick (N.succ (s_tick st)) st) Li BLi LSi n INV0 TF0' ltac:(lia)
pans_mem pupd_mem pans_mem_range m ans m st2 g idx
ltac:(unfold SMALL_REQ, RSMALL_MAX, IB, UNIT in *; change (size_class 27) with 255; lia) F1) as [SC1 SC2].
exists g, idx. cbn [ps_m set_hdr_ps set_m fst snd].
change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). change (s_slots (strip st2)) with (s_slots st2).
split; [| split; [exact SC1| exact SC2]].
rewrite Eslot. subst stride. exact SSL. }

intros AE. unfold ptr_addr. cbn [ps_m set_hdr_ps set_m fst snd].
unfold raddr_exposed in AE. pose proof (BIG AE) as HT. subst tag. rewrite HT.
change (conc (strip st2) slot) with (conc st2 slot).
rewrite <- (conc_same st2 st' slot) by (rewrite Eslot; cbn [fst]; exists rg; rewrite Er; auto).
unfold A. rewrite Epa. apply X0q7.conc_aadd. rewrite Eslot. cbn [fst]. exists rg. rewrite Epa, Eslot in HrS. exact HrS.
-
cbn [rcoreQ] in CQ.
first [ sf_destruct 29%nat CQ as m1 errv1 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 -> MR2 TK2 MI2 ST2 ERR2 AUX2 PE2 MREL BL2 PSM PSF PSO | sf_fb; destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO) ].
eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_hdr_ps hdr1 (set_m (strip st2) s') /\ msx = _)).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] sx msx [-> ->]. apply implM_ret.
apply evt_done. unfold rmalloc_post. sf_eexists 15%nat. exists m1, errv1.
pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
split; [exact PSF|]. split; [exact PSO|].
split; [reflexivity|].
exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
split; [split|].
+ apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
+ eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
+ split.
*
eapply rheap_pres_rw_cells; [| exact RPL| exact RPLR].
eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN].
*

cbn [ps_hdr set_hdr_ps set_m]. subst hdr1. rewrite <- Hst.
apply (rga_malloc_none ref_reserved st LB (ps_hdr s) n m m ans st2 AR GA ltac:(lia) F1).
intros rid r0 Hr0. destruct MREL as [RR _ _]. first [ pose proof (RR rid r0 Hr0) as sfP_; sf_destruct 4%nat sfP_ as r1 Hr1 K1 _ | sf_fb; destruct (RR rid r0 Hr0) as (r1 & Hr1 & K1 & _) ]. exists r1. auto.
Qed.

#[using="as_pre as_inv RAS AS_PRE RBIG"] Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.

eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
{ unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
intros ms' ->.
exact (rlibc_malloc_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
HEAP AUXB SB ST CLO LO ERR MI TP HA N).
Qed.
End TOPLEVEL.

