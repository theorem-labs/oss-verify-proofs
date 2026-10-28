(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qb X0pc X0px X0qc X0q2 X0q3 X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qi X0q4 X0pk X0p3 X0oz X0p4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lz X1m0 X1m5 X1lh X1kw X1ks.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0q7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0q9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rauxv_ok_pres_B {RCEIL : RunCeiling} : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
rauxv_ok m' B.
Proof.
intros C m m' B sfH_; first [ sf_destruct 14%nat sfH_ as av x3 x4 x5 x16 x6 x11 x12 x23 rnd C1 A1 A2 H | sf_fb; destruct sfH_ as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) ]; intros HP HB HC.
first [ unshelve sf_eexists 10%nat; [ exact (av) | exact (x3) | exact (x4) | exact (x5) | exact (x16) | exact (x6) | exact (x11) | exact (x12) | exact (x23) | exact (rnd) | ] | sf_fb; exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd ]. split; [|split; [|split; [|exact H]]].
- eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
- eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
- eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

Section FP.
Context {RCEIL : RunCeiling}.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 316332 <= a < 316336) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 316332 <= a < 316336.

#[using="RCEIL m MR LO LS"] Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof.
intros Ha. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- pose proof (rfree_fp_lt st m lo sp a MR ltac:(unfold alloc_ceiling; lia) LS FP). lia.
- first [ sf_destruct 6%nat DR as rid r Hr _ _ Hin | sf_fb; destruct DR as (rid & r & Hr & _ & _ & Hin) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- lia.
Qed.

#[using="RCEIL m MR LO"] Lemma rfp_not_img a : 0x3b000 <= a < 0x6e000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (316332 <= a < 316336) -> ~ FPT a.
Proof.
intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ exact (N1 X).
+ first [ sf_destruct 5%nat X as rid r Hr _ Hin | sf_fb; destruct X as (rid & r & Hr & _ & Hin) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint _ _ RF) as sfP_; first [ sf_destruct 4%nat sfP_ as ? ? ? ? | sf_fb; destruct sfP_ as (? & ? & ? & ?) ]. pose proof (lr_lo_ge r). lia.
+ first [ sf_destruct 4%nat X as b gh Hb Hin | sf_fb; destruct X as (b & gh & Hb & Hin) ]. first [ pose proof (rgroup_conc st b gh WF Hb) as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb _ Sb0 Sb1 _ | sf_fb; destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _) ].
first [ pose proof (WR _ _ Hrb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint _ _ RF) as sfP_; first [ sf_destruct 4%nat sfP_ as ? ? ? ? | sf_fb; destruct sfP_ as (? & ? & ? & ?) ]. lia.
+ first [ sf_destruct 7%nat X as rid r v Hr _ Hin _ | sf_fb; destruct X as (rid & r & v & Hr & _ & Hin & _) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint _ _ RF) as sfP_; first [ sf_destruct 4%nat sfP_ as ? ? ? ? | sf_fb; destruct sfP_ as (? & ? & ? & ?) ]. lia.
- first [ sf_destruct 6%nat DR as rid r Hr _ _ Hin | sf_fb; destruct DR as (rid & r & Hr & _ & _ & Hin) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint _ _ RF) as sfP_; first [ sf_destruct 4%nat sfP_ as ? ? ? ? | sf_fb; destruct sfP_ as (? & ? & ? & ?) ]. lia.
- exact (N2 ER).
Qed.

#[using="RCEIL m MR LO"] Lemma rfp_not_image a : 0x3b000 <= a < 0x6e000 -> ~ ralloc_static a -> ~ FPT a.
Proof.
intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

#[using="RCEIL m C MR LO BLKR SHR"] Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
destruct (UNK a Hab) as [h UNKa].
first [ pose proof (WR _ _ Hrg) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RGC RGF | sf_fb; destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF) ]. pose proof (rreserved_disjoint _ _ RGF) as sfP_; first [ sf_destruct 4%nat sfP_ as ? ? ? ? | sf_fb; destruct sfP_ as (? & ? & ? & ?) ]. unfold alloc_ceiling in RGC.
pose proof (lr_lo_group rg Krg) as LRG.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ unfold RCTX in X. lia.
+ first [ sf_destruct 5%nat X as rid r Hr NK Hin | sf_fb; destruct X as (rid & r & Hr & NK & Hin) ].
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
destruct (DJ _ _ _ _ Hr Hrg NE); lia.
+ first [ sf_destruct 4%nat X as b gh Hb Hin | sf_fb; destruct X as (b & gh & Hb & Hin) ]. destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
* specialize (HD b gh Hb E). unfold IB in HD. lia.
* first [ pose proof (rgroup_conc st b gh WF Hb) as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb Krb Sb0 Sb1 _ | sf_fb; destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _) ].
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
+ first [ sf_destruct 7%nat X as rid r v Hr Kr Hin HC | sf_fb; destruct X as (rid & r & v & Hr & Kr & Hin & HC) ]. destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
* rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
* pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- first [ sf_destruct 6%nat DR as rid r Hr Hr' Kr Hin | sf_fb; destruct DR as (rid & r & Hr & Hr' & Kr & Hin) ].
destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- lia.
Qed.

#[using="RCEIL st st' lo C MR LO LS BLKR SHR PE FPT"] Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof.
intros HLB a Ha CA. apply PE; [exact Ha|].
destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
- apply rfp_not_high. exact CA.
- apply rfp_not_image; assumption.
- apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

#[using="st st' lo MR LO LS PE FPT"] Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof.
intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
- intros a Ha. apply rfp_not_high. lia.
- intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

Theorem rlibc_free_spec_proof {RCEIL : RunCeiling} : rlibc_free_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0.
first [ sf_destruct 8%nat HP as st LB0 PERM Hst MR [BL AR] RPL GA | sf_fb; destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR] & RPL & GA) ].
assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
pose proof (X0q9.areach_cinv_proof _ _ AR) as C.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
cbn [blk_addr blk_slot fst snd] in OA.
pose proof (X0q7.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
(fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
/\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
- exact Hst.
-   rewrite <- Hst, s_ceil_strip. exact (X0q7.areach_s_ceil _ _ _ AR).
- exact HOK.
- apply rimplT_reach.
apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
[unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
- intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
first [ sf_destruct 26%nat FE as w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m' -> MI' ST' ERR' MR' PE SHR BLKR EB BRKR | sf_fb; destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR) ].
pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
unfold rfree_post. sf_eexists 16%nat. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
assert (HPf : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m').
{ apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
split; [exact HPf|].
split; [reflexivity|]. split; [reflexivity|].
exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
split; [reflexivity|]. split; [exact MR'|]. split; [split| split].
+   unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
+ destruct LEAF as (ans & o' & FO).
eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
+
eapply rheap_pres_rw_cells; [exact HPf| exact RPL|].
right; left. unfold RREPLACED, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
+
cbn [ps_hdr set_m]. destruct LEAF as (ans & o' & FO). unfold lbrm.
eapply (rga_free ref_reserved st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' (ps_hdr s) AR Hin0); [reflexivity| | exact FO| exact GA].
cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.

Theorem rfree_spec_proof {RCEIL : RunCeiling} : rfree_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0.

eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
{ unfold RFREE_SYM. step. apply evt_done. reflexivity. }
cbv beta. intros ms' ->.
exact (rlibc_free_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0).
Qed.
