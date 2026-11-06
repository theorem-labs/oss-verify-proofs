(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free F_free_spec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RF_ntf RF_free_K RF_free.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_free_spec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMalloc_iface."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0B"; "0C"; "1list"; "2and"; "2not"; "3Z"; "0FPT"; "0LB'"; "0LB0"; "0RUNp"; "4lbrm"; "5blk_addr"; "5blk_size"; "5block"; "6mem"; "7alloc_ceiling"]; ["8RAUXV_CELL"; "8RCTX"; "9rauxv_ok"; "9rpres_except"; ":ralloc_static"; ":rdeep_pres"; ":rfree_stmt"; ":rheap_pres"; ":rimg_pres"; ";In"; "<add"; "<le"; "<lt"; "<pow"; "0a"; "0b"]; ["0blk"; "0blk'"; "0lo"; "0m"; "0m'"; "0sp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_rauxv_ok_pres_B := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "Q>'5!p021&>&Bv9r3r1%43321&Cr5r4%33216&K%1237&4r8r2%211%411p061pQNE1'3&@%;21A&L&J+8%2251%42F1%8261r9%11?%B11p041pQNQ31r6%Q13Q01Kp031p0B1p0L1p0Q11p2Q:1pR:Q81pR8Q91p4Q;1")) (only parsing).
Variable C : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres_B) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres_B) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres_B) 2%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres_B) 3%nat 0%nat).
Lemma rauxv_ok_pres_B : ltac:(sec_stmt2 constr:(SEC_T_rauxv_ok_pres_B) 4%nat 0%nat).
Proof.
intros (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
- eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
- eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
- eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.
End SE.
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 818108 <= a < 818112) m m'.
Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 818108 <= a < 818112.
Lemma rfp_not_high : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "<'5&KvQ5r1%3221&4v6r2%211%411p061pQN;1").
Proof. intros a.
intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
intros [FP|[DR|ER]].
- pose proof (rfree_fp_lt st m lo sp a MR ltac:(pose_ceil; lia) LS FP). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rfp_not_img := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "Q3'5'3&K+elP0r1%3221&L+mTP0%2241%8241&4&Ar2%;221&J+m0%2251%;251%A251%911+hnmLr3%D221+hnn0%B231%H231%@11v6r4%211%D11p051p0=1p0H1pQNQ21")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rfp_not_img) 0%nat 0%nat).
Lemma rfp_not_img : ltac:(sec_stmt2 constr:(SEC_T_rfp_not_img) 1%nat 0%nat).
Proof.
intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ exact (N1 X).
+ destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
+ destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
+ destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- exact (N2 ER).
Qed.
End SE.
Lemma rfp_not_image : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "F'5'3&K+elP0r1%3221&L+mTP0%2241%8241&4&Dr2%211%411v6r3%211%811p051p0;1pQNE1").
Proof. intros a.
intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rfp_not_block := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "N&='5&Ir2&:v8vQ0%3221%63851'3&K&;r3%211%421;&L&J&<%116%3261%52A1%<271&4v6%11<%311p051p0C1pQNK1pR4M1")) (only parsing).
Variable blk' : ltac:(sec_ty2 constr:(SEC_T_rfp_not_block) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rfp_not_block) 1%nat 0%nat).
Lemma rfp_not_block : ltac:(sec_stmt2 constr:(SEC_T_rfp_not_block) 2%nat 0%nat).
Proof.
intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
destruct (UNK a Hab) as [h UNKa].
destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). pose_ceil.
pose proof (lr_lo_group rg Krg) as LRG.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ unfold RCTX in X. lia.
+ destruct X as (rid & r & Hr & NK & Hin).
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
destruct (DJ _ _ _ _ Hr Hrg NE); lia.
+ destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
* specialize (HD b gh Hb E). unfold IB in HD. lia.
* destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
+ destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
* rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
* pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- lia.
Qed.
End SE.
Lemma rheap_pres_free : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "E'2&=%211&Ir1r2%33521&:v8vQ0%3221%83:61p061pR0<1&GvQ5vQ3vQ4%44=321p061p@B1").
Proof. intros LB'.
intros HLB a Ha CA. apply PE; [exact Ha|].
destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
- apply rfp_not_high. exact CA.
- apply rfp_not_image; assumption.
- apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.
Lemma rfp_not_img_all : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "Q3'5'3&K+RPP0r1%3221&L+mTP0%2241%8241&4&Ar2%;221&J+m0%2251%;251%A251%911+hnmLr3%D221+hnn0%B231%H231%@11v6r4%211%D11p051p0=1p0H1pQNQ21").
Proof. intros a.
intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ exact (N1 X).
+ destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
+ destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
+ destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- exact (N2 ER).
Qed.
Lemma rimg_pres_free : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "4&HvQ3vQ4%3221").
Proof.
intros a Ha N1 N2. refine (proj1 (PE a _ _)); [lia| apply rfp_not_img_all; [exact Ha| exact N1| unfold RERRNO in N2; exact N2]].
Qed.
Lemma rfp_not_deep : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "C'5'3&K&?v9%211r1%5221&LvQ2%2241%:241&4v6r2%211%411p061pQNB1").
Proof. intros a.
intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ unfold RCTX in X. lia.
+ destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
+ destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). pose_ceil. lia.
+ destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- lia.
Qed.
Lemma rdeep_pres_free : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec ">&LvQ5&M+2+R0%3221%6251&Ev9vQ2vQ3vQ4%544321p071").
Proof.
intros Hsp a Ha. refine (proj1 (PE a _ _)); [pose_ceil; lia| apply rfp_not_deep; exact Ha].
Qed.
Lemma rauxv_ok_free : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "@'5&Bv9vQ3r1%43321&KvQ5r2%3221vQ4r3%;3:21p041p091p2?1").
Proof. intros B.
intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
- intros a Ha. apply rfp_not_high. lia.
- intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.
Theorem rfree_spec_proof : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_spec "3&Fv9%211").
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0.
destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
cbn [blk_addr blk_slot fst snd] in OA.
pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
{ unfold RFREE_SYM. step. apply evt_done. reflexivity. }
cbv beta. intros ms' ->.
eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
(fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
/\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
- exact Hst.
- exact HOK.
- apply rimplT_reach.
apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
[unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
- intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
unfold rfree_post. do 16 eexists. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
split. { pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
exact (rdeep_pres_free st st' lo (bv_unsigned sp) m m' MR SLO' PE ltac:(lia)). }
split. { exact (rimg_pres_free st st' lo (bv_unsigned sp) m m' MR LO PE). }
split; [reflexivity|]. split; [reflexivity|].
exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
split; [reflexivity|]. split; [exact MR'|]. split.
+ unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
+ destruct LEAF as (ans & o' & FO).
eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.
End CEIL_WRAP_1.
