(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W9 RASlot_W12 RASlot_W19 RASlot_M0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RASlot_M2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W9."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMalloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1option"; "2and"; "2eq"; "2iff"; "2not"; "3N"; "3Z"; "0RUNp"; "4meta_slot"; "5grp_hdr_cov"; "5mrel"; "5unk_agree"; "6wa"; "7rta_fp"; "8RCTX"]; ["8rmrep"; "9rmalloc_fp"; ":RKGroup"; ":Unknown"; ":aptr"; ":cell_read"; ":cellval"; ":conc"; ":get_shadow"; ":ghdr"; ":mstate"; ":r_base"; ":r_kind"; ":r_len"; ":region"; ":rkind"]; [":round_up_pg"; ":s_groups"; ":s_regions"; ":s_shadow"; ":shadow"; ";add"; ";le"; ";lt"; "0a"; "0b"; "0h"; "0lo"; "0m"; "0mE"; "0o"; "0off"]; ["0q"; "0r"; "0rid"; "0sp"; "0st"; "0st0"; "0stE"; "<is_Some"; "<lookup"; "=bv"; "=bv_unsigned"; ">N_countable"; ">Z_countable"; ">prod_countable"; "?prod_eq_dec"; "@gmap"]; ["@gmap_lookup"; "Aeq_dec"; "Beq_dec"; "0tp"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.
Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.
Definition rHAG_stmt : Prop :=
forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -144) ->
rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (ag_body f sc req k bail st2 mm) s' Q
(MS (rag_regs (Z_to_bv 64 0x9bc8c) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
F (Z_to_bv 64 0x9bc98) fc None m3 (seg_rom rsegs)).
Hypothesis HAG : rHAG_stmt.
Lemma rerrno_lit2 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M2 ";'3'7&Q5&QJyR0vR3%3221-U4%6221+hnmL%:3921").
Proof. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma rconc_meta_stable : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M2 "D'J&D';vQDr2%3221&9%1243'3'7&Gr4r3%3221%42;2%73621p091p0<1pS2A1pS>C1").
Proof. intros stE q.
intros REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rta_fp_malloc_fp := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M2 "Q<'J'QIyR0%211'1y8%511%311p051'7&@v8r3r2%43321';vQDr4%3221&D&9r1%2261r7%421;p031pS271&>vQ;&QJvQC%22M1%54@41?&AvQEr5%36I2=851p051p0<1p0E1p0J1pRBQ01pRLQ21pS>Q;1")) (only parsing).
Variable stE : ltac:(sec_ty2 constr:(SEC_T_rta_fp_malloc_fp) 0%nat 0%nat).
Variable mE : ltac:(sec_ty2 constr:(SEC_T_rta_fp_malloc_fp) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rta_fp_malloc_fp) 2%nat 0%nat).
Lemma rta_fp_malloc_fp : ltac:(sec_stmt2 constr:(SEC_T_rta_fp_malloc_fp) 3%nat 0%nat).
Proof.
intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. exact X.
- left. right. right. left. exact X.
- left. do 3 right.
pose proof (AREAS q MSq) as MSq'.
destruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. split; [exact H0|]. split; [exact K0|].
rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
- do 3 right. left. pose proof MR as (WF & _).
destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
rewrite Cb in Xq. lia.
Qed.
End SE.
Lemma rta_fp_not_image : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M2 "Q1'7'2&Q6+RPP0r1%3221&Q7+mTP0%2241%8241&5&?r2%;221&Q5+m0%2251%;251%A251%911&>vQDvQ;&QJyR0vQC%3221r3%847621%C11p0;1p0F1pRBQ01").
Proof. intros a.
intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- pose_ceil. lia.
- exact (Hc X).
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). pose_ceil. lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.
Lemma rta_fp_not_high : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M2 "A'7&Q6&QJyR0vQC%3221r1%6221&5&>vQDvQ;r2%443281%611p081pRB@1").
Proof. intros a.
pose proof (RAS_STACK_ge sc) as ASG. pose_ceil.
intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- unfold RCTX in X. lia.
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). pose_ceil. lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). pose_ceil. lia.
Qed.
Lemma runk_agree_keep : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M2 "T2'J'QIyR0%211'1y8%511%311pT:51'3'QO'6&R1&QK'Q4%544321&Q3r2%211vQD%411%<3631'N'O&Lr1%211(B%C3521%I17&QH%E4DCB9&R0%14FED;r3&Q2r6%211%86K@7541(0%12BG%Q03<31r4%81H%>6Q1F=;21%62G;%Q53A21p061p0D1pS4K1pS6Q71&D&4&QG'I&QN'7&R2%34Q?Q>21&QM&QL%26QBQAQ@541%QD4;418%O4<529&Q1r5%211%Q56@=54Q:1%?2>1%51QB%Q86C@87Q=1%B2A1%D241pRDF1%QB1Q0%R23QD1Q@'2&Q6z%221Q5&Q7&Q0&M%11B%311%52Q;1%:271'F&E&Hr7%22R81%421K(C%11QD%RF3831&5&:r8%23R@1QO%411r=&=&Q5&K%117%321@%511%711vQ<%113%S63S831p0<1p0B1p0L1p0Q81p0R61pRFQM1pS0QN1pS4S11pS6S=1&<vQ>%23RG1QJp041p0QD1p0R<1p0S:1pRLSH1pS>T11").
Proof. intros stE mE.
intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.
Section SE.
Local Abbreviation SEC_T_rta_fp_not_inband := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M2 "R0'6'N'7'3'1%114&QH'QO&R1&QK%34:219&R0%14<43;r3&Q2vQD%211%;6A@7541(0r2%22C1%B3@41'O&L%11;(B%G3421'2&Q6z%221A&Q7&Q0&Mr4%211%411%62H1%;281&5&:r6%23K18%411&>vQ;&QJyR0vQC%3221&Q5&K%11;r5%4221%;4Q8:61%A11p0>1p0D1p0Q11p0Q71pS0QK1pS4QM1pS6QO1")) (only parsing).
Variable rid : ltac:(sec_ty2 constr:(SEC_T_rta_fp_not_inband) 0%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_rta_fp_not_inband) 1%nat 0%nat).
Variable off : ltac:(sec_ty2 constr:(SEC_T_rta_fp_not_inband) 2%nat 0%nat).
Lemma rta_fp_not_inband : ltac:(sec_stmt2 constr:(SEC_T_rta_fp_not_inband) 3%nat 0%nat).
Proof.
intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). pose_ceil.
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
- destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rag_phase := (forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte), ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m1 -> mem_inv rsegs m1 -> rw_cells rsegs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
rimplT o (as_grp full_lay f sc req k bail st1) s Q
(MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
F (Z_to_bv 64 0x9bc74) fc None m1 (seg_rom rsegs))) (only parsing).
Variable st1 : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 0%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 1%nat 0%nat).
Variable t0' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 2%nat 0%nat).
Variable t1' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 3%nat 0%nat).
Variable a0' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 4%nat 0%nat).
Variable a1' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 5%nat 0%nat).
Variable a2' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 6%nat 0%nat).
Variable a3' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 7%nat 0%nat).
Variable a4' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 8%nat 0%nat).
Variable a5' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 9%nat 0%nat).
Variable a6' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 10%nat 0%nat).
Variable a7' : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 11%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rag_phase) 12%nat 0%nat).
Lemma rag_phase : ltac:(sec_stmt2 constr:(SEC_T_rag_phase) 13%nat 0%nat).
Proof.
intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. pose_ceil.
pose proof rerrno_lit2 as EA.
pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
rewrite (as_grp_eq f sc req k bail st1).
riprefixT. unfold rag_regs.
eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.
assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
assert (BL1 : brk_link_ps st1 s).
{ unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
{ apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| pose_ceil; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
- intros a Ha. apply rta_fp_not_high. exact Ha.
- intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
assert (ERR2 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
[ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
| rewrite unsigned_lit by lia; exact ST1 | exact CLO
| rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
intros st2 mo s' ms' PO BL2 LF.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL).
rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
replace (ret_pc (Z_to_bv 64 0x9bc8c)) with (Z_to_bv 64 0x9bc8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof MR3 as (WF3 & _). pose proof WF3 as (RS3 & WR3 & DJ3 & _).
assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0xe9000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0xc7bbc <= a < 0xc7bc0)) ->
~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
{ intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. lia.
- unfold RCTX in *. lia.
- destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). pose_ceil.
pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
- destruct X as [XC XF]. pose_ceil.
pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk)).
{ eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }
assert (REL02 : mrel st st2).
{ split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
{ intros q (ar & arr & kk & Ha & Hk & E). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
exists ar, arr', kk. auto. }
assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
{ eapply rpres_except_trans.
- eapply rpres_except_mono; [exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
- eapply rpres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
+ left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
+ do 4 right. eapply (fresh_addr_anti st0 st1); [| | exact X].
* rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
* intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }
assert (UA3 : unk_agree st2 o m3).
{ eapply (runk_agree_keep st2 m3).
- rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
- intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
+ destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
+ exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
- intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
- intros rid r off h Hr Hk Ho Hc NG.
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). pose_ceil.
transitivity (m1 (wa (r_base r + off))).
+ refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
* lia.
* rewrite unsigned_lit in X by lia. destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
* destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
* assert (Hr2 : (s_regions st2) !! rid = Some r).
{ rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. exact Hk. }
assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
* rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
+ refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
destruct mo as [mm|].
-
destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _). pose_ceil.
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [pose_ceil; lia| exact MI3]. }
cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply evt_done.
eapply (HAG st1 st2 mm m3 s'); try eassumption.
+ eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
+ eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
+ eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
+ eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
-
cbn iota.
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| exact MI3]. }
cbv beta. intros ms' ->. cbn [Z.eqb].
eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
cbv beta. intros ms' (a1x & a2x & -> & ST4). apply evt_done.
apply HK. unfold ras_post2.
do 14 eexists. exists m3, errv3. split; [reflexivity|].
split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
split. { constructor.
- intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
- intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
- rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
- intros H; exfalso; lia.
- intros _ H; exfalso; lia. }
split. { rewrite (amr_counter _ _ _ REL). unfold ctx. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
left. reflexivity.
Qed.
End SE.
End LEVEL.
End CEIL_WRAP_1.
