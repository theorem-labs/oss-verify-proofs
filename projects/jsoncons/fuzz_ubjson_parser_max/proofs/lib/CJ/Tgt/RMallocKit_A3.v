(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMallocKit_A3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "3N"; "3Z"; "4ov_read_bytes"; "4write_to_mem"]; ["0RUNp"; "5b8"; "5meta_slot"; "5pw"; "6C1"; "6C8"; "6cell"; "7munch"; "7wmono"; "8wa"; "9rw_cells"; ":Unknown"; ":aptr"; ":c_mmap_counter"; ":cell_read"; ":cellval"]; [":conc"; ":ctx"; ":get_shadow"; ":ghdr"; ":mkGhdr"; ":mstate"; ":put_group"; ":s_groups"; ":set_bounce"; ":set_group_active_idx"; ";rsegs"; "<RCTX"; "<rmrep"; "=add"; "=land"; "=le"]; ["=lt"; "=modulo"; "=pow"; "0ai"; "0ai0"; "0b"; "0g"; "0gh"; "0h"; "0i"; "0m"; "0m'"; "0o"; "0q"; "0st"; ">lookup"]; ["?bv"; "?bv_unsigned"; "@N_countable"; "@Z_countable"; "@prod_countable"; "Aprod_eq_dec"; "Bgmap"; "Bgmap_lookup"; "Ceq_dec"; "Deq_dec"; "0v"; "0w8'"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma rmrep_set_bounce : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A3 "QA'Q5'R0yR0%211'5y8%511%311p051'=&Q<v@r4r3%43321'9&Q?z%2215&Q@+Q0%2281%7241&Q8r6%23=<1&?r5&I&Q=&Q;+k@%3221%421E%611(1&A%11H(4%11Q1%53Q231%?3>71%Q03OA1p0E1p0N1pTFQ41pSDQ51pSFQ71pSNQ@1").
Proof.
intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
apply (u8arr_write rsegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.
End CEIL_WRAP_1.
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_rconc_meta_inj := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A3 "Q4'Q5'R0yR0%211'5y8%511%311p051&L&Q<v@r4r3%43321&Br5%2214r6%4216':'=&Q0r7%221<%3229%63521%73B;9p021p0:1p0=1p0A1pSLG1pS>H1pSFJ1pSNQ31")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 1%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 2%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 3%nat 0%nat).
Lemma rconc_meta_inj : ltac:(sec_stmt2 constr:(SEC_T_rconc_meta_inj) 4%nat 0%nat).
Proof using Type st m g q.
intros MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
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
End SE.
End CEIL_WRAP_2.
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | tauto ]]);
clear MUq WMq CH end.
Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_rmrep_regroup := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A3 "T5'Q5'R0yR0%211'5y8%511%311p051'7'<'=%3221'Q3&L&Q<v@r8r7%43321':%A18&QO'R6&R5&R8&R9%34A2@1&R4&R2&R3%36E62D51%94B51C&R7%14D73Er6&Q7r9%211%A6KJ7541(0r5%22M1%G3F41'9&Q?zr1%3221&Q@+9%2241%8241';'O&N&Q2r=&2r:%23QBQA1%5241&Q=&8%13QFQE5r3%4221%<261(K%11F%QB3@31qSBQL1%C2QM1p0E1pSJQO1&G(1%R42R2R2(6&Q0r;%221R0%D21Q0%54R8R821(4%118%:3931%<31LQB&H&Q:%231:O&J%=2Q3Q1'F(E&C%QH2RBR?%22Q81%411(D%11R1%A18%J3921%K3:51%=4?H<1&Q>&R1%12S6RI+O%4221%52RM2%RK3S421&Q6r<%R:2S4QGr?%4432R?1%S63S51QLp071p0?1p0N1p0Q21p0Q@1p0R@1p0S91pTHSG1pS8SC1pS>SA1pS@SC1pS<SE1pSHSJ1pSFSK1pSNT41")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_regroup) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_regroup) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_regroup) 2%nat 0%nat).
Lemma rmrep_regroup : ltac:(sec_stmt2 constr:(SEC_T_rmrep_regroup) 3%nat 0%nat).
Proof using Type st m m'.
intros b gh g ai w8' MR Hb UNK MU WM RC Hw8.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
pose proof (rmrep_del_group st m b MR) as MR1.
assert (MR2 : rmrep (del_group b st) m').
{ eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
pose proof (round_up_pg_ge (r_len r)).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4. lia.
- change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
- unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
rewrite lookup_delete_ne in Hb2 by congruence.
destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
+ rewrite E, Hr in Hr2. inversion Hr2; subst r2.
assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
+ destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
- change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
destruct (N.eq_dec q (fst b)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
- unfold RGOT_SSP in R8. lia.
- unfold RSSP_GUARD in R9. lia. }
rewrite <- put_group_del.
eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.
End SE.
#[using="Type"] Lemma rmrep_set_group_ai : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A3 "T8'Q5'R0yR0%211'5y8%511%311p051'7'<'=%3221&L&Q<v@r8r7%43321':'Q3%A11&QO'R6&R5&R8&R9%34A2@1&R4&R2&R3%36E62D51%94C51<&R7%14E73>r6&Q7r9%211%A6KC7541(0(Q4r5%32N1r4%4221%62J1%L3J81'9&Q?zr1%3221&Q@+9%2241%8241';'O&N&Q2r=&2r:%23QFQE1%5241&Q=&8%13QJQI5r3%4221%<261(K%11F%QG3@31qSBR01%C2R11p0E1pSJR31&G(1%R82R6R6(6&Q0r;%221R5%D21Q0%54R<R<21(4%118%:3931%<31LQF&H&Q:%231:O&J%=2Q3Q1'F(E&C%QL2RGQO%22Q81%411(D%11R5%A18%J3921%K3:51%=4?H<1&Q>&R1%12S:RN+O%4221%52S22%S03S821&Q9r<r?%332RB1%S:3S91QKp061p0>1p0M1p0Q11p0Q?1p0R?1p0S=1pTHSJ1pS8SF1pS:SG1pS>SF1pS<SH1pSHSM1pSFSN1pSNT71").
Proof.
intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
eapply rmrep_regroup; eauto.
Qed.
#[using="Type"] Lemma rmrep_ctr_byte_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A3 "QO'Q5'R0yR0%211'5y8%511%311p051&Q<v@r2r1%43321'9&Q?z&M&Q1r3%211%411%7261&Q@&QB+2+Q0%3221%5271%?271':'3%11J%M11&>&Q:&I&Q=&Q;+<%3221%511u1%948H21(0(1&A&QAr4%O11%Q111+X0%5221%711(4%11QA%;3QB31%=2I1%L3I?1p0N1p0Q?1pSFQE1pSNQN1").
Proof.
intros st m (_ & (HD & _) & _) CR.
destruct HD as [[_ HB] _]. unfold ctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
rewrite (bytes_at_read rsegs m RCTX _ 12 1 HB).
all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
change (Z.to_nat 12) with 12%nat.
unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End CEIL_WRAP_3.
