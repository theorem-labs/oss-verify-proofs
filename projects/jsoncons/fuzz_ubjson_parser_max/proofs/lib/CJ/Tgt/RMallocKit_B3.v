(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMallocKit_B3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "3N"; "3Z"; "4write_to_mem"]; ["0RUNp"; "5grp_del"; "6b8"; "6wz"; "7le8"; "7wa"; "8Unknown"; "8aptr"; "8c_unmap_seq"; "8cell_read"; "8cellval"; "8conc"; "8del_group"; "8get_shadow"; "8ghdr"; "8mctx"]; ["8mstate"; "8s_groups"; "8set_seq"; "8set_unmap_seq_map"; "8set_usage"; "8upd_ctx"; "9RCTX"; "9rmrep"; ":add"; ":le"; ":lt"; ":mul"; "0bs"; "0c"; "0g"; "0gh"]; ["0h"; "0i"; "0m"; "0o"; "0p"; "0sc"; "0st"; ";insert"; ";lookup"; "<bv"; "=N_countable"; "=Z_countable"; "=prod_countable"; ">prod_eq_dec"; "?map_insert"; "@gmap"]; ["@gmap_lookup"; "@gmap_partial_alter"; "Aeq_dec"; "Beq_dec"; "0v"]]).
Ltac rctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_rmrep_set_usage := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B3 "QB'Q0'QIyR0%211'7y8%511%311p051'>&Q7v@r4r3%43321':&Q9z%2215&Q:+Q@%2281%7241&Q4r6%23=<1&?r5&E&Q8&Q6+^@%3221&Q;+8%221G%7241%911&D&C%11K%311%@3?51%Q13Q0B1p0F1p0O1pT:Q51pS<Q61pS6Q81pS>QA1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_usage) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_usage) 1%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_usage) 2%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_usage) 3%nat 0%nat).
Lemma rmrep_set_usage : ltac:(sec_stmt2 constr:(SEC_T_rmrep_set_usage) 4%nat 0%nat).
Proof.
intros MR Hsc.
pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le8 (wz v)) as L8.
pose proof (munch_write [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8)] m m (RCTX + 464 + 8 * sc) (le8 (wz v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v)) (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st (set_usage sc v st) m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite usages_set_usage by lia. replace (RCTX + 464 + 8 * sc) with ((RCTX + 464) + 8 * sc) by lia.
apply u64arr_write; [exact X3| rewrite usages_length; lia].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_usage upd_ctx c_seq c_brk set_usage_map]. reflexivity.
Qed.
End SE.
Lemma rmrep_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B3 "QA'Q0'QIyR0%211'7y8%511%311p051'>&Q7v@r3r2%43321':&Q9z%2215&Q:+X0%2281%7241&Q5&Q2%11=r5%4221&?r4&E&Q8&Q6+l@%3221%511(1&B%11J(6%11Q2%53Q331%>3=71%Q13Q0@1p0F1p0O1pT:Q51pS6Q71pS>Q@1").
Proof.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [(RCTX + 912, RCTX + 913)] m m (RCTX + 912) [b8 v] (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 912)) [b8 v] (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_seq v) st) m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left.
pose proof (rw_cells_write rsegs m (RCTX + 912) (ctx_tail_cells st) 0 (C1 (b8 (c_seq (ctx st)))) (C1 (b8 v)) X6 eq_refl eq_refl I) as W.
rewrite Z.add_0_r in W. cbn [cbytes cell_upd ctx_tail_cells Nat.eqb] in W.
unfold ctx_tail_cells, brk_word, ctx in *. cbn [s_ctx upd_ctx set_seq c_seq c_brk]. exact W.
Qed.
Lemma rmrep_set_unmap_seq : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B3 "R2'Q0'QIyR0%211'7y8%511%311p051'>&Q7v@r4r3%43321':&Q9z%2215&Q:+Q0%2281%7241&Q5'O&Q3&QG'QO&R3&QK%34E21E&QN&R1%14H54H%34II41r5&Hr1%211%=7NN954K1%?213qRLA1r6%D221&?&E&Q8&Q6+j@%3221%421Q6%611(1&B%11Q9(6%11QB%53QC31%>3G71%QA3Q@@1p0Q61p0Q?1pT:QE1pS4QF1pS6QH1pS>R11").
Proof.
intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [(RCTX + 848 + i, RCTX + 848 + i + 1)] m m (RCTX + 848 + i) [b8 v] (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 848 + i)) [b8 v] (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite unmap_seqs_set by lia. replace (RCTX + 848 + i) with ((RCTX + 848) + i) by lia.
apply (u8arr_write rsegs m (RCTX + 848) (unmap_seqs st) i (b8 v)); [exact X4| rewrite unmap_seqs_length; lia].
- right. split; [reflexivity| rctx_same].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_group_hdr_zero := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B3 "S4'Q0'QIyR0%211'7y8%511%311p051'8'='>%3221'N'4%119&Q7v@r5r4%43321';%B19&QH'QO&G&QM&R2&R3%34C2B1&QL&QJ&QK%36G62F51%:4951E&R0%14;73G&Q1r6%211%A6LK64E1(0r3%22N1%G3F41':&Q9zr1%3221&Q:+<%2241%8241'<'J&I&Mr:&2r8%23QCQB1%5241&Q8&9%13QGQF5%321H%;251(F%11E%QA3?31qS2QL1%B2QM1p0D1pS8QO1'5&3%12R7QJu8%QJ3421&Lr7r9%3221&?&E&K%1256%311%53M1R7%R:3R971p0<1p0B1p0QA1p0R:1pRJR@1pS0RC1pS:RE1pS6RJ1pS>S31")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_group_hdr_zero) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_group_hdr_zero) 1%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_rmrep_group_hdr_zero) 2%nat 0%nat).
Variable gh : ltac:(sec_ty2 constr:(SEC_T_rmrep_group_hdr_zero) 3%nat 0%nat).
Variable bs : ltac:(sec_ty2 constr:(SEC_T_rmrep_group_hdr_zero) 4%nat 0%nat).
Lemma rmrep_group_hdr_zero : ltac:(sec_stmt2 constr:(SEC_T_rmrep_group_hdr_zero) 5%nat 0%nat).
Proof.
intros MR Hp UNK L8.
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (rgroup_conc st p gh WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
pose proof (round_up_pg_ge (r_len r)) as RU. pose_ceil.
eapply rmrep_transport_unowned.
- apply rmrep_del_group. exact MR.
- apply (munch_write [(conc st p, conc st p + 8)] m m (conc st p) bs (munch_refl _ m)); [lia| rewrite L8; cbn; lia| rewrite L8; cbn [inside]; lia].
- apply wmono_write. apply wmono_refl.
- intros lo hi a [E|[]] Ha. inversion E; subst lo hi. clear E.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ unfold RCTX in C. lia.
+ unfold RMLOCK in C. lia.
+ unfold RNEED_LOCKS in C. lia.
+ unfold RPAGE_SIZE in C. lia.
+ destruct C as (ak & ar & Hak & Hin). cbn in Hak.
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
assert (NE : fst ak <> fst p) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
change (conc (del_group p st) ak) with (conc st ak) in Hin.
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Kr).
destruct (DJ (fst ak) ra (fst p) r Hra Hr NE); lia.
+ destruct C as (b & gh' & Hb & Hin). cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [NEb Hb].
change (conc (del_group p st) b) with (conc st b) in Hin.
destruct (rgroup_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & _).
destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
assert (snd b <> snd p) by (intros E2; apply NEb; destruct b, p; cbn in *; congruence).
Z.div_mod_to_equations. lia.
* pose proof (lr_lo_group rb Krb). pose proof (lr_lo_group r Kr). destruct (DJ (fst b) rb (fst p) r Hrb Hr NE); lia.
+ destruct C as (rid & r' & v & Hr' & Hk' & Hin & HC). cbn in Hr'. change (get_shadow (del_group p st) rid) with (get_shadow st rid) in HC.
destruct (N.eq_dec rid (fst p)) as [E|NE].
* subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
destruct (UNK (a - r_base r - snd p) ltac:(lia)) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in HC. discriminate.
* pose proof (lr_lo_group r' Hk'). pose proof (lr_lo_group r Kr). destruct (DJ rid r' (fst p) r Hr' Hr NE); lia.
+ unfold RGOT_SSP in C. lia.
+ unfold RSSP_GUARD in C. lia.
Qed.
End SE.
Lemma rmrep_grp_del_eq : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B3 "L'Q0'QIyR0%211'7y8%511%311p051&G&Q7v@&Lr1r4%3221r3%73621&Ar5r2%33251%<3;18p061pS:?1pRN@1pS6B1pS>K1").
Proof. intros. unfold grp_del. apply rmrep_del_slots. exact H. Qed.
End CEIL_WRAP_1.
