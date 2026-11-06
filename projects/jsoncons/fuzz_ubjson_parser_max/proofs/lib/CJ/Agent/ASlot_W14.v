(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W14 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W14.CEIL_WRAP_1.TAIL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0AV"; "1Some"; "1app"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "3add"; "4firstn"; "4skipn"]; ["5N"; "5Z"; "0FR"; "0L"; "6Z_to_le_bytes"; "7stFin"; "7st_model"; "8sxv"; "9wz"; ":le2"; ":le8"; ";Unknown"; ";aptr"; ";cell_read"; ";cellval"; ";get_meta_rec"]; [";get_shadow"; ";hdr_havoc"; ";mask_upto"; ";meta"; ";mstate"; ";optr"; ";put_group"; ";r_cells"; ";s_tick"; ";set_slots"; "<lt"; "=add"; "=land"; "=le"; "=lor"; "=lt"]; ["=modulo"; "=mul"; "=of_nat"; "=pow"; "=shiftl"; "=shiftr"; "=sub"; "0W"; "0W'"; "0a"; "0ai"; "0b"; "0c"; "0cnt"; "0g"; "0h"]; ["0i"; "0k"; "0n"; "0o"; "0q"; "0s0r"; "0sc"; "0st"; ">lookup"; "?Z_to_bv"; "?bv"; "?bv_swrap"; "?bv_unsigned"; "@N_countable"; "@Z_countable"; "@prod_countable"]; ["Aprod_eq_dec"; "Bgmap"; "Bgmap_lookup"; "Ceq_dec"; "Deq_dec"; "0t"; "0v"; "0x"; "0y"; "0z"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma land_high_low : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "L'A&Q=zr3%3221':&Q?&QC+2r4%3221%5281%7281';&Q<&QAr6r5%;2:1%4231%621;%83E1Cp0:1p0C1p0D1pUBI1pT4J1pU@K1").
Proof. intros x k y.
intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n k) as [LT|GE].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_shl_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "N'A&Q=zr3%3221':&Q?&QC+2r4%3221%5281%7281';&Q>&QAr6r5%;2:1%4231%621;&Q;%123=%:3G31p0<1p0E1p0F1pUBK1pT4L1pU@M1").
Proof. intros x k y. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.
Lemma lor_small_shl : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "N'A&Q=zr3%3221':&Q?&QC+2r4%3221%5281%7281';&Q>&QAr6r5%;2:1%4231%62;1&Q;%123=%:3G31p0<1p0E1p0F1pUBK1pT4L1pU@M1").
Proof. intros x k y. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.
Lemma lor_32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "C'A':&Q=zr1%3221&Q?+Q0%2241%8241';&Q>r2%2216&Q;%1238%63@31p081pSJB1").
Proof. intros c. intros. change 32 with (1 * 2^5) at 1. rewrite lor_small_shl by lia. lia. Qed.
Lemma land_pg_mask : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "H'A':&Q=zr1%3221&Q?&QC+2+QD%3221%5271%;271';&Q<&QA+TP0r2%3221+_ooooooooolP0%6221%83E13p0:1pT:G1").
Proof. intros q.
intros Hq. replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma hdr_byte_facts : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "Q0'A':&Q=zr2%3221&Q?+X0%2241%8241+Q0%5271%;271&Q>&Q<r4+_ooooooooooo0%3221r3%6221%B2A1%?22>%E221';+O%;261%33J18%J251p0@1p0D1pSFN1pU@O1").
Proof. intros x ai.
intros Hx Hai.
assert (E : Z.land x 18446744073709551584 = Z.land x 224).
{ replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite <- !Z.land_assoc. reflexivity. }
rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
split.
- change 256 with (2^8). apply lor_lt_pow2; lia.
- rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.
Lemma tail_low16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "QH'A':&Q=zr3%3221&Q?+Q@%2241%8241+1%9217+Q0%;291%=231+@%:2<1%@2<1';&Q>&QA&Q<r6+QO%3221&QC+2+6%3221%9251&QFr5%221F+O%=221%@21G%A271+TP0r4%C221+_ooooooooolP0%D221%G261&Q;%12<Q0+R0%J21H%4231%5219%O3QA71p0Q11p0Q51p0Q;1pT:QE1pSLQF1pT>QG1").
Proof. intros sc cnt q.
intros Hsc Hc Hq.
replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite land_pg_mask by lia.
replace 32 with (1 * 2^5) at 1 by reflexivity. rewrite (lor_small_shl 1 5 (cnt - 1)) by lia.
rewrite (lor_shl_small sc 6) by (cbn; lia).
replace (4096 * q) with (q * 2^12) by (cbn; lia). rewrite (lor_small_shl q 12) by (cbn; lia). cbn. lia.
Qed.
Lemma firstn_le_bytes : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "F'5'A';'4'R:y8%211%411&>r3&D&=r2%2241r1%5221%83:71%7283%@3;21pUDB1pT4D1pT6E1").
Proof. intros n k z. revert z. induction n as [|n IH]; intros z; [reflexivity|]. cbn [Z_to_le_bytes Nat.add firstn]. f_equal. apply IH. Qed.
Lemma skipn_le_bytes : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "M'5'A';'4'R:y8%211%411&?r3&D&=r2%2241r1%5221%83:71&QE&QA+8&QB%11<%4231%6291%>2<1%G3B91pUDI1pT4K1pT6L1").
Proof. intros n k z.
revert z. induction n as [|n IH]; intros z.
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [Z_to_le_bytes Nat.add skipn]. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma tail_word_bytes : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "R2'R:yR0%211'A':&Q=zr2%3221&Q?&QC+2+R0%3221%5271%;271r5%<2;1+RPP0%:231%@231';&Q@&R<r7%22H1%4218r6%73I21%72=;%93K16&QE+@%2261%32:2%>3Q021'4y8%Q611%311&2&Ir:%211&?u2&J&Hr8%211%411%73=61%<3>91%61M%811%Q23@31p0E1p0K1p0N1p0Q71p0Q=1p0Q>1pSBQK1pS@QL1pQ8QM1pT<QO1").
Proof. intros s0r L W W'.
intros HW HW' HL HS HM HH.
unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by lia.
change 8%nat with (2 + 6)%nat. rewrite skipn_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
rewrite <- (firstn_skipn 2 (Z_to_le_bytes (2 + 6) W')). rewrite firstn_le_bytes, skipn_le_bytes.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. rewrite HH. f_equal.
rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned s0r) 16) by (cbn; lia).
rewrite <- (Z_to_le_bytes_mod 2 W' 16) by (cbn; lia).
change (2^16) with 65536. rewrite HS, HM. reflexivity.
Qed.
Lemma word_low16_bytes : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "Q4'A':&Q=zr1%3221&Q?&QC+2+R0%3221%5271%;271';'4'R:y8%211%411&>u2&J&Hr2%211%411%73961&I&Q@+RPP0%2271%911%511%D3?71p0F1pS@Q31").
Proof. intros W.
intros HW. unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by (try lia; Z.div_mod_to_equations; lia).
change 8%nat with (2 + 6)%nat. rewrite firstn_le_bytes.
change 65536 with (2^16). rewrite Z_to_le_bytes_mod by (cbn; lia). reflexivity.
Qed.
Lemma sllw2_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "Q5'A':&Q=zr1%3221&Q?+Q0%2241%8241';'R:yR0%211&R9&R;yQ0&QD+2&Q@r2%221>%5241%8271%:2<1&H&G&QC&Q;+1%22:1%42=1%611%811%H3E:1p0J1pT2Q41").
Proof. intros i.
intros Hi. rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_subw_sxv_word := (ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "M'A';'R:yR0%211&R9&R;yQ0&QF&R<&H&Gr2%211%411%62<1r1%611%811%:2@1%<251%?2>1%A2C1%?2;7%=11%?11%I3F41pSHK1pSDL1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_subw_sxv_word) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_subw_sxv_word) 1%nat 0%nat).
Lemma subw_sxv_word : ltac:(sec_stmt2 constr:(SEC_T_subw_sxv_word) 2%nat 0%nat).
Proof.
rewrite !wz_unsigned by (apply sxv_range). unfold wz, sxv.
rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 a mod 2 ^ 64 - bv_swrap 32 b mod 2 ^ 64))). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_cell_read_hdr_havoc_old := (ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "R<'Q4'8'@'A%3221';&Q@&9r2%23761+@%5221z%83:21':&Q=%1248&Q?+<%22;1%6241'6%E2CD%211&R8'RA&RD&R>%34I216&RB%14K438&Q;r6%J3ON1r5%4221&Q7&Q0r7&3%13Q6Q58%4231%611%C6Q8E?=81(1(7r1%24Q<Q=Q71%42J1%Q<3J61&Q:&Q8r8%211%42Q>1p061pU<QF1pU>QF1'<'N&M&Q1%12NH%J21G%421M(K%11D%QN3831qT0R11%;2R21p0=1p0QC1p0QK1pT8R61pSHR61pT@R;1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_cell_read_hdr_havoc_old) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_cell_read_hdr_havoc_old) 1%nat 0%nat).
Variable o : ltac:(sec_ty2 constr:(SEC_T_cell_read_hdr_havoc_old) 2%nat 0%nat).
Lemma cell_read_hdr_havoc_old : ltac:(sec_stmt2 constr:(SEC_T_cell_read_hdr_havoc_old) 3%nat 0%nat).
Proof.
intros B16 Ho OLD.
unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id].
unfold cell_read. cbn [r_cells r_hav r_havp].
replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
rewrite lookup_insert_eq. cbn [default from_option id].
replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
unfold hav_add. unfold stale. cbn [existsb fst snd].
replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
- specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
- cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed.
End SE.
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
(r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.
Definition stA : mstate := hdr_havoc p stT.
Definition stB : mstate := set_usage sc (usage stT sc + cnt) stA.
Definition recA : meta := mkMeta None None (Some p) AV FR 0 0 0 ml.
Definition stC : mstate := put_meta mt recA stB.
Definition stD : mstate := put_group p (Some mt) ai stC.
Definition recF : meta := mkMeta (Some mt) (Some mt) (Some p) (AV - 1) FR (cnt - 1) 1 sc ml.
Definition stE : mstate := put_meta mt recF stD.
Definition stFin : mstate := set_active sc (Some mt) stE.
Definition st_model : mstate :=
let st := hdr_havoc p stT in
let st1 := set_usage sc (usage st sc + cnt) st in
let avail := mask_upto ai in
let freed := mask_upto (cnt - 1) - avail in
let st2 := upd_meta mt (fun r =>
m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
(m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
let st3 := put_group p (Some mt) ai st2 in
let st4 := add_slots mt p (get_stride (get_meta_rec st3 mt)) cnt st3 in
let st5 := upd_meta mt (fun r => m_set_avail (m_avail r - 1) r) st4 in
let st6 := upd_meta mt (fun r => m_set_prev (Some mt) (m_set_next (Some mt) r)) st5 in
set_active sc (Some mt) st6.
Lemma mask_upto_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "J'A':&Q=zr1%3221+O%5231%7231+1&Q2r2%211%;241&Q?&QC+2+Q0%3221%5271%C271%625:%D21:%F231p0@1pT4I1").
Proof. intros k.
intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
change (2^32) with (2 * 2^31). lia.
Qed.
Lemma AV_FR_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "H':&Q=+1v0%3221&Q?&QC+2+Q0%3221%5271%;271zvB%=221%:226%@221&QF%12?@%B271%?22;%E221%F261%G2<1").
Proof.
pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
assert (mask_upto ai <= mask_upto (cnt - 1)).
{ unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
unfold AV, FR. lia.
Qed.
Lemma rec_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "N'Q4'RA&L&R@'@&RC'A&RD%544321&R?&R=&R>%36872651'8%12<8%>4=731';'Q3&O&Q9r2r3%3221r1%6221%7242%:3921pT:I1pU>=1pT@M1"). Proof. intros st v q. reflexivity. Qed.
Lemma rec_put_group : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "F'Q4&L&Q5'A';'Q3&O&Q6r4r3r2r5%544321r1%8221%9242%<3;21pT:@1pSD?1pSNA1pSHC1pT@E1"). Proof. intros st b g a q. reflexivity. Qed.
Lemma rec_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 "@'Q4&L';'Q3&O&Q1r2r3%3221r1%6221%7242%:3921pT:<1pSH=1pT@?1"). Proof. intros st b q. reflexivity. Qed.
Lemma st_model_eq_rec : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W14 ";&L';'Q3&O&Fr1%3221&E%5213%83731pT::1").
Proof. intros q.
unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
rewrite !rec_set_active.
destruct (decide (q = mt)) as [->|NE].
- rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
change (Z.land 1 1) with 1. reflexivity.
- rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed.
End TAIL.
End CEIL_WRAP_1.
