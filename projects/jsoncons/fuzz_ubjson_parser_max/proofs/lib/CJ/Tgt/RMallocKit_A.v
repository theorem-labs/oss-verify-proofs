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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMallocKit_A () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocTree."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0B"; "0C"; "1Some"; "1cons"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "2or"; "3N"]; ["3Z"; "4write_to_mem"; "0RUNp"; "5rdv"; "6ticks_ok"; "6wz"; "7mem"; "7pans_mem"; "8ivl"; "8munch"; "8outside"; "8wmono"; "9bytes_at"; "9le4"; "9wa"; ":RKGroup"]; [":aptr"; ":conc"; ":get_shadow"; ":ghdr"; ":mstate"; ":r_base"; ":r_kind"; ":r_len"; ":region"; ":rkind"; ":round_up_pg"; ":s_groups"; ":s_regions"; ":shadow"; ":wr32"; ";rsegs"]; ["<RAUXV_CELL"; "<rmrep"; "=rauxv_ok"; "=rpres_except"; ">add"; ">le"; ">lt"; ">of_nat"; ">pow"; "0W"; "0a"; "0b"; "0bs"; "0gh"; "0m"; "0m'"]; ["0m0"; "0p"; "0q"; "0q'"; "0r"; "0st"; "?lookup"; "@bv"; "@bv_unsigned"; "AN_countable"; "AZ_countable"; "Aprod_countable"; "Bprod_eq_dec"; "Cgmap"; "Cgmap_lookup"; "Deq_dec"]; ["Eeq_dec"; "0stx"; "0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma rmrep_wr32 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A "T;'Q4'R7yR0%211'8y8%511%311p051'9'?'@%3221'Q8&QAvBr5r4%43321&Dr6%211'<%C1:&R6'R=&R?&R9%34B21?&R>%14D43A&4%13FE@&Q<r7%211%<6JG8641(2r3%22J1%B3A41'Q9&Q6%11J(O%G3421&QEz&:%13Q7Q6?%4231&QDr8%53Q;Q:1+4%4221&Q:&Q7%11Q6%311%>251'Q3%QJ11&Q0&R<&R@%24QHQ8QG1&R;&R:%26QKQ;Q:QJ41%Q=47419%Q:4852:r2&Q;r=%211%QD6R0?6541r1%Q92A1%QI3A31%QA3R6R5Q:r<%QC3R8R71%QM3R931'>%Q53R;R:;%Q321Q0%Q73R=R<R6%Q:221+9%Q7231%Q=216%8241p0:1p0?1pSLQ21pSHRD1';r9%QE2QD1&QF&QH+2+Q0%3221%5271%9271&Q>r;r:%3321Q4&A&N&Q5%11@%R33S9S87%R1221%511&M&E%11;%311%;3Q951%S=3S<=1%S91>%L221p0D1p0O1p0R41p0R?1p0RE1p0RK1p0S?1p0SC1pT:SI1pU6SL1pT4SL1pSNT11pT<T:1").
Proof.
intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
rewrite le4_bytes by lia.
change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
(wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
(wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
rewrite !wa_succ.
unfold wr32.
assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
{ split; [|apply ticks_ok_wr8; exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S1 as [M1 T1].
assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
/\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
{ split; [|apply ticks_ok_wr8; exact T1].
replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S2 as [M2 T2].
assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
(write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
/\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
{ split; [|apply ticks_ok_wr8; exact T2].
replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S3 as [M3 T3].
split; [|apply ticks_ok_wr8; exact T3].
replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.
Lemma rrdv_mem : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A "S8'Q4'R7yR0%211'8y8%511%311p051&Q0'Q8&QAvBr6r4%43321'<'Q=&Q2&4'?'@%33218%52:1r7%7213%:3931&Q1r8r1%3221r9%5213%A3<31pT8I1%O1I&R6'R=&R?&R9%34D21N&R>%14F43Q0%H3GFN&Q<%11>%:6JQ46431(2r5%22Q71%Q23?41'Q9&Q6%11Q8(O%Q73421';&QEz&:%13Q8Q7Q0%4231&QF&Q:&Q7%11Q9%311%5271%<271&L&Q?r:&QD&Q5%11Q>%@3QGQFQ<%4221(3(7%11R9%33R:QH1%<4;:51&C&F&Gr;r<%554321@&R8%12RDQM%R:3R531p0:1p0H1p0Q61p0Q<1p0QM1p0R61p0RB1pU8RL1pT:RI1pT6RK1pSNRM1pU4S61pT<S71").
Proof.
intros st stx m q r x MR Hsh Hconc Hr Hk Ho Hb.
unfold rdv. rewrite Hsh. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read rsegs m _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite Hconc, (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *.
destruct (m (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). pose_ceil.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rauxv_ok_pres := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A "Q>'@!p021&F&QBvBr3r1%43321&QCr5r4%33216&QE%1237&=r8r2%211%411p061pSFE1';&Q@%;21A&QF&QD+8%2251%42F1%8261r9%11?%B11p041pSFQ31r6%Q13Q01Kp031p0B1p0L1p0Q11p2Q:1pT0Q81pSNQ91p4Q;1")) (only parsing).
Variable C : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres) 2%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_rauxv_ok_pres) 3%nat 0%nat).
Lemma rauxv_ok_pres : ltac:(sec_stmt2 constr:(SEC_T_rauxv_ok_pres) 4%nat 0%nat).
Proof.
intros (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
- eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
- eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
- eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.
End SE.
Lemma rpres_write : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A "QL'@!p021&F'6'R7y8%211%411&QCr5r4r3%43321&QEz%2214&QD&QG&5%12=8%311%52;1&QH+2+R0%3221%=251';r6r1%A221&QF%>2JG%@11%B261%4261%9261r:r2%211p041pU8Q:1r9r8&Ar7&N%11C%4331Q7%Q93761p091p0I1p0Q51p0Q91pSJQ?1pSFQH1pSNQF1pT2QG1p4QI1").
Proof.
intros C m0 m a bs HP Ha Hl HC x Hx HCx.
destruct (HP x Hx HCx) as [E W].
assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
{ rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
exfalso. apply HCx, HC. lia. }
split.
- rewrite NE. exact E.
- intros Hw. apply wview_write_mono. apply W, Hw.
Qed.
Lemma rpres_except_munch_frame : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_A "QM'@!p021&F'R7yR0%211'8y8%511%311p051'6&H%211&QCr5r4r3%43321&Ir2%23154&K&Q?%23198';&QEzr1%3221&QF&QH+2+R0%3221%5271%;271&=r:%11C%311&Jr7%221Jp041p091pU8Q?1r9r8r6%Q43321p051p0L1p0Q01p0Q41pSDQ:1pT0Q>1pSNQG1pT2QH1p4QJ1").
Proof.
intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.
End CEIL_WRAP_1.
