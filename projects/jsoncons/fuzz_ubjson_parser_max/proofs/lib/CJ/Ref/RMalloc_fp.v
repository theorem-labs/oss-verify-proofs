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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export Malloc_fp.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_enframe RMallocKit_A.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RMalloc_fp () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMalloc_fp.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0B"; "0C"; "1Some"; "1bool"; "1cons"; "1fst"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3N"; "3Z"; "0G"; "4write_to_mem"; "0P0"; "0RUNp"; "5rdv"; "6b8"; "6lr_lo"; "6meta_cells"; "6meta_slot"; "6ticks_ok"; "6wz"; "7mem"; "7pans_mem"]; ["8free_slot_addr"; "8grp_hdr_cov"; "8slot_ok"; "8unk_agree"; "9bytes_at"; "9le2"; "9le4"; "9wa"; "9wr_at"; ":alloc_ceiling"; ";rw_cells"; "<rsegs"; "=renframe_off_mem"; "=renframe_tail_mem"; ">ref_reserved"; ">rmrep"]; ["?rpres_except"; "@rmalloc_fp"; "ARKGroup"; "Aaptr"; "Aconc"; "Aenframe_at"; "Aget_meta_rec"; "Aget_stride"; "Aghdr"; "Am_avail"; "Am_mem"; "Am_set_avail"; "Ameta"; "Amstate"; "Aoptr"; "Ar_base"]; ["Ar_kind"; "Ar_len"; "Aranges_free"; "Aregion"; "Arkind"; "Around_up_pg"; "As_groups"; "As_regions"; "Awr16"; "Awr32"; "Awr8"; "Badd"; "Bdiv"; "Ble"; "Blt"; "Bmodulo"]; ["Bmul"; "Bpow"; "Bsub"; "0a"; "0b"; "0g"; "0idx"; "0k"; "0lo"; "0m"; "0m0"; "0m1"; "0m4"; "0mr"; "0mx"; "0n"]; ["0o"; "0off"; "0p"; "0q"; "0r"; "0r'"; "0r0"; "0res"; "0rid"; "0rid'"; "0rid0"; "0sp"; "0st"; "0st2"; "0sta"; "0stb"]; ["Clookup"; "Dbv"; "Dbv_unsigned"; "EN_countable"; "EZ_countable"; "Eprod_countable"; "Fprod_eq_dec"; "Ggmap"; "Ggmap_lookup"; "Heq_dec"; "Ieq_dec"; "0stride"; "0stx"; "0v"; "0w"; "0x"]; ["0x1"; "0x2"; "0x3"]]).
Notation RMFACTS := (@MFACTS_g ref_reserved).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma rreserved_disjoint2 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "Q2'B'='3&R2&Q>r2r1%43321(;%83721&R>z%2217'<'@&R=&R;r4r3%3221+RPP0%6221+elP0%8216%:231%:263+mTP0%<21:%>231%@251p0B1p0F1pV0Q01pU:Q11").
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.
Lemma wr8_comm : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "Q2'9'A'B%3221'QM'=&5r5%23761r4%43981%63:31&?&:r6%23>=1%33?>9%<3?21%611&R:r7r3%338=1%433@1%534A3%63;@1%E3F31p091p0A1pVJI1pWNL1pWLM1pV8M1pV6N1").
Proof. intros p q v w st.
intros Hf Hs.
assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
{ intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.
Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.
Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.
Lemma rconc_b : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "='='Bv0&R;&QOvS4%211&:'AvRD%33291%8251%<3;:1").
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.
Lemma rsk_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "7&R=z&R@vSKvRG%3221%6251").
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.
Lemma rwr8_rep : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "S<'QM'SAyR0%211'7y8%511%311p051'B&Q?vFr4r3%43321&Lr5%211'='SG'A&SI&SC'R3%544321&R7r6%211vS=%411%<3631&QC&SF&SJ%24>=I1&SE&SD%26A@?L41'QH%D48521&R6r7%211%31?%J3521'<&R=&RB&R;&:vRD%23OQ:1+@%5221&R@vSKvRG%3221%:251+4%=221%?21Q3&R>%?258%A215%32Q71%E251z%F21Q:+X0%82Q<1%J231&R:(8&5%13QGR2Ir8%44QIR421r:%732Q61&Dr9&Q7&QOvS4%211%Q621:%511(4&H%11QA(6%11RF%53RG31%>3=71%RE3RD@1%RA1A%QD221p0K1p0Q11p0QH1p0R71p0RE1p0RI1pWLRO1pV2S01pUNS21pWJS;1").
Proof.
intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr8; exact TKx].
apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.
Lemma rwr16_rep : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "S='QM'SAyR0%211'7y8%511%311p051'B&Q?vFr4r3%43321&Lr5%211'='SG'A&SI&SC'R3%544321&R7r6%211vS=%411%<3631&QC&SF&SJ%24>=I1&SE&SD%26A@?L41'QH%D48521&R6r7%211%31?%J3521&R=&RB&R;&:vRD%23NQ91+@%5221&R@vSKvRG%3221%:251+4%=221%?21Q2+2%?2E1%@269%B216%D231'<z%G21K&R>+RPP0%22N1%6241&R8(8&5%13QHR3Kr9%44QJR521r8r;%83321&Dr:&Q7&QOvS4%211%Q921;%511&Q5&M%11=%311%<3;51%RE3RD>1%RA1?%O221p0J1p0Q21p0Q81p0QI1p0R81p0RF1p0RJ1pWLS01pV2S11pUNS31pWJS<1").
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr16; exact TKx].
apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.
Lemma rwr32_rep : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "S?'QM'SAyR0%211'7y8%511%311p051'B&Q?vFr4r3%43321&Lr5%211'='SG'A&SI&SC'R3%544321&R7r6%211vS=%411%<3631&QC&SF&SJ%24>=I1&SE&SD%26A@?L41'QH%D48521&R6r7%211%31?%J3521&R=&RB&R;&:vRD%23NQ91+@%5221&R@vSKvRG%3221%:251+4%=221%?21Q2%>2D3%?258%A215%C231'<z%F21J&R>&RA+2+Q0%3221%52Q01%9271&R9(8&5%13QJR5Mr9%44QLR721r8r;%83321&Dr:&Q7&QOvS4%211%Q;21;%511&Q6&M%11=%311%<3;51%RG3RF>1%RC1?%Q2221p0J1p0Q51p0Q:1p0QK1p0R:1p0RH1p0RL1pWLS21pV2S31pUNS51pWJS>1").
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.
Lemma wr16_wr8_comm : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "Q:'9'A'B%3221'QM'=&5r5%23761r4%43981%63:31&?&:%13=<7r6%33?>1%<3?31%611&R;r7%83DC1+1%4221%C3F81%=11&R:&R8r8%231>D%43:G1%53;HF%534A1%L3M31p091p0A1p0I1pVJQ11pWNQ41pWLQ51pV8Q51pV6Q61").
Proof. intros p q v w st.
intros Hf H0 H1. unfold wr16.
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.
Lemma wr32_wr8_comm : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "Q4'9'A'B%3221'QM'=&5r5%23761r4%43981%63:31&R;&:%13=<7+1%4221r6%53A@1%>3A31&R:&R9r7r3%332A1%538@1%639A3%635D1%G3H31p0:1p0C1pVJK1pWNN1pWLO1pV8O1pV6Q01").
Proof. intros p q v w st.
intros Hf H1. unfold wr32.
rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.
Lemma renframe_mrep : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "R1'9'QM&QC%3221&QEvS=vREvRGvROvS1%6554321'<&Q?vF&5r1%23?>1&Q=&Q<vRLvE%3321<&R;&R@+@%221@%4261&RBvSK%7291+4%4221&R<v0%7281%821;%421<%D6@;6MN1%J3IF1&L%11H'='B&QD&:%13Q<Q;N%32Q91%6351E'A%Q33174vRD%Q53391%;3431%935;8%:36<4%Q121O%Q12LQA%Q3221%Q421Q1%B3A61%QA281%QB2>1%QC2F1%QD2I1tV@QMQF1").
Proof.
pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
unfold aadd. cbn [fst snd].
set (stC := if negb (off =? 0) then _ else _).
assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
/\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
/\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
/\ (forall q, conc (fst stC) q = conc st2 q)).
{ subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
- subst off. rewrite Z.mul_0_r, Z.add_0_r.
split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
-
rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
unfold UNIT in *.
replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
cbn [fst snd].
unfold renframe_tail_mem. cbv zeta.
set (po := snd b + (UNIT + stride * k) + UNIT * off).
assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
{ unfold po, P0, UNIT. f_equal; lia. }
rewrite Eq.
assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
{ unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
split; [apply Z.div_pos; lia| exact Q16]. }
rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.
unfold set_size, aadd. cbn [fst snd id].
set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
rewrite Ersv.
assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
set (stF := if negb (rsv =? 0) then _ else _).
set (mF := if rsv =? 0 then _ else _).
assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
{ subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
- split; [exact ME|]. split; [exact TE|]. split; assumption.
- destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
split; [exact MF|]. split; [exact TF|]. split; assumption. }
clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
set (stG := if 5 <=? rsv then _ else _).
set (mG := if 5 <=? rsv then _ else _).
assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
/\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
{ subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
-
rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
- split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
destruct PG as (MG & TG & -> & R2 & ERg & EGg).
assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
{ rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
split; [exact MH|]. split; [exact TH|].
split; [|split; [reflexivity| unfold po, UNIT; lia]].
rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.
Lemma rpres_enframe : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "R>'B!p021&N&Q@r9r8r7%43321&R=zr5%3221&R;&R@+@%2219r6%5221+4%7221%<21?r:%>241r;%<213&RA+2+R0%3221%E251'<&RBr=%221?r1%K221&R>r<%J261%821E%4261%;261rAr2%211p041pX0Q?1r@r?&Q=&Q<r>%231DM%Q82Q7N%Q:2F1&R<%I22QC%J21Q;%321Q<%:675DQ6QG1%QI3=<1p0?1p0Q11p0Q91p0Q<1p0QF1p0QG1p0QL1p2R51pU@R61pV0R71pV4R81pWHR91pQ<R:1pUJR81pUFR91p4R;1").
Proof.
intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
{ unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
unfold renframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : rpres_except C m0 mE).
{ subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : rpres_except C m0 mF).
{ subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
- split; [exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.
Lemma rrdv_agree : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "S0'QM&N&QC'R3'SAy8%211&Q?vFr6r5%43321&Q3r7%23145'='7%11>&S@'A'SG&SI&SC%34421D&SH%14643F&5'B%2391B&R7r8%211%>6=M9741(2r4%22Q01%E3C41'R4&R0%11M(QB%J3421'<&R=z&:%13KCQ1%4231&R>&R5&R1%11Q:%311%5271%<271&?&Q1r;%Q03Q7OL%>3Q8Q0M%43321%611&Q4&Q;&R;&QO%11Q4r9%G3QAQ91%5231(4(6%11R2%33R3QL1%<4;A51&G&Or=r:%45R>3F21&SB%12R<QC%R33QG31p091p0G1p0O1p0Q=1p0QC1p0R:1p0R>1pX0RD1pV:RH1pV8RJ1pV2RL1pUHRM1pVJRO1").
Proof.
intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read rsegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). pose_ceil.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rmeta_chunk_facts := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "SK'QM'SAyR0%211'7y8%511%311p051&QC&Q?vFr3r2%43321&Kr4%2214'B&QDr5%2219'<&Q:&Q;r1&Jr6&QF%122=%4231%847;61&R>z%2219&R=&R;+Q8%22=1&Q9%11M%6231'@+RPP0%9261+elP0%;21E%5231%=2:3+mTP0%?21I%9231'A'R3'=%QC12&S@'SG&SI&SC%348217&SH%14:439&R7r8%211%:6>=64QE1(2%12?Q;%?3>31'R4&R0%11QK(QB%D3421%Q72QGQ6&QO%11R1%Q;231&R5&R1%11R5%311%Q?261%QA21R0%Q;271p0<1p0B1pV<Q31pVDQ51'>&?%E1R3%Q73G1D%311&I%11R7%QN21RE%QN2RFQM%G1R:%D1R;%F11%R2231%R4251%RB271%RC2;1%RD2Q51qV>QF1%B2QG1qVFQI1%D2QJ1%RI2F1%RJ2QM1%RK2R21%RL2R91%RM2RA1%RN2RE1tQ8S3S01p0S51p0S91pU<S?1pUDSA1pVJSJ1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmeta_chunk_facts) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmeta_chunk_facts) 1%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rmeta_chunk_facts) 2%nat 0%nat).
Lemma rmeta_chunk_facts : ltac:(sec_stmt2 constr:(SEC_T_rmeta_chunk_facts) 3%nat 0%nat).
Proof.
intros MR MS G.
split; [apply rmrep_meta_chunk; assumption|].
pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
destruct MS as (a & ara & kk & Ha & Hkk & Eg).
destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
{ subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
- intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
- exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.
End SE.
Lemma rregion_facts : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "RA'QM'SAyR0%211'7y8%511%311p051'A'R3&Q?vFr4r3%43321'=%=17&S@'SG&SI&SC%34=21<&SH%14?43>&R7r5%211%:6CB64>1(2r2%22E1%@3?41'<&R=+TP0&QO%11G%4231'B&R?%1246z%K3421&R;&R5&R1%11Q1%311%52<1&Q9%11Q7%B231&R>%12<6'@%D1Q;%;1Q<%=11%?231+RPP0%K221+elP0%M217%9231p0;1%Q0274+mTP0%Q221<%>231p0@1%Q6261%Q72D1%Q82N1%Q92Q41p0Q;1p0QM1pV:R31pVBR51pUDR71pVJR@1").
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.
Lemma rslot_facts : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "SA'>'SAy8%211'<&Q8&Q;vRK&RBvE+4%3221vSK%847621&Q4(4&Hz%211&SBr3%22C1%611r2%52F1%911r1%82I1%<11(6%11K%@3L31%A3M71%B3N;1%C3O@1%E4MLH1'='B&G&N&OvS0vS<(8'A&5vRD%233:1&R;&:%136=4+@&R@vRF%22Q:1%7241%8261-3%:221%@4?F<1%F5EDCB1%I3H1Q8-2%?271%E4DKA1%K5JIHG1%N3M1Q:+1%D251%J4IQ0F1%Q05ONML1%Q33Q21Q<v0&QOvS4%211%L21J%Q93Q851&R=+TP0%2215%Q12R8R5&R5&R1%11:%311%Q62;1%9261&Q9vF%211%=251'@+RPP0%@281+elP0%B21E%5231%RN271%RO2<1%S02D1%S12H1%S22O1%S32Q51%S42Q;1%S52R61%S62RM1qX2S81%S<2S91qX4S:1%S>2S;1qX6S<1%S@2S=1").
Proof.
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). pose_ceil.
assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
assert (WRs : wr_at rsegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
assert (WR3 : wr_at rsegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
exists x3, x2, x1.
assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
{ intros d Hd (b' & gh & Hb' & Hf & Hc).
pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
clear - Hd Hc AL' B16 SMOD IDX S16.
destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
pose proof Ybs as (_ & _ & YB).
assert (Y3 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
{ split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
assert (Y2 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
{ split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
assert (Y1 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
{ split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
split; [exact WRs|].
split.
{ rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y3| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y2| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
- eapply bytes_at_at; [exact Y1| lia]. }
split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed.
End SLOT.
Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
\/ fresh_addr st a.
Lemma rmalloc_fp_mono : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "R2'QM'B'A'R3'='7%113&S@'SG&SI&SC%349218&SH%14;43:r2&R7r7%211%;6@?7541(2r1%22B1%B3@41'>'<r4r8%<11%E6JIA?31%I3G18'R4&R0%11<r3%311%O3531&QO%11A%215%Q33Q621&R=&R1%119%21G%4221%E261%F2;1%G2B1qV<Q=1%J2Q>1p0L1pV:Q@1pVBQB1&QAr6%25Q71NFQ9r5%45O31Q0Hp031p071pU8QK1pVHQL1pUBQM1pW0QO1pVNR01pVJR11").
Proof. intros st sta stb lo sp a.
intros HR [H|[H|H]]; [| right; left | right; right; exact H].
- destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
- destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.
Lemma rget_meta_rec_st2 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "B'='QL&QFvS=vRE%3221&QK&RB&QIvRM%211&RA+2vRG%3221%8251%:217%A3@<1").
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.
Lemma rfast_slot_ok : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMalloc_fp "R='>&QC'R3'<'Q2vS=vREr2r1vRGvRO%76654321'B&R=&RB&R;&QO%11:&:'Ar3%33291%7251+@%9221&R@&QGvRM%211%421D%?261+4%B221%D21I&R>%D257%F215%32M1%Q3251&Q0vS<%221Q2p041pU8O1+Q0%;2Q41'=&QN&QJ%11F(2%12QBQ<%63531'7%11QD&S@'SG&SI&SC%34Q821QI&SH%14Q:43QK&5%13Q<QCQH&R7%11I%;6Q?R07531%A2R1QK%F3>21%R22A1%R32I1%R42L1%R52QM1qV:R71%R:2R81qU:R:1%R<2R;1").
Proof.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
unfold UNIT, IB in *.
assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
pose proof (AVAI k K0 TBk) as KAI.
assert (K32 : k < 32) by lia.
assert (P2k : 0 < 2 ^ k <= m_avail mr).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
rewrite LBK in E'. rewrite E'. exact LE'. }
assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
exists b, r. pose proof rget_meta_rec_st2 as E2.
split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
- pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
| (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
| (intros off O0 OF;
assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
apply Z.div_lt_upper_bound; lia)
| lia ].
- intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End FASTFACTS.
End CEIL_WRAP_1.
