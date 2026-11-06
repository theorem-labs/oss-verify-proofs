(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JatLeaf JatAllocG JatPoison JatInitCache ArtRuns ArtRunsMem JatFp JatPopulate1 JatCls JatClsRep JatSecAllocPost JatFxQ
JatRecycle2C JatRecycle3L JatRecycle4P JatRecycle4S JatRecycle5A JatRecycle5B JatRecycle5I JatRecycle5G JatRecycle5T JatRecycle5C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRecycle5D () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxQ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5D.DoRecycle."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5T."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2not"; "3le"; "4Forall"; "4map"; "5Z"; "0EVOK"]; ["0G"; "0GR"; "0HI"; "6machine_state"; "7bvmap"; "0M"; "0M'"; "0Q"; "8cell"; "8wr"; "9aev"; "9aruns"; ":ret_ok"; ";art_evok_list"; "<art_qbatch"; "<art_qbytes"]; ["<art_qhead"; "<art_qlist"; "<qb_addr"; "=art_rel"; "=art_rel_steps"; "=art_rg"; ">art_dr_fcells"; ">art_rb_ok"; ">art_rb_q"; ">art_rb_work"; ">art_rbatch"; "?art_rcy_inv"; "?art_rel_mem"; "@art_rcy_trx"; "@art_rels_events"; "@art_rels_pre"]; ["@art_rels_sep"; "Agetr"; "Amkst"; "Bloaded_segments"; "CIn"; "Dadd"; "Dle"; "Dlt"; "Dof_nat"; "Dpow"; "Dsub"; "0a"; "0b"; "0bs"; "0cbs"; "0ctx"]; ["0e"; "0f"; "0fx"; "0g18"; "0g19"; "0g20"; "0g21"; "0g22"; "0g23"; "0g24"; "0g25"; "0g8"; "0g9"; "0k"; "0key"; "0l"]; ["0last"; "0log"; "0parr"; "0qs"; "0raw"; "0regs"; "0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0t"]; ["0tp"; "0tsd"; "0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section SE.
Variables (M M' : word -> option byte).
Lemma art_qlist_trf : forall bs f l, (forall b, In b bs -> forall a (k : nat) v, qb_addr b <= a -> a + Z.of_nat k <= qb_addr b + 8192 -> cellA M a k v -> cellA M' a k v) ->
art_qlist M bs f l -> art_qlist M' bs f l.
Proof.
intros bs.
induction bs as [|b r IH]; intros f l T H; cbn [art_qlist] in *; [exact H|].
destruct H as (Ef & (L & C1 & C2 & CI) & El & Cn & Hr). pose proof (T b (or_introl eq_refl)) as Tb.
split; [exact Ef|]. split.
{ split; [exact L|]. split; [apply Tb; [lia|cbn; lia|exact C1]|]. split; [apply Tb; [lia|cbn; lia|exact C2]|].
intros j it Hj. assert (Hjl : (j < length (qb_items b))%nat) by (apply nth_error_Some; congruence). apply Tb; [lia|cbn; lia|exact (CI j it Hj)]. }
split; [exact El|]. split; [apply Tb; [lia|cbn; lia|exact Cn]|]. apply IH; [|exact Hr]. intros b' Hb'. apply T. right. exact Hb'.
Qed.
End SE.
Section DoRecycle.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.
Hypothesis Htp0 : 0x65cbe8 <= tp - 88.
Hypothesis Htsd0 : 0x65cbe8 <= tsd.
#[local] Notation INV := (art_rcy_inv HI t ctx tp key tsd spb ris qs parr).
#[local] Notation TRX := (art_rcy_trx HI t spb ris parr).
Definition art_rbatch : Type := (Z * list art_rel * Z)%type.
Definition rb_wb (x : art_rbatch) : Z := fst (fst x).
Definition rb_items (x : art_rbatch) : list art_rel := snd (fst x).
Definition rb_size (x : art_rbatch) : Z := snd x.
Definition art_rb_work1 (x : art_rbatch) : list art_rel := rb_items x ++ [REB (rb_wb x)].
Definition art_rb_work (bs : list art_rbatch) : list art_rel := flat_map art_rb_work1 bs.
Definition art_rb_q (x : art_rbatch) : art_qbatch := (spb + 24 * 2 ^ 32 + 16 * rb_wb x, map (art_rel_addr spb) (rb_items x), rb_size x).
Definition art_rb_ok (x : art_rbatch) : Prop := rb_items x <> [] /\ Forall art_rel_is_item (rb_items x) /\ 0 <= rb_size x < 2 ^ 64.
#[using="Type"] Lemma art_rb_work_len : ltac2:(TCodec.tc2 tcn__JatRecycle5D "='3&Q:%211';&2r1%2251'Q3&Q9%114%6231%8251pSL:1").
Proof. induction bs as [|x r IH]; [cbn; lia|]. change (art_rb_work (x :: r)) with (art_rb_work1 x ++ art_rb_work r). unfold art_rb_work1. rewrite !length_app. cbn [length]. lia. Qed.
Definition art_dr_fcells (M : word -> option byte) (sp : Z) (raw : word) (g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 : Z) : Prop :=
cellA M (sp - 8) 8 (U raw) /\ cellA M (sp - 16) 8 g8 /\ cellA M (sp - 24) 8 g9 /\ cellA M (sp - 32) 8 g18 /\ cellA M (sp - 40) 8 g19 /\ cellA M (sp - 48) 8 g20
/\ cellA M (sp - 56) 8 g21 /\ cellA M (sp - 64) 8 g22 /\ cellA M (sp - 72) 8 g23 /\ cellA M (sp - 80) 8 g24 /\ cellA M (sp - 88) 8 g25 /\ cellA M (sp - 104) 8 (t + 208).
#[using="Type"] Lemma art_dr_fcells_tr : ltac2:(TCodec.tc2 tcn__JatRecycle5D "R6'RMyR0%211'6y8%511%311p051'>&QF+S@r<%3221&QGr=&QI+2+R0%3221%6251'8&QJr?%221=&RNr1%22I1%B241%?226%9221'9rAr2%211rB%113%63N31p081pV8Q41&Q6r>r;r:r9r8r7r6r5r4%:=BK9Q3Q687654321r@%<=D1M;Q5Q8:987654p031p0?1p0Q31p0Q;1pTFQ@1pTDQA1pTBQB1pT@QC1pT>QD1pT<QE1pT:QF1pT8QG1pTJQH1pTHQI1pU:R01pUDQK1pQ>QM1pQ<QN1").
Proof.
intros M M' sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 Hsp Hsp' F (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
assert (T : forall a v, sp - 112 <= a -> a + 8 <= sp -> cellA M a 8 v -> cellA M' a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_agree _ M M'); [intros x Hx; apply F; cbn in Hx; lia|lia|cbn; lia|exact C]. }
unfold art_dr_fcells. repeat split; apply T; first [lia|assumption].
Qed.
#[using="GEO Htp0 Htsd0"] Lemma art_dr_batches_aruns : ltac2:(TCodec.tc2 tcn__JatRecycle5D "ZL'3&Q:%211'J%411'C!p021p041&Dy5'RMyR0%211%5241'6y8%611%311p061'>'Q5'9&QArA(RK+2(7%33B21%6251&RL&QJr=+S@%3221%52G1%>3G71rB+4%>3M1<%A231vS0%<2N1%E3N31rC+8%E3Q41C%H231r?%C2Q51%L3Q531rD+9%L3Q;1J%O231+QVmdH%J2Q<1%Q33Q<31rE+:%Q33QB1Q1%Q6231&QH&2rH%22R01%411%Q52QG1%Q>3QG71rF+E%Q>3QM1Q<%QA231&QI+Q5%22QA1%Q>2R01%QG3R051&L%11L&QFvB+]@%QD2Q01%4231&QG&QE+Q0%22N1+Q?%A2R01%6231&:rM(5%11RN%R:3RN31%511'<&Q7rN%33S421&O&=&N&Q8rO%44S:321%611+R0%Q52RD1%J231&I&QCrLrI%RE21Q2+Z0%645421rJ%847K1Q1&Q6rKrGr@%4=I3;:QM2QHR3R:RARHS51&H%Q92=RBu8&Q0rQ3%L4T2KJ1%311%75DK651rQ0+H%QB2Q;1rQ4%Q34T9Q2Q11%Q511%>5K64<1&Q1rQ1rQ5%Q94T?Q8Q71%@11%54421QE&Q;vROvQOvR>vS1vRJvRGvRCvRB'Q3&Q9rQ6%211%S1241%S311rQ2%@=RB?>SJ=<;:982SG1&Q?rQ7%911%32SD1&Q@rQ8%=11%32C1&Q<r1%23F1@qT2C1rQ9%D11%R@3F31&Mv?&Q>rQ:%J11%311%635@1r2%U421TO%TN2U@N%U73U@21r3%U821TA%U22UDQA%U;3UD21r4%U<21T>%U>3UG14r5+B%U>3UM1U<%UA231%UC3UL19r6+C%UC3V21UA%UF231%UH3V11>r7+D%UH3V71UF%UK231%UM3V61Cr8%UN21T>%V03V91Fr9+F%V03V?1UN%V3231%V53V>1Kr:+G%V53VD1V3%V8231%V:3VC1Q0r;%V93VHRKV7%V<221%V>3VG1Q4r<+I%V>3VM1V<%VA231%VC3VL1Q9%VO1W0&QD(1+3%VE3W41VC+J%VG3W61VE+K%VI3W81VG%TE19%83:21%93;51%:3<V?1%;3=91%=3>R;1%W22V9QOrQG%W421R1%W63W?31p051pV8D1z&Q4rQI%S511%321S5%SA=UCS@S?VKS>S=S<S;S:S951W4&Q=rQC%W821W6%UB22UArQJ%S=11rQFr>%8;ULSISESDSB65S8321&0rQK%SC11%RL11%43X?A1&QBvR2rQE%352TJ1W6;%>251p0;1p0E1p0L1p0QB1p0QH1p0QM1p0R31p0R91p0R=1p0RC1p0RI1p0RO1p0S31p0S81pQ>XC1pU>XI1'KvArQ;+Z_aD%XC3Y01XA/01Y0%K5JSN1T5T9%77UNSK6K5SI1p091p0SH1p0T01p0T81p0T=1p0TB1p0U41p0U;1p0UC1p0UL1p0V21p0V51p0V=1p0VH1p0VM1p0W41p0W<1p0WB1p0WE1p0WO1p0X;1p0XC1p0XK1p0Y31pQ2YC1pTFYE1pTDYF1pTBYG1pT@YH1pT>YI1pT<YJ1pT:YK1pT8YL1pTJYM1pTHYN1pU2YO1pUDZ01pU:Z81pUBZ31pQ<Z41pU<Z:1pU4ZE1pQ@ZB1pSLZI1").
Proof.
induction bs as [|x bs' IH]; intros Q log regs M rom raw sp last g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 G H2 H4 H8 H9 H10 H21 Hret HHI Hsp' Hne OKS Htb W Wt FC Chd Ctb QL INV0 PRE SEP MEM EV K;
[contradiction|]. clear Hne.
destruct x as [[wb items] size]. pose proof (Forall_inv OKS) as (Hitems & ITEMS & Hsize). cbn [rb_size rb_items snd fst] in Hitems, ITEMS, Hsize. pose proof (Forall_inv_tail OKS) as OKS'.
assert (Hqb : forall l, Forall art_rb_ok l -> 0 <= art_qbytes (map art_rb_q l)).
{ induction l as [|y l IHl]; intros Hl; [cbn; lia|]. change (art_qbytes (map art_rb_q (y :: l))) with (rb_size y + art_qbytes (map art_rb_q l)).
pose proof (Forall_inv Hl) as (_ & _ & Y). pose proof (IHl (Forall_inv_tail Hl)). lia. }
change (art_qbytes (map art_rb_q ((wb, items, size) :: bs'))) with (size + art_qbytes (map art_rb_q bs')) in Htb, Ctb.
pose proof (Hqb bs' OKS') as Hqb'. set (tb := size + art_qbytes (map art_rb_q bs')) in *. assert (Etb : tb = size + art_qbytes (map art_rb_q bs')) by reflexivity. clearbody tb.
assert (Htb' : 0 <= tb < 2 ^ 64) by (clear - Etb Hqb' Hsize Htb; lia).
change (art_rb_work ((wb, items, size) :: bs')) with ((items ++ [REB wb]) ++ art_rb_work bs') in *.
pose proof (art_rels_pre_static _ _ PRE) as STall. apply Forall_app in STall. destruct STall as [_ STrest].
set (rest := art_rb_work bs') in *.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _ & _ & _ & _ & G13 & G14 & _ & _ & _ & _ & G19 & G20 & G21 & G22).
cbn [map art_qhead art_qlist] in Chd, QL. destruct QL as (_ & QR & _ & Cnx & QL').
unfold art_qrec, qb_addr, qb_items, qb_size in QR, Cnx, Chd. cbn [art_rb_q fst snd rb_wb rb_items rb_size] in QR, Cnx, Chd.
destruct QR as (Hl1021 & Cni & Csz & Citems). rewrite length_map in Hl1021, Cni.
set (b := spb + 24 * 2 ^ 32 + 16 * wb) in *. assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * wb) by reflexivity. clearbody b.
set (ni := Z.of_nat (length items)) in *. assert (Hni : 1 <= ni <= 1021) by (unfold ni; destruct items; [contradiction|cbn [length] in *; lia]).
rewrite !length_app in INV0. cbn [length] in INV0.
apply art_rels_pre_app in PRE. destruct PRE as [PRE1 PRE']. apply art_rels_pre_app in PRE1. destruct PRE1 as [PREi PREb]. destruct PREb as [PREb _].
apply art_rels_sep_app in SEP. destruct SEP as (SEP1 & SEP' & SEPx). apply art_rels_sep_app in SEP1. destruct SEP1 as (SEPi & _ & SEPib).
apply Forall_app in MEM. destruct MEM as [MEM1 MEM']. apply Forall_app in MEM1. destruct MEM1 as [MEMi _].
rewrite !art_rels_events_app in EV, K. cbn [art_rels_events flat_map art_rel_events app] in EV. rewrite app_nil_r in EV. apply art_evok_list_app in EV. destruct EV as [EV1 EV']. pose proof EV1 as EVi.
cbn [art_rels_events flat_map art_rel_events app] in K. rewrite app_nil_r in K.
pose proof PREb as PREb0. cbn [art_rel_pre] in PREb.
assert (Hwb : 0 <= wb /\ 16 * wb + 8192 <= 3758096384).
{ destruct PREb as ((Hw0 & Hwsz & _) & _). rewrite (art_rel_steps_au items G 24) in Hwsz. destruct INV0 as (ICLS & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _).
destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _). lia. }
destruct Hwb as (Hwb0 & Hwb1).
assert (Hk : Z.of_nat (length ((wb, items, size) :: bs')) < 2 ^ 32).
{ destruct INV0 as (ICLS & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _ & Rm). destruct OK as (_ & _ & _ & _ & _ & _ & _ & (_ & Hmfa1) & _).
destruct PREb as ((Hw0 & Hwsz & _) & _). rewrite (art_rel_steps_au items G 24) in Hwsz. specialize (Rm ltac:(lia)).
pose proof (art_rb_work_len bs') as Lw. fold rest in Lw. cbn [length]. clear - Rm Hmfa1 Lw. unfold art_rbatch in *. lia. }
assert (WB' : forall x', In x' bs' -> 0 <= rb_wb x' /\ 16 * rb_wb x' + 8192 <= 3758096384).
{ intros x' Hx'. assert (Hin : In (REB (rb_wb x')) rest). { unfold rest, art_rb_work. apply in_flat_map. exists x'. split; [exact Hx'|]. unfold art_rb_work1. apply in_or_app. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) STrest _ Hin) as (Hw0 & Hwsz & _). destruct INV0 as (ICLS & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _).
destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _). lia. }
assert (Hnext : 0 <= art_qhead (map art_rb_q bs') < 2 ^ 64).
{ destruct bs' as [|x' bs'']; cbn [map art_qhead]; [lia|]. destruct (WB' x' (or_introl eq_refl)) as (Y0 & Y1). unfold art_rb_q, qb_addr. cbn [fst]. clear - Y0 Y1 G1 G2 G4 G6 Eris. lia. }
destruct (art_dr_pop regs M rom sp (Z.of_nat (length ((wb, items, size) :: bs'))) b (art_qhead (map art_rb_q bs')) size tb ni H8 H10
ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:(unfold apart; (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:(clear - Hk; cbn [length] in *; lia) Hnext Hsize Htb' ltac:(clear - Hni; lia) Wt Chd Cnx Csz Ctb Cni)
as (r1 & M1 & RUN1 & A20 & A22 & A23 & A24 & A25 & AK & GW1 & AG1 & Ck1 & Cnx1 & Ctb1).
assert (AG1h : art_agree [(HI, 2 ^ 64 - HI)] M M1). { eapply art_agree_sub; [exact AG1|]. intros z Hz H. cbn [art_out fst snd] in H |- *. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb H Hz; unfold apart in *; cbn in *; lia). }
assert (AG1x : art_agree [(sp - 112, sp + 32 - (sp - 112))] M M1). { eapply art_agree_sub; [exact AG1|]. intros z Hz H. cbn [art_out fst snd] in H |- *. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb H Hz; unfold apart in *; cbn in *; lia). }
pose proof (art_rcy_trx_own HI t spb ris parr (sp - 112) (sp + 32) G M M1 ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) GW1 AG1x) as TRX0.
pose proof (art_rcy_inv_above HI t ctx tp key tsd spb ris qs parr GEO _ G M M1 GW1 AG1h INV0) as INV1.
assert (FC1 : art_dr_fcells M1 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25).
{ apply (art_dr_fcells_tr M M1 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia))); [|exact FC]. intros z Hz. apply AG1. cbn [art_out fst snd]. split; [lia|exact I]. }
assert (Citems1 : forall i e, nth_error items i = Some e -> cellA M1 (b + 24 + 8 * (0 + Z.of_nat i)) 8 (art_rel_addr spb e)).
{ intros i e Hi. assert (Hil : (i < length items)%nat) by (apply nth_error_Some; rewrite Hi; discriminate). fold ni in Hni.
apply (art_cell_tr _ M M1 _ _ _ AG1); [cbn [art_gap fst snd]; split; [unfold apart; (clear - Hil Hni Eb Hwb0 Hwb1 HHI G1 G2 G4 G6 Eris Espb; lia)|exact I]|(clear - Eb Hwb0 G4 Espb; lia)|cbn; (clear - Hil Hni Eb Hwb0 Hwb1 G1 G2 G4 G6 Eris; lia)|].
replace (b + 24 + 8 * (0 + Z.of_nat i)) with (b + 24 + 8 * Z.of_nat i) by lia. apply Citems. apply map_nth_error. exact Hi. }
assert (MEMi1 : Forall (fun e => art_rel_mem spb e M1) items).
{ apply (art_rels_mem_trx HI t ctx tp key tsd spb ris qs parr GEO _ (sp - 112) (sp + 32) G [] items M M1 INV0 (art_rels_pre_static _ _ PREi) ltac:(constructor) TRX0 MEMi). }
pose proof FC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ccb1).
eapply ar_steps; [exact RUN1|].
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st X; exact X].
apply (art_dr_items_aruns HI t ctx tp key tsd spb ris qs parr EVOK GR GEO Htp0 Htsd0 items (fun lg st => aruns ASEGS EVOK GR Q lg st) log r1 M1 rom (sp - 112) wb ni 0
(1 + Z.of_nat (length rest)) G
ltac:(rewrite AK by inl; exact H2) ltac:(rewrite AK by inl; exact H4) ltac:(rewrite <- Eb; rewrite A23; f_equal; lia) A24 ltac:(rewrite A25; f_equal; lia)
ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:(lia) ltac:(lia) Hitems ltac:(unfold ni; lia) ltac:(clear - Hni; lia) Hwb0 Hwb1
ltac:(eapply wr_grows; [exact GW1|]; replace (sp - 112 - 320) with (sp - 432) by lia; exact W)
ltac:(replace (sp - 112 + 8) with (sp - 104) by lia; exact Ccb1)
ltac:(rewrite <- Eb; exact Citems1)
ltac:(replace (1 + Z.of_nat (length rest) + Z.of_nat (length items)) with (Z.of_nat (length items + 1 + length rest)) by lia; exact INV1)
PREi SEPi MEMi1 ITEMS
ltac:(rewrite <- Eb; apply Forall_forall; intros e He; pose proof (Forall_inv (proj1 (Forall_forall _ _) SEPib e He)) as X; unfold art_zsep in X; cbn [art_rel_zone fst snd] in X; rewrite <- Eb in X; exact X)
EVi).
intros r2 M2 BK INV2 TR2.
pose proof TR2 as (F2 & W2 & _ & _).
set (G1' := art_rel_steps items G) in *.
pose proof INV2 as (_ & _ & IPC2 & _). pose proof IPC2 as (Cspb2 & _).
assert (FC2 : art_dr_fcells M2 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25).
{ apply (art_dr_fcells_tr M1 M2 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia))); [|exact FC1]. intros z Hz. apply F2. lia. }
pose proof FC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ccb2).
destruct (art_dr_bd_call r2 M2 rom (sp - 112) spb 24 (16 * wb) (t + 208)
ltac:(rewrite BK by inl; rewrite AK by inl; exact H2) ltac:(rewrite BK by inl; rewrite AK by inl; exact H9) ltac:(rewrite BK by inl; rewrite <- Eb; exact A20)
ltac:(rewrite BK by inl; rewrite AK by inl; exact H21) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G7 G8 G1 G2; lia)) Cspb2
ltac:(replace (sp - 112 + 8) with (sp - 104) by lia; exact Ccb2))
as (r3 & RUN3 & C1 & C10 & C11 & C12 & C13 & CK).
eapply ar_steps; [exact RUN3|].
replace (1 + Z.of_nat (length rest)) with (Z.of_nat (length rest) + 1) in INV2 by lia.
destruct (art_rcy_batch_step HI t ctx tp key tsd spb ris qs parr GEO r3 M2 rom (0x53eb8 : bv 64)%bv (sp - 112) (Z.of_nat (length rest)) wb G1'
C1 ltac:(unfold ret_ok; bveq) ltac:(rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H2) C10 C11 C12 C13
ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:(apply W2; [(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|left; (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|]; eapply wr_grows; [exact GW1|]; replace (sp - 112 - 320) with (sp - 432) by lia; exact W) ltac:(lia) INV2 PREb0)
as (r4 & M3 & RUN4 & D2 & DK & INV3 & GW3 & AG3).
eapply ar_steps; [exact RUN4|].
destruct (art_rel_geo_of_inv HI t ctx tp key tsd spb ris qs parr (Z.of_nat (length rest) + 1) G1' M2 (REB wb) ltac:(lia) INV2 PREb0) as (RGb & BGb).
pose proof (art_rcy_tr_one HI t ctx tp tsd spb ris qs parr GEO (sp - 112) G1' (REB wb) M2 M3 RGb BGb ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) AG3
ltac:(intros a n _ _ _ Wa; eapply wr_grows; [exact GW3|exact Wa])) as TRb.
pose proof TRb as (F3 & W3 & _ & _).
assert (TRXa : TRX (sp - 112) (sp + 32) G (items ++ [REB wb]) M M3).
{ apply (art_rcy_trx_app HI t spb ris parr (sp - 112) (sp + 32) G items [REB wb] M M2 M3); [|apply art_rcy_trx_of_tr; [(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|exact TRb]].
apply (art_rcy_trx_app HI t spb ris parr (sp - 112) (sp + 32) G [] items M M1 M2 TRX0). apply art_rcy_trx_of_tr; [(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|exact TR2]. }
assert (EG3 : art_rel_step (REB wb) G1' = art_rel_steps (items ++ [REB wb]) G) by (unfold G1'; rewrite art_rel_steps_app; reflexivity).
rewrite EG3 in INV3.
assert (FC3 : art_dr_fcells M3 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25).
{ apply (art_dr_fcells_tr M2 M3 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia))); [|exact FC2]. intros z Hz. apply F3. lia. }
assert (TT : forall a v, sp <= a -> a + 8 <= sp + 32 -> cellA M1 a 8 v -> cellA M3 a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_agree _ M2 M3); [intros z Hz; apply F3; cbn in Hz; lia|(clear - Ha HHI G1; lia)|cbn; (clear - Ha' Hsp'; lia)|].
apply (art_cell_agree _ M1 M2); [intros z Hz; apply F2; cbn in Hz; lia|(clear - Ha HHI G1; lia)|cbn; (clear - Ha' Hsp'; lia)|exact C]. }
destruct bs' as [|x' bs''].
-
cbn [length] in Ck1. replace (Z.of_nat 1 - 1) with 0 in Ck1 by lia.
pose proof FC3 as (E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & _).
destruct (art_dr_next_done r4 M3 rom raw sp sp g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 D2
ltac:(rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H8) Hret ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia))
ltac:(apply TT; [lia|lia|exact Ck1]) E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25)
as (r5 & RUN5 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & PK).
eapply ar_steps; [exact RUN5|]. apply ar_done.
unfold rest in *. cbn [art_rb_work flat_map art_rels_events length] in *. rewrite ?app_nil_r in *.
apply (K r5 M3 P2 P8 P9 P18 P19 P20 P21 P22 P23 P24 P25); [|exact INV3|exact TRXa].
intros z Hz. rewrite (PK z Hz). cbn [In] in Hz.
repeat (destruct Hz as [<-|Hz]; [rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; apply AK; inl|]). destruct Hz.
-
destruct (art_dr_next_more r4 M3 rom sp (Z.of_nat (length (x' :: bs'')))
ltac:(rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H8) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)) ltac:(clear - Hk; unfold art_rbatch in *; cbn [length] in *; lia)
ltac:(apply TT; [lia|lia|]; replace (Z.of_nat (length (x' :: bs''))) with (Z.of_nat (length ((wb, items, size) :: x' :: bs'')) - 1) by (unfold art_rbatch; cbn [length]; lia); exact Ck1))
as (r5 & RUN5 & P10 & PK).
eapply ar_steps; [exact RUN5|].
pose proof INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG0 & IBK0 & IPK0).
destruct TRXa as (Fa & Wa & Pa & Aa).
assert (QL3 : art_qlist M3 (map art_rb_q (x' :: bs'')) (art_qhead (map art_rb_q (x' :: bs''))) last).
{ apply (art_qlist_trf M M3 _ _ _); [|exact QL']. intros bq Hbq a k v Ha Hkk C. apply in_map_iff in Hbq. destruct Hbq as (xq & <- & Hxq).
destruct (WB' xq Hxq) as (Y0 & Y1). unfold art_rb_q, qb_addr in Ha, Hkk. cbn [fst] in Ha, Hkk.
assert (Hinq : In (REB (rb_wb xq)) rest). { unfold rest, art_rb_work. apply in_flat_map. exists xq. split; [exact Hxq|]. unfold art_rb_work1. apply in_or_app. right. left. reflexivity. }
destruct (Pa (spb + 24 * 2 ^ 32 + 16 * rb_wb xq) 8192 ltac:(lia) ltac:(clear - Y0 Y1 G1 G2 G4 G6 Eris; lia) ltac:(left; exists 24; split; [lia|clear - Y0 Y1; lia])
ltac:(apply Forall_forall; intros e He; exact (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) SEPx e He) _ Hinq))) as (_ & Tq).
apply Tq; [exact Ha|exact Hkk|clear - Ha Y0 G4 Espb; lia|clear - Hkk Y1 G1 G2 G4 G6 Eris; lia|exact C]. }
assert (MEM3 : Forall (fun e => art_rel_mem spb e M3) rest).
{ apply (art_rels_mem_trx HI t ctx tp key tsd spb ris qs parr GEO _ (sp - 112) (sp + 32) G (items ++ [REB wb]) rest M M3 INV0 STrest SEPx (conj Fa (conj Wa (conj Pa Aa))) MEM'). }
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st X; exact X].
apply (IH (fun lg st => aruns ASEGS EVOK GR Q lg st) (log ++ art_rels_events items) r5 M3 rom raw sp last g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 (art_rel_steps (items ++ [REB wb]) G)
ltac:(rewrite PK by inl; exact D2) ltac:(rewrite PK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H4)
ltac:(rewrite PK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H8)
ltac:(rewrite PK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H9) P10
ltac:(rewrite PK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H21)
Hret HHI Hsp' ltac:(discriminate) OKS').
+ clear - Etb Htb Hsize Hqb'. lia.
+ apply Wa; [(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|left; (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|exact W].
+ apply Wa; [(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|(clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|left; (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' Hwb0 Hwb1 Eb; lia)|exact Wt].
+ exact FC3.
+ apply TT; [lia|lia|exact Cnx1].
+ apply TT; [lia|lia|]. replace (art_qbytes (map art_rb_q (x' :: bs''))) with (tb - size) by (clear - Etb; lia). exact Ctb1.
+ exact QL3.
+ exact INV3.
+ exact PRE'.
+ exact SEP'.
+ exact MEM3.
+ exact EV'.
+ intros r6 M6 U2 U8 U9 U18 U19 U20 U21 U22 U23 U24 U25 UK INV6 TRX6. apply ar_done.
rewrite app_assoc in K.
apply (K r6 M6 U2 U8 U9 U18 U19 U20 U21 U22 U23 U24 U25); [|rewrite art_rel_steps_app; exact INV6|].
* intros z Hz. rewrite (UK z Hz). cbn [In] in Hz.
repeat (destruct Hz as [<-|Hz]; [rewrite PK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; apply AK; inl|]). destruct Hz.
* apply (art_rcy_trx_app HI t spb ris parr (sp - 112) (sp + 32) G (items ++ [REB wb]) rest M M3 M6 (conj Fa (conj Wa (conj Pa Aa))) TRX6).
Qed.
#[using="GEO Htp0 Htsd0"] Theorem art_dorecycle_aruns : ltac2:(TCodec.tc2 tcn__JatRecycle5D "YG'3&Q:%211'J%411'C!p021p041&Dy5'RMyR0%211%5241'6y8%611%311p061'>'Q5'9&QAr8(RK+1(7%33B21%6251r5%93B21&Lr6%211r:+2%<3K1:%?231&RL%12L7%C3L31r;+4%C3Q21A%F231vS0%82Q31%J3Q331r<+;%J3Q91H%M231%>2Q9M%Q03Q921r=+<%Q03Q?1N%Q3231&QEvRO+V@%3221%H2QC1%Q:3QC61r>+=%Q:3QI1Q8%Q=231r9%O2QJ1%QA3QJ31&QFvB&QJ+]@%22Q21%5241&QG+Q0%E2O1&QI+Q?%22Q?1%6241'8z%?21Q6+R0%82QE1%<2Q91%6241&:rE(5%11RN%R:3RN31%511'<&Q7rF%33S421&O&=&N&Q8rG%44S:321%611%O21D&I&QCrDrA%Q821Q7%54431Q8rB%746H1Q6&HrCu8&QH&2rJ%22SK1%411%85?J761+8%R52@1&Q0rK%L4T2KJ1%311%?5FK5=1rH+H%R=2Q;1rL%Q34T9Q2Q11%Q511%F5M64D1&Q1rIrM%Q94T?Q8Q71%@11%54421Q2&Q;vQOvR>vS1vRJvRGvRCvRB'Q3&Q9rN%211%Q5241%Q711%>=RHS5=SC<;:9871QAQ6&Q?rO%811%32R81&Q@rQ0%<11%32B1&Q<r1%23E1?qT2B1rQ1%C11%R>3E31&Mv?&Q>rQ2%I11%311%635@1r2%U221TD%TC2U>M%U53U>21%UA1UB&QD(1+3%U73UF1U5%U83UGR2U6+9%U:3UI1U8+B%U<3UK1U:+C%U>3UM1U<+D%U@3UO1U>+E%UB3V11U@+F%UD3V31UB+G%UF3V51UD%UG3V6R9UE+I%UI3V81UG+J%UK3V:1UI+K%UM3V<1UK%SI1K%J3L21%K3M51%L3N81%M3O;1%N3Q0=1%O3Q1@1%Q03Q2C1%Q13Q3F1%Q23Q4I1%Q33Q5L1%Q43Q6O1%Q53Q7Q21%Q63Q8UH1%Q73Q9Q51%Q93Q:QK1%V@2V9Q?rQ5%VB21QA%VD3VM31p051pV8Q@1&Q4rQ7%RC11%321S1r3%RO=U9UFRNV4RMRLRKRJRIRHTL21&Q=+S@%U;2R71%UK2R8U7rQ8%RL11rQ4r4%8;UBUOS4S3S165RN321&0rQ9%S211%R<11%43WMB1&QBvR2rQ3%352W31W6;%>251p0;1p0E1p0L1p0R>1pQ>WG1pU>WM1'KvA+Z_]L%WF3X31WD/01X3%@5?S31S:S>%67U3S05@?RN1p081p0RM1p0S51p0S=1p0SB1p0SG1p0T71p0T>1p0TF1p0TN1p0U81p0U;1p0UB1p0UK1p0V01p0V71p0V?1p0VG1p0VN1p0W61p0WA1p0WH1p0X01p0X81p0X<1pQ2XG1pU2XI1pSNXJ1pUDXK1pU:Y31pUBXN1pQ<XO1pU<Y51pU4Y@1pQ@Y=1pSLYD1").
Proof.
intros bs Q log regs M rom raw sp cbs last G H1 Hret H2 H4 H11 H12 H13 HHI Hsp' Hcbs Hne OKS Hqb W Wt Ck Chd Ctb QL INV0 PRE SEP MEM EV K.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _).
pose proof (art_rels_pre_static _ _ PRE) as STall.
assert (WB : forall x, In x bs -> 0 <= rb_wb x /\ 16 * rb_wb x + 8192 <= 3758096384).
{ intros x Hx. assert (Hin : In (REB (rb_wb x)) (art_rb_work bs)). { unfold art_rb_work. apply in_flat_map. exists x. split; [exact Hx|]. unfold art_rb_work1. apply in_or_app. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) STall _ Hin) as (Hw0 & Hwsz & _). destruct INV0 as (ICLS & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _).
destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _). lia. }
assert (Hk : 1 <= Z.of_nat (length bs) < 2 ^ 32).
{ destruct bs as [|x bs']; [contradiction|]. assert (Hin : In (REB (rb_wb x)) (art_rb_work (x :: bs'))). { unfold art_rb_work. apply in_flat_map. exists x. split; [left; reflexivity|]. unfold art_rb_work1. apply in_or_app. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) STall _ Hin) as (Hw0 & Hwsz & _). destruct INV0 as (ICLS & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _ & Rm).
destruct OK as (_ & _ & _ & _ & _ & _ & _ & (_ & Hmfa1) & _). specialize (Rm ltac:(lia)). pose proof (art_rb_work_len (x :: bs')) as Lw. clear - Rm Hmfa1 Lw. unfold art_rbatch in *. cbn [length] in *. lia. }
destruct (art_dr_pro regs M rom raw sp sp (t + 208) cbs (Z.of_nat (length bs)) H1 H2 H11 H12 H13 ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)) ltac:(eapply wr_sub; [exact W|(clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)|(clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)]) ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia))
ltac:((clear - G7 G8 G1 G2; lia)) Hcbs ltac:(clear - Hk; lia) Ck)
as (r1 & RUN1 & A2 & A8 & A9 & A18 & A19 & A21 & A10 & AK).
set (M1 := art_f112 M sp raw regs (t + 208) cbs) in *.
assert (F1 : mem_grows M M1 /\ art_agree [(sp - 112, 112)] M M1 /\ art_dr_fcells M1 sp raw (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
(U (getr regs 21)) (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) (U (getr regs 25))).
{ unfold M1, art_f112, art_dr_fcells. assert (X0 : 0x691000 + 112 <= sp) by (clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia). assert (X1 : sp < 2 ^ 64) by (clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia). clear - X0 X1.
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. repeat split; zcell. }
destruct F1 as (GW1 & AG1 & FC1). clearbody M1.
assert (AG1h : art_agree [(HI, 2 ^ 64 - HI)] M M1). { eapply art_agree_sub; [exact AG1|]. intros z Hz H. cbn [art_out fst snd] in H |- *. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' H Hz; unfold apart in *; cbn in *; lia). }
assert (AG1x : art_agree [(sp - 112, sp + 32 - (sp - 112))] M M1). { eapply art_agree_sub; [exact AG1|]. intros z Hz H. cbn [art_out fst snd] in H |- *. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 HHI Hsp' H Hz; unfold apart in *; cbn in *; lia). }
pose proof (art_rcy_trx_own HI t spb ris parr (sp - 112) (sp + 32) G M M1 ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)) GW1 AG1x) as TRX0.
pose proof (art_rcy_inv_above HI t ctx tp key tsd spb ris qs parr GEO _ G M M1 GW1 AG1h INV0) as INV1.
assert (TT : forall a v, sp <= a -> a + 8 <= sp + 32 -> cellA M a 8 v -> cellA M1 a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_tr _ M M1 _ _ _ AG1); [cbn [art_gap fst snd]; split; [unfold apart; cbn; (clear - Ha; lia)|exact I]|(clear - Ha HHI G1; lia)|cbn; (clear - Ha' Hsp'; lia)|exact C]. }
eapply ar_steps; [exact RUN1|].
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st X; exact X].
apply (art_dr_batches_aruns bs (fun lg st => aruns ASEGS EVOK GR Q lg st) log r1 M1 rom raw sp last (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
(U (getr regs 21)) (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) (U (getr regs 25)) G
A2 ltac:(rewrite AK by inl; exact H4) A8 A9 A10 A21 Hret HHI Hsp' Hne OKS Hqb
ltac:(eapply wr_grows; [exact GW1|]; eapply wr_sub; [exact W|(clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)|(clear - G1 G2 Espb G4 Eris G6 HHI Hsp'; lia)]) ltac:(eapply wr_grows; [exact GW1|exact Wt]) FC1
ltac:(apply TT; [lia|lia|exact Chd]) ltac:(apply TT; [lia|lia|exact Ctb])).
- apply (art_qlist_trf M M1 _ _ _); [|exact QL]. intros bq Hbq a k v Ha Hkk C. apply in_map_iff in Hbq. destruct Hbq as (xq & <- & Hxq).
destruct (WB xq Hxq) as (Y0 & Y1). unfold art_rb_q, qb_addr in Ha, Hkk. cbn [fst] in Ha, Hkk.
apply (art_cell_tr _ M M1 _ _ _ AG1); [cbn [art_gap fst snd]; split; [unfold apart; (clear - Ha Hkk Y0 Y1 HHI G1 G2 G4 G6 Eris; lia)|exact I]|(clear - Ha Y0 G4 Espb; lia)|(clear - Hkk Y1 G1 G2 G4 G6 Eris; lia)|exact C].
- exact INV1.
- exact PRE.
- exact SEP.
- apply (art_rels_mem_trx HI t ctx tp key tsd spb ris qs parr GEO _ (sp - 112) (sp + 32) G [] (art_rb_work bs) M M1 INV0 STall ltac:(constructor) TRX0 MEM).
- exact EV.
- intros r2 M2 U2 U8 U9 U18 U19 U20 U21 U22 U23 U24 U25 UK INV2 TRX2. apply ar_done.
apply (K r2 M2 U2); [|exact INV2|exact (art_rcy_trx_app HI t spb ris parr (sp - 112) (sp + 32) G [] (art_rb_work bs) M M1 M2 TRX0 TRX2)].
intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|Hx]; [rewrite UK by inl; apply AK; inl|]. destruct Hx as [<-|Hx]; [rewrite UK by inl; apply AK; inl|].
destruct Hx as [<-|Hx]; [rewrite U8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite U9; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite U18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite U19; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite U20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite U21; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite U22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite U23; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite U24; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite U25; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite UK by inl; apply AK; inl|]. destruct Hx as [<-|Hx]; [rewrite UK by inl; apply AK; inl|]. destruct Hx.
Qed.
End DoRecycle.
