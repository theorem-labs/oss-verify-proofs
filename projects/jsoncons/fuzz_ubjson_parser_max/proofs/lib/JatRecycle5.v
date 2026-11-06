(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JatLeaf JatAllocG JatPoison JatInitCache ArtRuns ArtRunsMem JatFp JatPopulate1 JatCls JatClsRep JatCARSpec JatSecAllocPost JatFxQ JatImgCell JatAllocate3
JatFree1 JatFxDrain
JatRecycle2C JatRecycle3L JatRecycle4P JatRecycle4S JatRecycle5A JatRecycle5B JatRecycle5R JatRecycle5I JatRecycle5G JatRecycle5T JatRecycle5C JatRecycle5D JatRecycle5E JatRecycle5F.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRecycle5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxDrain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxQ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5D."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5E."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5F."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5T."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3Forall"; "3map"; "4Z"]; ["0EVOK"; "0F"; "0G"; "0GB"; "0GL"; "0GR"; "0HI"; "0L"; "5machine_state"; "6bvmap"; "0M"; "0M'"; "0M1"; "0Q"; "7Wn"; "7apart"]; ["7cell"; "7wr"; "8aev"; "8aruns"; "9ret_ok"; ":art_evok_list"; ";art_agree"; "<art_drain_mem"; "=art_qbatch"; "=art_qbytes"; "=art_qhead"; "=art_qlist"; "=art_qsep"; "=qb_addr"; ">art_drain_W5"; "?art_rel"]; ["?art_rel_steps"; "?art_rg"; "@art_rel_is_item"; "Aart_rb_ok"; "Aart_rb_q"; "Aart_rb_work"; "Aart_rbatch"; "Bart_qin"; "Bart_rcy_npop"; "Cart_qin24"; "Cart_rcy_trq"; "Dart_rcy_inv"; "Dart_rel_mem"; "Eart_rels_events"; "Eart_rels_pre"; "Eart_rels_sep"]; ["Eart_zapart"; "Fgetr"; "Fmkst"; "Gmem_grows"; "Hloaded_segments"; "IIn"; "Jadd"; "Jle"; "Jlt"; "Jmul"; "Jof_nat"; "Jpow"; "Jsub"; "0b"; "0bytes"; "0c"]; ["0cbs"; "0ctx"; "0e"; "0fx"; "0gbytes"; "0gq"; "0key"; "0log"; "0mn"; "0msz"; "0parr"; "0pre"; "0qs"; "0raw"; "0regs"; "0regs'"]; ["0rest"; "0ris"; "0rom"; "0sp"; "0spb"; "KBV"; "KZ_to_bv"; "Kbv"; "Kbv_unsigned"; "0t"; "0tp"; "0tsd"; "0work"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_drain_W5 (sp c GL GB : Z) : list (Z * Z) :=
[(sp - 48, 48); (0x137970 + 152, 16); (0x137970 + 176, 16); (c, 32); ((if GL =? 0 then 0x137970 + 168 else GB), 8)].
Section SE.
Variables (M : word -> option byte).
Variables (raw : word).
Variables (regs : bvmap 5 word).
Variables (sp c L F B bytes GL GB gbytes : Z).
Lemma art_drain_mem_facts : 0x691000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x691000 <= c) -> apart (sp - 48) 48 c 32 ->
(GL <> 0 -> 0x691000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart c 32 GB 8 /\ wrA M GB 8) ->
wrA M (sp - 48) 48 -> wrA M c 32 -> wrA M (0x137970 + 152) 40 ->
let M1 := art_drain_mem M sp raw regs c L F B bytes GL GB gbytes in
mem_grows M M1 /\ art_agree (art_drain_W5 sp c GL GB) M M1
/\ cellA M1 c 8 0 /\ cellA M1 (c + 8) 8 0 /\ cellA M1 (c + 16) 8 0 /\ cellA M1 (c + 24) 8 0
/\ cellA M1 (0x137970 + 160) 8 (GL + L) /\ cellA M1 (0x137970 + 176) 8 B /\ cellA M1 (0x137970 + 184) 8 (gbytes + bytes)
/\ (GL = 0 -> cellA M1 (0x137970 + 168) 8 F) /\ (GL <> 0 -> cellA M1 GB 8 F)
/\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
/\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (0x137970 + 152) 4 0.
Proof.
intros IMG Hsp' Hc Hc' Hci Ac HGB W Wc Wq M1.
pose proof Ac as Xc. unfold apart in Xc.
assert (FACTS : mem_grows M M1 /\ art_agree (art_drain_W5 sp c GL GB) M M1
/\ cellA M1 c 8 0 /\ cellA M1 (c + 8) 8 0 /\ cellA M1 (c + 16) 8 0 /\ cellA M1 (c + 24) 8 0
/\ cellA M1 (0x137970 + 160) 8 (GL + L) /\ cellA M1 (0x137970 + 176) 8 B /\ cellA M1 (0x137970 + 184) 8 (gbytes + bytes)
/\ (GL = 0 -> cellA M1 (0x137970 + 168) 8 F) /\ (GL <> 0 -> cellA M1 GB 8 F)
/\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
/\ cellA M1 (sp - 40) 8 (U (getr regs 19))).
{ unfold art_drain_W5, M1, art_drain_mem, art_drain_frame. destruct (Z.eqb_spec GL 0) as [EG|NG].
- split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
repeat split; try (intros E; try contradiction); try zcell. rewrite EG. zcell.
- destruct (HGB NG) as (GB0 & GB1 & AGs & AGc & WGB). unfold apart in AGs, AGc.
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
repeat split; try (intros E; try contradiction); try zcell. }
destruct FACTS as (G1 & A1 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & F1 & F8 & F9 & F18 & F19).
repeat (split; [assumption|]).
unfold M1. apply art_drain_mem_lock; try assumption. intros NG. destruct (HGB NG) as (GB0 & GB1 & _). split; assumption.
Qed.
End SE.
Section DrainRcy.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.
Hypothesis Htp0 : 0x65cbe8 <= tp - 88.
Hypothesis Htsd0 : 0x65cbe8 <= tsd.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
#[local] Abbreviation INV := (art_rcy_inv HI t ctx tp key tsd spb ris qs parr).
#[local] Abbreviation rbq := (art_rb_q spb).
#[local] Abbreviation TRQ := (art_rcy_trq HI t spb ris parr).
#[using="GEO Htp0 Htsd0"] Lemma art_recycle_locked_aruns : ltac2:(TCodec.tc2 tcn__JatRecycle5 "]>'4&QF%211'Q2%411'H!p021p041&Iy5'S7yR0%211%5241'7y8%611%311p061'?'QA&Q8%G11&>&QDvS4%211&1r=r<%33N21%84O:51'Q?%Q211&QEr>%211':&R1r;(S5+1(8%33Q221%6251r8%93Q221&Q4r9%211+2%;3Q:19%>2H1&S6%12Q;6%B3Q;31+4%A3Q@1?%D2G1vS:%72QA1%H3QA31r?+:%H3QG1F%K231+QVn[@%>2QH1%O3QH31r@+;%O3QN1M%Q2231%D2QNQ2%Q53QN21rA+<%Q53R41Q3%Q8231&R6vS9+V@%3221%N2R81%Q?3R861rB+=%Q?3R>1Q=%QB231%Q42R>QL%QE3R>21&R7vF&R<+`0%22Q11%5241&R8&R;+Q?%22QB1%42Q01'9z%=21Q:+R0%82QH1%:2Q=1%6241'5&QH%12Q4RC&3rJ%22SB1%R>3641'=&QCrK%33SG21&R9+`P0&R:%;2S6QM%211%5241&Q9%11R1%Q5231%31QL+QF%Q12RA1%Q3231rE%Q;2O1%91QL%Q7231%Q3231&Q<%11QF&QG%11QArC%K3SJ21&QI%11SHrD%O3SN21&R0r1&Q=r2%211+XP0%64T1521qU6SK1%Q83SL1GqTLT81rQ1%T84TOT:T51%Q<3T;31&QB%11=r3%>1?+8%B4T=321qTLTB1rH%QE3TD21p081qU6T;1%QH3T<1Q7&Q1&R4rOrL%RD21RC%54431RD%645E?>qTLTO1%R13U01=&Q0+TH%S92SF1u4%45<L21RCrQ2+UH%S>2SK1u8%R11R>%:5B5321rQ3+U0%SD2T11%RD2U?R>%R;11%@5H5381rQ4+U8%SJ2T71&Q:%11K%F5N53>1rQ5+U@%T02T=1%J5Q231BQ1&Q;rQ6rN%:11rQ0%544321&QKvRAvRFvS;vS1vRLvRJ%S>2UN;%S511rQ7%:=T5TA9U687V86542<1&QN%12R5QD&QO%12V<@&QLrQ;%23V?RC1qU6V91%SF3V:1R<&Q5v@rQ=&QM%11QD%53431%V;2RJV6rQ<%V>3W721%V>2RAV1%V02W:3%VA3W:21%W=1W>&R5(2+3%VC3WB1VA%VD3WCRGVB+9%VF3WE1VD+B%VH3WG1VF+C%VJ3WI1VH+D%VL3WK1VJ+E%VN3WM1VL+F%W03WO1VN+G%W23X11W0+H%W43X31W2+I%W63X51W4+J%W83X71W6+K%W:3X91W8(6%11M%L3N31%M3O61%N3Q091%O3Q1<1%Q03Q2?1%Q13Q3B1%Q23Q4E1%Q33Q5H1%Q43Q6K1%Q53Q7N1%Q63Q8Q11%Q73Q9Q41%Q83Q:W81%Q93Q;Q71%Q;3Q<T>1r6%WO21T>rQC%X121T@%X33XL31p061pVLQC1&Q@rQ8rQ:%3221r4%RI=VDW0RHWERGRFXGRERDRCV921&QJrQ?rQ9rQBr5%5;VJW6XMRKRI4R?3921rQG%V82YH1%UO11%T45T<FSGSL1r7rQH%Y64YMY8Y31%SD11%T95TA4SFT11rQI%Y:4Z1Y<Y71%V411%T=5TEXFT6T51rQJ%QB1Z5%Y13Z521r:%TB5TJ1SIT:W1p031&;rQK%Y73Z;17%311%TH5U0Y7SOT@Jp021%TJ5U2Y9THTGW9rQM%YK4ZBYMYH1%T911%T34YG21Q>rQN%YO4ZFZ1YL1%VI11rQF%WN221%S<1Q6%Z03ZI:1&R2vRC%251Y0NYKJ%:241p071p0=1p0B1p0D1p0K1p0Q21p0Q71p0Q=1p0QB1p0QI1p0R01p0SE1p0SI1pQHZK1pV0[11'Q3vErQ@rQ>+Z^bD%Z<3[91Z:/01[9&N+X0%24UOT;V01%M5L741T7%;7V<T>:M9R81p0=1p0T<1p0TC1p0TI1p0TL1p0TO1p0U;1p0UB1p0UG1p0UN1p0V51p0V<1p0VB1p0VF1p0VM1p0W:1p0WH1p0WM1p0X21p0X51p0X;1p0X@1p0XJ1p0XO1p0Y71p0Y?1p0YE1p0YL1p0Z31p0Z>1p0ZE1p0ZM1p0[41p0[;1p0[?1tVJ[M[J1tU<\9\01pQ6\<1pQ:\>1pU2\?1pUB\@1pV8\A1pUL\I1pV6\D1pQJ\E1pUN\K1pU@]61pQL]31pV2]:1pUH];1").
Proof.
intros pre rest Q log regs M1 rom raw sp mn cbs GL G gq work H1 Hret H2 H4 H10 H11 H12 H13 HHI HS47 Hcbs Hnp OKS Hmerge Hqb Hmn SEP QIN Q24 SEPR SEPI W WL Clk Cgb Ccnt Cgf Cgl QL INV0 PRE RSEP MEM EV K.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & _).
assert (QB : forall b, In b gq -> 0x691000 <= qb_addr b /\ qb_addr b + 8192 <= HI) by (intros b Hb; destruct (proj1 (Forall_forall _ _) QIN b Hb) as (X1 & X2 & _); split; assumption).
set (M2 := Wn 4 M1 (0x137970 + 152) 256).
assert (WK : wokA M1 (0x137970 + 152) 4) by (apply (wr_wok _ _ _ _ (art_img_wr M1 (0x137970 + 152) 4 ltac:(lia) ltac:(lia) ltac:(lia))); cbn; lia).
assert (GR12 : mem_grows M1 M2) by (unfold M2; zgrows).
assert (AG12 : art_agree [(0x137970 + 152, 4)] M1 M2) by (unfold M2; exact (art_agree_Wn 4%nat M1 (0x137970 + 152) 256 ltac:(lia) ltac:(cbn; lia))).
assert (GAPq : forall a n, (a + n <= 0x137970 + 152 \/ 0x137970 + 156 <= a) -> art_gap [(0x137970 + 152, 4)] a n).
{ intros a n Ha. cbn [art_gap fst snd]. unfold apart. clear - Ha. repeat split; try exact I; lia. }
assert (TC : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= 0x137970 + 152 \/ 0x137970 + 156 <= a) -> cellA M1 a k v -> cellA M2 a k v).
{ intros a k v Ha Hk Hq C. apply (art_cell_tr _ M1 M2 a k v AG12); [apply GAPq; exact Hq|exact Ha|exact Hk|exact C]. }
assert (AGW : art_agree (art_rcy_W HI []) M1 M2).
{ eapply art_agree_sub; [exact AG12|]. intros z Hz Ho. unfold art_rcy_W in Ho. cbn [art_out app map fst snd] in Ho |- *. clear - Ho. repeat split; try exact I; lia. }
assert (INV2 : INV (Z.of_nat (length work)) G M2) by exact (art_rcy_inv_trq HI t ctx tp key tsd spb ris qs parr GEO Htp0 Htsd0 [] _ G M1 M2 (Forall_nil _) GR12 AGW INV0).
pose proof (art_rels_pre_static _ _ PRE) as STall.
assert (MEM2 : Forall (fun e => art_rel_mem spb e M2) work).
{ apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) MEM e He) as Me. pose proof (proj1 (Forall_forall _ _) STall e He) as Se.
destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; [| |exact I].
- destruct (art_rel_static_prot HI t ctx tp key tsd spb ris qs parr _ G M1 _ INV0 Se) as (Pz & Hz & _ & Z1 & Z2).
destruct (art_rcy_prot_below HI t ctx tp tsd spb ris qs parr GEO G _ _ ltac:(destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK); exact (conj ISG (conj IBK IPK))) Pz) as (Lo & Hi).
apply (art_rel_mem_tr spb G _ M1 M2 Se); [|exact Me]. intros a kk v Ha Hkk C. apply TC; [clear - Ha Lo; lia|clear - Hkk Hi G2; lia|right; clear - Ha Lo; lia|exact C].
- destruct (art_rel_static_prot HI t ctx tp key tsd spb ris qs parr _ G M1 _ INV0 Se) as (Pz & Hz & _ & Z1 & Z2).
destruct (art_rcy_prot_below HI t ctx tp tsd spb ris qs parr GEO G _ _ ltac:(destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK); exact (conj ISG (conj IBK IPK))) Pz) as (Lo & Hi).
apply (art_rel_mem_tr spb G _ M1 M2 Se); [|exact Me]. intros a kk v Ha Hkk C. apply TC; [clear - Ha Lo; lia|clear - Hkk Hi G2; lia|right; clear - Ha Lo; lia|exact C]. }
assert (QG2 : Forall (art_qgeo [(0x137970 + 152, 4)]) gq).
{ apply Forall_forall. intros b Hb. destruct (QB b Hb) as (X1 & X2). split; [clear - X1; lia|]. split; [clear - X2 G2; lia|]. apply GAPq. right. clear - X1. lia. }
apply (art_recycle_aruns HI t ctx tp key tsd spb ris qs parr GEO Htp0 Htsd0 EVOK GR pre rest Q log regs M2 rom raw sp mn cbs GL G H1 Hret H2 H4 H10 H11 H12 H13 HHI HS47 Hcbs Hnp OKS Hmerge Hqb Hmn SEP QIN Q24 SEPR SEPI
ltac:(eapply wr_grows; [exact GR12|exact W]) ltac:(eapply Forall_impl; [|exact WL]; intros b Wb; eapply wr_grows; [exact GR12|exact Wb])
ltac:(unfold M2; apply cell_Wn_hit; [lia|cbn; lia])
ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Cgb]) ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Ccnt]) ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Cgf])
ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Cgl]) (art_qlist_tr _ M1 M2 gq _ _ AG12 QG2 QL) INV2 PRE RSEP MEM2 EV).
intros regs' M' R1' R2' K' INV' TR C160 C168 C184 C176a C176b Clk' QL' Hrest.
apply (K regs' M' R1' R2' K' INV'); try assumption.
destruct TR as (FR & WR & PT & AG). split; [|split; [|split]].
- intros x Hx. rewrite (FR x Hx). apply AG12. cbn [art_out fst snd]. clear - Hx HHI G1. repeat split; try exact I; lia.
- intros a n Ha Hn HHa Wr. apply WR; [exact Ha|exact Hn|exact HHa|]. eapply wr_grows; [exact GR12|exact Wr].
- intros zlo zlen Hz Hhi Pz FZ FLk Hq. destruct (PT zlo zlen Hz Hhi Pz FZ FLk Hq) as (P' & CT). split; [exact P'|].
intros a k v Ha Hka Ha0 Hak C. apply (CT a k v Ha Hka Ha0 Hak). apply TC; [exact Ha0|exact Hak|clear - Ha Hka Hq; lia|exact C].
- eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ AG12 AG)|]. intros z Hz Ho. apply art_out_app. split; [|exact Ho].
unfold art_rcy_W2 in Ho. cbn [art_out app fst snd] in Ho |- *. clear - Ho. repeat split; try exact I; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_drain_rcy_aruns := (ltac2:(TCodec.tc2 tcn__JatRecycle5 "`?'4&QF%211'Q2%411'H!p021p041&Iy5'S7yR0%211%5241'7y8%611%311p061'?'QA&Q7r>r;r<r?&R6vS9+R@%3221r:r9r8r7r6r5r4%@<?>=<87654321&Q8%Q811&>&QDvS4%211&1rDrC%33Q?21%84Q@:51'Q?%QC11&QErE%211':&R1rB(S5+1(8%33QC21%6251%83QB1Q5&Q4r@%211+2%:3QJ18%=2G1&S6%12QK6%A3QK31+4%@3R01>%C2F1vS:%72R11%G3R131rF+:%G3R71E%J231+QVn[@%>2R81%N3R831rG+;%N3R>1L%Q1231%D2R>QL%Q43R>21rH+<%Q43RD1Q2%Q7231+V@%R62R51%L2RF1%Q<3RF41rI+=%Q<3RL1Q:%Q?231%Q22RLR?%QB3RL21&R7vF&R<+a@%22O1%5241&R8&R;+Q?%22Q@1%42N1'9z%=21RM+R0%82QF1%:2S01%6241%B2R1Q0+QO%=2QK1%?2Q31%;241%G2;Q5%B2Q69%>221%J2>QE+L%E2R31rJ%S=2QB1%I231%Q02D3rKrO%SB221%N21@&;rL%RJ3SM1K%311+VbTP0%Q:214+8%SK261%Q=21Q<&O+Q0%24SL1:5&Q1&R4rQ5%3421>9%Q:251%Q;291%Q<2=1p0@1rQ2%QH21QG%:4981QHrQ6%<4;1T9>&Q0rQ7+TH%T@2RH1u4%55A421QGrQ8%TD2RLQGu8%95E321Q;rQ9+R8%TI2S11rN%>5J4261%R=2R1Q;%R82Q<QO%R4221rQ;%C5O1TM;BrQ<%U22TOQ8%F5Q221>ErQ=+@%U62U31%J5Q631BIrQ>+H%U:2U71%N5Q:31FMrQ?+U0%U>2SF1%Q25Q>31JQ1%TD3UGMRE%QM11rQA+U@%UD2SL1%Q85QD31Q0Q2p051+UH%UH2T01%Q<5QH71Q4Q;&Q9rQ3%211%UM2Q:N%U23V521&R:&3rQ4%22UF1%411%V42Q5H%U93V<21'5&QH%12QAR6rQI%:2W41%U?3531'=&QCrQJ%33W921&R9+`P0%B2V6R4%D11%4231%K1R7%T7221%M1R4+QF%T32UA1%T5231%Q11R4%T72QH1&Q<rQ:%211&QG%11TA%F3VF1R3&QI%11VD%I3VI1R4&R0r1&Q=r2%211+XP0%64VL521qU6VF1%Q23VG1R:qTLW31rR0%W34X;W5W01%Q63W631&QB%11=r3%>1?%A4W721SMqTLW<1rQ@%Q>3W>21p071qU6W51%QA3W61RI%SN4SMR<8T4qTLWC1%QD3WD1RD+U8%X22V:1&Q:%11;%SH5T4RC3S@1&Q;rQB%51RF%342RG1QK&QKvRAvRFvS;vS1vRLvRJ%RA2WJRO%RC11rQDrQC%;=V5XD:W498X5765321&QNrQE%221A&QO%12X:6&QLrQG%23X=QF1qU6X71%RC3X81<&Q5v@rR7&QM%11=%53431%X92QMX4rR6%X<3YF21%X<2QDX0%WO2YI3%X?3YI21%YL1YM&R5(2+3%XA3Z11X?%XB3Z2UGX@+9%XD3Z41XB+B%XF3Z61XD+C%XH3Z81XF+D%XJ3Z:1XH+E%XL3Z<1XJ+F%XN3Z>1XL+G%Y03Z@1XN%Y13ZATGXO+I%Y33ZC1Y1+J%Y53ZE1Y3+K%Y73ZG1Y5(6%11L%K3M31%L3N61%M3O91%N3Q0<1%O3Q1>1%Q03Q2A1%Q13Q3D1%Q23Q4G1%Q33Q5J1%Q43Q6M1%Q53Q7Q01%Q63Q8Q31%Q73Q9Y61%Q83Q:Q61%Q:3Q;S@1%YK2Z@S?rR=%YM21SA%YO3[931p051pVLQA1&Q@rQKrQN%3221%RH=XB[1RGYARFREZBRDRCRBX71ZH&QJrR9rQOrQLrQM%5;XH[7ZHRJRH43218ZOrRA%U:2\41%U<11%VO5W;[4UNVG1rRB%[04\8[2ZM1%S<11%W35W?[9S>VK1rRC%[44\<[6[11%UI11%W75WC[>ULVO1rRD%Q?1\@%ZK3\@21%W;5WG[DV4W3XMp021rRE%ZO3\D15%X811rR<%WA5WM\1V:W91p031%WC5WO\3W@W?Y5rRG%[D4\L[F[A1%T011%SN4\621Q;rRH%[H4]0[J[E1%V=11%YI21Q4rR5%S711%[I3]3:1&R2vRC%251\?M\BI%:241p081p0=1p0B1p0D1p0K1p0Q11p0Q61p0Q;1p0Q@1p0QG1p0QM1p0S@1p0SD1pQH]51pV0];1'Q3vErR:rR8+Z^U@%\53]C1\3/01]C%J5I41T4SO%87Y6T67J6R31p0:1p0T41p0T;1p0TA1p0TD1p0TH1p0U51p0U:1p0U@1p0UD1p0V01p0V>1p0VB1p0VF1p0VJ1p0VM1p0W21p0W:1p0W?1p0WF1p0WN1p0X41p0X81p0X@1p0XE1p0XJ1p0XO1p0Y31p0Y61p0Y:1p0Y@1p0YE1p0YL1p0YO1p0Z31p0ZH1p0ZM1p0ZO1p0[51p0[91p0[81p0[91p0[=1p0[C1p0[K1p0\11p0\81p0\?1p0\H1p0\O1p0]71p0]>1p0]E1p0]I1tVJ^6^31tU<^B^91tQJ_8^E1pQ6_71pU2_91pUD_:1pU:_;1pQ8_<1pQ:_=1pTN_>1p2_?1pQ4_@1pQ@_A1pV8_B1pUL_J1pV6_E1pQF_F1pUN_L1pU@`71pQL`41pV2`;1pUH`<1")) (only parsing).
Variable pre : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 0%nat 0%nat).
Variable rest : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 1%nat 0%nat).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 2%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 3%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 5%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 6%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 7%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 8%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 9%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 10%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 11%nat 0%nat).
Variable bytes : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 12%nat 0%nat).
Variable GL : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 13%nat 0%nat).
Variable GB : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 14%nat 0%nat).
Variable gbytes : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 15%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 16%nat 0%nat).
Variable cbs : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 17%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_aruns) 18%nat 0%nat).
Theorem art_drain_rcy_aruns : ltac:(sec_stmt2 constr:(SEC_T_art_drain_rcy_aruns) 19%nat 0%nat).
Proof using GEO Htp0 Htsd0 pre rest Q log regs M rom raw sp L F B bytes GL GB gbytes msz cbs G.
intros M1 gq work H1 Hret H2 H4 H10 H11 H12 H13 HHI HS47 Hcbs HL HF HB Hby Hgb Hbig HGL HGL' HGB0 W Wc
Clk Cmax Cmin Hmsz CL CF CB Cby CGL CGB Cgb Eqb Elen Hnp OKS Hmerge Hqb Hmn SEP QIN Q24 SEPR SEPI WL Cgf QL INV0 PRE RSEP MEM EV K.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & Gt0 & Gt1 & Gti & _).
assert (Ac : apart (sp - 48) 48 (t + 80) 32) by (unfold apart; clear - Gt1 HHI; lia).
assert (HGB : GL <> 0 -> 0x691000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart (t + 80) 32 GB 8 /\ wrA M GB 8).
{ intros NG. destruct (HGB0 NG) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [clear - X2 G2; lia|]. split; [unfold apart; clear - X2 HHI; lia|]. split; assumption. }
assert (W48 : wrA M (sp - 48) 48) by (eapply wr_sub; [exact W|clear; lia|clear; lia]).
assert (Wq : wrA M (0x137970 + 152) 40) by (apply art_img_wr; lia).
destruct (art_drain_pre regs M rom raw sp (t + 80) L F B bytes GL GB gbytes H1 H2 H10 H11 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - Gt0; lia) ltac:(clear - Gt1 G2; lia)
ltac:(clear - Gti; lia) Ac HL HF HB Hby Hgb ltac:(clear - Hqb Eqb; unfold gq in *; lia) HGL HGL' HGB W48 Wc Wq Clk CL CF CB Cby CGL CGB Cgb)
as (r1 & RUN1 & R1_2 & R1_10 & RK1).
destruct (art_drain_mem_facts M raw regs sp (t + 80) L F B bytes GL GB gbytes ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - Gt0; lia) ltac:(clear - Gt1 G2; lia)
ltac:(clear - Gti; lia) Ac HGB W48 Wc Wq)
as (GR1 & AG1 & C1 & C2 & C3 & C4 & C160 & C176 & C184 & C168a & C168b & F1 & F8 & F9 & F18 & F19 & LK1).
fold M1 in RUN1, GR1, AG1, C160, C176, C184, F1, F8, F9, F18, F19, LK1.
assert (GAPi : forall a n, (a + n <= 0x137970 + 152 \/ 0x137970 + 192 <= a) -> 0 <= n -> a + n <= 0x691000 -> apart a n (t + 80) 32 -> art_gap (art_drain_W5 sp (t + 80) GL GB) a n).
{ intros a n Hq Hn0 Han At. unfold apart in At. unfold art_drain_W5. cbn [art_gap fst snd]. unfold apart. destruct (Z.eqb_spec GL 0) as [EG|NG].
- clear - Hq Hn0 Han At HHI G1. repeat split; try exact I; lia.
- destruct (HGB0 NG) as (X1 & _). clear - Hq Hn0 Han At HHI G1 X1. repeat split; try exact I; lia. }
assert (Cmax1 : cellA M1 (0x137970 + 64) 8 (2 ^ 28)).
{ apply (art_cell_tr _ M M1 _ 8%nat _ AG1); [apply GAPi; [left; cbn; clear; lia|cbn; clear; lia|cbn; clear; lia|unfold apart; cbn; clear - Gti; lia]|lia|cbn; lia|exact Cmax]. }
assert (Cmin1 : cellA M1 (0x137970 + 72) 8 msz).
{ apply (art_cell_tr _ M M1 _ 8%nat _ AG1); [apply GAPi; [left; cbn; clear; lia|cbn; clear; lia|cbn; clear; lia|unfold apart; cbn; clear - Gti; lia]|lia|cbn; lia|exact Cmin]. }
pose proof (art_drain_rcy_fn r1 M1 rom raw sp (gbytes + bytes) msz (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) R1_2 R1_10
ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - Hbig Hqb Eqb; unfold gq in *; lia) Hmsz (u64_range _) (u64_range _) (u64_range _) (u64_range _)
ltac:(clear - HHI G1; lia) C184 Cmax1 Cmin1 LK1 (art_img_wr M1 (0x137970 + 152) 4 ltac:(lia) ltac:(lia) ltac:(lia)) F1 F8 F9 F18 F19) as RUN2.
eapply ar_steps; [exact RUN1|]. eapply ar_steps; [exact RUN2|].
match goal with |- aruns _ _ _ _ _ (mkst ?r _ _ _) => set (r2 := r) end.
assert (R2K : forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr regs x).
{ intros x Hx. unfold r2. cbn [In] in Hx.
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; first [apply Z_to_bv_bv_unsigned | apply RK1; inl]. }
apply (art_recycle_locked_aruns pre rest Q log r2 M1 rom raw sp msz cbs B G).
- unfold r2. gres. reflexivity.
- exact Hret.
- unfold r2. gres. reflexivity.
- rewrite R2K by inl. exact H4.
- unfold r2. gres. exact R1_10.
- unfold r2. gres. reflexivity.
- unfold r2. gres. rewrite RK1 by inl. exact H12.
- unfold r2. gres. rewrite RK1 by inl. exact H13.
- clear - HHI. lia.
- exact HS47.
- exact Hcbs.
- exact Hnp.
- exact OKS.
- exact Hmerge.
- exact Hqb.
- split; [clear - Hmsz; lia|exact Hmn].
- exact SEP.
- exact QIN.
- exact Q24.
- exact SEPR.
- exact SEPI.
- eapply wr_grows; [exact GR1|]. eapply wr_sub; [exact W|clear; lia|clear; lia].
- exact WL.
- exact LK1.
- fold gq. rewrite Eqb. exact C184.
- fold gq. rewrite Elen. exact C160.
- exact Cgf.
- exact C176.
- exact QL.
- exact INV0.
- exact PRE.
- exact RSEP.
- exact MEM.
- exact EV.
- intros regs' M' R1' R2' K' INV' TR D160 D168 D184 D176a D176b Dlk QL' Hrest.
apply (K regs' M'); try assumption.
intros x Hx. rewrite (K' x Hx). exact (R2K x Hx).
Qed.
End SE.
End DrainRcy.
