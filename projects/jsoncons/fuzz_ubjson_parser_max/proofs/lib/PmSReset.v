(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmSResetP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSReset () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "0B1"; "0B2"; "1app"; "1bool"; "1fst"; "1length"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["2not"; "2or"; "3le"; "4map"; "5Z"; "0HI"; "0KS"; "0L"; "0LB"; "0LB1"; "0LB2"; "0LBX"; "6Segment"; "7VmMaps"; "0M"; "0M1"]; ["0P"; "8client_addr"; "8credit"; "8hi_heap"; "8in_block"; "9u32_at"; "9u64_at"; "9u8_at"; ":pm_addrs"; ";CHUNK"; ";VLong"; ";p_b"; ";p_src"; ";p_stk"; ";p_tb"; ";parser_at"]; [";parser_own"; ";pst"; ";pstate"; ";sr_qc"; ";vstr"; ";vstr_at"; "<T3"; "<T4"; "<pst_reset"; "=reset_spec"; ">mem_grows"; "0SCFG_P"; "?eqb"; "@In"; "@existsb"; "@forallb"]; ["Aadd"; "Ale"; "Alt"; "Apow"; "0VM"; "0a"; "0c"; "0cr"; "0i"; "0k"; "0l"; "0l1"; "0l2"; "0m"; "0m1"; "0m2"]; ["0n"; "0ois"; "0op"; "0p"; "0s"; "0scr"; "0segs"; "0sp"; "BNoDup"; "Belem_of"; "Blist_elem_of"; "CZ_to_bv"; "Cbv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSRS.
Import PMS.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Lemma elem_of_In : ltac2:(TCodec.tc2 tcn__PmSReset "?'D'8%112&QMr2r1%33621&RI'RJ%119r3%45;9217p061pTF;1pUL>1").
Proof. intros x l. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_app : ltac2:(TCodec.tc2 tcn__PmSReset "Q5'8'<'D%2211%411'RH&C&6%1266&4r6r5%33921%74:;51%92<1&QM(;r4%24@@71r7%53A21r3%64DD51%83D14&@'?%13H7?%311p051p091p0@1pU0M1p8N1pTNO1p6Q01pTJO1pTHQ01").
Proof. intros l1 l2 B1 m1 B2 m2.
induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
destruct H1 as [->|H1].
- cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_In. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
- apply IH; assumption.
Qed.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmSReset "J'8'9%211'?'5&QO&QN&QLr1%211r3%53:21qTD;1%83<15(=%<3;21&QM%13@97r2r5%43C21p041pTDE1p081pTFF1pQ>G1").
Proof. intros KS l.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma own_nodup : ltac2:(TCodec.tc2 tcn__PmSReset "QF'QA'8'<'D%2211%411'RH&C&6%1266&4&Q@r2%211r1%53;21%94<=71%;2>1'>&@'?&QC&Q<r3%211%411&Q;%114%83I31%:11'QD&Q>r6%211(Q:%13<GE%@3631r7%@11%B11%D3Q51L%F11%@15%G3Q81O%I11%K241p0:1pU8Q<1pU2Q=1pT>Q>1%Q02E1p0Q21pQHQ?1pU:QE1").
Proof. intros s LBX.
intros ND. unfold PM.parser_own, PM.src_own, PM.vec_own in ND. cbn [app map fst] in ND.
inversion ND as [|x l NI ND1]. subst x l. inversion ND1 as [|x l NI1 ND2]. subst x l.
split.
- intros E. apply NI. rewrite E. apply elem_of_In. left. reflexivity.
- intros c n p TB. rewrite TB in NI, NI1. cbn [PM.vs_own app map fst] in NI, NI1. split.
+ intros E. apply NI. rewrite E. apply elem_of_In. right. left. reflexivity.
+ intros E. apply NI1. rewrite E. apply elem_of_In. left. reflexivity.
Qed.
Lemma reset_post : ltac2:(TCodec.tc2 tcn__PmSReset "V5'8'L%211'Q8'RLyR0%211':y8%511%311p051pUL62'D'QA!p031&Q?r8r7&QF&QGr6r4r3r2%9887654321'Bu1&7'QB&Q=%118%4231%7261&R1z%221?&R0+\0%22E1&R3+2+R0%3221%:251&QC&Q<%11J%311%?2>1%41Q0%611&Q9%@221%D21;'>r1%G2F1&R2%123@%5231&@r9%11Q7%311'?r>&RK%12R0Q=%311r?%113%73QO31p091p0>1pTBQO1&QJr=r<%3221'A%Q?24I+8%Q>261%J2L1%N241+@%QB2:1%QF21Q0+Z@%QE2=1%Q12Q31%Q5241+[8%QI2A1%QM21Q7+[@%QL2D1%Q82Q:1%Q<241+[H%R02H1%R421Q>%R22JR1%Q>2Q@1%QB231r;%QM11%QO11%R;21QE%R922QJ%QE2QG1%QI231%Q1281%Q22?1%Q32G1%Q42O1%;1RM%QI11p031pTBS<1&Q7rA+1%342QJQ91rB%RI2QLQ<%RJ214%743QJ1RM&Q5rCr@+<%S02QO1%54431S3&Q6rD%S426Q9&Q;%11R9+Q0%S8221%746D51rE%61R:%@42D1S>rF%91@%S?21R2%>43C1SBrG%=1M%SC21R2%Q043A1SFrH%A1N+H%SH221%G44?1SK&QErI%SL2BR8&Q>&QH%11Q2%311%756TCD51rJ%51Q0%TI829TFTECGJ1p041p0=1p0C1p0H1p0M1p0Q11p0Q:1p0QA1p0QF1p0QK1p0S51p0S:1p0T01p0T61p0T<1p0TE1p0TI1p0U21pR2U=1pU:U@1pU4UB1pU6UC1pR0UE1pQNUG1p2V01pU>V21").
Proof. intros segs A M M1 op ois s P.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) LEN Ho Ho' Hq Hq' FRZ MG AV
C8 C9 C12 C368 E0 E8 E16 E24 TB1.
assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
{ intros a n Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
assert (DG : forall a n, L5.defined M a n -> L5.defined M1 a n) by (intros a n Dn i Hi; apply MG; apply Dn; exact Hi).
unfold PM.parser_at. cbn [PMSP.pst_reset PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H0]|].
split; [apply DG; exact D|]. split; [exact I|]. split; [exact C8|]. split; [replace (op + 9) with (op + 8 + 1) by lia; exact C9|].
split; [exact C12|].
split; [apply (L5C.u8_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H20]|].
split; [apply (PMF.nullis_at_agree segs A M M1); [lia|lia| apply AG; [lia|lia| intros i Hi; apply AV; lia]| exact NI]|].
split; [apply (PMF.src_fields_at_agree segs M M1 (op + 24) ois (ois + 16) (PM.p_src s)); [lia|lia|exact Hq|exact Hq'| apply AG; [lia|lia| intros i Hi; apply AV; lia]
| apply AG; [lia|lia| intros i Hi; apply AV; lia]| exact SRC]|].
split; [apply (PMF.u32_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H328]|].
split; [exact I|]. split; [exact TB1|].
split; [| split; [right; reflexivity|]; split; [left; reflexivity|]; unfold PM.MAX_DEPTH; lia].
destruct VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
pose proof (PM.pow2_pos (PM.p_k s) ltac:(lia)) as P2k.
split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact V0]|].
split; [cbn [length]; replace (PM.p_b s + 32 * Z.of_nat 1) with (PM.p_b s + 32) by lia; replace (op + 360 + 8) with (op + 368) by lia; exact C368|].
split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact V16]|].
split; [exact Hk|]. split; [cbn [length]; lia|]. split; [exact Hal|].
split; [apply DG; exact DB|]. split; [exact I|]. split; [exact I|].
intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth Z.of_nat].
unfold PM.pstate_at, PM.ps_root. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. rewrite Z.add_0_r.
split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24].
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Lemma blocks_apart_heap : ltac2:(TCodec.tc2 tcn__PmSReset "QH'8'<'D%2211%411&Q2'RLyR0%211':y8%511%311p051'M&Q3vEr8r7r6r5%6554321&QM(;r4%24GG51r9%53H21r3%64KK51r:%93L21&@'?%13Q0@>%311'A&R1&R0%12FE%321E%32FE%521I%7231p091p0>1p0C1p0J1pU0Q>1p8Q?1pTNQ@1p6QA1pT:Q61pQNQ81pT@QA1pQBQC1").
Proof. intros LB cr M VM B1 m1 B2 m2.
intros HH H1 H2 NE. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B1, m1) H1) as (_ & _ & AP). cbn [fst snd] in AP.
apply (L5C.blocks_apart_in B1 m1 (lb_remove B1 LB) B2 m2 AP). apply L5C.in_lb_remove_neq; [exact H2| intros E; apply NE; symmetry; exact E].
Qed.
Lemma heap_nodup : ltac2:(TCodec.tc2 tcn__PmSReset "Q2'8'<'D%2211%411&Q2'RLyR0%211':y8%511%311p051'M&Q3vEr4r3r2r1%6554321'RH&C&6%12GGr5%44HI21%62J1p081pT:@1pQNB1pT@K1pQBM1").
Proof. intros LB cr M VM. intros HH. exact (proj1 (proj2 (hio_wf L SCFG HI HIok LB cr M VM HH))). Qed.
Lemma own_not_in : ltac2:(TCodec.tc2 tcn__PmSReset "QG'8'<'D%2211%411&Q2'RLyR0%211':y8%511%311p051'M&Q3vE&4r8r7%33A21r6r5r4%9584321&QM(;r3%24JJ51r9%53K21'>&R1%12;6&R2&R0%12>=%32:1%7251&@&Q4r:%221C%411p061p0?1p0F1pT<Q=1pTLQ>1p4Q?1pT:Q41pQNQ61pT@Q?1pQFQA1pQDQB1").
Proof. intros LB1 LB2 cr M VM B m a.
intros HH Hin Ha ((B2 & m2) & HX & Hr). cbn [fst snd] in Hr.
assert (NE : B <> B2) by (apply (fst_neq_app LB1 LB2 B m B2 m2 (heap_nodup _ _ _ _ HH) Hin HX)).
destruct (blocks_apart_heap _ _ _ _ B m B2 m2 HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror HX)) NE); lia.
Qed.
Lemma own_not_client : ltac2:(TCodec.tc2 tcn__PmSReset "QK'8'<'D%2211%411&Q2'RLyR0%211':y8%511%311p051'M&Q3vE&4r:r9%33A21r8r7r6%9584321&QM(;r5%24JJ51r;%53K21'>&R1%12;6&R2&R0%12>=%32:1%7251&@&Q1vGr<r4%4532A1E%611p081p0A1p0H1pU<Q?1pU@Q@1pT<QA1pTLQB1p4QC1pT:Q81pQNQ:1pT@QC1pQFQE1pQDQF1").
Proof. intros LB1 LB2 cr M VM B m a sp scr.
intros HH Hin Ha [IB|[[S1 _]|[IM _]]].
- exact (own_not_in LB1 LB2 cr M VM B m a HH Hin Ha IB).
- destruct (PMFR.brange_of_heap L HI HIok _ LB1 cr M VM HH (fun x H => in_or_app _ _ _ (or_introl H)) B m Hin) as (_ & _ & Q4). lia.
- destruct (PMFR.brange_of_heap L HI HIok _ LB1 cr M VM HH (fun x H => in_or_app _ _ _ (or_introl H)) B m Hin) as (_ & Q1 & _). lia.
Qed.
Theorem reset_ok : ltac2:(TCodec.tc2 tcn__PmSReset "5&QIvQKvGvE%43321").
Proof.
unfold PMS.reset_spec, PMSP.reset_spec.
intros fx R M model K LBX cr sp r fb s HH MOK K0 ENT FR A10 PA LEN KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
change (PMSP.pm_scr 1) with 14336 in *.
destruct FR as (Fsp & Ftop & Fal). change (pa_frame AD) with 752 in Ftop.
set (op := PMSP.o_p AD fb) in *. assert (Eop : op = fb + 40) by reflexivity.
set (ois := PMSP.o_is AD fb) in *.
assert (HO : bv_unsigned (getr R (reg 10)) = op) by (rewrite A10; apply L5.unsigned_lit; lia).
set (src := PM.p_src s) in *. set (b := PM.p_b s) in *. set (k := PM.p_k s) in *.
assert (INO : incl (PM.parser_own s) (PM.parser_own s ++ LBX)) by (intros x Hx; apply in_or_app; left; exact Hx).
pose proof (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH INO) as BR.
assert (Iq : In (PM.sr_qc src, PM.CHUNK) (PM.parser_own s)) by (unfold PM.parser_own; left; reflexivity).
assert (Ib : In (b, 32 * 2 ^ k) (PM.parser_own s)) by (unfold PM.parser_own; right; left; reflexivity).
destruct (BR _ _ Iq) as (Q0 & Q1 & Q4). destruct (BR _ _ Ib) as (Pb0 & Pb1 & Pb4).
pose proof (heap_nodup _ _ _ _ HH) as ND.
destruct (own_nodup s LBX ND) as (Nqb & Ntb).
pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ib) Nqb) as Aqb.
pose proof PA as (P0 & PD & _ & P8 & P9 & P12 & P16 & P20 & PNI & PSRC & P320 & P328 & _ & PTB & PVEC & PB1 & PB2 & PB3).
pose proof PVEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
assert (P2kh : 2 ^ k <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in P2kh.
assert (Cb : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (b <= i < b + 32)) by (intros i Hi X; destruct Aqb; lia).
pose proof (L5C.stk_writable RSEGS _ M sp 14336 STK) as WR.
assert (WRop : L5.writable RSEGS M op 384) by (apply (L5C.writable_of_defined RSEGS M op 384 PD); lia).
assert (WRb : L5.writable RSEGS M b 32) by (apply (L5C.writable_of_defined RSEGS M b 32); [apply (L5.defined_sub M b (32 * 2 ^ k) b 32 DB); lia|lia|lia]).
assert (BRX : PMFR.brange L LBX) by (apply (PMFR.brange_of_heap L HI HIok _ LBX cr M _ HH); intros x Hx; apply in_or_app; right; exact Hx).
pose proof (ly_img_hi L LY) as Himg.
assert (HSP : 0x7fff80000000 <= hl_sptop L) by (destruct STOP as [STOP1 _]; exact STOP1).
destruct (PM.p_tb s) as [n|c n p] eqn:TB.
-
destruct PTB as (TD & _ & Hn & T0).
pose proof (PMF.even_byte n) as EVB.
pose proof (PMSRSP.rsS_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => 2 * n | 34%nat => b | 35%nat => 32 * 2 ^ k | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG & _ & FRZ0 & MS & KS & _ & _ & C12 & C368 & E24 & E16 & E8 & E0 & (C336 & _) & (C8 & C9) & _)); PMK.pvz_clrT.
set (P := fun a => (sp - 40 <= a < sp - 40 + 40) \/ (op + 8 <= a < op + 8 + 8) \/ (op + 336 <= a < op + 336 + 2) \/ (op + 368 <= a < op + 368 + 8)
\/ (b <= a < b + 32)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia
|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia]. }
unfold PMSP.cfg. cbn [pa_reset AD].
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x35984 R1 0x35aa8 M1 P K HH Mh Ml HSP MS MG FRZ).
{ intros a Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|X]]]];
[apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M sp 14336 a STK); lia ..
|apply (PMK.cwr_block L (PM.parser_own s ++ LBX) b (32 * 2 ^ k) a (INO _ Ib)); lia]. }
{ intros a. unfold P. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS 1%nat) by PMK.inl; exact Rra).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x35aa8 (ltac:(oW' 0x35aa8%Z)) r (ltac:(oF' 0x35aa8%Z)) ltac:(reflexivity) (ltac:(oD' 0x35aa8%Z)) RA1 Hr1 Hr2)|].
apply (KONT fx1 R1 M1); [| | |exact HH1].
+ apply PMK.preserved_by_index. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply (reset_post RSEGS AD M M1 op ois s P PA LEN).
all: try change (PM.p_src s) with src; try change (PM.p_b s) with b.
1-4: lia. 1: exact FRZ. 1: exact MG. 2-9: assumption.
* intros i Hi X. unfold P in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]]; [destruct X as [X|[X|[X|[X|X]]]]; cdisj; lia ..|].
destruct X as [X|[X|[X|[X|X]]]]; [cdisj; lia|cdisj; lia|cdisj; lia|cdisj; lia| exact (Cb i Hi X)].
* unfold PMSP.pst_reset. cbn [PM.p_tb]. rewrite TB. split; [intros i Hi; apply MG; apply TD; exact Hi|]. split; [exact I|].
split; [lia| exact C336].
+ change (PMSP.o_tb AD fb) with (op + 336). change (PMSP.o_vec AD fb) with (op + 360).
apply (PMK.hpres_of L LBX sp 14336 _ M M1).
* apply (PMK.ek_piece L LBX sp 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|X]]]].
-- destruct CA as [((bb & mm) & Hbb & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bb mm Hbb) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
-- apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- apply (OW (op + 336, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- apply (OW (op + 360, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- exact (own_not_client (PM.parser_own s) LBX cr M _ b (32 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
* destruct (PMK.stk_grows L M M1 sp 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
* apply PMK.dk_grows. exact MG.
-
destruct PTB as (TD & _ & T0 & T8 & T16 & Hnc & Hc & Hce & TDp & _).
assert (Ip : In (p, c) (PM.parser_own s)) by (unfold PM.parser_own; rewrite TB; right; right; left; reflexivity).
destruct (BR _ _ Ip) as (Pp0 & Pp1 & Pp4). destruct (Ntb c n p eq_refl) as (Nqp & Nbp).
pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ip) Nqp) as Aqp.
assert (Cp : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (p <= i < p + 1)) by (intros i Hi X; destruct Aqp; lia).
pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Ib) (INO _ Ip) Nbp) as Abp.
pose proof (PMF.u8_of_u64 RSEGS M (op + 336) (c + 1) ltac:(lia) T0) as T0b.
pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
assert (Dpb : p + 1 <= b \/ b + 32 <= p) by (destruct Abp as [X|X]; [right|left]; lia).
assert (Dpf : (sp - 80) + 80 <= p \/ p + 1 <= sp - 80) by (right; lia).
assert (Dpo : p + 1 <= op \/ op + 384 <= p) by (left; lia).
assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
assert (WRp : L5.writable RSEGS M p 1) by (apply (L5C.writable_of_defined RSEGS M p 1); [apply (L5.defined_sub M p c p 1 TDp); lia|lia|lia]).
pose proof (PMSRSP.rsL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => (c + 1) mod 256 | 34%nat => b | 35%nat => 32 * 2 ^ k
| 37%nat => p | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG & _ & FRZ0 & MS & KS & _ & _ & C12 & C368 & E24 & E16 & E8 & E0 & C344 & Cp0 & (C8 & C9) & _)); PMK.pvz_clrT.
set (P := fun a => (sp - 40 <= a < sp - 40 + 40) \/ (op + 8 <= a < op + 8 + 8) \/ (op + 344 <= a < op + 344 + 8) \/ (op + 368 <= a < op + 368 + 8)
\/ (b <= a < b + 32) \/ (p <= a < p + 1)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia
|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia]. }
unfold PMSP.cfg. cbn [pa_reset AD].
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x35984 R1 0x35aa8 M1 P K HH Mh Ml HSP MS MG FRZ).
{ intros a Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|X]]]]];
[apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M sp 14336 a STK); lia ..
|apply (PMK.cwr_block L (PM.parser_own s ++ LBX) b (32 * 2 ^ k) a (INO _ Ib)); lia
|apply (PMK.cwr_block L (PM.parser_own s ++ LBX) p c a (INO _ Ip)); lia]. }
{ intros a. unfold P. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS 1%nat) by PMK.inl; exact Rra).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x35aa8 (ltac:(oW' 0x35aa8%Z)) r (ltac:(oF' 0x35aa8%Z)) ltac:(reflexivity) (ltac:(oD' 0x35aa8%Z)) RA1 Hr1 Hr2)|].
apply (KONT fx1 R1 M1); [| | |exact HH1].
+ apply PMK.preserved_by_index. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply (reset_post RSEGS AD M M1 op ois s P PA LEN).
all: try change (PM.p_src s) with src; try change (PM.p_b s) with b.
1-4: lia. 1: exact FRZ. 1: exact MG. 2-9: assumption.
* intros i Hi X. unfold P in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]]; [destruct X as [X|[X|[X|[X|[X|X]]]]]; cdisj; lia ..|].
destruct X as [X|[X|[X|[X|[X|X]]]]]; [cdisj; lia|cdisj; lia|cdisj; lia|cdisj; lia| exact (Cb i Hi X)| exact (Cp i Hi X)].
* unfold PMSP.pst_reset. cbn [PM.p_tb]. rewrite TB. split; [intros i Hi; apply MG; apply TD; exact Hi|]. split; [exact I|].
assert (AGL : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
{ intros a0 n0 Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|X]]]]]; cdisj; lia]|lia|lia|exact T0]|].
split; [replace (op + 336 + 8) with (op + 344) by lia; exact C344|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|X]]]]]; cdisj; lia]|lia|lia|exact T16]|].
split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MG; apply TDp; exact Hi| exact I].
+ change (PMSP.o_tb AD fb) with (op + 336). change (PMSP.o_vec AD fb) with (op + 360).
apply (PMK.hpres_of L LBX sp 14336 _ M M1).
* apply (PMK.ek_piece L LBX sp 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|X]]]]].
-- destruct CA as [((bb & mm) & Hbb & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bb mm Hbb) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
-- apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- apply (OW (op + 336, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- apply (OW (op + 360, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- exact (own_not_client (PM.parser_own s) LBX cr M _ b (32 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
-- exact (own_not_client (PM.parser_own s) LBX cr M _ p c a sp 14336 HH Ip ltac:(lia) CA).
* destruct (PMK.stk_grows L M M1 sp 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
* apply PMK.dk_grows. exact MG.
Qed.
End WithHeap.
End PMSRS.
