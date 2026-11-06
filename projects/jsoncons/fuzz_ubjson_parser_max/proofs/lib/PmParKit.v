(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParSpecs.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmParKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmFrame.PMFR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK.Kit.Upd."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecs.PMPS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "0B'"; "0B1"; "0B2"; "1app"; "1bool"; "1fst"; "1length"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"]; ["2eq"; "2ex"; "2not"; "2or"; "3sub"; "4le"; "4lt"; "5map"; "5nth"; "6Z"; "0HI"; "0HIok"; "0KS"; "0L"; "0LB"; "0LB2"]; ["0LBX"; "0LBc"; "7VmMaps"; "0M"; "0M'"; "0M1"; "0M2"; "0M3"; "0OWN"; "0P"; "8credit"; "8heap_iface_ok"; "8heap_layout"; "8hi_heap"; "8hl_b_overhead"; "8hl_img_hi"]; ["8hl_img_lo"; "8hl_k_per_malloc"; "8hl_sptop"; "9agree_on"; "9hpres"; "9stk"; ";defined"; ";outside"; ";range"; ";u32_at"; ";u64_at"; ";u8_at"; ":SCFG"; "<brange"; "=CHUNK"; "=PST"]; ["=SRC"; "=STRM"; "=VLong"; "=VShort"; "=iss_at"; "=p_b"; "=p_depth"; "=p_done"; "=p_k"; "=p_src"; "=p_stk"; "=p_tb"; "=p_tg"; "=parser_at"; "=pot_parser"; "=pot_text"]; ["=pst"; "=pstate"; "=sm_eg"; "=sm_g"; "=sr_qc"; "=srcst"; "=stack_shape"; "=strm"; "=vec_at"; "=vs_data"; "=vstr"; "=vstr_at"; "?set_more"; ">dkr"; "@with_src"; "AT3"]; ["AT4"; "Acredit_keep"; "Acredit_le"; "Asrc_step"; "Bcs_all"; "Bdk"; "Bek"; "BinW"; "Cmem_grows"; "0SCFG_P"; "Deqb"; "EIn"; "Eexistsb"; "Eforallb"; "Eincl"; "Eremovelast"]; ["Fadd"; "Fle"; "Flt"; "Fmodulo"; "Fmul"; "Fof_nat"; "Fpow"; "Fsub"; "0VM"; "0W"; "0W'"; "0W2"; "0a"; "0a'"; "0b"; "0c"]; ["0cr"; "0cr1"; "0cr2"; "0d"; "0de'"; "0g'"; "0i"; "0k"; "0ks"; "0l"; "0l1"; "0l2"; "0m"; "0m'"; "0m1"; "0m2"]; ["0n"; "0n'"; "0o"; "0ois"; "0op"; "0p"; "0p1"; "0rem'"; "0s"; "0s1"; "0s2"; "0scr'"; "0segs"; "0sm"; "0sm1"; "0sm2"]; ["0sm3"; "0sp'"; "0src1"; "0src2"; "0src3"; "0st'"; "GNoDup"; "Gelem_of"; "Glist_elem_of"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0stk"; "0str"; "0v"; "0w"]; ["0x"]]).
Module PMPK.
Definition dkr (M M' : word -> option byte) (a n : Z) : Prop :=
forall i, a <= i < a + n -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Lemma dkr_grows : ltac2:(TCodec.tc2 tcn__PmParKit "F'U:yR0%211';y8%511%311p051'I&S8r4r3%3221&RMr5r2%342651p051pY2:1pWJ;1pR:=1pR8>1").
Proof. intros M M' a n. intros G i _ D. apply G. exact D. Qed.
Lemma dkr_agree : ltac2:(TCodec.tc2 tcn__PmParKit "G'U:yR0%211';y8%511%311p051'I&QCr4r3r2r1%544321&RMr5%241765p041pY2;1pWJ<1pR:>1pR8?1").
Proof. intros M M' a n. intros AG i Hi D. rewrite AG by exact Hi. exact D. Qed.
Lemma dkr_sub : ltac2:(TCodec.tc2 tcn__PmParKit "Q1'U:yR0%211';y8%511%311p051'I&RMr6r5r4r3%544321&SA%1253&S@%1265%2298%5221r9r8%>421<;p041p091p0<1pY4C1pWLD1pY2E1pWJF1pR:H1pR8I1").
Proof. intros M M' a n a' n'. intros D H1 H2 i Hi. apply D. lia. Qed.
Lemma dkr_trans : ltac2:(TCodec.tc2 tcn__PmParKit "J'U:yR0%211';y8%511%311p051'I&RMr5r4r2r1%544321r3%746514r7%941873p031p061pY2=1pWJ>1pR@@1pR>A1pR<B1").
Proof. intros M1 M2 M3 a n. intros D1 D2 i Hi D. apply (D2 i Hi). apply (D1 i Hi). exact D. Qed.
Lemma defined_dkr : ltac2:(TCodec.tc2 tcn__PmParKit "I'U:yR0%211';y8%511%311p051'I&RMr4r3r2r1%544321&QFr5%23165%33287p021p061pY2=1pWJ>1pR:@1pR8A1").
Proof. intros M M' a n. intros D Df i Hi. apply D; [lia| apply Df; exact Hi]. Qed.
Lemma agree_of_frz : ltac2:(TCodec.tc2 tcn__PmParKit "R2'U:yR0%211';y8%511%311p[251'I!p021'?&SAzr1%3221&SB&SF+2+R0%3221%5271%;271&Br5r2%211%411'@r7&U9r3%22O1%411r8%113%83N31p0:1p0@1pX>O1%L2K9&S@r4%221<%Q021Hr6%Q221Q0%622G%Q02Q21%Q6231%@1I%L11p031pX>Q=1&QCr9%241F;Q0p041p0>1p0C1p0E1pY2QE1pWJQF1pRDQE1pR:QI1pR8QJ1").
Proof. intros M M' P a n. intros F H1 H2 N i Hi. apply F; [lia| apply N; exact Hi]. Qed.
Lemma cs_in : ltac2:(TCodec.tc2 tcn__PmParKit "I'9':%211'@'6&S=&S<&S:r1%211r2%53:21qX@;1&S4%93=21(>%=3<21&S;%13A:5r4%33C:1p031pX@E1p071pQJF1").
Proof. intros KS. intros H k Hk. apply L5K.In_of_mem. rewrite forallb_forall in H. apply H. exact Hk. Qed.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmParKit "J'9':%211'@'6&S=&S<&S:r1%211r3%53:21qX@;1%83<15(>%<3;21&S;%13@97r2r5%43C21p041pX@E1p081pXBF1pQJG1").
Proof. intros KS ks. intros H k Hk. apply L5K.In_of_mem. rewrite forallb_forall in H. apply H. exact Hk. Qed.
Lemma word_id : ltac2:(TCodec.tc2 tcn__PmParKit ";'U:yR0%211'@&U9&U;r1%2261%4271%63713p[081").
Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.
Lemma m16_8 : ltac2:(TCodec.tc2 tcn__PmParKit ">'I'@&SCr1+@%3221z%63721r2+8%8221%:3;15p051p[2=1").
Proof. intros x. intros H. apply Z.mod_divide in H; [|lia]. destruct H as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. Qed.
Lemma m8_add : ltac2:(TCodec.tc2 tcn__PmParKit "B'I'@&SCr2+8%3221z%63721&S@r3&SD%1278%4231%;219%=3>18p081pX@@1p[2A1").
Proof. intros x k. intros H. rewrite Z.mul_comm, Z.mod_add by lia. exact H. Qed.
Section Kit.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : PMFR.brange L LBc.
Lemma ag_hi : ltac2:(TCodec.tc2 tcn__PmParKit "Q6'I&SAvU1r2%3221&S@r3%2214&SF+2+R0%3221%;251'?r5r1%?221&SBr4%>251%3251%8251&B&S7vSJ%221F%411p061pX>L1&QCvQ3vQ4%3421B>p051p0F1p0O1pY2Q41pWJQ51").
Proof. intros a n.
intros H1 H2 N. apply (PMKP.ek_agree_stack segs L KL LBc sp' scr' W' M M' a n E STKc SCR0 H1 H2). intros i Hi.
apply PMFR.outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_sub_blk : ltac2:(TCodec.tc2 tcn__PmParKit "Q<'I&S;'=%1233(<r4r3%347721vQ1%83621&SAr5%2216&S@%1298r6%3215%7231'?r1%:251&SB%1236%5231&B&S7vSJr2%3221%511p071pX>O1&QCvQ3vQ4%3421DHp051p0D1p0J1p0N1pY2Q81pWJQ91pXJQ:1p4Q;1").
Proof. intros B m a n.
intros Hin H1 H2 N. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
pose proof STKc as (_ & SLO & SHI & STOP & _).
apply (PMKP.ek_agree L LBc sp' scr' W' M M' a n E). intros i Hi.
apply (PMKP.kept_block segs L KL LBc sp' scr' W' B m i Hin); [lia| lia| exact Q4| exact Q1| lia|].
apply PMFR.outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_blk : ltac2:(TCodec.tc2 tcn__PmParKit "Q3'I&S;'=%1233(<r2r1%347721vQ1%83621'?&SAr4%2217&SB&S@r3%2251%42<1%9261&B&S7vSJ%221B%411p061pX>J1&QCvQ3vQ4%3421B>p051p0G1pXJQ11p4Q21").
Proof. intros B m. intros Hin N. apply (ag_sub_blk B m B m Hin); [lia| lia| exact N]. Qed.
End Along.
Lemma ek_drop_own : ltac2:(TCodec.tc2 tcn__PmParKit "S2'9'='I%2211%411&QH%611'U:yR0%211';y8%511%311p051&S6vM&5r8r7%33A21r6r5r3r2r1%;7:654321&S;(<%14KK54r;%43L21'?&SA&S@%12<;&SG&QB%11F+XPPP0%4221%8261'C&Q@%11L%<2:1&Q?%11O%?21I%7241r=%H3Q@F1%B2ON%D21N%E2CQ1%=221p051pXLQG1p6QH1%K2:1%L2C1p0N1pXJQL1p4QM1&QG%12Q>Q8%22Q?Q:'Ar>%Q:3R2Q81r4%Q62Q?1&SB%Q72QAQ@%2241%Q;241%Q<271qXJR;1%;2R<1q4R=1%=2R>1%Q72?1p0A1pWJRA1r:r9%R77R621R4R3R0@p041p0I1p0QO1pR:R<1pR8R=1pWHRF1pWDRG1pYHRL1pZ4RM1pR2RL1pRBRM1").
Proof. intros OWN LBX sp' scr' W W2 M M'.
intros E HOWN HW a (Ha & Hc & He & Ho). apply E. split; [exact Ha|]. split; [|split; [exact He|]].
- destruct Hc as [(b & Hb & Hr)|Hc]; [left; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]| right; exact Hc].
- destruct (HW a Ho) as [O|(B & m & Hin & HB)]; [exact O|]. exfalso. destruct (HOWN B m Hin) as (Z1 & Z2 & Z3).
destruct Hc as [((B', m') & Hb & Hr)|[(S1 & S2)|(I1 & I2)]].
+ cbn in Hr. destruct (Z3 B' m' Hb); lia.
+ lia.
+ lia.
Qed.
Lemma dk_incl : ltac2:(TCodec.tc2 tcn__PmParKit "Q3'9'='I%2211%411'U:yR0%211';y8%511%311p051&S5vMr5r4r3r2r1%76654321&S>r7r6%33E21r8%=6<13;:9p031p081pR:A1pR8B1pYHM1pZ4N1pR0M1pQNN1").
Proof. intros LB LB2 sp' scr' M M'.
intros D I a Ha Hc He HM. apply (D a Ha); [|exact He| exact HM].
destruct Hc as [(b & Hb & Hr)|Hc]; [left; exists b; split; [apply I; exact Hb| exact Hr]| right; exact Hc].
Qed.
Lemma elem_of_In : ltac2:(TCodec.tc2 tcn__PmParKit "?'I'9%112&S;r2r1%33621&U7'U8%119r3%45;9217p061pXD;1p[2>1").
Proof. intros x l. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_app : ltac2:(TCodec.tc2 tcn__PmParKit "Q5'9'='I%2211%411'U6&G&7%1266&5r6r5%33921%74:;51%92<1&S;(<r4%24@@71r7%53A21r3%64DD51%83D14&B'@%13H7?%311p051p091p0@1pY0M1p:N1pXNO1p8Q01pXHO1pXFQ01").
Proof. intros l1 l2 B1 m1 B2 m2.
induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
destruct H1 as [->|H1].
- cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_In. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
- apply IH; assumption.
Qed.
Lemma blocks_apart_heap : ltac2:(TCodec.tc2 tcn__PmParKit "QO'Q;vM&QLvS9%211vJ%63521'9'='I%2211%411&Q:'U:yR0%211';y8%511%311p051'Q2&Q=r8r7r6r5%55F4321&S;(<r4%24FF51r9%53G21r3%64JJ51r:%93K21&B'@%13O@>%311'C&SA&S@%12FE%321E%32FE%521I%7231p091p0>1p0C1p0J1pY0Q=1p:Q>1pXNQ?1p8Q@1pWBQ51pR8Q71pX2Q@1pQNQB1pQHQH1").
Proof. intros HIok LB cr M VM B1 m1 B2 m2.
intros HH H1 H2 NE. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B1, m1) H1) as (_ & _ & AP). cbn [fst snd] in AP.
apply (L5C.blocks_apart_in B1 m1 (lb_remove B1 LB) B2 m2 AP). apply L5C.in_lb_remove_neq; [exact H2| intros E; apply NE; symmetry; exact E].
Qed.
Lemma heap_nodup : ltac2:(TCodec.tc2 tcn__PmParKit "Q9'Q;vM&QLvS9%211vJ%63521'9'='I%2211%411&Q:'U:yR0%211';y8%511%311p051'Q2&Q=r4r3r2r1%55F4321'U6&G&7%12FFr5%44GH21%62I1p081pWB?1pR8A1pX2J1pQNL1pQHQ21").
Proof. intros HIok LB cr M VM. intros HH. exact (proj1 (proj2 (hio_wf L SCFG HI HIok LB cr M VM HH))). Qed.
Lemma heap_block_defined : ltac2:(TCodec.tc2 tcn__PmParKit "Q='Q;vM&QLvS9%211vJ%63521'9'='I%2211%411&Q:'U:yR0%211';y8%511%311p051'Q2&Q=r6r5r4r3%55F4321&S;(<r2%24FF51r7%53G21&QF%13<:9p031p0:1pXJM1p4N1pWBC1pR8E1pX2N1pQNQ01pQHQ61").
Proof. intros HIok LB cr M VM B m. intros HH H1. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B, m) H1) as (_ & D & _). exact D. Qed.
Lemma dkr_hpres_blk : ltac2:(TCodec.tc2 tcn__PmParKit "QG'9'='I%2211%411&QH%611'U:yR0%211';y8%511%311p051&QDvMr8r7r6r5r4r3%877654321&S;(<r2%24II51r9%53J21&QMr:%22@1&SA&QB%11C&SF+2+Q?%3221%7251&RM%14IHGFp031p0<1p0@1p0G1pXJQ=1p4Q>1pR:Q31pR8Q41pWFQ=1pYHQB1pZ4QC1pR4QB1").
Proof. intros LBc sp' scr' W' M M' B m.
intros HP Hin BRc TOP i Hi D. destruct (BRc B m Hin) as (Q0 & Q1 & Q4). pose proof (PMK.kl_errno segs L KL) as KE. pose proof (PMK.kl_img segs L KL) as KI.
apply (L5C.hpres_cdef L LBc sp' scr' W' M M' i HP); [unfold hl_ceil in Q4; lia| left; exists (B, m); split; [exact Hin| cbn; lia]| unfold in_errno; lia| exact D].
Qed.
Lemma dkr_hpres_hi : ltac2:(TCodec.tc2 tcn__PmParKit "QH'9'='I%2211%411&QH%611'U:yR0%211';y8%511%311p051&QDvMr8r7r6r5r4r3%877654321&QE&QB%11:%3417:9&SAz%221=r:%421<&S@%12?>&SF+2+R0%3221%;251&RMr9%241IHGp041p0<1p0?1p0C1p0H1pY2Q>1pWJQ?1pR:Q41pR8Q51pWFQ>1pYHQC1pZ4QD1pR4QC1").
Proof. intros LBc sp' scr' W' M M' a n.
intros HP (_ & SLO & SHI & STOP & _) S0 H1 H2 i Hi D. pose proof (PMK.kl_errno segs L KL) as KE. pose proof (PMK.kl_img segs L KL) as KI.
apply (L5C.hpres_cdef L LBc sp' scr' W' M M' i HP); [lia| right; left; unfold hl_ceil; split; [lia| lia]| unfold in_errno; lia| exact D].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "Q2'U:yR0%211';y8%511%311p051'I'RJ'RG&R4vTLv0&ROr4r3r2r1%877654321&QFr5&RC%116&SG&RB%119%3214%83751p0:1pYLD1pZLF1pY8H1pR8J1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma iss_unread_defined : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
- destruct H as (Hn & _). apply (L5.defined_sub M (ois + 80) 24); [exact D| lia| lia].
- destruct H as (_ & _ & _ & Hn & _ & _ & DB & _). apply (L5.defined_sub M p c); [exact DB| lia| lia].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "QM'U:yR0%211';y8%511%311p051'I'RJ'RG&R4vTLv0&ROr4r3r2r1%877654321'C'?&SA&S@+RA%22:1&RC%11:%6231&RB%11=+S8%92A1%;231%=261'A'@r6(R2%13GFE%43O31r5%@11%E2I1%?13%F2KM%H221%J241%K281qY<Q91%?2Q:1qY2Q;1%A2Q<1qX0Q=1%C2Q>1%Q32E1p0Q51pYLQ?1pZLQA1pY8QC1pR8QE1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma iss_unread_where : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
- destruct H as (Hn & _). left. lia.
- destruct H as (_ & _ & _ & Hn & _). right. exists c, n, p. split; [reflexivity| lia].
Qed.
End S.
Lemma iss_size_lt : ltac2:(TCodec.tc2 tcn__PmParKit "Q:'U:yR0%211';y8%511%311p051'I'RJ'RG&R4vTLv0&ROr4r3r2r1%877654321'?&SAz&SG&RB%118&RC%11:%5231%8271&SB&SF+2+K%3221%5271%@271p0B1pYLL1pZLN1pY8Q01pR8Q21").
Proof. intros M ois str sm.
intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
- destruct H as (Hn & _). lia.
- destruct H as (_ & _ & _ & Hn & Hc & _). lia.
Qed.
Section Upd.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Lemma vstr_at_keep : ltac2:(TCodec.tc2 tcn__PmParKit "Q>'I'RJ&SAzr2%3221&S@r3+H%3221&SF+2+R0%3221%<251&QCvQ3vQ4r4%44321;'@r7(R2r1%23AD1%53H41&RM%14;:G9p031pY<M1pY2N1pX0O1&RKvTL&ROr6r5%5543E21%6554EA3p021p091p0F1p0L1p0Q61pYBQ;1pY6Q=1").
Proof. intros o s.
intros Ho Ho' AG DKB (D & _ & H). split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [exact I|].
destruct s as [n|c n p].
- destruct H as (Hn & B0). split; [exact Hn|]. u8x AG B0.
- destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & _).
split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|]. split; [exact Hn|]. split; [exact Hc|]. split; [exact He|].
split; [apply (defined_dkr M M' p c (DKB c n p eq_refl) DB)| exact I].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "S='I'RJ'RG&R4vTLv0&ROvQ3r5r4r3%877654321&SAzr6%3221&S@r7+X@%3221&SF+2+R0%3221%<251&QCvQ4r8+Q8%44F321r9+Q@%@221+S8%94K821r:+TL%E221+SD%>4Q0=21&RMr;%J21>+8%44Q5B21r<+TH%O221+4%94Q:G21'@r?(R2r2r1%33Q=21%63QG51%A4QBO4Q@p021pY<QK1pY2QL1pX0QM1&QJr>%Q@21Q4%34QMQ71H&QI%QC2@E%24R0Q:1K'?&RIr@+R@%QI221%421Gr=%R0221&RB%11?%R3241%;241'C%Q03RB7R5%Q13RC8QN%3221rBrA(R1%;1A%23Q61J%RG7RFRERDR0541p071p0<1p0I1p0M1p0Q21p0Q?1p0QE1p0QK1p0R11p0R71p0R=1p0RG1p0RL1pZ<S81pX<S91pYLS81pZLS:1pY8S<1")) (only parsing).
Variable ois : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable g' : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable st' : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Lemma iss_upd : ltac:(sec_stmt2 constr:(SECT) 5%nat 0%nat).
Proof.
intros (H0 & D & _ & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2) Ho Ho' AG1 AG2 AG3 DK1 DK2 AGB G' ST' GR STR.
destruct IOS as (J0 & J32 & J36 & J40 & J48 & Z & JD & _ & _).
cbn [PM.sm_g PM.sm_eg PM.sm_st].
split; [u64x AG1 H0|].
split. { intros i Hi. destruct (Z_lt_le_dec i 40) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 48) as [Y|Y]; [apply DK1; [lia| apply D; lia]| rewrite AG2 by lia; apply D; lia]. }
split; [exact I|]. split; [u64x AG1 H16|]. split; [u64x AG1 H24|]. split; [u64x AG1 H32|].
split; [exact G'|]. split; [u64x AG2 H48|]. split; [u64x AG2 H64|].
split. { apply vstr_at_keep; [lia| lia| eapply L5C.agree_on_sub; [exact AG2|lia|lia]| exact AGB| exact VS]. }
split; [u64x AG2 H104|]. split; [u32x AG2 H112|].
split.
{ split; [u64x AG2 J0|]. split; [replace (ois + 120 + 32) with (ois + 152) by lia; exact ST'|]. split; [u32x AG3 J36|]. split; [u64x AG3 J40|].
split; [u64x AG3 J48|].
split. { apply (PMF.zeros_at_agree M M'); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]| exact Z]. }
split. { intros i Hi. destruct (Z_lt_le_dec i 32) as [X|X]; [rewrite AG2 by lia; apply JD; lia|].
destruct (Z_lt_le_dec i 36) as [Y|Y]; [apply DK2; [lia| apply JD; lia]| rewrite AG3 by lia; apply JD; lia]. }
split; [exact I| exact STR]. }
split; [exact E1| exact GR].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "T>'I'R@&R=vTLv0&RO&S0vQ3r5r4r3%9887654321&SAzr6%3221&S@r7+\0%3221&SF+2+R0%3221%<251&QCvQ4r8+XH%44F321r9+Z0%@221%84J71;&RMr:%D218+Q8%44O<21&RD&R9%11;%311&QN%:4Q5B21&R5%11;%Q32Q21r;%411&SD+Q0&R8%115%Q22Q11%5241%Q8271%Q=21Q2r<%>11%812%Q92Q81%<2;1%Q64QHQ541'@'RJ&R;r@%211(R2r2r1%33QN21%93851%Q84R3Q@4R1p021pY<R<1pY2R=1pX0R>1&QJ+Y0%R12>1r>%Q;11%Q=11%64RBQK41rA+Y8%R8221%:4RFQO1Q>rB+Y@%R<221r?%?4RKR421rC+YH%RA221%C4ROR815%QK19%QM11%RI21?%RJ2RI@%RG28=rD%R111%R311%RK21R0%S0251rGrF&RNrE(R0%R:12%R<11%331<E%6251%SD8SCSBSAS@RL981p0;1p0B1p0D1p0H1p0M1p0Q31p0Q81p0Q@1p0R01p0R71p0RB1p0RF1p0RM1p0S31p0S81p0S>1p0SH1p0SM1pY@T91pX:T:1pYBT:1pY8T<1pY:T=1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable de' : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable rem' : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Lemma parser_src_upd : ltac:(sec_stmt2 constr:(SECT) 5%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 DK DKC Hb Hb' AGV AGT C1 C2 C3 C4 Q1 Q2 Q3.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
unfold PMPS.with_src. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem].
split; [u64x AG1 H0|].
split. { intros i Hi. destruct (Z_lt_le_dec i 280) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 320) as [Y|Y]; [apply DK; [lia| apply D; lia]| rewrite AG2 by lia; apply D; lia]. }
split; [exact I|]. split; [u8x AG1 H8|]. split; [u8x AG1 H9|]. split; [u32x AG1 H12|]. split; [u8x AG1 H16|]. split; [u32x AG1 H20|].
split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG1|lia|lia]| exact NI]. }
split.
{ split; [u64x AG1 F1|]. split; [u64x AG1 F2|].
split. { apply (defined_dkr M M'); [eapply dkr_sub; [exact DK|lia|lia]| exact F3]. }
split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [u32x AG2 H320|]. split; [u64x AG2 H328|]. split; [exact I|].
split. { apply vstr_at_keep; [lia| lia| eapply L5C.agree_on_sub; [exact AG2|lia|lia]| exact AGT| exact TB]. }
split. { apply (PMF.vec_at_agree segs M M'); [lia| lia| exact Hb| exact Hb'| eapply L5C.agree_on_sub; [exact AG2|lia|lia]| exact AGV| exact VEC]. }
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
Lemma vstr_short_keep : ltac2:(TCodec.tc2 tcn__PmParKit "Q:'I&SAzr2%3221&S@r3+H%3221&SF+2+R0%3221%<251&QCvQ3vQ4r4+1%544321&RMr5%A214+G%449821&RKvTL&ROr6(R3%119%6554@31r7%415%9587B21p041p0<1p0B1p0I1p0Q31pY2Q81pY6Q91").
Proof. intros o n.
intros Ho Ho' AG DK (D & _ & Hn & B0). split.
{ intros i Hi. destruct (Z_lt_le_dec i 1) as [X|X]; [rewrite AG by lia; apply D; lia| apply DK; [lia| apply D; lia]]. }
split; [exact I|]. split; [exact Hn|]. u8x AG B0.
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "TB'I'R@&R=vTLv0&RO&S0vQ3r5r4r3%9887654321&SAzr6%3221&S@r7+\0%3221&SF+2+R0%3221%<251&QCvQ4r8+XH%44F321r9+Z0%@221+@%94K821r:+[8%E221+H%>4Q0=21&RMr;%J21>+Q8%44Q5B21r<+Z@%O221%84Q9F1:&RKr=%Q3215&R;%11<%55QCQAL31&RD&R9%11<%311&QN%D4QEQ221&R5%11<%QC2QB1r>%411&SD+Q0&R8%115%QB2QA1%5241%QH271%QM21QBr?%>11%812%QI2QH1%<2;1%QF4R8QE41&QJrB+Y0%R3221r@%M11%O11%74RDQM41rC+Y8%R:221%;4RHR11Q0rD+Y@%R>221rA%@4RMR621rE+YH%RC221%D4S1R:15%Q=19%Q?11%RK21?%RL2RK@%RI28=rF%QC11%QE11%RM21QB%S2251rIrH&RNrG(R0%QL12%QN11%331<E%6251%SF8SESDSCSBRN981p0;1p0B1p0D1p0H1p0M1p0Q31p0Q81p0QA1p0QH1p0R31p0R71p0R>1p0RE1p0RJ1p0S01p0S61p0S<1p0SB1p0SL1p0T11pY@T=1pX:T>1pYBT>1pY8T@1pY:TA1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable de' : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable rem' : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Lemma parser_src_tb_upd : ltac:(sec_stmt2 constr:(SECT) 5%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 AG3 DK DKT TB' DKC Hb Hb' AGV C1 C2 C3 C4 Q1 Q2 Q3.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
unfold PMPS.with_src. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem].
split; [u64x AG1 H0|].
split. { intros i Hi. destruct (Z_lt_le_dec i 280) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 320) as [Y|Y]; [apply DK; [lia| apply D; lia]|].
destruct (Z_lt_le_dec i 336) as [Y2|Y2]; [rewrite AG2 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 360) as [Y3|Y3]; [apply DKT; [lia| apply D; lia]| rewrite AG3 by lia; apply D; lia]. }
split; [exact I|]. split; [u8x AG1 H8|]. split; [u8x AG1 H9|]. split; [u32x AG1 H12|]. split; [u8x AG1 H16|]. split; [u32x AG1 H20|].
split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG1|lia|lia]| exact NI]. }
split.
{ split; [u64x AG1 F1|]. split; [u64x AG1 F2|].
split. { apply (defined_dkr M M'); [eapply dkr_sub; [exact DK|lia|lia]| exact F3]. }
split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [u32x AG2 H320|]. split; [u64x AG2 H328|]. split; [exact I|].
split; [exact TB'|].
split. { apply (PMF.vec_at_agree segs M M'); [lia| lia| exact Hb| exact Hb'| exact AG3| exact AGV| exact VEC]. }
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "RC'I'R@&R=vTLv0&RO&S0vQ3r3r2r1%9887654321&SAzr4%3221&S@r5+\0%3221&SF+2+R0%3221%<251&QCvQ4r6%34E21:&RM&RD&R9%11?%311&QN%64L921&R5%11:%J2I1r7%411&SD+Q0&R8%115%I2H1%5241%O271%Q421Ir8%>11%812%Q02O1%<2;1%M4Q?L41'@'RJ&R;r<%211(R2%13QEQDQC%73631%Q24QHQ5QFQAp021pY<R11pY2R21pX0R31r;r:%R48R3R2R1R0Q<<21p041p0B1p0I1p0Q41p0Q81p0Q@1p0QE1p0QO1p0R41pYBR?1pY8RA1pY:RB1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma parser_at_keep : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros PA Ho Ho' AG DKC Hb Hb' AGV DKT.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). destruct SRC as (_ & _ & _ & F4 & F5 & F6 & F7 & G1 & G2 & G3 & _).
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem] in *.
apply (parser_src_upd op ois (PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) de rem PA Ho Ho'); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; try assumption.
- eapply L5C.agree_on_sub; [exact AG|lia|lia].
- eapply L5C.agree_on_sub; [exact AG|lia|lia].
- apply dkr_agree. eapply L5C.agree_on_sub; [exact AG|lia|lia].
- replace (op + 288) with (op + 24 + 264) by lia. u64x AG F4.
- replace (op + 296) with (op + 24 + 272) by lia. u64x AG F5.
- replace (op + 304) with (op + 24 + 280) by lia. u64x AG F6.
- replace (op + 312) with (op + 24 + 288) by lia. u64x AG F7.
Qed.
End S.
Definition set_more (s : PM.pst) (v : Z) : PM.pst :=
PM.PST v (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s).
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "S?'I'R@&R=vTLv0&RO&S0vQ3r4r3r2%9887654321&SAzr5%3221&S@r6+\0%3221&SF+2+R0%3221%<251&QCvQ4r7+8%44F321r8+9%@221+[G%94K821&RMr9%E219+1%44Q0=21&QKr:%J21>%34Q8A1@'C'@%13Q>@Q1%23Q?A9%4221&RD&R9%11:%311&QN%C4Q?L21&R5r;%211%Q>2Q=1r<%511&SD+Q0&R8%115%Q=2Q<1%5241%QC271%QH21Q=r=%?11%812%QD2QC1%<2;1%QA4R3Q@41'RJ&R;rA%211(R2r1%23R8R71%Q53741%Q@4R<QIR9R;p021pY<RE1pY2RF1pX0RG1r@&RLr?r>%3221%RK8RJRIRHRGR3@51p071p0E1p0L1p0Q71p0Q<1p0QC1p0QI1p0QN1p0R41p0R:1p0R@1p0RJ1p0RO1pZNS;1pYBS;1pY8S=1pY:S>1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma parser_more_upd : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 DK V8 Hv DKC Hb Hb' AGV AGT.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
unfold set_more. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG3 : forall a n, op + 9 <= a -> a + n <= op + 384 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
split; [u64x AG1 H0|].
split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 9) as [Y|Y]; [apply DK; [lia| apply D; lia]| rewrite AG2 by lia; apply D; lia]. }
split; [exact I|]. split; [exact V8|]. split; [apply (L5C.u8_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H9]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H12]|].
split; [apply (L5C.u8_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H20]|].
split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG3; lia| exact NI]. }
split.
{ split; [u64x AG2 F1|]. split; [u64x AG2 F2|].
split. { apply (L5C.defined_agree M M'); [apply AG3; lia| exact F3]. }
split; [u64x AG2 F4|]. split; [u64x AG2 F5|]. split; [u64x AG2 F6|]. split; [u64x AG2 F7|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H320]|]. split; [u64x AG2 H328|]. split; [exact I|].
split. { apply vstr_at_keep; [lia| lia| apply AG3; lia| exact AGT| exact TB]. }
split. { apply (PMF.vec_at_agree segs M M'); [lia| lia| exact Hb| exact Hb'| apply AG3; lia| exact AGV| exact VEC]. }
split; [exact Hv|]. split; [exact B2| exact B3].
Qed.
End S.
Lemma removelast_len : ltac2:(TCodec.tc2 tcn__PmParKit "E'9'RA%211'Eu1&8r1%2261%5241'@':&S?r2%22<1%92=1&D%;2?4%221=%93841p0;1pXDB1").
Proof. intros l.
intros H. destruct l as [|x l]; [cbn in H; lia|]. rewrite (app_removelast_last x (l := x :: l)) at 2 by discriminate.
rewrite length_app. cbn. lia.
Qed.
Lemma nth_removelast_lt : ltac2:(TCodec.tc2 tcn__PmParKit "G'9'RA%211':&Fr2&8&S?r3%2281%4291%7261'@&Hr4%82>1%34?81;%44@93<%63A21p081pX8C1pX>B1pXDD1").
Proof. intros l i d.
intros H. destruct l as [|x l]; [cbn in H; lia|]. rewrite (app_removelast_last x (l := x :: l)) at 2 by discriminate.
rewrite app_nth1 by exact H. reflexivity.
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "RB'I'9'RA%211&RHvTL&RO&S0vQ3r4r3r2r1%9887654321'Eu1&8%12?6%4231&SAzr6%3221&S@r7+H%3221&SF+2+R0%3221%<251%=2<8r8&SD+Q0%928<%3221%?251%D219&QCvQ4r:+8%44Q4321r;+@%H221%84Q8715%F2E7%@2?1%;4Q;:61&QJr=%O21;&SGr<&SE%Q:2QH@%211%J2I1%Q6251%721K%;4QJF91r>&S?%12R0E%QO8QNQMQLJ3>;1p051p0B1p0F1p0K1p0Q11p0Q91p0Q;1p0QE1p0QJ1p0R01pZJR;1pX@R?1pWNR@1pZNRA1")) (only parsing).
Variable v : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Lemma vec_at_pop : ltac:(sec_stmt2 constr:(SECT) 4%nat 0%nat).
Proof.
intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL) H1 Hv Hv' Hb Hb' AG0 AG16 AGB C8.
pose proof (PM.pow2_pos k ltac:(lia)) as P2. pose proof (removelast_len stk H1) as RL.
split; [u64x AG0 V0|].
split; [rewrite RL; rewrite Nat2Z.inj_sub by lia; replace (b + 32 * (Z.of_nat (length stk) - Z.of_nat 1)) with (b + 32 * Z.of_nat (length stk) - 32) by lia; exact C8|].
split; [u64x AG16 V16|].
split; [exact Hk|]. split; [rewrite RL; lia|]. split; [exact Hal|].
split; [apply (L5C.defined_agree M M' b _ AGB DB)|]. split; [exact I|]. split; [exact I|].
intros n Hn. rewrite (nth_removelast_lt stk n PM.ps_root Hn). rewrite RL in Hn.
apply (PMF.pstate_at_agree segs M M'); [lia|lia| |apply EL; lia].
apply (L5C.agree_on_sub M M' b (32 * 2 ^ k)); [exact AGB|lia|lia].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "U='I'R@&R=vTLv0&RO&S0vQ3r3r2r1%9887654321&SAzr4%3221&S@r5+\0%3221&SF+2+R0%3221%<251'Eu1&8'RA&R:%11@%4231%7261&QCvQ4r7+8%44N321r8+9%H221+3%94Q3821r9+@%M221+[0%>4Q8=21r:+[H%Q2221%B4Q<A1?&RMr;%Q621B+1%44QAF21r<+<%Q;221+4%94QFK21r=+[@%Q@221%=4QJO1M&QKr>%QD21Q0%34R2Q31>&QIr?%QH21>&SG&R6%11=%321E%74R:Q;51%41;%621H%R42R31&QJrA%R321D&R5%11>&SD+Q0&SE%QL1B%QO2QN1%311%6251%R=281%E217%>4RLQM<1&RD&R9r@%211%411&QN%QB4ROR421%C1E%RL2RK1rB%F11&R8%113%RI2RH1%H2G1%RO251%S421RIrC%N11%812%S02RO1%O2N1%RE4S?RD41'@'RJ&R;rG%211(R2%13SESDSC%73631%R;4SHRMSFSAp021pY<T11pY2T21pX0T31rF(QO&R7rE%211%QO12%R121RC%Q:14%C15&R<%117%QK18%Q519&S?%SE1;%22SG1%?9RM<:986541%TC8TBTAT@T?SCKA1p0C1p0Q11p0Q81p0QA1p0QD1p0QL1p0R<1p0R@1p0RI1p0RN1p0S31p0S91p0S?1p0SD1p0SJ1p0T01p0T61p0T?1p0TI1p0TN1pYBU91pY8U;1pY:U<1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma parser_pop_upd : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' HL AG1 AG9 AG2 AG3 DK8 DK12 DK368 C8 C12 Hd C368 DKC Hb Hb' AGV AGT.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 368 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
split; [u64x AG1 H0|].
split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 9) as [Y|Y]; [apply DK8; [lia| apply D; lia]|].
destruct (Z_lt_le_dec i 12) as [Y1|Y1]; [rewrite AG9 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 16) as [Y0|Y0]; [apply DK12; [lia| apply D; lia]|].
destruct (Z_lt_le_dec i 368) as [Y2|Y2]; [rewrite AG2 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 376) as [Y3|Y3]; [apply DK368; [lia| apply D; lia]| rewrite AG3 by lia; apply D; lia]. }
split; [exact I|]. split; [exact C8|].
split; [apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG9|lia|lia]|lia|lia|exact H9]|].
split; [exact C12|].
split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H20]|].
split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG4; lia| exact NI]. }
split.
{ split; [u64x AG2 F1|]. split; [u64x AG2 F2|].
split. { apply (L5C.defined_agree M M'); [apply AG4; lia| exact F3]. }
split; [u64x AG2 F4|]. split; [u64x AG2 F5|]. split; [u64x AG2 F6|]. split; [u64x AG2 F7|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H320]|]. split; [u64x AG2 H328|]. split; [exact I|].
split. { apply vstr_at_keep; [lia| lia| apply AG4; lia| exact AGT| exact TB]. }
split. { apply (vec_at_pop (op + 360) (PM.p_b s) (PM.p_k s) (PM.p_stk s) VEC HL); [lia|lia|exact Hb|exact Hb'| apply AG4; lia| eapply L5C.agree_on_sub; [exact AG3|lia|lia] | exact AGV|].
replace (op + 360 + 8) with (op + 368) by lia. exact C368. }
split; [right; reflexivity|]. split; [exact B2| cbn [PM.p_depth]; unfold PM.MAX_DEPTH in *; lia].
Qed.
End S.
End Upd.
End Kit.
Lemma pot_text_le_parser : ltac2:(TCodec.tc2 tcn__PmParKit "Q9'Q<'R@&Q:&SAz&QAr3%211%5241&Q>r4%211%9281'?&R8%115%=2<1+;%?231%6231&S2&R>r6r5%3221%521?&R?r7&R;%117&R<%119%63531%=21:p091p0@1p0H1p0M1pX2Q41pYBQ61pQLQ81").
Proof. intros L s cr.
intros HK HB Hk. unfold PMSP.credit_le, PM.pot_parser, PM.credit_add, PM.pot_stack. cbn [fst snd].
assert (P : 2 ^ (PM.p_k s + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
assert (Q : 0 <= hl_k_per_malloc L * (11 - PM.p_k s)) by (apply Z.mul_nonneg_nonneg; lia).
assert (Q2 : 0 <= (11 - PM.p_k s) * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; lia).
intros (C1 & C2). split; lia.
Qed.
Lemma credit_keep_text : ltac2:(TCodec.tc2 tcn__PmParKit "Q>'Q<&Q:'R@&S1r6r5&R>r7r3%3221r2%5241%948731&R?r8&R;%118&R<%11:%63531%51:%41;%93821%D4CB41'@'I&R8%11Cr4%311%63531r9r:%K21M%L226%Q044L21p061p0>1p0J1pYFQ51pYDQ61pYBQ71pX6Q91pX4Q:1pX2Q;1pQLQ=1").
Proof. intros L cr cr1 cr2 s s1 s2.
unfold PMSP.credit_keep, PM.pot_parser, PM.credit_add. cbn [fst snd]. intros (A1 & A2) (B1 & B2) E. rewrite E. lia.
Qed.
Lemma credit_le_keep : ltac2:(TCodec.tc2 tcn__PmParKit "@&Q:&S2r2r4%3221&S1r5r3%342516%8223p021p071pY><1pY<=1pX4>1pX2?1").
Proof. intros cr cr1 p p1. unfold PMSP.credit_le, PMSP.credit_keep. intros (A1 & A2) (B1 & B2). split; lia. Qed.
Lemma src_step_trans : ltac2:(TCodec.tc2 tcn__PmParKit "B'RE'RG&S3r6r5r3r2%544321r8%741654p031p041pZ2;1pZ0<1pYN=1pZ:?1pZ8@1pZ6A1").
Proof. intros src1 src2 src3 sm1 sm2 sm3.
unfold PMSP.src_step. intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5).
split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply B4; apply A4; exact X| lia].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit "C'9'RA%211&RFr1%211'Eu2&8r2%2291%5241&S?r3%22=1%<11p051p0<1pZJ@1")) (only parsing).
Variables (stk : list PM.pstate).
Lemma stack_shape_pop : ltac:(sec_stmt2 constr:(SECT) 1%nat 0%nat).
Proof.
intros (H1 & H2 & H3 & H4 & H5) HL. pose proof (removelast_len stk ltac:(lia)) as RL.
split; [rewrite RL; lia|]. split; [rewrite RL; lia|].
split; [rewrite (nth_removelast_lt stk 0 PM.ps_root) by (rewrite RL; lia); exact H3|].
split.
- intros i Hi. rewrite RL in Hi. rewrite (nth_removelast_lt stk i PM.ps_root) by (rewrite RL; lia). apply H4. lia.
- intros i Hi. rewrite RL in Hi. rewrite (nth_removelast_lt stk i PM.ps_root) by (rewrite RL; lia). apply H5. lia.
Qed.
End S.
End PMPK.
