(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JatCls JatCellEx JatDepot ArtBridge JatInv JatInvMalloc JatLift JatWrapKit
JatFsInv JatFsInvLaws.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInvLaws."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatWrapC.Wrap."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BASE"; "0BUDGET"; "1None"; "1bool"; "1false"; "1fst"; "1list"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"]; ["3Z"; "0FF"; "0FP"; "0G"; "0K"; "0LB"; "0LK"; "4mkCfg"; "5Model"; "5m_halted"; "5m_vm_lazy"; "5page_base"; "5page_in_ranges"; "6bvmap"; "0M"; "0M1"]; ["0MAPS0"; "0Mr"; "0Mr'"; "0Mr0"; "0NOACC0"; "0Q"; "0R"; "0R'"; "0RESV0"; "7BInv"; "7bhid"; "8cell"; "9MInv"; "9mrestrict"; ":msteps"; ";credit"]; [";in_block"; "<fframe"; "<in_fframe"; "<in_shadow_of"; "<model_rt"; "<shadow_blk"; "<vml_of"; "=art_fsg"; "=art_fsinv"; "=cs_zone"; ">fs_zone3"; "?art_alloc_rep"; "?art_client_ok"; "?art_gs"; "?art_kn_ok"; "?art_lazy_ok"]; ["?art_ri_inv"; "?art_run"; "?g_fs"; "?g_log"; "?rn_HI"; "?rn_loff"; "?rn_tp"; "@art_alloc_zone'"; "Amkst"; "Aseg_rom"; "BTSet"; "Csrealizes"; "Dmem_grows"; "Eloaded_segments"; "FIn"; "Gadd"]; ["Gle"; "Glt"; "Gmodulo"; "0a"; "0b"; "0cr"; "0fx"; "0model"; "0model'"; "0n"; "0pc0"; "0pc1"; "0rn"; "0scfg"; "HZ_to_bv"; "Hbv"]; ["Hbv_unsigned"; "0u"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Pure.
Variables (A : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model) (Mr' : word -> option byte).
Hypothesis B : bstep A M model A M1 model' 0 0 false.
Hypothesis E : mrestrict (bhid A model') M1 = Mr'.
#[using="M M1 B"] Lemma art_bstep_pure_hid : ltac2:(TCodec.tc2 tcn__JatWrapC ">'ROyR0%211'='4&Q:v0vRHr1%43321vRG%63513%93831pV6;1").
Proof.
intros x. destruct B as (_ & B2 & B3 & _). destruct (bhid A model' x) eqn:E1.
- destruct (B2 x E1) as (H & _). symmetry; exact H.
- destruct (bhid A model x) eqn:E0; [|reflexivity]. exfalso. specialize (B3 x E0 E1). lia.
Qed.
#[using="model' B E"] Lemma art_bstep_pure_mem : forall x, M1 x = if bhid A model x then M x else Mr' x.
Proof.
intros x. rewrite <- art_bstep_pure_hid. destruct B as (_ & B2 & _). destruct (bhid A model' x) eqn:E1.
- exact (proj2 (B2 x E1)).
- rewrite <- E. unfold mrestrict. rewrite E1. reflexivity.
Qed.
#[using="model' B E"] Lemma art_bstep_pure_frame : ltac2:(TCodec.tc2 tcn__JatWrapC "J'ROyR0%211'='8y8%611%311vQ2r1%211&Q=&Q:v0vRG%3221vN%63218%?3;81vOr2%211%612%D3@21p061pV6G1").
Proof. intros x H. rewrite art_bstep_pure_mem. unfold mrestrict in H. destruct (bhid A model x); [reflexivity | exact H]. Qed.
#[using="model' B E"] Lemma art_bstep_pure_grows : ltac2:(TCodec.tc2 tcn__JatWrapC "=&R<&Q=&Q:v0vRG%3221vN%6221vQ2%9221vO%;251p031").
Proof.
intros G x Hx. rewrite art_bstep_pure_mem. destruct (bhid A model x) eqn:E0; [exact Hx|]. apply G. unfold mrestrict. rewrite E0. exact Hx.
Qed.
#[using="A M M1 B"] Lemma art_bstep_pure_lazy : ltac2:(TCodec.tc2 tcn__JatWrapC "G'ROyR0%211'='4&L&Kr1%211&JvRH%211%7241(;%;3:21r2%:11vRG%911%>231%A3@17p071pV6D1").
Proof. intros x H. destruct B as (_ & _ & _ & _ & B5). destruct (B5 x H) as [L | (N & _)]; [exact L | discriminate N]. Qed.
End Pure.
Section Keep.
Variable FSG : Type.
#[using="Type"] Lemma art_lazy_ok_shrink : forall rn (G : art_gs FSG) A lazy lazy', art_lazy_ok FSG rn G A lazy ->
(forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) -> art_lazy_ok FSG rn G A lazy'.
Proof.
intros rn G A lazy lazy' (L1 & L2 & L3 & L4) SH. split; [|split; [|split; [exact L3 | exact L4]]].
- intros w Hw. apply L1. apply SH. exact Hw.
- intros w Hw. destruct (L2 w Hw) as [X | [X | X]]; [left; exact X | right; left; exact X | right; right].
intros x Hx. specialize (X x Hx). destruct (page_in_ranges (page_base x) lazy') eqn:E1; [|reflexivity]. rewrite (SH x E1) in X. discriminate X.
Qed.
#[using="Type"] Lemma art_shadow_blk_frame : ltac2:(TCodec.tc2 tcn__JatWrapC "Q@'ROyR0%211'8y8%511%311p051'@&R@zr2%3221'=&RBr3+8%3221%53:18&RA%12:5&QCr6r5r1%43321r8&RN%12KA%311r9%113%C3J31p081pU8J1&QE%13:>=r7%33<1@p031p061p0E1p0H1p0O1pUDQ41pV4Q51pR0Q71pQNQ81").
Proof.
intros M M1 u n Hu H8 Hn AG (SZ & SP). unfold in_shadow_of, HeapIfaceA.S in AG.
pose proof (Z.div_mod u 8 ltac:(lia)) as DU. rewrite H8, Z.add_0_r in DU.
pose proof (Z.div_mod n 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as RN.
assert (HI : forall j, 0 <= j -> 8 * j + 1 <= n -> u / 8 + j <= (u + n - 1) / 8).
{ intros j Hj Hjn. apply Z.div_le_lower_bound; lia. }
split.
- intros j Hj. unfold byte_at. rewrite AG; [exact (SZ j Hj)|]. unfold HeapIfaceA.S. specialize (HI j ltac:(lia) ltac:(lia)). lia.
- intros Hm. unfold byte_at. rewrite AG; [exact (SP Hm)|]. unfold HeapIfaceA.S. specialize (HI (n / 8) ltac:(apply Z.div_pos; lia) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma art_client_ok_frame : ltac2:(TCodec.tc2 tcn__JatWrapC "QJ'R1'7'9'@%2211%411&QA%611'ROyR0%211'8y8%511%311p051&QLr7r6r5r4r3r2%76654321&R<%1243&R>r:%23H61&QC&6%13LL:&:%13NN<%5331<'=&RN%12L@%E11r8%113%63K31p081p0?1pU8Q91pU:Q91r9%O6D18NMKp031p0H1p0K1pR0Q41pQNQ51p2Q@1pQ>Q?1pQ4Q@1pQ<QC1pUJQI1").
Proof.
intros rn LB FF LK A M M1 (C1 & CR) GR AG. split; [|exact CR].
intros b Hb. destruct (C1 b Hb) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
split. { intros i Hi. apply GR. exact (K7 i Hi). }
split; [|exact K9]. apply (shadow_blkR_frame M M1 (fst b) (snd b)); [lia | | lia | intros a Ha; exact (AG b a Hb Ha) | exact K8].
pose proof (Z.div_mod (fst b) 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (fst b / 16)) with ((2 * (fst b / 16)) * 8) by ring. apply Z_mod_mult.
Qed.
End Keep.
Section Wrap.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Context {fx : PropExec.FPState}.
Definition art_alloc_zone' (G : art_gs art_fsg) (x : Z) : Prop :=
art_alloc_zone art_fsg rn G x \/ (rn_tp rn - 88 <= x < rn_tp rn - 80) \/ (rn_tsd rn + 8 * rn_key rn <= x < rn_tsd rn + 8 * rn_key rn + 8).
Definition art_alloc_rep_frame_law' : Prop :=
forall G LB M M', art_alloc_rep art_fsg rn G LB M -> mem_grows M M' ->
(forall x : word, art_alloc_zone' G (U x) -> ~ in_block LB (U x) -> M' x = M x) -> cellA M' (rn_tp rn + rn_loff rn) 4 0 -> art_alloc_rep art_fsg rn G LB M'.
Hypothesis AFL : art_alloc_rep_frame_law'.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).
#[using="Hwx AFL"] Theorem art_wrap_pure : ltac2:(TCodec.tc2 tcn__JatWrapC "X3&R:&My5'ROyR0%211%5241'8y8%611%311p061'H'7'9'@%2211%411&QA%611&Q?!p071p0<2p0C1p0C1&R0'QGvQ0vQ8vQ4v1v2&QHvRLr7r6r5r4r3r9&QFr8%211%B?A@?>=<;:9876541'=%Q71Q9&I%118(3%11Q=%63531'Q<r:%22A1'QM%11M&QKr1r;&Q=&Q:r<%22L1r=%5221%95Q7Q0871&R2r2%22Q:1r>%Q65Q52<B1&QLr?%26Q8:<?Q21&QN%13Q@Q?Q:&QO&Jr@%211%45QFQ?Q<F1'Q9&R=&R4%11QC&R3%12QLQCrBrA%8;7QNQMQL5QKQJ3L21'<'>'Q>&R8vRFrHrGrE%Q62D1rF%Q9221&R9%11D%:598731%;5:R2Q5Q?2%=3G21&R<%127QB&?&S0%12S;QE%Q111%411%R;1Q>%QF2KB%QH31DQ@%R83S;31p051pV6SB1&Q;&R?&R6%11RI&R5%11RK%5231u4z%95Q>R7321%QL3RKQNR8%Q8221%Q92=1%Q:2I1%Q;2L1qR6SL1%Q<2SM1qUHT41%Q>2T51qR@T51%Q@2T61%R=1RC&R7%12S7R;&Q@rD%221S;p041p071pV6T61%QK2:1p0QM1p0R71p0R=1p0R@1p0RD1p0RJ1pQ8S51%SK1S4&QJ%12SNRL&QB%12S2SKp031p061pV6TF1%SL1S<&QI%12T6S4%QL11p041pV6TL1&R>%13TMS9S4&QC&6%13U1U1T9&:%13U3U3T;%5331S?%SF1T=%R811p031p0:1pV6U91pU:U91%SJ3TETDTCrC%TC1SH%U3?U2U1U0TOTNTMTLTKQ<2S5S4S>TF1%RC2RMTH%S71R@%RC11%TN1SMrJ%11SO%TG3UJ31p051pV6V11'4rI%T<3QH1T?(5%TN3421%U21T8%U51T9%U13V421p041pV6V;1%TD3S?U>TG%TE3S@@TH%U63<21pV6V?1&QD%12DUC%U32SCU='R;vRM(G%SM5SLTKTMU6SD%221UDrQ0%64T;521p081p0:1p0=1p0B1p0M1p0Q61p0Q81p0Q<1pUBVK1pR0VM1pR6VN1pUHW51pR@W51%T>5T=QATDTCT5%C21TN%F4TKE1RMp041p0QG1p0R61p0R=1p0RF1p0UN1p0V21p0V:1pR<VN1pQ6W21p2W81pU<W61pQ>W81pQ4W91pQ<W<1pU@WB1pQNWD1pUFWK1pR>WK1pQ:X21").
Proof.
intros K R pc0 M model LB FF LK cr A FP Q INV Hhalt HMI RUN FPFS FPCS FPSH CONT.
destruct INV as (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in REPr, BV, LZ, EG.
pose proof (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hhalt HMI) as B0.
change (mkH (m_vm_lazy model) A) with (bhid A model) in REPr.
destruct (RUN G REPr FS CLI KN LZ B0) as ((R' & pc1 & Mr' & MS & GRr & FRr & LSAN & HQ) & FPAZ).
apply (bridge_msteps ASEGS scfg Hwx MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log art_fsg G) A (mkst R pc0 M (seg_rom ASEGS)) model
(mkst R' pc1 Mr' (seg_rom ASEGS)) K B0).
{ rewrite restrict_mkst. exact MS. }
intros ms' model' Est B1 RT BS. destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr0). set (M1 := ms_mem ms') in *. rewrite Ems. assert (EMr : mrestrict (bhid A model') M1 = Mr') by (symmetry; exact EMr0).
change (ms_mem (mkst R pc0 M (seg_rom ASEGS))) with M in BS.
pose proof (art_bstep_pure_frame A M M1 model model' Mr' BS EMr) as FRAME.
pose proof (art_bstep_pure_grows A M M1 model model' Mr' BS EMr GRr) as GROW.
pose proof (art_bstep_pure_hid A M M1 model model' BS) as HID.
assert (FR1 : forall x : word, ~ FP (U x) -> M1 x = M x) by (intros x Hx; apply FRAME; apply FRr; exact Hx).
apply (CONT R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
- exists G. cbn [vml_of fst snd].
split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. apply (AFL G LB _ Mr' REPr GRr).
- intros x Hz Hb. apply FRr. intros HF. apply Hb. exact (FPAZ _ HF Hz).
- exact LSAN. }
split. { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M1 FS GROW).
- intros x a Hz Hn. apply FR1. intros HF. apply Hn. exact (FPFS _ HF Hz).
- intros x Hz. apply FR1. intros HF. exact (FPCS _ HF Hz). }
split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
split; [exact CRED|].
split. { apply (art_client_ok_frame rn LB FF LK A M M1 CLI GROW). intros b a Hb Ha.
pose proof CLI as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _).
assert (Ra : 0 <= a < 2 ^ 64).
{ unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Ha). }
split; [exact KN|].
split. { apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
- intros x Hx. rewrite (art_bstep_pure_mem A M M1 model model' Mr' BS EMr). rewrite Hx. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_art_zone_below := (ltac2:(TCodec.tc2 tcn__JatWrapC "QH'QM'QG%211'7'9'@%2211%411'ROyR0%211'8y8%511%311p051'H&QKvRLr7r6r3%55E4321&QNvQ0vQ8%33218'Q9&R=vQ4&R4%11=v1v2&R3r9%22Q31r4%;;:>=97652CB1&R7r:%2214&RAr5%221=p041p081p0E1p0J1pV6Q<1pU@Q21pR4Q41pQNQ51p2Q>1pQ<Q?1pQ8QE1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_zone_below) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_zone_below) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_zone_below) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_zone_below) 3%nat 0%nat).
Variable Mr : ltac:(sec_ty2 constr:(SEC_T_art_zone_below) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_art_zone_below) 5%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_zone_below) 6%nat 0%nat).
Lemma art_zone_below : ltac:(sec_stmt2 constr:(SEC_T_art_zone_below) 7%nat 0%nat).
Proof using Type G LB A M Mr model x.
intros REP KN B0 Z.
pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
assert (SHB : forall y, 0 <= y <= 2 ^ 47 -> HeapIfaceA.S y + 1 < rn_HI rn).
{ intros y Hy. unfold HeapIfaceA.S, HeapIfaceA.SB. assert (y / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. lia. }
destruct Z as [Z | [Z | Z]]; [|lia|lia].
destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]].
- unfold art_zone_statics in Z. lia.
- unfold art_zone_thread in Z. lia.
- lia.
- unfold art_zone_kspace in Z. lia.
- destruct Z as [Z | (p & Hp & Z)]; [lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & _). lia.
- unfold art_zone_depot, dprivD in Z. lia.
- destruct Z as [Z | (p & Hp & Z)].
+ pose proof (SHB (rn_kbase rn + 0x2000011000) ltac:(lia)). lia.
+ destruct (LIVE p Hp) as (L1 & L2 & L3 & _). pose proof (SHB (fst p + snd p) ltac:(lia)). lia.
- lia.
Qed.
End SE.
#[using="Type"] Lemma art_fs_zone3_below : ltac2:(TCodec.tc2 tcn__JatWrapC "Q2'QM'QG%211'7'9'@%2211%411'ROyR0%211'8y8%511%311p051&QKvRLr4r3r2%55D4321&QJ%1263&RA&R4%119%3281p051p081pV6I1pR4@1pQ<I1pQ8O1").
Proof.
intros G LB Mr x REP Z. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. unfold fs_zone3, FS_BYTES in *. lia.
Qed.
#[using="Type"] Lemma art_block_shadow_below : ltac2:(TCodec.tc2 tcn__JatWrapC "Q='7'9'@%2211%411&QA%611'ROyR0%211'8y8%511%311p051&QLvRLr7r6r5r4r3%76654321&R>r8%23F41&QC&6%13JJ8&:%13LL:%5331:&RA+`PQoooPP0%22>1p041p0;1p0?1pV6Q41pU:Q41pQNJ1p2Q51pQ>Q41pQ4Q51pQ<Q81").
Proof.
intros LB FF LK A M b x CLI Hb Hx. pose proof CLI as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _).
unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in Hx. assert ((fst b + snd b - 1) / 8 <= (2 ^ 47 - 8388609) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 47 - 8388609) / 8) with 17592184995839 in *. lia.
Qed.
#[using="Type"] Lemma art_lsan_kept : ltac2:(TCodec.tc2 tcn__JatWrapC "R0'QM'QG%211'7'9'@%2211%411'ROyR0%211'8y8%511%311p051!p0<1&QKvRLr5r4r3%55F4321&?&S0r1%22B1%611%511'=r2%<11r6%113%53E31p071pV6K1%A1<&R@&R4%11F%321;p051pV6Q71&Q;&R=&R?&R6%11N&R5%11Q0%5231u4z%:59Q3321p0<1p0D1p0Q31pQ6Q:1pR6Q=1pR8Q>1pQ<QG1pQ8QM1").
Proof.
intros G LB Mr0 Mr' FP REP FR HIFP. pose proof REP as (ROK & _ & (_ & _ & _ & _ & _ & _ & _ & C) & _). rok_open ROK. geo_open GEO.
apply (JatAllocG.cell_agree Mr0 Mr'); [|lia|cbn; lia|exact C]. intros x Hx. apply FR. intros HF. specialize (HIFP _ HF). cbn in Hx. lia.
Qed.
End Wrap.
