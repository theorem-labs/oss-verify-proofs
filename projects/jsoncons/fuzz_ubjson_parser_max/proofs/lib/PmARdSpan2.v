(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmTxtKit2 PmASrcKit PmAReset1 PmARsKit PmARdSpanP PmARdSpan1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARdSpan2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARdSpan1.PMARSP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw0"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "3Z"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK0"; "4Model"]; ["5bvmap"; "0M"; "0M0"; "0R"; "0R0"; "6credit"; "7fframe"; "8SCFG"; "9bregs"; "9fields_eq"; "9kept_rs"; "9os"; "9st_ok"; "9tb"; ":p_src"; ":p_tb"]; [":pst"; ":sr_rem"; ":srcst"; ":strm"; ":vs_size"; ";cfg"; ";src_step"; "<FPState"; "<getr"; "=srealizes"; ">loaded_segments"; "0S"; "0SCFG_P"; "?add"; "?div"; "?le"]; ["?of_nat"; "?sub"; "0a"; "0ar"; "0b"; "0c"; "0cr"; "0cr0"; "0fb"; "0fx"; "0len"; "0model"; "0model0"; "0s"; "0s0"; "0sa"]; ["0sb"; "0sc"; "0sm"; "0sm0"; "@Z_to_bv"; "@bv"; "0str"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMARSP2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PMARSP1.pot.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PMSPA.ffroomA 6 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PMSPA.frame_okA FF fb.
Hypothesis SA32 : S mod 32 = 0.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 24576) 3072.
Hypothesis FBS : PMA.fill_buffer_spec L ar HI.
Hypothesis SRDS : PMA.srd_read_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (PMSPA.o_tb AD fb + 1 <= ptr /\ ptr + n <= PMSPA.o_tb AD fb + 24)) ->
L5.defined M' ptr n -> PMSPA.accA M' ptr n ->
PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' -> PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm' ->
PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSPA.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) (PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)]) M0 M' ->
PMSPA.credit_keep cr0 cr' (pot L ar s0) (pot L ar s') ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
#[local] Abbreviation op := (PMARSP1.op fb).
#[local] Abbreviation os := (PMARSP1.os fb).
#[local] Abbreviation ois := (PMARSP1.ois fb).
#[local] Abbreviation tb := (PMARSP1.tb fb).
#[local] Abbreviation W0 := (PMARSP1.W0 fb).
#[local] Abbreviation U := (PMARSP1.U R0).
#[local] Abbreviation saves9 := (PMARSP1.saves9 R0 S).
#[local] Abbreviation kept_rs := (PMARSP1.kept_rs R0).
#[local] Abbreviation memrel := (PMARSP1.memrel L ar M0 LBX FF S fb).
#[local] Abbreviation fields_eq := (PMARSP1.fields_eq s0).
#[local] Abbreviation st_ok := (PMARSP1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str).
#[local] Abbreviation bregs := (PMARSP1.bregs R0 S fb len).
#[local] Abbreviation finish_rs := (PMARSP1.finish_rs L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PMARSP1.call_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation vpack := (PMARSP1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation outside_W0 := (PMARSP1.outside_W0 L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 FBS SRDS KONT).
Lemma src_step_trans : ltac2:(TCodec.tc2 tcn__PmARdSpan2 "B'Q2'Q3&Q6r6r5r3r2%544321r8%741654p031p041pT4;1pT2<1pT0=1pS<?1pS:@1pS6A1").
Proof. intros a b c sa sb sc.
unfold PMSPA.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Lemma fast : ltac2:(TCodec.tc2 tcn__PmARdSpan2 "S<'Q7&@y5'R5yR0%211%5241'3y8%611%311p061'?'Q0'Q3&E'2&F%211'4'7%2211%611&HvDvQ;vQHvQJr8%6554321'6&Q8r9&R4&Q@u<%211%42Q31%7261&Q1&Nr6%211%411%;2Q81%?3Q871'5&Q?+1%221Fr7%;11%=11%62J1%8251&Lv;vQCv9vBvQLv<v8v>v1vQGvQNvR6r:r5r4%@F?>=Q?<;:9876Q>Q=543Q7Q;EN21&I%127Q9&Q6%Q319%Q418vR3%44321Q>'Q9&Q:&GvQ<%211&Q5r?r>+fQZ8r=r<%66:54321v:%=4<921p0?1p0E1p0H1p0Q:1p0QD1p0R51p2R=1pLRB1pS>RF1pT6RH1pSLRJ1pSHRL1pQ4RN1pQ8S41pSDS;1").
Proof using All. intros fx R M model s sm cr LK Aw.
intros (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP) A12 Hl SO FE STEP.
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (PMARSP1.geo fb) as (Eop & Eos & Eois & Etb). pose proof (PMARSP1.fbb FF fb FOK) as (F1024 & rs & Hfb).
pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _).
destruct SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & G1 & G2 & G3 & G4 & DC & CC & C240).
set (qc := PM.sr_qc (PM.p_src s)) in *. set (de := PM.sr_de (PM.p_src s)) in *. set (rem := PM.sr_rem (PM.p_src s)) in *.
replace (op + 24) with os in * by lia. unfold PM.CHUNK in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
assert (QIN : In (qc, 16384) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
destruct (WB _ QIN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
set (MV := mrestrict (ahid Aw model) M) in *.
cfeed PP (PMARSPP.arpF_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => rem | 35%nat => de | 36%nat => os | 37%nat => tb | 38%nat => len
| 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
| _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
| |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
| |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E13 & E18 & E19 & E20 & E21 & E22 & E23 & C288 & C280).
unfold PMSPA.cfg.
set (P := fun a => os + 256 <= a < os + 256 + 8 \/ os + 280 <= a < os + 280 + 16).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb0548 R1 0xb066c M1v P K HH AM MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha Wa. unfold P in Wa. split.
- unfold aclientw, aclient_g. right; right; right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia.
- lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
set (s' := PMSPA.with_src s (PM.SRC qc (de + len) (rem - len))).
assert (OWN' : PM.parser_own s' = PM.parser_own s) by reflexivity.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
assert (BK1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 256 \/ os + 264 <= a) -> (a + n <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a n).
{ intros a n Ha Hn X Y i Hi. apply FR1; [lia| unfold P; lia]. }
assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
{ intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
apply FR1; [lia|]. unfold P. destruct OBIG; lia. }
assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= os \/ os + 296 <= q).
{ intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (AGB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> PMFA.agA M M1 q m).
{ intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & VEC & _).
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
destruct (BRB _ VIN) as (VB0 & VB1). cbn [fst snd] in VB0, VB1.
assert (PA1 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s').
{ apply (PMASK.parser_src_fieldsA M M1 op ois s (de + len) (rem - len) PA); [lia| lia| | | | lia| cbv [PM.CHUNK]; lia| | lia| lia| | | exact MGM1| | | | | lia| lia| cbv [PM.CHUNK]; lia].
- split; [apply AGO; lia| apply AGSH; lia].
- split; [apply AGO; lia| apply AGSH; lia].
- apply AGSH; lia.
- exact (AGB _ _ QIN).
- exact (AGB _ _ VIN).
- intros c0 n0 p0 E. apply AGB. apply in_or_app; left. unfold PM.parser_own. rewrite E. right; right; left; reflexivity.
- apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 288) with (os + 264) by lia; exact F264].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 296) with (os + 272) by lia; exact F272].
- replace (op + 304) with (os + 280) by lia. apply BK1; [lia| lia| exact C280].
- replace (op + 312) with (os + 288) by lia. apply BK1; [lia| lia| exact C288]. }
set (Wp := [(os + 256, 8); (os + 280, 16)]).
assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 24576 Wp M M1).
{ apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. unfold P in Pa. destruct Pa as [X|X]; [apply (OWx (os + 256, 8))| apply (OWx (os + 280, 16))]; try (unfold Wp; cbn; auto); unfold L5.in_rng; cbn [fst snd]; lia. }
assert (WAPPp : PMKA.wapp Wp).
{ unfold Wp. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia|].
apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia| apply PMKA.wapp_nil]. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
assert (AOI : PMSPA.aobjA FF ois 272).
{ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
{ apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| | |exact IA].
- intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
- intros c0 n0 p0 E i Hi r0 Hr. assert (Ip : In (p0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia. }
assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
{ apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PMARSP1.W0, PMSPA.W_srcf; left; reflexivity|].
unfold L5.in_rng, P in *; cbn [fst snd] in *. unfold PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_p ADDR_A] in *. lia. }
pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2. unfold FS_BYTES in FF2.
assert (SO1 : st_ok M1 model1 s' sm cr LK Aw).
{ split; [split; [|split]|].
- exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
- apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
- exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
- split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption])|].
split; [exact PA1|]. split; [exact IA1|].
split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
split; [exact TBOK|]. split; [rewrite OWN'; exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK]. }
apply (finish_rs fx1 R1 M1 model1 s' sm cr LK Aw de len); try assumption.
- intros x Hx. rewrite (KS1 x) by (revert x Hx; intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
- lia.
- lia.
- right. left. exists qc, 16384. split; [rewrite OWN'; left; reflexivity| lia].
- intros i Hi. apply MGM1. replace (de + i) with (qc + (de - qc + i)) by lia. apply DC. lia.
- pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC1 & _). destruct SRC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CC1 & _).
change (PM.sr_qc (PM.p_src s')) with qc in CC1. unfold PM.CHUNK in CC1. intros x Hx. apply CC1. lia.
- apply (src_step_trans _ _ _ _ _ _ STEP). unfold s', PMSPA.src_step, PM.unread. cbn [PMSPA.with_src PM.p_src PM.sr_qc PM.sr_rem].
split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia].
Qed.
Lemma at_srd : ltac2:(TCodec.tc2 tcn__PmARdSpan2 "V7'Q7&@y5'R5yR0%211%5241'3y8%611%311p061'?'Q0'Q3&E'2&F%211'4'7%2211%611'6&Q8r8&R4&Q@u1%211%42L1%7261+fQ_@%72M1%;3M31r9u2%:11%<2Q41%?241&QAvQ;+R@%3221%B2Q81%F3Q861r:u8%E11%G2Q?1%J241vQJ%J2Q@1%N3Q@31r;u9%M11%O2QG1%Q2241&MvQH%211%Q42QJ1%Q83QJ51r<uB%Q711%Q92R11%Q<241&K%11:%Q=2R31%QA3R341r=uC%Q@11%QB2R:1%QE241&Q=&Q>+8%22D1+QoooPP0%5221%QJ2R@1%QN3R@81r>uE%QM11%QO2RG1%R2241%R12RG9%R53RG21r?uF%R411%R62RN1%R9241+Y0%E2M1%E21D%G21C%R<2S21%R@3S261&JvDr@%3221rAu:%RC11%RE2S=1%RH241%RJ3S<1Q:rBu;%RI11%RK2SC1%RN241%S03SB1QIrCu<%RO11%S12SI1%S4241%S63SH1R9&Q?+1%221R=&Lv;vQCv9vBvQLv<v8v>v1vQGvQNvR6rD%>F=<;Q6:987654S6RC321GMQ3Q5QBQI&I%125I&Q6&N%118%217vR3%54321O&Q4&OrE%211%411z%T73T:21'Q9&Q:&GvQ<%211&Q5rJrI+fU[4rHrG%66:54321v:%=4<921p0?1p0G1p0N1p0Q11p0QA1p0QE1p0QL1p0R31p0R:1p0R?1p0RK1p0S31p0SA1p0SK1p0T61p0T?1p0TK1p2U81pLU=1pS>UA1pT6UC1pSLUE1pSHUG1pQ4UI1pQ8UO1pSDV61").
Proof using All. intros fx R M model s sm cr LK Aw.
intros A1 A2 A8 A9 A18 A19 A21 A22 KP A10 A11 A12 Hl SO FE STEP SZ0.
pose proof SO as (_ & _ & PA & IA & _).
assert (UN : 0 <= PM.unread (PM.p_src s) sm < 2 ^ 26).
{ pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
pose proof (PMASK.iss_size_ltA M ois str sm IA). destruct STEP as (_ & _ & _ & _ & U1). unfold PM.unread in *. lia. }
apply (call_srd fx R M model s sm cr LK Aw 722416 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 SO ltac:(lia) ltac:(lia)).
intros fx2 R2 M2 model2 LK2 Aw2 s2 sm2 cr2 d RP2 Y10 Hd CONS2 SZ2 G1 G2 G3 G4 G5 G6 STEP2 SO2.
pose proof (vpack M2 model2 s2 sm2 cr2 LK2 Aw2 SO2) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO2 as ((EK2 & DK2 & STK2) & SV2 & PA2 & IA2 & BASE2 & TBOK2 & HH2 & AM2 & MRT2 & ILK2 & IAW2 & CRL2 & CRK2).
pose proof (PMARSP1.geo fb) as (Eop & Eos & Eois & Etb).
assert (UN2 : 0 <= PM.unread (PM.p_src s2) sm2).
{ pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2' & _).
pose proof (PMASK.iss_size_ltA M2 ois str sm2 IA2). unfold PM.unread in *. lia. }
assert (Hd2 : d < 2 ^ 26) by (unfold PMSPA.consumed in CONS2; lia).
assert (FE2 : fields_eq s2) by (destruct FE as (F1 & F2 & F3 & F4 & F5 & F6); unfold PMARSP1.fields_eq; repeat split; congruence).
assert (STEP02 : PMSPA.src_step (PM.p_src s0) (PM.p_src s2) sm0 sm2) by exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
pose proof SV2 as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (op + 336) with tb in VS by lia.
assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (L5SAR.cs_of_preserved R R2 2%nat RP2) by inl; exact A2).
assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (L5SAR.cs_of_preserved R R2 8%nat RP2) by inl; exact A8).
assert (B9 : getr R2 (reg 9) = Z_to_bv 64 tb) by (rewrite (L5SAR.cs_of_preserved R R2 9%nat RP2) by inl; exact A9).
assert (B18 : getr R2 (reg 18) = Z_to_bv 64 os) by (rewrite (L5SAR.cs_of_preserved R R2 18%nat RP2) by inl; exact A18).
assert (B19 : getr R2 (reg 19) = Z_to_bv 64 (tb / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R R2 19%nat RP2) by inl; exact A19).
assert (B21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R R2 21%nat RP2) by inl; exact A21).
assert (B22 : getr R2 (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R R2 22%nat RP2) by inl; exact A22).
assert (KP2 : forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R0 (reg x)).
{ intros x Hx. rewrite (L5SAR.cs_of_preserved R R2 x RP2) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
revert VS SZ2. destruct (PM.p_tb s2) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ2; cbn [PM.vs_size] in SZ2, SZ0.
-
destruct VS as (Hn1 & BY0). pose proof (PMF.even_byte n1) as EV.
cfeed PP (PMARSPP.arpES_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => 2 * n1
| 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
| _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u8_at _ _ tb _ => unfold MV2; vis8 TAV
| |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23).
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 0xb05f0 R3 0xb066c M3v K HH2 AM2 MS3 MG3 FRZ3).
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
assert (SO3 : st_ok M2 model3 s2 sm2 cr2 LK2 Aw2).
{ split; [exact (conj EK2 (conj DK2 STK2))|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|].
split; [first [exact TBOK2| rewrite ETB; exact TBOK2]|]. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]|].
split; [exact ILK2|]. split; [exact IAW2|]. split; [first [exact CRL2| rewrite ETB; exact CRL2]| first [exact CRK2| rewrite ETB; exact CRK2]]. }
replace (2 * n1 / 2) with n1 in E11 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
apply (finish_rs fx3 R3 M2 model3 s2 sm2 cr2 LK2 Aw2 (tb + 1) n1); try assumption.
+ intros x Hx. rewrite (KS3 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx.
+ lia. + lia.
+ right. right. lia.
+ apply (L5.defined_sub M2 tb 24 (tb + 1) n1 VD); lia.
+ intros x Hx. apply VC. lia.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
pose proof (PMF.u8_of_u64 RSEGS M2 tb (c1 + 1) ltac:(lia) W0') as BY0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
pose proof (PMARSPP.arpEL_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => (c1 + 1) mod 256
| 40%nat => n1 | 41%nat => q1
| 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
| _ => 0 end)) as PP.
cbn beta iota in PP.
assert (Hq1 : 0 <= q1 < 2 ^ 64 /\ 0 <= n1 < 2 ^ 64).
{ pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH2 (q1, c1)) as X. cbn [fst snd] in X.
destruct X as (X0 & X1); [apply in_or_app; left; unfold PM.parser_own; rewrite ETB; right; right; left; reflexivity|]. lia. }
L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u8_at _ _ tb _ => unfold MV2; vis8 TAV
| |- L5.u64_at _ _ (tb + _) _ => unfold MV2; vis64 TAV
| |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23).
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 0xb05f0 R3 0xb066c M3v K HH2 AM2 MS3 MG3 FRZ3).
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
assert (SO3 : st_ok M2 model3 s2 sm2 cr2 LK2 Aw2).
{ split; [exact (conj EK2 (conj DK2 STK2))|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|].
split; [first [exact TBOK2| rewrite ETB; exact TBOK2]|]. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]|].
split; [exact ILK2|]. split; [exact IAW2|]. split; [first [exact CRL2| rewrite ETB; exact CRL2]| first [exact CRK2| rewrite ETB; exact CRK2]]. }
apply (finish_rs fx3 R3 M2 model3 s2 sm2 cr2 LK2 Aw2 q1 n1); try assumption.
+ intros x Hx. rewrite (KS3 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx.
+ lia. + lia.
+ right. left. exists q1, c1. split; [unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| lia].
+ apply (L5.defined_sub M2 q1 c1 q1 n1 DQ); lia.
+ intros x Hx. apply CQ. lia.
Qed.
End Call.
End WithHeap.
End PMARSP2.
