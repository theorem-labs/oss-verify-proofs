(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit PmTxtSpecs PmTxtKit PmTxtKit2 PmSSrd1 PmSRdSpanP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSRdSpan1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSRdSpan1.PMSRS1.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSSrd1.PMSSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1app"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"]; ["4VmMaps"; "5bvmap"; "0M"; "0M'"; "0R"; "0R'"; "0R0"; "6credit"; "6hi_heap"; "6hl_sptop"; "6regs_preserved"; "7hpres"; "7stk"; "9defined"; "9outside"; "9ra_ok"]; ["9range"; "8SCFG"; ":ADDR_S"; ";CHUNK"; ";p_b"; ";p_depth"; ";p_done"; ";p_k"; ";p_more"; ";p_src"; ";p_stk"; ";p_tb"; ";parser_own"; ";pst"; ";pstate"; ";sm_eg"]; [";sm_g"; ";sm_st"; ";sr_rem"; ";strm"; ";unread"; ";vs_size"; "<W0"; "<kept_rs"; "<memrel"; "<saves4"; "<st_ok"; "=fields_eq"; ">cfg"; ">consumed"; ">src_step"; "?base_ok"]; ["@ek"; "@inW"; "AFPState"; "Agetr"; "Bsrealizes"; "Cloaded_segments"; "0S"; "0SCFG_P"; "DIn"; "Eadd"; "Ele"; "Elt"; "Eof_nat"; "Epow"; "Esub"; "0VM"]; ["0W'"; "0X"; "0a"; "0cr"; "0cr'"; "0d"; "0fb"; "0fx"; "0fx'"; "0len"; "0m"; "0model"; "0model'"; "0n"; "0ptr"; "0s"]; ["0s'"; "0s0"; "0scr'"; "0sm"; "0sm'"; "0sm0"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSRS1.
Import PMS.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis FR1 : S <= fb.
Hypothesis FR2 : fb + 752 <= hl_sptop L.
Hypothesis FR3 : fb mod 16 = 0.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis FBS : PMPSS.fill_buffer_spec L HI.
Hypothesis SRDS : PMTXS.srd_read_spec RSEGS AD L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (PMSP.o_tb AD fb + 1 <= ptr /\ ptr + n <= PMSP.o_tb AD fb + 24)) ->
L5.defined M' ptr n ->
PM.parser_at RSEGS AD T3 T4 M' (PMSP.o_p AD fb) (PMSP.o_is AD fb) s' -> PM.iss_at RSEGS AD T3 M' (PMSP.o_is AD fb) str sm' -> PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSP.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5C.hpres L LBX S (PMSP.pm_scr 6) (PMSP.W_srcf AD fb ++ [(PMSP.o_tb AD fb, 24)]) M0 M' ->
PMSP.credit_keep cr0 cr' (PM.pot_text L (PM.p_tb s0) (PM.p_tg s0)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
model_but_vm model0 model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition W0 : list L5.range := PMSP.W_srcf AD fb ++ [(PMSP.o_tb AD fb, 24)].
Definition saves4 (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
/\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition memrel (M : word -> option byte) : Prop :=
PMK.ek L LBX S 24576 W0 M0 M /\ PMK.dk L LBX S 24576 M0 M /\ L5C.stk (hl_sptop L) M S 24576.
Definition st_ok (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) : Prop :=
memrel M /\ saves4 M /\ PM.parser_at RSEGS AD T3 T4 M (fb + 40) (fb + 440) s /\ PM.iss_at RSEGS AD T3 M (fb + 440) str sm
/\ PMST.base_ok RSEGS AD M /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
/\ hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) /\ PMSP.model_ok model /\ model_but_vm model0 model
/\ PMSP.credit_le (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) cr
/\ PMSP.credit_keep cr0 cr (PM.pot_text L (PM.p_tb s0) (PM.p_tg s0)) (PM.pot_text L (PM.p_tb s) (PM.p_tg s)).
Definition bregs (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 32) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 (fb + 376)
/\ getr R (reg 18) = Z_to_bv 64 (fb + 64) /\ kept_rs R.
Lemma inW_W0 : ltac2:(TCodec.tc2 tcn__PmSRdSpan1 "B':&R1&QFr1%3221'6&R:vRFr2%3221&R;&R9+g@%2261%4261%:261p0<1pU6A1").
Proof using All. intros a.
intros (r0 & Hin & Hr). unfold W0, PMSP.W_srcf, PMSP.o_src, PMSP.o_tb, PMSP.o_is, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 : ltac2:(TCodec.tc2 tcn__PmSRdSpan1 ";':&R;r1vR6%3221&N&QFr2%3221p051pU6:1").
Proof using All. intros a. intros Ha r0 Hr0 Hin. assert (I : PMK.inW W0 a) by (exists r0; split; assumption). apply inW_W0 in I. lia. Qed.
Lemma base_keep : ltac2:(TCodec.tc2 tcn__PmSRdSpan1 "Q0'S7yR0%211'3y8%511%311p051&R0v=v>vR6+hP0&QFr2r1%877654321&L&I%11:r3%4421:9&QO&R5&Q2r4%43321p011p071p0=1pQ8G1pQ6H1").
Proof using All. intros M M'.
intros E (_ & SLO & _ & STOP & _) B. apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX S 24576 W0 M M' E); [| | | |exact B].
all: intros a Ha; apply outside_W0; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha; destruct STOP; lia.
Qed.
Lemma unread_nn : ltac2:(TCodec.tc2 tcn__PmSRdSpan1 "QH'S7yR0%211'3y8%511%311p051'?'Q='QC&G&QJr5r4r3r2r1%6554321'6&R:z&QD&Q9%11:%321:%6251'9'7':&QA%11@%4331;+2%63531%8231&QB%11=%B2A1&Q3%D231%F231&Q@%11L&Q?%11N%J231%L261%M2=1%N2G1p0Q01pU8Q81pV8Q:1pV0Q<1pUHQ>1pQ6Q@1").
Proof using All. intros M model s sm cr.
intros (_ & _ & PA & IA & _).
destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.
Lemma finish_rs : ltac2:(TCodec.tc2 tcn__PmSRdSpan1 "UN'R2&Ay5'S7yR0%211%5241'3y8%611%311p061'?'Q='QC&G':'7&R3r8&S6&R<u1%211%42F1%7261&S8vF%:214%32I1%:2J1%>3J61r9u2%=11%?2Q11%B241vR6%B2Q21%F3Q231r:u8%E11%G2Q91%J241%K2B2%D2Q:1%K2Q;1%O3Q;41r;u9%N11%Q02QB1%Q3241%Q42K2%M2QC1%Q42QD1%Q83QD41r<uB%Q711%Q92QK1%Q<241%Q=2Q42%Q62QL1%Q=2QM1%QA3QM41&QGr=%211r>u:%QC11%QE2R71%QH241%QG2R7QH%QK3R721r?u;%QJ11%QL2R>1%QO241%R13R=17'6&R:z%221QFvRI%42QH1%6231&R;&R=+2+J%3221%52QG1'9%R@3RAQ7<%RA3RBQA=%@221'8&R8'5%12RGRG(4r2r1%34RKRK21&Q<rA%211%:3841%L27Q:&R9%12Q<Q>%22:9%Q0221%Q2251%Q3271qUFS71%D2S81q2S91%F2S:1vRF+[H%<221+1%>221%Q<21R6%@2R7R@+H%B261%Q@231%QB251%Q62<1%Q72Q41&MrB%231R6R@&QJrCr@%3525Q11R1&QKvS1%2218&QN&Q9%114%219vS5%54321>'R4&R5&Q1vR7%211&QLrHrG+Vko@rFrE%66:54321v<%=4<921p0?1p0F1p0J1p0O1p0Q31p0R<1p0RC1p0RK1p0S21p0S:1p0S>1p0SH1p0T21p0T<1p0TE1pULU51pUNU61pU8U81pV8U:1pV0U<1pUHU>1pQ6U@1pQ:UF1pU@UM1").
Proof using All. intros fx R M model s sm cr ptr n.
intros E1 E2 E8 E9 E18 KP E10 E11 Hn Hn2 LOC DEF ((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & MOK & MB & _ & CK) (F1 & F2 & F3 & F4 & F5 & F6) STEP.
pose proof MOK as (Mh & Ml & Mm). pose proof RAok as (Hr1 & Hr2).
assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx R M 0x36ff0 (ltac:(oW' 0x36ff0%Z)) r (ltac:(oF' 0x36ff0%Z)) ltac:(reflexivity) (ltac:(oD' 0x36ff0%Z)) RA Hr1 Hr2)|].
apply (KONT fx R M model s sm cr ptr n); try assumption.
- apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|].
apply KP. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn; auto 12.
- unfold PMSP.o_tb, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. replace (fb + 40 + 336) with (fb + 376) by lia. exact LOC.
- apply (PMK.hpres_of L LBX S 24576 W0 M0 M EK); [destruct STK as (_ & _ & _ & _ & D); exact D| exact DK].
Qed.
Lemma src_callee_mem : ltac2:(TCodec.tc2 tcn__PmSRdSpan1 "S7'S7yR0%211'3y8%511%311p051'Q=&G'@':'2&Q0%211&QHr7%211&QIr8%211&Hv;&1'5%12>>&Q<%11;v>%63421r6r9r5%<5;4321'6&R:z%2215&R>+hP0+Q0%3221%72:1%9261&Kv=%D1?%H3F1CvR6%;219r;r:%87753FD21&R1r1%22Q71'9&QFr2%6221'8&R8(4%14QDQD59r>%Q711%53Q931r4%Q12:1&R;&R9%12=A%3251%Q7251%Q8281qUFR01%@2R11q2R21%B2R31%G2D1p0I1pU6R61r<%R411%R212&R0r=%27Q:QKQ7Q@N15%QF241%QG261p091p0Q71p0QA1p0QL1p0R:1p0R>1pU2RB1pV6RF1pU0RH1pU8RJ1pV0RL1pQ8RN1pQ6RO1").
Proof using All. intros M M' s cr VM scr' W'.
intros (EK & DK & STK) SV HH Hs HP FP.
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
set (LBc := PM.parser_own s ++ LBX).
assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
pose proof (PMSSR1.own_apart L HI HIok s LBX cr M VM HH) as OWNF.
assert (OWNLO : forall a B m, In (B, m) (PM.parser_own s) -> B <= a < B + m -> a < S - 24576).
{ intros a B m Hin Ha. destruct (OWNF B m Hin) as (Q & _). lia. }
assert (EKr : PMK.ek L LBc (S - 32) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
assert (STKr : L5C.stk (hl_sptop L) M (S - 32) scr').
{ apply (PMK.stk_call L M S 24576 (S - 32) scr' STK); [lia|lia|lia|]. replace (S - 32) with (S + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (SC0 : 0 <= scr') by lia.
assert (EKn : PMK.ek L LBX S 24576 W0 M M').
{ apply (PMPK.ek_drop_own L (PM.parser_own s) LBX S 24576 W0 (W0 ++ PM.parser_own s) M M').
- apply (PMK.ek_callee_in' RSEGS L KL LBc LBc S 24576 (S - 32) scr' (W0 ++ PM.parser_own s) W' M M' HP (incl_refl _));
[lia|lia|lia| destruct STOP; lia| exact (PMFR.brange_hi L LBc BR)|].
intros a I. right. destruct (FP a I) as [(r0 & Hr0 & Hin)|(B & m & Hin & Ha)].
+ exists r0. split; [apply in_or_app; left; exact Hr0| exact Hin].
+ exists (B, m). split; [apply in_or_app; right; exact Hin| unfold L5.in_rng; cbn [fst snd]; lia].
- exact OWNF.
- intros a O. apply PMSSR1.outside_own. exact O. }
assert (NOTW : forall a n, S - 32 <= a -> a + n <= S -> forall i, a <= i < a + n -> ~ PMK.inW W' i).
{ intros a n H1 H2 i Hi I. destruct (FP i I) as [I'|(B & m & Hin & Ha)]; [apply inW_W0 in I'; lia| apply (OWNLO i B m Hin) in Ha; lia]. }
split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 24576 W0 M0 M M' EK EKn).
- apply (PMK.dk_trans L LBX S 24576 M0 M M' DK).
apply (PMK.dk_callee L LBX LBc S 24576 (S - 32) scr' W' M M' HP); [intros x Hx; apply in_or_app; right; exact Hx| lia| lia].
- apply (PMK.stk_after RSEGS L KL LBc M M' S 24576 (S - 32) scr' W' STK HP); lia.
- split; [|exact EKn].
destruct SV as (S8 & S16 & S24 & S32).
unfold saves4. repeat split; (apply (PMFR.u64_keep RSEGS L KL LBc (S - 32) scr' W' M M' EKr STKr SC0); [lia|lia| apply NOTW; lia| eassumption]).
Qed.
Lemma call_fill (fx : FPState) R M model s sm cr (X : Z) :
getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 32) -> kept_rs R ->
getr R (reg 10) = Z_to_bv 64 (fb + 64) -> getr R (reg 11) = Z_to_bv 64 (PM.sr_qc (PM.p_src s)) -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
st_ok M model s sm cr ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (sm' : PM.strm) (c : Z),
regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
(PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
(PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2) ->
PMSP.src_step (PM.p_src s) (PM.p_src s) sm sm' ->
st_ok M' model s sm' cr ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x36a08 M model) K.
Proof using All.
intros A1 RAX A2 KP A10 A11 A12 SO NEXT.
pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
assert (STKr : L5C.stk (hl_sptop L) M (S - 32) (PMSP.pm_scr 3)).
{ apply (PMK.stk_call L M S 24576 (S - 32) (PMSP.pm_scr 3) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
replace (S - 32) with (S + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
pose proof FBS as SR. unfold PMPSS.fill_buffer_spec, PMPS.fill_buffer_spec, PMPS.src_spec in SR. cbn [pa_fill_buffer AD PmLayoutS.ADDR_S] in SR.
apply (SR fx R M model K LBX cr (S - 32) X fb s str sm [] HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact FR3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. replace (fb + 40 + 24) with (fb + 64) by lia. exact A10. }
{ unfold PMPS.fill_args. rewrite L5K.rl11, L5K.rl12. split; [exact A11| exact A12]. }
{ reflexivity. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S]. exact PA. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutS.ADDR_S]. exact IA. }
{ exact BASE. }
{ exact INCS. }
intros fx' R' M' src' sm' RP PA' IA' STEP RES HP HH'.
unfold PMSP.o_p, PMSP.o_is in PA', IA'. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in PA', IA'.
change (PMSP.pm_scr 3) with 18432 in HP. rewrite app_nil_r in HP.
destruct RES as (-> & c & Y10 & Hc & G & ST0 & ST2).
rewrite PMSSR1.with_src_id in PA'.
apply (NEXT fx' R' M' sm' c RP Y10 Hc G ST0 ST2 STEP).
destruct (src_callee_mem M M' s cr _ 18432 (PMSP.W_src AD fb (PM.p_src s)) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
{ intros a (r0 & Hin & Hr). unfold PMSP.W_src in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
- left. exists r0. split; [unfold W0; apply in_or_app; left; exact Hin| exact Hr].
- right. exists (PM.sr_qc (PM.p_src s)), PM.CHUNK. split; [unfold PM.parser_own, PM.src_own; left; reflexivity| exact Hr]. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TBOK|].
split; [exact HH'|]. split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.
Lemma call_srd : ltac2:(TCodec.tc2 tcn__PmSRdSpan1 "VO'R2&Ay5'S7yR0%211%5241'3y8%611%311p061'?'Q='QC&G':'7&R3r7&S6&R<u1%211%42F1%7261r1%72G1%;3G31&Or2%211r9u2%=11%?2Q11%B241&R>vR6+Q0%3221%E2Q51%I3Q561&QGr:%211r;u:%K11%M2Q?1%Q0241&R9vRF+R0%3221%Q32QC1%Q73QC61r<u;%Q611%Q82QJ1%Q;241+[H%<2;1%Q<2QL1%Q@3QL41r=u<%Q?11%QA2R31%QD241vRI%QD2R41%QH3R431&QJ%159BMOQ;&R;&QD&Q9%11F%321Q2&R=+2+J%3221%9251&QE&Q;%11F%311%<1H%>21Q2%Q9231%A219&JrI%221R=r8%R@21QA%R?2ROR5%RC3RO21'6&R:zr3%3221%422Q3%6221&QM%O1>%Q01RKrHr6%544321r4%S23S321%M1C%O11rJ%Q011%Q211r5%R7221%S:3S;61&Q8%11RMrK%311%S?3S@31&Q6%11RFrL%311%SD3SE31&Q5%11RIrM%311%SI3SJ31&Q4%11RCrN%311%SN3SO31&Q7%11R?rO%311%T33T431'2'Q>%211&Q:r>%211rQ0%411%T<3631&QNrQ1%RB11r?%RD11%54318:rBrAr@%RM53216>'R4&R5&Q1vR7%211&QLrErDrC%46832F1=v<%;4:721p0=1p0B1p0I1p0Q31p0Q91p0Q?1p0QE1p0QK1p0R11p0R:1p0RC1p0RK1p0S01pU<UA1pU:UC1pV:UE1pV2UG1pUJUI1pQ8UK1pQ<V11pUBV81+VnV4%M6Q1JQ61Q5Q4%Q34Q2O1Ip041p0S@1p0SI1p0T41p0T71p0T@1p0TJ1p0U61p0U:1p0UF1p0UJ1pU4V71pU8V91pV8V;1pV0V=1pUHV?1pQ6VA1pQ:VG1pU@VN1").
Proof using All. intros fx R M model s sm cr X.
intros A1 RAX A2 KP A10 A11 A12 SO UN UNS NEXT.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
assert (STKr : L5C.stk (hl_sptop L) M (S - 32) (PMSP.pm_scr 5)).
{ apply (PMK.stk_call L M S 24576 (S - 32) (PMSP.pm_scr 5) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
replace (S - 32) with (S + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
pose proof SRDS as SR. unfold PMTXS.srd_read_spec in SR. cbn [pa_srd_read AD PmLayoutS.ADDR_S] in SR.
apply (SR fx R M model K LBX cr (S - 32) X fb len s str sm HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact FR3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. replace (fb + 40 + 24) with (fb + 64) by lia. exact A10. }
{ rewrite L5K.rl11. unfold PMSP.o_tb, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. replace (fb + 40 + 336) with (fb + 376) by lia. exact A11. }
{ rewrite L5K.rl12. exact A12. }
{ exact Hlen. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S]. exact PA. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutS.ADDR_S]. exact IA. }
{ exact BASE. } { exact TBOK. } { exact INCS. } { exact UN. } { exact UNS. } { exact CRL. }
intros fx' R' M' model' s' sm' cr' d RP Y10 Hd CONS SZ PA' IA' TB' F1 F2 F3 F4 F5 F6 STEP HP CK MB' HH'.
unfold PMSP.o_p, PMSP.o_is in PA', IA'. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in PA', IA'.
change (PMSP.pm_scr 5) with 22528 in HP.
apply (NEXT fx' R' M' model' s' sm' cr' d RP Y10 Hd CONS SZ F1 F2 F3 F4 F5 F6 STEP).
assert (EKr : PMK.ek L LBX (S - 32) 22528 (PMSSR1.W0 fb) M M') by (apply (PMK.ek_of_hpres L); exact HP).
assert (SC0 : 0 <= 22528) by lia.
assert (BR : PMFR.brange L LBX) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); intros x Hx; apply in_or_app; right; exact Hx).
assert (EKn : PMK.ek L LBX S 24576 W0 M M').
{ apply (PMK.ek_callee_in' RSEGS L KL LBX LBX S 24576 (S - 32) 22528 W0 (PMSSR1.W0 fb) M M' HP (incl_refl _));
[lia|lia|lia| destruct STOP; lia| exact (PMFR.brange_hi L LBX BR)|].
intros a I. right. exact I. }
assert (NOTW : forall a n, S - 32 <= a -> a + n <= S -> forall i, a <= i < a + n -> ~ PMK.inW (PMSSR1.W0 fb) i).
{ intros a n H1 H2 i Hi I. apply inW_W0 in I. lia. }
split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 24576 W0 M0 M M' EK EKn).
- apply (PMK.dk_trans L LBX S 24576 M0 M M' DK).
apply (PMK.dk_callee L LBX LBX S 24576 (S - 32) 22528 (PMSSR1.W0 fb) M M' HP); [apply incl_refl| lia| lia].
- apply (PMK.stk_after RSEGS L KL LBX M M' S 24576 (S - 32) 22528 (PMSSR1.W0 fb) STK HP); lia.
- split.
{ destruct SV as (S8 & S16 & S24 & S32).
unfold saves4. repeat split; (apply (PMFR.u64_keep RSEGS L KL LBX (S - 32) 22528 (PMSSR1.W0 fb) M M' EKr ltac:(apply (PMK.stk_call L M S 24576 (S - 32) 22528 STK); [lia|lia|lia| replace (S - 32) with (S + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact A16]) SC0); [lia|lia| apply NOTW; lia| eassumption]). }
split; [exact PA'|]. split; [exact IA'|].
split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TB'|].
split; [exact HH'|]. split; [exact (PMFR.model_ok_but_vm model model' MOK MB')|].
split; [exact (L5C.model_but_vm_trans _ _ _ MB MB')|].
split; [apply (PMPK.credit_le_keep cr cr' _ _ CRL CK)|].
unfold PMSP.credit_keep in *. destruct CRK, CK. split; lia.
Qed.
End Call.
End WithHeap.
End PMSRS1.
