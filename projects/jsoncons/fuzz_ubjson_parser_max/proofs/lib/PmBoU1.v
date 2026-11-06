(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmCertKitG PmBaKit PmBoUStmts PmBoUP1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Specif."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoU1.PMBOU1.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmFrame.PMFR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecs.PMPS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1app"; "1bool"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3sumbool"; "4Z"]; ["0HI"; "0K"; "0L"; "0LB0"; "0LBX"; "5Model"; "5VmMaps"; "5event"; "5m_vmmaps"; "6bvmap"; "0M"; "0M'"; "0M0"; "0M2"; "0MKE"; "0OWN"]; ["0R"; "0R'"; "0R0"; "0R1"; "7credit"; "7hi_heap"; "7hl_img_hi"; "7hl_img_lo"; "7hl_sptop"; "7regs_preserved"; "8agree_on"; "8hpres"; "8stk"; ":defined"; ":outside"; ":ra_ok"]; [":range"; "9SCFG"; ";FPB"; ";WP"; ";blk_ok"; ";post_ok"; ";wok"; "<CSK"; "<SCR"; "<kept0"; "<mem_ok"; "<regs_at"; "<saves"; "<world"; "=brange"; ">pa_errcat_obj"]; [">pa_gp"; ">pa_tp"; "?ADDR_U"; "@inv"; "@p_src"; "@p_tb"; "@p_tg"; "@parser_at"; "@parser_own"; "@pot_parser"; "@pst"; "@sr_qc"; "@srcst"; "@strm"; "@tb_ok"; "@unread"]; ["@vs_own"; "Asrc_spec"; "Awith_src"; "BT3"; "BT4"; "BW_run"; "Bcfg"; "Bcredit_keep"; "Bcredit_le"; "Bec_at"; "Bmodel_ok"; "Brun_pre"; "Cmake_ec_spec"; "Dek"; "DinW"; "EFPState"]; ["Egetr"; "Fsrealizes"; "Gmem_grows"; "Hloaded_segments"; "0S"; "0SCFG_P"; "0SPEC"; "Ieqb"; "JIn"; "Jexistsb"; "Jforallb"; "Jincl"; "Kadd"; "Kle"; "Klt"; "Kmodulo"]; ["Kof_nat"; "Kpow"; "Ksub"; "0VM"; "0W'"; "0Wextra"; "0Wx"; "0a"; "0args"; "0cat"; "0cr"; "0cr'"; "0cr0"; "0cr1"; "0e"; "0e'"]; ["0e0"; "0e1"; "0fb"; "0fx"; "0fx'"; "0h"; "0i"; "0k"; "0ks"; "0m"; "0model"; "0model0"; "0n"; "0pc"; "0r"; "0ra"]; ["0res"; "0s"; "0s'"; "0s0"; "0s1"; "0scr'"; "0sm"; "0sm'"; "0sm0"; "0sm1"; "0sp'"; "0src'"; "LZ_to_bv"; "Lbv"; "Lbv_unsigned"; "0str"]; ["0v"; "0w"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMBOU1.
Import PMU.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (cr0 : credit) (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis PRE : PMBOUS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBOUS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBOUS.kept0 R0).
Local Abbreviation regs_at := (PMBOUS.regs_at R0 S fb).
Local Abbreviation saves := (PMBOUS.saves R0 S).
Local Abbreviation mem_ok := (PMBOUS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBOUS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBOUS.SCR.
Lemma HH0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "A&Q5v@&1'8'?%2211&R8vTC%211vD%83521vSLvL&HvT;%211%@5?6541"). Proof. apply PRE. Qed.
Lemma MOK0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "3&RJvT;%211"). Proof. apply PRE. Qed.
Lemma K0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "5vA(5'G%211%411"). Proof. apply PRE. Qed.
Lemma Rra0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "@';'TMyR0%211&S0vQ2&TLy5&S@u1%211%5241%8271vT>%82<1%?3<31"). Proof. destruct PRE as (_ & _ & _ & (X & _) & _). exact X. Qed.
Lemma RA0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "B':&S=zvT>%3221&S>&SA+2+Q?%3221%5271%;271';'?&S?%12<8%4331>%A261"). Proof. destruct PRE as (_ & _ & _ & (_ & X & _) & _). exact X. Qed.
Lemma Rsp0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "@';'TMyR0%211&S0vQ2&TLy5&S@u2%211%5241%8271vS4%82<1%?3<31"). Proof. destruct PRE as (_ & _ & _ & (_ & _ & X & _) & _). exact X. Qed.
Lemma Rgp0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "B';'TMyR0%211&S0vQ2&TLy5&S@u3%211%5241%8271&R0&R2%211%:2>1%A3>51"). Proof. destruct PRE as (_ & _ & _ & (_ & _ & _ & X & _) & _). exact X. Qed.
Lemma Rtp0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "B';'TMyR0%211&S0vQ2&TLy5&S@u4%211%5241%8271&R1&R2%211%:2>1%A3>51"). Proof. destruct PRE as (_ & _ & _ & (_ & _ & _ & _ & X & _) & _). exact X. Qed.
Lemma STK0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "8&Q<&Q8vB%211vLvS4&QH%744321"). Proof. destruct PRE as (_ & _ & _ & (_ & _ & _ & _ & _ & X) & _). exact X. Qed.
Lemma FOK : ltac2:(TCodec.tc2 tcn__PmBoU1 "E':&S=vS4vT2%3221&S<+g@%2241&Q8vB%211%:241';'?&S?+@%22=1z%63521%C281%D2@1"). Proof. destruct PRE as (_ & _ & _ & _ & X & _). exact X. Qed.
Lemma ARGS : ltac2:(TCodec.tc2 tcn__PmBoU1 "Q6':';'TMyR0%211&S0vQ2&TLy5&S@u:%211%5241%8271&S<vT2+Q8%3221%;2?1%B3?61u;%<11%?2>1%B2A1+]@%;2:1%C2G1%J3G41u<%D11%G2F1%J2I1+8%C2B1%K2O1%Q23O41%Q4291%Q52B1").
Proof. destruct PRE as (_ & _ & _ & _ & _ & X & _). exact X. Qed.
Lemma RPRE0 : ltac2:(TCodec.tc2 tcn__PmBoU1 ":&RK&S3&R2vLvT2vTCvTOvTHvT0%9887654321"). Proof. apply PRE. Qed.
Lemma INCS : ltac2:(TCodec.tc2 tcn__PmBoU1 "9&S;'8'?%2211&R@vTO%211vD%83521"). Proof. apply PRE. Qed.
Lemma INV0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "3&R3vTC%211"). Proof. apply PRE. Qed.
Lemma EC0 : ltac2:(TCodec.tc2 tcn__PmBoU1 ":&RI&S3vL&S<vT2+8%3221zvSI%9587321"). Proof. apply PRE. Qed.
Lemma UNR0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "<&S>&R?&R4vTC%211vTH%5221&SA+2+J%3221%;251"). Proof. apply PRE. Qed.
Lemma CRED0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "7&RH&R9vBvTC%3221vSL%6221"). Proof. apply PRE. Qed.
Lemma SBND : ltac2:(TCodec.tc2 tcn__PmBoU1 "Q5':&S=&S<+SoomohPPP0+jP0%3221vS4%6221&Q8vB%211%:251+SoonPPPPP0%<213&SA+2+Q?%3221%A281%C261';'?&S?+@%22B1z%63521&SB+G%?2>1%32D1%M21K%O21J%Q1271%Q22?1%Q32H1%Q42M1").
Proof.
pose proof (L5C.stk_floor _ _ _ _ STK0) as X. pose proof STK0 as (A16 & B & C & D & _). unfold PMBOUS.SCR in *. lia.
Qed.
Definition post_ok (M : word -> option byte) (s' : PM.pst) (sm' : PM.strm) (e' : bool) : Prop :=
(exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M (fb + 8) v (pa_errcat_obj AD) /\ PM.p_more s' = 0 /\ e' = true)
\/ (PMSP.ec_at RSEGS M (fb + 8) 0 cat /\ PM.inv s' /\ PMSP.prog_value s0 s' sm0 sm').
Lemma fin : ltac2:(TCodec.tc2 tcn__PmBoU1 "TE'RO&Iy5'TMyR0%211%5241'6y8%611%311p061'E'R:'R='2&Q4';&S0r7&TL&S@u1%211%42F1%7261&TNvQ2%:214%32I1%:2J1%>3J61r8u2%=11%?2Q11%B241vS4%B2Q21%F3Q231r9u8%E11%G2Q91%J241%K2B2%D2Q:1%K2Q;1%O3Q;41r:u9%N11%Q02QB1%Q3241%Q42K2%M2QC1%Q42QD1%Q83QD41r;uB%Q711%Q92QK1%Q<241%Q=2Q42%Q62QL1%Q=2QM1%QA3QM41r<uC%Q@11%QB2R41%QE241%QF2Q=2%Q?2R51%QF2R61%QJ3R641r=uD%QI11%QK2R=1%QN241%QO2QF2%QH2R>1%QO2R?1%R33R?41r>uE%R211%R42RF1%R7241%R82QO2%R12RG1%R82RH1%R<3RH41&QIr?%22R51&QJvBvLvDvT2%56432R117&QMv@vT;vSLvTCvTOvTHvT0r@%9@>87<6;54321AKQ4Q=QF&QErA%241DNQ7'S1&S3&QAvS5%211&RFrDrC+WQm@rB%5694321<vA%<4;821p0>1p0B1p0M1p0Q41p0Q81p0QB1p0QL1p0R61p0R@1p0RJ1p0S41p0S=1pWHSM1pX0SO1pY@T11pY6T31pXFT51pQFT71pR2T=1pX8TD1").
Proof. intros fx R M model s' sm' e' cr'.
intros E1 E2 E8 E9 E18 E19 E20 E21 KP (EK & DK & STK) (RP & HH & MB & STEP & EE & CK) POST.
pose proof (PMFR.model_ok_but_vm model0 model MOK0 MB) as (Mh & Ml & _). pose proof RA0 as (Hr1 & Hr2).
unfold PMSP.cfg. eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx R M 0x387b0 (ltac:(oW' 0x387b0%Z)) r (ltac:(oF' 0x387b0%Z)) eq_refl (ltac:(oD' 0x387b0%Z))); [rewrite E1, Z_to_bv_bv_unsigned; exact Rra0| lia| exact Hr2]. }
apply (KONT fx R M model s' sm' e' cr').
- apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
destruct Hk as [<-|Hk]; [rewrite E2; symmetry; exact Rsp0|].
destruct Hk as [<-|Hk]; [apply KP; cbn; auto 10|]. destruct Hk as [<-|Hk]; [apply KP; cbn; auto 10|].
destruct Hk as [<-|Hk]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hk as [<-|Hk]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hk as [<-|Hk]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hk as [<-|Hk]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
apply KP. unfold PMBOUS.CSK. cbn. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; auto 10.
- unfold PMSP.run_post. split; [exact RP|]. split; [exact STEP|]. split; [exact EE|].
unfold PMSP.o_ec. cbn [pa_off_ec AD PmLayoutU.ADDR_U]. exact POST.
- change (PMSP.pm_scr 7) with SCR. apply (PMK.hpres_of L LBX S SCR _ M0 M EK); [destruct STK as (_ & _ & _ & _ & D); exact D| exact DK].
- exact CK.
- exact MB.
- exact HH.
Qed.
Definition WP : list L5.range := [(fb + 48, 8); (fb + 400, 24)].
Definition FPB (B m a : Z) : Prop := (S - SCR <= a < S) \/ (fb + 48 <= a < fb + 56) \/ (fb + 400 <= a < fb + 424) \/ (B <= a < B + m).
Definition blk_ok (B m : Z) : Prop :=
m = 0 \/ (4096 <= B /\ B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\ forall B' m', In (B', m') LBX -> B + m <= B' \/ B' + m' <= B).
Lemma FPB_dec : ltac2:(TCodec.tc2 tcn__PmBoU1 "='?'>&QBr3r2r1%43321&<%112%8231pW@:1pXD;1p2<1").
Proof. intros B m a. unfold FPB. repeat apply PMK.or_dec; apply PMK.rng_dec. Qed.
Lemma brx : ltac2:(TCodec.tc2 tcn__PmBoU1 "4&QNvBvD%3221").
Proof. apply (PMFR.brange_of_heap L HI HIok _ LBX cr0 M0 _ HH0). apply incl_appr. apply incl_refl. Qed.
Lemma ek_fp : ltac2:(TCodec.tc2 tcn__PmBoU1 "QG'TMyR0%211'6y8%511%311pZ651'?':&S=zr1%3221&S>&SA+2+R0%3221%5271%;271&<&QBr4r3r2%43321%611';r6&TL%12N7%311r7%113%73M31p091p0A1pX>N1&QD%12@?&RMvBvDvS4&QH&QCr5%7765432C1p091p0<1pXDQ;1p2Q<1pQHQ>1pQFQ?1").
Proof. intros M M' B m.
intros FR BK. pose proof SBND as (X1 & X2 & X3 & X4 & X5). pose proof brx as BR.
apply (PMK.ek_piece L LBX S SCR WP M M' (FPB B m) FR). intros a Ha CA NE OW P.
destruct P as [P|[P|[P|P]]].
- destruct CA as [((b1 & b2) & Hb & Hr)|[[S1 S2]|[IM _]]].
+ destruct (BR b1 b2 Hb) as (_ & _ & Z4). cbn [fst snd] in Hr. unfold hl_ceil in Z4. unfold PMBOUS.SCR in *. lia.
+ exact (S2 P).
+ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in IM. unfold PMBOUS.SCR in *. lia.
- apply (OW (fb + 48, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (OW (fb + 400, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- destruct BK as [Bm|(B0 & B1 & B2 & B3)]; [subst m; lia|].
destruct CA as [((b1 & b2) & Hb & Hr)|[[S1 S2]|[IM _]]].
+ cbn [fst snd] in Hr. destruct (B3 b1 b2 Hb); lia.
+ unfold hl_ceil in *. lia.
+ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in IM, B2. lia.
Qed.
Lemma WP_run : ltac2:(TCodec.tc2 tcn__PmBoU1 "='?&Q>&RE&R2vT2%3221r1%6221&QCr2%9221p041pW@<1").
Proof. intros a.
intros O r0 Hr Hin. unfold WP in Hr. unfold PMSP.W_run, PMSP.W_srcf, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p in O.
cbn [pa_off_p pa_off_is pa_off_ec AD PmLayoutU.ADDR_U app] in O.
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
- apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (O (fb + 40 + 360, 24)); [do 5 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma WP_hi : ltac2:(TCodec.tc2 tcn__PmBoU1 "G'?&RN&QCr1%3221'=&S=vS4r2%3221':&Q7vB%211%8216&S>&Q6%115%32:1%9251%?2;1p0A1pW@F1").
Proof. intros a. intros (r0 & Hr & Hin). pose proof FOK as (F1 & _). left. unfold WP in Hr. destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. Qed.
Lemma keep_step : ltac2:(TCodec.tc2 tcn__PmBoU1 "T7'TMyR0%211'6y8%511%311p051'E'R:'R='2&Q4'?&QMvBv@vT;vDvSLvT2vTCvTOvTHvT0r:r8r7r5r4r3%A@@?>=<;:987654321&QJvLvS4r;%46E3B2@1&S2r<%2214':&S=zr1%3221&S>&SA+2+R0%3221%5271%;271&<&QBr6r2%33M21%511';r?&TL%12QLO%311r@%113%73QK31p091p0@1pX>QG1&QD%12@Q:&Q5&1'8%12QMQM&R8%11Q9%5331QKr>&Hr=%211%;5R25QH41&R7&S3&R2&RC&RD&S<+Q8%22R61+]H%42R81%:89876Q231QG&R>&R5%11@&R6%11B%5231'R<&R4%11H%21Q<%Q>3421&RG&R9%12RLRF%22RMQA%44RJR721rCrB%S2@S1S0RORNRMRLRKRJRIRH21QAQEQ2Q0%RA6S2R@ROR?RM3%R:221p061p0<1p0B1p0I1p0Q51p0QB1p0QE1p0RC1p0RG1p0RM1pXDS@1p2SA1pWFSC1pWNSE1pY>SG1pY6SI1pY4SJ1pXFSL1pQHSN1pQFSO1").
Proof. intros M M' model s s' sm e cr B m.
intros (RP & HH & MB & STEP & EE & CK) (EK & DK & STK) MG FR BK HH' PA' TB' ES CK'.
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
assert (EKP : PMK.ek L LBX S SCR WP M M') by exact (ek_fp M M' B m FR BK).
assert (SC0 : 0 <= SCR) by (unfold PMBOUS.SCR; lia).
assert (NW : forall a n, fb + 424 <= a -> forall i, a <= i < a + n -> ~ PMK.inW WP i).
{ intros a n H1 i Hi (r0 & Hr & Hin). unfold WP in Hr. destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
destruct RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
split; [split; [|split; [exact HH'|split; [exact MB|split; [rewrite ES; exact STEP|split; [exact EE| exact CK']]]]]|].
- unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split; [exact PA'|].
split. { apply (PMFR.iss_keep RSEGS AD L KL LBX S SCR WP M M' EKP STK SC0 brx WP_hi); [lia|lia| |exact INCS| exact IA]. apply NW. lia. }
split. { apply (PMFR.visitor_keep RSEGS AD L KL LBX S SCR WP M M' EKP STK SC0); [lia|lia| |exact VIS]. apply NW. lia. }
split. { apply (PMFR.u64_keep RSEGS L KL LBX S SCR WP M M' EKP STK SC0); [lia|lia| |exact VREF]. apply NW. lia. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX S SCR WP M M' EKP); [| | | | exact BASE].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros (r0 & Hr & Hin); unfold WP in Hr;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha;
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
split; [|exact TB'].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBX S SCR WP M M' EKP); [| | exact ERR].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros (r0 & Hr & Hin); unfold WP in Hr;
cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha;
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
- split; [|split].
+ apply (PMK.ek_trans L LBX S SCR _ M0 M M' EK).
apply (PMK.ek_weaken L LBX LBX S SCR S SCR _ WP M M' EKP); [apply incl_refl| intros x Hx; exact Hx| exact WP_run].
+ apply (PMK.dk_trans L LBX S SCR M0 M M' DK). apply PMK.dk_grows. exact MG.
+ exact (PMK.stk_grows L M M' S SCR MG STK).
Qed.
Lemma own_blk : ltac2:(TCodec.tc2 tcn__PmBoU1 "QH'3'8'?%2211%411&Q4'TMyR0%211'6y8%511%311p051'F&Q5v@&1r6vD%33A21r5r4r3%9584321&S8(7r2%24JJ51r7%53K21':&QD%12;:&S=z%221>&S<%12@?&SB&Q8vB%211+XPPP0%5221%;271%?2:1%@2>1p0B1p0I1pXDQ@1p2QA1pW8Q61pQFQ81pWFQA1pQ8QC1").
Proof. intros LB0 cr M VM B m.
intros HH Hin. assert (HB : In (B, m) (LB0 ++ LBX)) by (apply in_or_app; left; exact Hin).
pose proof (PMFR.brange_of_heap L HI HIok _ _ cr M VM HH (incl_refl _) B m HB) as (Z0 & Z1 & Z4).
split; [right; split; [exact Z0|]; split; [exact Z4|]; split; [exact Z1|]|split; lia].
intros B' m' Hin'. assert (HB' : In (B', m') (LB0 ++ LBX)) by (apply in_or_app; right; exact Hin').
assert (NE : B <> B') by (apply (PMPK.fst_neq_app LB0 LBX B m B' m' (PMPK.heap_nodup L HI HIok _ cr M VM HH) Hin Hin')).
exact (PMPK.blocks_apart_heap L HI HIok _ cr M VM B m B' m' HH HB HB' NE).
Qed.
Local Ltac prep_ctx M W MO :=
let PA := fresh "PA" in let IA := fresh "IA" in let VIS := fresh "VIS" in let VREF := fresh "VREF" in let BASE := fresh "BASE" in
let ERR := fresh "ERR" in let TB := fresh "TB" in let HH := fresh "HH" in let MB := fresh "MB" in let STEP := fresh "STEP" in
let EE := fresh "EE" in let CK := fresh "CK" in let EK := fresh "EK" in let DK := fresh "DK" in let STK := fresh "STK" in
pose proof W as ((PA & IA & VIS & VREF & BASE & ERR & TB) & HH & MB & STEP & EE & CK);
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF; cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF;
pose proof MO as (EK & DK & STK);
let MOK := fresh "MOK" in pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK;
let Mh := fresh "Mh" in let Ml := fresh "Ml" in pose proof MOK as (Mh & Ml & _);
let F1 := fresh "F1" in let F2 := fresh "F2" in let F3 := fresh "F3" in pose proof FOK as (F1 & F2 & F3);
let X1 := fresh "X1" in let X2 := fresh "X2" in let X3 := fresh "X3" in let X4 := fresh "X4" in let X5 := fresh "X5" in
pose proof SBND as (X1 & X2 & X3 & X4 & X5);
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBOUS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU1 "B'TMyR0%211':&S=z&TNr1%2271%5241&S>&SA+2+R0%3221%5271%=271pZ4?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBOUP1.aligned; first [assumption | lia]].
Lemma kept0_of : ltac2:(TCodec.tc2 tcn__PmBoU1 "Q?&Iy5'TMyR0%211%5241'3'4%211&S8r1r2%33521';&S0r4&TL&S@%117%32B1%6251r5%8213%:3C31p0<1pZ6B1'2&S:&S9&S7%11Dr3%43I21qX@J1&QG%83L21(9%H3;21&QIvQ2%221Cp011p051p0B1pXBQ41pR8Q81pR2Q91").
Proof. intros R R1 ks. intros KS C KP k Hk. rewrite (KS k) by (apply (PMBOUS.CSK_in ks C k Hk)). apply KP. exact Hk. Qed.
Lemma tail_z : ltac2:(TCodec.tc2 tcn__PmBoU1 "RG'RO&Iy5'TMyR0%211%5241'6y8%611%311p061'E'R:'R=&Q4'?&QKvQ2vS4vT2r7%544321&QL%13653&QJvBvLvDr8%56432;:1&QMv@vT;vSLvTCvTOvTHvT0r9r6(9r5%<@A;:?9G87654>F321':&S=+1%2215+R0%4271%6231&RI&S3r;&S<+8%22Q41&QO&R2%211%95874D1'S1&QAvS5%211&RFr>r=+WQWDr<%56B4321AvA%;4D821p0=1p0H1p0Q01p0Q>1p0QE1p0QH1pZ2QO1pWLR11pYDR31pY:R51pXFR71pQFR91pR2R?1pX8RF1").
Proof. intros fx R M model s1 sm1 cr1 v.
intros (R2 & R8 & R9 & R18 & R21 & KP) SV MO W Hv ECV.
prep_ctx M W MO.
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
cfeed P (PMBOUP1.uboZ_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 40%nat => bv_unsigned (getr R0 (reg 1)) | 41%nat => bv_unsigned (getr R0 (reg 8)) | 42%nat => bv_unsigned (getr R0 (reg 9))
| 43%nat => bv_unsigned (getr R0 (reg 18)) | 44%nat => bv_unsigned (getr R0 (reg 19)) | 45%nat => bv_unsigned (getr R0 (reg 20))
| 46%nat => bv_unsigned (getr R0 (reg 21)) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & Z8).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s1 ++ LBX) cr1 M model fx fx1 R 0x384f4 R1 0x387b0 M1 (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) K
HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOUS.SCR; lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr1 M _ _ _ HH VIN) as (_ & V0 & V4).
destruct (keep_step M M1 model _ (PMPK.set_more (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) 0) sm1 true cr1 0 0 W MO MG1) as (W1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi|]. intros X. apply N. unfold FPB. right; left. lia. }
{ left; reflexivity. }
{ exact HH1. }
{ apply (PMPK.parser_more_upd RSEGS AD M M1 (fb + 40) (fb + 440) _ 0 PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG; lia.
- apply AG; lia.
- apply PMPK.dkr_grows. exact MG1.
- exact Z8.
- left. reflexivity.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- clear - V4 X3. unfold hl_ceil in *. lia.
- apply AG; [lia|clear - V4 X3; unfold hl_ceil in *; lia| clear - V4 X5 F1; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
{ exact TB. }
{ reflexivity. }
{ exact CK. }
apply (fin fx1 R1 M1 model (PMPK.set_more (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) 0) sm1 true cr1); try assumption.
- apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- left. exists v. split; [exact Hv|]. split; [|split; reflexivity].
apply (PMBK.ec_agree RSEGS M M1); [apply AG; lia|lia|lia| exact ECV].
Qed.
Definition wok (OWN : list (Z * Z)) (W' : list L5.range) : Prop :=
forall a, PMK.inW W' a -> PMK.inW (PMSP.W_run AD fb) a \/ (exists B m, In (B, m) OWN /\ B <= a < B + m) \/ (S - 26624 <= a < S).
Lemma call_keep : ltac2:(TCodec.tc2 tcn__PmBoU1 "R4'3'8'?%2211%411&Q4'TMyR0%211'6y8%511%311p051'F&Q@%@11&Q5v@&1r8vD%33C21r7r6r4%9584321&QJvBvLvS4vT2%5643;219&Q;r:%@3Q01>r5r3%57:32=1B?&S=&SB+jP0%22<1%32C7%5221%62F?z%821H&QFr>%221Kr<%I6HGOFE1p031p071p0:1p0<1p0C1p0J1p0Q11pW:Q<1pY<QK1pYFQL1pW8QA1pQLQC1pQFQD1pWFQM1pR0QO1").
Proof. intros OWN cr M M2 VM sp' scr' W'.
intros HH (EK & DK & STK) HP H1 H2 H3 WK. pose proof SBND as (X1 & X2 & X3 & X4 & X5).
split; [|split].
- apply (PMK.ek_trans L LBX S SCR _ M0 M M2 EK). intros a (Ha & CA & NE & OW).
apply (L5C.hpres_kept L _ sp' scr' W' M M2 a HP). split; [exact Ha|]. split; [|split; [exact NE|]].
+ apply (PMK.client_mono L LBX _ S SCR sp' scr' a CA); [apply incl_appr; apply incl_refl| intros x Hx; unfold PMBOUS.SCR; lia].
+ intros r0 Hr Hin. destruct (WK a (ex_intro _ r0 (conj Hr Hin))) as [I|[(B & m & HB & HBa)|I]].
* exact (PMK.inW_not_outside _ a I OW).
* destruct (own_blk OWN cr M VM B m HH HB) as ([Bm|(B0 & B1 & B2 & B3)] & _ & _); [subst m; lia|].
destruct CA as [((b1 & b2) & Hb & Hrb)|[[S1 S2]|[IM _]]].
-- cbn [fst snd] in Hrb. destruct (B3 b1 b2 Hb); lia.
-- unfold hl_ceil in *. lia.
-- rewrite (ly_img_lo L LY), (ly_img_hi L LY) in IM, B2. lia.
* destruct CA as [((b1 & b2) & Hb & Hrb)|[[S1 S2]|[IM _]]].
-- pose proof brx as BR. destruct (BR b1 b2 Hb) as (_ & _ & Z4). cbn [fst snd] in Hrb. unfold hl_ceil in Z4. lia.
-- apply S2. unfold PMBOUS.SCR. lia.
-- rewrite (ly_img_lo L LY), (ly_img_hi L LY) in IM. lia.
- apply (PMK.dk_trans L LBX S SCR M0 M M2 DK). apply (PMK.dk_callee L LBX _ S SCR sp' scr' W' M M2 HP); [apply incl_appr; apply incl_refl|unfold PMBOUS.SCR; lia|lia].
- apply (PMK.stk_after RSEGS L KL _ M M2 S SCR sp' scr' W' STK HP); unfold PMBOUS.SCR; lia.
Qed.
Lemma errp : ltac2:(TCodec.tc2 tcn__PmBoU1 "SE&RLvS5vBv@%43321'RO&Iy5'TMyR0%211%5241'6y8%611%311p061'E'R:'R='2&Q4'?';&S0r8&TL&S@u1%211%42G1%7261+WQWD%72H1%;3H31&QKvQ2vS4vT2r9%544321r:u:%@11%B2Q51%E241&S<+8%22:1%G2Q81%K3Q851r;u;%J11%L2Q?1%O241r4%O2Q@1%Q33Q@31&QL%13HG9&QJvLvDr<%46QO32LK1&QMvT;vSLvTCvTOvTHvT0r=%8@R8R77;6Q454321:GQ1Q3QA':&S=+1%221QE+R0%42QG1%6231&Q=r?+@%332Q51'S1&S3&QA%11RH&RFrBrA+VlU<r@%5684321<vA%;4:821p0=1p0B1p0J1p0Q41p0Q:1p0Q=1p0QF1p0R11p0R81pZ2RE1pWLRG1pX4RI1pYDRK1pY:RM1pXFRO1pQFS11pR2S71pX8S>1pQNS@1").
Proof. intros MKE fx R M model s1 sm1 e1 cr1 v.
intros X1r (R2 & R8 & R9 & R18 & R21 & KP) X10 X11 SV MO W Hv ED.
prep_ctx M W MO.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (STKc : L5C.stk (hl_sptop L) M (S - 112) 14336).
{ apply (PMK.stk_call L M S SCR (S - 112) 14336 STK); unfold PMBOUS.SCR; [lia|lia|lia|]. replace (S - 112) with (S + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact X4. }
unfold PMU.make_ec_spec, PMSP.make_ec_spec in MKE. cbn [pa_make_ec AD PmLayoutU.ADDR_U] in MKE.
apply (MKE fx R M model K LB1 cr1 (fb + 8) v (S - 112) 0x384f4 e1 HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1r|]. split; [split; [lia| reflexivity]|]. split; [exact R2|].
split; [rewrite (KP 3%nat) by PMK.inl; exact Rgp0|]. split; [rewrite (KP 4%nat) by PMK.inl; exact Rtp0|]. exact STKc. }
{ rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hv. } { lia. } { lia. }
{ replace (fb + 8) with (fb + 8 * 1) by lia. apply PMPK.m8_add. apply PMPK.m16_8. exact F3. }
{ exact ED. } { exact BASE. } { exact ERR. }
intros fx2 R2' M2 RP2 EC2 ERR2 HP2 HH2.
change (PMSP.pm_scr 1) with 14336 in HP2.
set (WE := (fb + 8, 16) :: (if e1 then [] else PMSP.err_W AD)) in HP2.
assert (WCE : forall a, PMK.inW WE a -> (fb + 8 <= a < fb + 24) \/ (0xc72b0 <= a < 0xc72b2) \/ (0xe8cf8 <= a < 0xe8f18)).
{ intros a (r0 & Hin & Hr). unfold WE in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|]. destruct e1; [destruct Hin|].
unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; right; [left|right]; lia. }
assert (WHIE : forall a, PMK.inW WE a -> (S - 112) <= a \/ hl_img_lo L <= a < hl_img_hi L).
{ intros a I. apply WCE in I. rewrite (ly_img_lo L LY), (ly_img_hi L LY). destruct I as [I|[I|I]]; [left; lia| right; lia| right; lia]. }
assert (EKc : PMK.ek L LB1 (S - 112) 14336 WE M M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 14336) by lia.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M _ HH); apply incl_refl).
assert (MO2 : mem_ok M2).
{ apply (call_keep _ cr1 M M2 _ (S - 112) 14336 WE HH MO HP2); [lia|lia|lia|].
intros a I. pose proof (WCE a I) as J. left. unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app].
destruct J as [J|[J|J]]; [do 6 apply PMK.inW_next; apply PMK.inW_here; lia| do 7 apply PMK.inW_next; apply PMK.inW_here; lia| do 8 apply PMK.inW_next; apply PMK.inW_here; lia]. }
assert (AGH : forall a n, S - 112 <= a -> a + n <= fb + 8 -> L5C.agree_on M M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 112) 14336 WE M M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I X1 X3 F1 F2. lia. }
assert (AGH' : forall a n, fb + 24 <= a -> a + n <= fb + 752 -> L5C.agree_on M M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 112) 14336 WE M M2 EKc STKc SCc a n); [lia|lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I F1 F2 X1 X3. lia. }
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
assert (QIN1 : In (PM.sr_qc src1, 16384) LB1) by (unfold LB1, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN1 : In (vb1, 32 * 2 ^ vk1) LB1) by (unfold LB1, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR1 _ _ VIN1) as (W0 & W1' & W4). unfold hl_ceil in W4.
assert (VI1 : forall a, vb1 <= a < vb1 + 32 * 2 ^ vk1 -> ~ (65536 <= a < 958464)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'. intros a Ha. clear - Ha W1'. lia. }
assert (PA2 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M2 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M2 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGH'; lia.
- apply (PMPK.dkr_hpres_blk RSEGS L KL LB1 (S - 112) 14336 WE M M2 (PM.sr_qc src1) 16384 HP2 QIN1 BR1). lia.
- lia.
- clear - W4 X3. lia.
- apply (PMPK.ag_blk RSEGS L KL LB1 (S - 112) 14336 WE M M2 EKc STKc BR1 vb1 (32 * 2 ^ vk1) VIN1).
intros i Hi I. apply WCE in I. destruct I as [I|I]; [clear - Hi I W4 X5 F1; lia| apply (VI1 i Hi); clear - I; lia].
- intros c0 n0 q0 E0. apply (PMPK.dkr_hpres_blk RSEGS L KL LB1 (S - 112) 14336 WE M M2 q0 c0 HP2); [|exact BR1|lia].
unfold LB1, PM.parser_own, PM.vs_own. cbn [PM.p_tb]. rewrite E0. cbn. right. right. left. reflexivity. }
assert (SINC1 : incl (PM.vs_own str) LB1) by (unfold LB1; apply incl_appr; exact INCS).
apply (tail_z fx2 R2' M2 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm1 cr1 v).
- split; [rewrite (PMK.cs_of_preserved R R2' 2 RP2) by PMK.inl; exact R2|].
split; [rewrite (PMK.cs_of_preserved R R2' 8 RP2) by PMK.inl; exact R8|].
split; [rewrite (PMK.cs_of_preserved R R2' 9 RP2) by PMK.inl; exact R9|].
split; [rewrite (PMK.cs_of_preserved R R2' 18 RP2) by PMK.inl; exact R18|].
split; [rewrite (PMK.cs_of_preserved R R2' 21 RP2) by PMK.inl; exact R21|].
intros k Hk. rewrite (PMK.cs_of_preserved R R2' k RP2); [apply KP; exact Hk|]. unfold PMBOUS.CSK in Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [PMK.inl|]). destruct Hk.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia|assumption]).
- exact MO2.
- split; [|split; [exact HH2|split; [exact MB|split; [exact STEP|split; [intros _; reflexivity| exact CK]]]]].
unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split; [exact PA2|].
split. { apply (PMFR.iss_keep RSEGS AD L KL LB1 (S - 112) 14336 WE M M2 EKc STKc SCc BR1 WHIE); [lia|lia| |exact SINC1| exact IA].
intros i Hi I. apply WCE in I. clear - Hi I F1 F2 X1 X3. lia. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH'; lia|lia|lia| exact VIS]. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH'; lia|lia|lia| exact VREF]. }
split; [|split; [exact ERR2| exact TB]].
apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 (S - 112) 14336 WE M M2 EKc); [| | | | exact BASE].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCE in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha.
all: clear - I Ha X1 X3 F1; lia.
- exact Hv.
- exact EC2.
Qed.
Lemma tail_z0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "T0'RO&Iy5'TMyR0%211%5241'6y8%611%311p061'E'R:'R=&Q4'?';&S0r7&TL&S@u2%211%42F1%7261&SBvS4+S@%3221%:2J1%>3J61r8u8%=11%?2Q11%B241&S<vT2+Q8%3221%E2Q51%I3Q561r9u9%H11%J2Q<1%M241+8%<2;1%N2Q>1%Q23Q>41r:uB%Q111%Q32QE1%Q6241+]@%E2D1%Q72QG1%Q;3QG41&QIvQ2r;%3221&QL%134Q73&QJvBvLvDr<%56432Q=Q21&QMv@vT;vSLvTCvTOvTHvT0r=(9%:@?98=7Q=65432<DO1Q8':&S=+1%221Q<+R0%42Q>1%6231&RI&S3r?&QO&R2%211%6554Q@Q=1'S1&QAvS5%211&RFrBrA+WQWDr@%56?4321>vA%;4A821p0=1p0E1p0M1p0Q91p0Q@1p0QC1p0QH1p0R21p0R<1p0RH1pZ2S81pWLS:1pYDS<1pY:S>1pXFS@1pQFSB1pR2SH1pX8SO1").
Proof. intros fx R M model s1 sm1 cr1 v.
intros R2 R8 R9 R18 KP SV MO W Hv ECV.
prep_ctx M W MO.
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
cfeed P (PMBOUP1.uboZ_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 40%nat => bv_unsigned (getr R0 (reg 1)) | 41%nat => bv_unsigned (getr R0 (reg 8)) | 42%nat => bv_unsigned (getr R0 (reg 9))
| 43%nat => bv_unsigned (getr R0 (reg 18)) | 44%nat => bv_unsigned (getr R0 (reg 19)) | 45%nat => bv_unsigned (getr R0 (reg 20))
| 46%nat => bv_unsigned (getr R0 (reg 21)) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & Z8).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s1 ++ LBX) cr1 M model fx fx1 R 0x384f4 R1 0x387b0 M1 (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) K
HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOUS.SCR; lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr1 M _ _ _ HH VIN) as (_ & V0 & V4).
destruct (keep_step M M1 model _ (PMPK.set_more (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) 0) sm1 true cr1 0 0 W MO MG1) as (W1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi|]. intros X. apply N. unfold FPB. right; left. lia. }
{ left; reflexivity. }
{ exact HH1. }
{ apply (PMPK.parser_more_upd RSEGS AD M M1 (fb + 40) (fb + 440) _ 0 PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG; lia.
- apply AG; lia.
- apply PMPK.dkr_grows. exact MG1.
- exact Z8.
- left. reflexivity.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- clear - V4 X3. unfold hl_ceil in *. lia.
- apply AG; [lia|clear - V4 X3; unfold hl_ceil in *; lia| clear - V4 X5 F1; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
{ exact TB. }
{ reflexivity. }
{ exact CK. }
apply (fin fx1 R1 M1 model (PMPK.set_more (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) 0) sm1 true cr1); try assumption.
- apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- left. exists v. split; [exact Hv|]. split; [|split; reflexivity].
apply (PMBK.ec_agree RSEGS M M1); [apply AG; lia|lia|lia| exact ECV].
Qed.
Lemma errp0 : ltac2:(TCodec.tc2 tcn__PmBoU1 "TJ&RLvS5vBv@%43321'RO&Iy5'TMyR0%211%5241'6y8%611%311p061'E'R:'R='2&Q4'?';&S0r8&TL&S@u1%211%42G1%7261+WQWD%72H1%;3H31r9u2%:11%<2O1%?241&SBvS4+S@%3221%B2Q31%F3Q361r:u8%E11%G2Q:1%J241&S<vT2+Q8%3221%M2Q>1%Q13Q>61r;u9%Q011%Q22QE1%Q5241+8%<2;1%Q62QG1%Q:3QG41r<uB%Q911%Q;2QN1%Q>241+]@%E2D1%Q?2R01%QC3R041&QIvQ2r=%3221r>u:%QF11%QH2R;1%QK241%QM3R:1Dr?u;%QL11%QN2RA1%R1241%R02RAR1%R43RA21&QL%13AQD8&QJvLvDr@%46S032QIQ>1&QMvT;vSLvTCvTOvTHvT0rA%8@S9S87;6QG54321:FLNQ9':&S=+1%221Q=+R0%42Q?1%6231&Q=rC+@%332QG1'S1&S3&QA%11SI&RFrFrE+VlU<rD%5684321<vA%;4:821p0=1p0B1p0J1p0Q41p0Q:1p0Q=1p0QE1p0QL1p0R11p0R;1p0RE1p0S11p0S=1pZ2SJ1pWLSL1pX4SN1pYDT01pY:T21pXFT41pQFT61pR2T<1pX8TC1pQNTE1").
Proof. intros MKE fx R M model s1 sm1 e1 cr1 v.
intros X1r R2 R8 R9 R18 KP X10 X11 SV MO W Hv ED.
prep_ctx M W MO.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (STKc : L5C.stk (hl_sptop L) M (S - 112) 14336).
{ apply (PMK.stk_call L M S SCR (S - 112) 14336 STK); unfold PMBOUS.SCR; [lia|lia|lia|]. replace (S - 112) with (S + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact X4. }
unfold PMU.make_ec_spec, PMSP.make_ec_spec in MKE. cbn [pa_make_ec AD PmLayoutU.ADDR_U] in MKE.
apply (MKE fx R M model K LB1 cr1 (fb + 8) v (S - 112) 0x384f4 e1 HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1r|]. split; [split; [lia| reflexivity]|]. split; [exact R2|].
split; [rewrite (KP 3%nat) by PMK.inl; exact Rgp0|]. split; [rewrite (KP 4%nat) by PMK.inl; exact Rtp0|]. exact STKc. }
{ rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hv. } { lia. } { lia. }
{ replace (fb + 8) with (fb + 8 * 1) by lia. apply PMPK.m8_add. apply PMPK.m16_8. exact F3. }
{ exact ED. } { exact BASE. } { exact ERR. }
intros fx2 R2' M2 RP2 EC2 ERR2 HP2 HH2.
change (PMSP.pm_scr 1) with 14336 in HP2.
set (WE := (fb + 8, 16) :: (if e1 then [] else PMSP.err_W AD)) in HP2.
assert (WCE : forall a, PMK.inW WE a -> (fb + 8 <= a < fb + 24) \/ (0xc72b0 <= a < 0xc72b2) \/ (0xe8cf8 <= a < 0xe8f18)).
{ intros a (r0 & Hin & Hr). unfold WE in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|]. destruct e1; [destruct Hin|].
unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; right; [left|right]; lia. }
assert (WHIE : forall a, PMK.inW WE a -> (S - 112) <= a \/ hl_img_lo L <= a < hl_img_hi L).
{ intros a I. apply WCE in I. rewrite (ly_img_lo L LY), (ly_img_hi L LY). destruct I as [I|[I|I]]; [left; lia| right; lia| right; lia]. }
assert (EKc : PMK.ek L LB1 (S - 112) 14336 WE M M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 14336) by lia.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M _ HH); apply incl_refl).
assert (MO2 : mem_ok M2).
{ apply (call_keep _ cr1 M M2 _ (S - 112) 14336 WE HH MO HP2); [lia|lia|lia|].
intros a I. pose proof (WCE a I) as J. left. unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app].
destruct J as [J|[J|J]]; [do 6 apply PMK.inW_next; apply PMK.inW_here; lia| do 7 apply PMK.inW_next; apply PMK.inW_here; lia| do 8 apply PMK.inW_next; apply PMK.inW_here; lia]. }
assert (AGH : forall a n, S - 112 <= a -> a + n <= fb + 8 -> L5C.agree_on M M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 112) 14336 WE M M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I X1 X3 F1 F2. lia. }
assert (AGH' : forall a n, fb + 24 <= a -> a + n <= fb + 752 -> L5C.agree_on M M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 112) 14336 WE M M2 EKc STKc SCc a n); [lia|lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I F1 F2 X1 X3. lia. }
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
assert (QIN1 : In (PM.sr_qc src1, 16384) LB1) by (unfold LB1, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN1 : In (vb1, 32 * 2 ^ vk1) LB1) by (unfold LB1, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR1 _ _ VIN1) as (W0 & W1' & W4). unfold hl_ceil in W4.
assert (VI1 : forall a, vb1 <= a < vb1 + 32 * 2 ^ vk1 -> ~ (65536 <= a < 958464)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'. intros a Ha. clear - Ha W1'. lia. }
assert (PA2 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M2 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M2 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGH'; lia.
- apply (PMPK.dkr_hpres_blk RSEGS L KL LB1 (S - 112) 14336 WE M M2 (PM.sr_qc src1) 16384 HP2 QIN1 BR1). lia.
- lia.
- clear - W4 X3. lia.
- apply (PMPK.ag_blk RSEGS L KL LB1 (S - 112) 14336 WE M M2 EKc STKc BR1 vb1 (32 * 2 ^ vk1) VIN1).
intros i Hi I. apply WCE in I. destruct I as [I|I]; [clear - Hi I W4 X5 F1; lia| apply (VI1 i Hi); clear - I; lia].
- intros c0 n0 q0 E0. apply (PMPK.dkr_hpres_blk RSEGS L KL LB1 (S - 112) 14336 WE M M2 q0 c0 HP2); [|exact BR1|lia].
unfold LB1, PM.parser_own, PM.vs_own. cbn [PM.p_tb]. rewrite E0. cbn. right. right. left. reflexivity. }
assert (SINC1 : incl (PM.vs_own str) LB1) by (unfold LB1; apply incl_appr; exact INCS).
apply (tail_z0 fx2 R2' M2 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm1 cr1 v).
- rewrite (PMK.cs_of_preserved R R2' 2 RP2) by PMK.inl; exact R2.
- rewrite (PMK.cs_of_preserved R R2' 8 RP2) by PMK.inl; exact R8.
- rewrite (PMK.cs_of_preserved R R2' 9 RP2) by PMK.inl; exact R9.
- rewrite (PMK.cs_of_preserved R R2' 18 RP2) by PMK.inl; exact R18.
- intros k Hk. rewrite (PMK.cs_of_preserved R R2' k RP2); [apply KP; exact Hk|]. unfold PMBOUS.CSK in Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [PMK.inl|]). destruct Hk.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia|assumption]).
- exact MO2.
- split; [|split; [exact HH2|split; [exact MB|split; [exact STEP|split; [intros _; reflexivity| exact CK]]]]].
unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split; [exact PA2|].
split. { apply (PMFR.iss_keep RSEGS AD L KL LB1 (S - 112) 14336 WE M M2 EKc STKc SCc BR1 WHIE); [lia|lia| |exact SINC1| exact IA].
intros i Hi I. apply WCE in I. clear - Hi I F1 F2 X1 X3. lia. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH'; lia|lia|lia| exact VIS]. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH'; lia|lia|lia| exact VREF]. }
split; [|split; [exact ERR2| exact TB]].
apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 (S - 112) 14336 WE M M2 EKc); [| | | | exact BASE].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCE in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha.
all: clear - I Ha X1 X3 F1; lia.
- exact Hv.
- exact EC2.
Qed.
Lemma own_with_src : ltac2:(TCodec.tc2 tcn__PmBoU1 "J'R:'R<';'?&R;r1%211&R4r2%211%611%93851'3'8%12;;%311&R8&RBr3%221;%411%513%D3721p0<1pYHG1pY:I1").
Proof. intros s1 src'. intros E. unfold PM.parser_own, PMPS.with_src, PM.src_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E. reflexivity. Qed.
Lemma src_call : ltac2:(TCodec.tc2 tcn__PmBoU1 "VD'?&Iy5'TMyR0%211%5241'6y8%611%311p061'R:!p021p0?1p0@1p061p0<1'3&Q@%211p019p0A1'R<'R=p01=p021p041p051p0C1p0I1p0J1&RAvS5&S3&R2vBv@r5r4r3r2r1%;::987654321'RO'E'2&Q4';&S0r9&TL&S@u1%211%42QF1%7261%62QF@%:3QF21&Q?%11D&QKvQ2vS4vT2r;%544321r<u:%A11%C2R51%F241&S<+R0%22:1%H2R81%L3R851':&S=zrC%3221+6%5231%7231r>r=&SB+S@%22J1%:5541JIr?r7%=221&RN%12Q=QE%B27QG&S>%;2Q3I%22QJ1%G241p061pW@S71&QLr@%23Q;Q:1&QJvLvDrA%46R:32Q?Q>1&QMvT;vSLvTCvTOvTHvT0rB%8@RCRB7;6QG54321:?LQ2Q1&Q9rI%221RCrMrJ&R4rG%211rF%675RKRJ2RI1RH%K3R4R3RLr6%J6S0IHR5R41rK&RB%12;4rH%J@S5S4IMHR9GFEDQ=42S31;%R22S2S1+Z0%R42R<1%QO231%R02S8S4%R72S9S8%Q?2S61%R4231&<rL%QF21S;%311p051pX>TH1&Q:rQ2%241R4SDSCp041p0?1p0QM1pXJTO1pW@U01'S1&QA%11T1&RFr:%26T3S41MSCQ:vA%74T5521p091p0Q01p0Q61p0Q91p0Q;1p0QC1pY@TF1pYHTH1pQHU61pR4U<1pX:T61rErD%B6TCQE2Q21S5%F4TDD1@p051p0R11p0R;1p0RA1p0RE1p0RO1p0S31p0S:1p0SC1p0SN1p0T51p0T81pW<U?1pY0V51pWLTF1pX4TH1pYDU?1pY:UM1pXFTL1pQFV01pR2V61pX8U01pV>U21pY2U?1pW>UI1pWBUO1pX<VB1pXLVC1").
Proof. intros pc h args Wx res SPEC fx R M model s1 sm1 e1 cr1 ra Wextra.
intros X1r RAra (R2 & R8 & R9 & R18 & R21 & KP) X10 Hh ARG WX WXin SV MO W KNT.
prep_ctx M W MO.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (Hscr : 0 <= PMSP.pm_scr h <= 24576) by (unfold PMSP.pm_scr; lia).
assert (STKc : L5C.stk (hl_sptop L) M (S - 112) (PMSP.pm_scr h)).
{ apply (PMK.stk_call L M S SCR (S - 112) (PMSP.pm_scr h) STK); unfold PMBOUS.SCR; [lia|lia|lia|]. replace (S - 112) with (S + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact X4. }
unfold PMPS.src_spec in SPEC.
apply (SPEC fx R M model K LBX cr1 (S - 112) ra fb s1 str sm1 Wextra HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1r|]. split; [exact RAra|]. split; [exact R2|].
split; [rewrite (KP 3%nat) by PMK.inl; exact Rgp0|]. split; [rewrite (KP 4%nat) by PMK.inl; exact Rtp0|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutU.ADDR_U]. replace (fb + 40 + 24) with (fb + 64) by lia. exact X10. }
{ exact ARG. } { exact WX. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U]. exact PA. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutU.ADDR_U]. exact IA. }
{ exact BASE. } { exact INCS. }
intros fx2 R2' M2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 HH2.
unfold PMSP.o_p, PMSP.o_is in PA2, IA2. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in PA2, IA2.
set (WS := PMSP.W_src AD fb (PM.p_src s1) ++ Wextra) in HP2.
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596)
\/ (PM.sr_qc (PM.p_src s1) <= a < PM.sr_qc (PM.p_src s1) + 16384) \/ (S - 112 <= a < S - 64)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_src, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|Hin]]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr.
- left. lia. - right; left. lia. - right; right; left. lia. - right; right; right; left. lia.
- right; right; right; right. apply WXin. exists r0. split; [exact Hin| exact Hr]. }
assert (QIN : In (PM.sr_qc (PM.p_src s1), 16384) (PM.parser_own s1)) by (unfold PM.parser_own, PM.src_own; cbn; left; reflexivity).
destruct (own_blk _ cr1 M _ _ _ HH QIN) as (QB & Q0 & Q4). destruct QB as [QB|(_ & _ & QB2 & _)]; [discriminate QB|].
rewrite (ly_img_lo L LY), (ly_img_hi L LY) in QB2.
assert (MO2 : mem_ok M2).
{ apply (call_keep _ cr1 M M2 _ (S - 112) (PMSP.pm_scr h) WS HH MO HP2); [lia|lia|lia|].
intros a I. pose proof (WCs a I) as J.
destruct J as [J|[J|[J|[J|J]]]]; [left| left| left| right; left; exists (PM.sr_qc (PM.p_src s1)), 16384; split; [exact QIN| exact J]| right; right; lia].
all: unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p;
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app].
- apply PMK.inW_next. apply PMK.inW_here. lia.
- do 2 apply PMK.inW_next. apply PMK.inW_here. lia.
- do 3 apply PMK.inW_next. apply PMK.inW_here. lia. }
assert (EKc : PMK.ek L LB1 (S - 112) (PMSP.pm_scr h) WS M M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= PMSP.pm_scr h) by lia.
assert (AGH : forall a n, S - 112 <= a -> a + n <= fb + 320 -> (forall i, a <= i < a + n -> ~ PMK.inW Wextra i) -> L5C.agree_on M M2 a n).
{ intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 112) (PMSP.pm_scr h) WS M M2 EKc STKc SCc a n H1); [lia|].
intros i Hi I. unfold WS in I. destruct I as (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
- unfold PMSP.W_src, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr;
clear - Hi H1 H2 Hr Q4 X5 F1; unfold hl_ceil in *; lia.
- apply (N i Hi). exists r0. split; [exact Hin| exact Hr]. }
assert (AGH' : forall a n, fb + 424 <= a -> a + n <= fb + 480 -> L5C.agree_on M M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 112) (PMSP.pm_scr h) WS M M2 EKc STKc SCc a n); [lia|lia|].
intros i Hi I. apply WCs in I. clear - Hi H1 H2 I Q4 X5 F1 X1. unfold hl_ceil in *. lia. }
assert (QC2 : PM.sr_qc src2 = PM.sr_qc (PM.p_src s1)) by (destruct STEP2 as (E & _); exact E).
apply (KNT fx2 R2' M2 src2 sm2 RP2 RES2).
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
assert (NX : forall a, S - 64 <= a -> forall i, a <= i < a + 8 -> ~ PMK.inW Wextra i) by (intros a H1 i Hi I; apply WXin in I; lia).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; [lia|lia| apply NX; lia]|lia|lia|assumption]).
- exact MO2.
- split; [|split; [rewrite (own_with_src s1 src2 QC2); exact HH2|split; [exact MB|split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP STEP2)|split; [exact EE| exact CK]]]]].
unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split; [exact PA2|]. split; [exact IA2|].
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH'; lia|lia|lia| exact VIS]. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH'; lia|lia|lia| exact VREF]. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 (S - 112) (PMSP.pm_scr h) WS M M2 EKc); [| | | | exact BASE].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCs in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha.
all: clear - I Ha X1 X3 F1 Q0 Q4 QB2; unfold hl_ceil in *; lia. }
split; [|exact TB].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1 (S - 112) (PMSP.pm_scr h) WS M M2 EKc); [| | exact ERR].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCs in I; cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha.
all: clear - I Ha X1 X3 F1 Q0 Q4 QB2; unfold hl_ceil in *; lia. }
- exact AGH.
Qed.
End Call.
End WithHeap.
End PMBOU1.
