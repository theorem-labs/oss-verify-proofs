(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBParseD PmBParseK PmBParseP5.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseX () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "1bool"; "1fst"; "1list"; "1option"; "1prod"; "1snd"; "2and"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"]; ["0LK"; "0LK1"; "0LK2"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0R"; "0R1"; "6credit"; "6heap_layout"; "6hl_b_overhead"; "6hl_k_per_malloc"; "7fframe"; "8SCFG"]; ["9aframe"; "9apctx"; "9lmem"; "9lregs"; ":ADDR_B"; ";p_tb"; ";p_tg"; ";parser_at"; ";pot_parser"; ";pst"; ";strm"; ";tb_ok"; ";vstr"; "<accA"; "<annA"; "<cfg"]; ["<ec_at"; "<o_ec"; "<o_p"; "=FPState"; ">TSet"; "?srealizes"; "@loaded_segments"; "0SCFG_P"; "Ale"; "0ar"; "0c"; "0cat"; "0cr"; "0cr1"; "0e"; "0e1"]; ["0fb"; "0fl"; "0fx1"; "0model"; "0model1"; "0model2"; "0ois"; "0op"; "0r"; "0s"; "0s1"; "0sm"; "0sm1"; "0sp"; "Bbv"; "0str"]; ["0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPX.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma pot_parser_nonnegA : ltac2:(TCodec.tc2 tcn__PmBParseX "QJ'K'R>yR0%211'5y8%511%311p051'9'Q9&Q7&QF&Q4&Q=&Q>r4r3r2r1%9887654321&Q;&Q5%115&Q6%117%5231&QHz&Mr7%211%5241&Lr8%211%9281'8&3&Q8r9r5%3221%53Q2Q21%A2@1&7%13Q5Q54%D2C1%;241p0=1p0B1p0I1p0Q01pTDQ;1pT>Q=1pT@Q>1pQ<Q@1pNQI1").
Proof. intros L M op ois s.
intros PA (T0 & T1 & T2) K0 B0.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB & VEC & _).
pose proof VEC as (_ & _ & _ & Hk & _).
unfold PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text. cbn [fst snd].
assert (P2 : 2 ^ (PM.p_k s + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
assert (CAP : PM.vs_cap (PM.p_tb s) <= 2 ^ 27 - 1).
{ destruct (PM.p_tb s) as [n|c n q]; cbn [PM.vs_cap]; [lia|]. destruct TB as (_ & _ & _ & _ & _ & _ & (_ & C2) & _). lia. }
split; nia.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma parse_exit : ltac2:(TCodec.tc2 tcn__PmBParseX "SN&QD&Dy5'R>yR0%211%5241'5y8%611%311p061'C'4'6'9%2211%411&N%611&J'Q9'Q<'Q:'2'QC&Q1vQGv>vQIv<rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrB%FEEDCBA@?>=<;:987654321&Q0rAr@r?r>%5BJIHGFEDCBA@?;74321&Q3rQ3r=&QB&Q4%221D&QA%123F%8676I31A&Q2rQ4r<r;r:r9r8r7r6%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&Q@&QF%?2AQ6r5%453I261'QE&O%11QF&Q?+ef]4%269Q2Q11Q0OrQ7%74;521p091p0?1p0J1p0Q41p0Q;1pSFR=1pU2R>1pSLR:1pT0R71pTJR91pTFR<1p4RA1pQ4R@1pT:RH1pQ>RJ1pQDS01pT6R>1pT<RL1pQ@RN1pQ6RG1pT4RL1pFRM1pSNRE1pTHRG1pU0RI1pTDRK1pSHS21pT2S31pTBS41pTLS51pSJS11p2S51pQ2S41pHS51pQ0S81pT8S>1pQ<S@1pQBSF1pLSM1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c.
intros CTX G LR LM EC1.
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof CTX as CTX0.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof RAok as (Hr1 & Hr2). rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
pose proof FOK as ((rs & Hfb) & Fal).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
_ (PM.parser_own s1) M1 model1 LK1 cr1 Aw1 BI) as (_ & OWNv & _).
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
unfold PMBLPK.lfacts in LF.
destruct LF as (K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41 & K42 & K43 & K44 & K45
& K46 & K47 & K48 & K49 & K50 & K51 & K52 & K53 & K54 & K55 & K56 & K57 & K58 & K59 & K60 & K61 & K62 & K63 & K64 & K65 & K66 & K67 & K68
& K69 & K70 & K71 & K72 & K73 & K74 & K75 & K76 & LSv & Q0a & Q0b & Q0c & Q0d & Q0e & Q0f).
destruct LSv as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18).
destruct OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
destruct LR as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & X3 & X4).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27.
change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27.
cfeed P (PMBLPP5.blpR_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26))
| 76%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP5.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & Z1 & Z2 & Z8 & Z9 & Z10 & Z11 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & FL0 & _).
assert (R2ra : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite Z1, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx2 R2 M2v 0xada78 (ltac:(oW' 0xada78%Z)) r (ltac:(oF' 0xada78%Z)) eq_refl (ltac:(oD' 0xada78%Z)) R2ra Hr1 Hr2) as MSr.
set (WR := PMSPA.W_run PMB.AD fb) in *.
unfold PMSPA.cfg.
apply (PMBUK.retire_core L ar C HI LYa HIok M model LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s1) M1 model1 LK1 cr1 Aw1 fx1 fx2 R1 0xad9a4 R2 r M2v K BI (msteps_trans _ _ _ _ MS2 MSr) MG2).
{ intros a Ha Nw. unfold PMBUK.Wret in Nw. change (ff_bytes 1) with 128 in Nw. change (128 / 8) with 16 in Nw.
apply FRZ2; [exact Ha| intros X; apply Nw; left; left; clear - X; lia| intros X; apply Nw; right; clear - X; lia| intros X; apply Nw; left; right; unfold SB; clear - X; lia]. }
{ exact FL0. }
intros Mf modelf FZf AHf MRTf AMf HHf.
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
assert (EKf : L5SAR.ek L ar (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf).
{ apply (PMBUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s1 ++ LBX) LK1 cr1 Aw1 M1 Mf _ [] (fun _ => False) G HH1 (fun a X => match X with end)).
intros a Ha N. apply FZf; [exact Ha| intros X; apply N; left; exact X]. }
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n Y1 Y2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Y1 Y2; lia. }
assert (Eop : op = fb + 464) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity.
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
apply (KONT fx2 R2 Mf modelf LK1 Aw1 s1 sm1 e1 cr1).
- apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite Z2; exact (eq_sym Rsp) | rewrite Z8; apply Z_to_bv_bv_unsigned | rewrite Z9; apply Z_to_bv_bv_unsigned
| rewrite Z18; apply Z_to_bv_bv_unsigned | rewrite Z19; apply Z_to_bv_bv_unsigned | rewrite Z20; apply Z_to_bv_bv_unsigned
| rewrite Z21; apply Z_to_bv_bv_unsigned | rewrite Z22; apply Z_to_bv_bv_unsigned | rewrite Z23; apply Z_to_bv_bv_unsigned
| rewrite Z24; apply Z_to_bv_bv_unsigned | rewrite Z25; apply Z_to_bv_bv_unsigned | rewrite Z26; apply Z_to_bv_bv_unsigned
| rewrite Z27; apply Z_to_bv_bv_unsigned
| rewrite (KS2 3%nat) by inl; exact X3 | rewrite (KS2 4%nat) by inl; exact X4 ] |]).
destruct Hj.
- unfold PMSPA.parse_post, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
+ apply (PMKB.parser_keepA RSEGS PMB.AD L ar (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf EKf PMKB.wapp_nil FRB BRB1 _ _ _ (AOF op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)));
[| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA1].
apply incl_appl, incl_refl.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf EKf PMKB.wapp_nil FRB BRB1 _ str sm1 (AOF (PMSPA.o_is PMB.AD fb) 272 ltac:(unfold PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; clear; lia) ltac:(unfold PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; clear; lia)));
[| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA1].
apply incl_appr. exact INCS.
+ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf EKf PMKB.wapp_nil FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [intros i _ r0 []| exact VIS1].
+ apply (PMKB.u64_keepA RSEGS L ar (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf EKf PMKB.wapp_nil FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF1].
+ apply (PMBSK.base_keep L ar C LY (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf EKf); [intros a _ r0 []| exact BASE1].
+ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf EKf e1 PMB.addrs_wf_A); [| exact ERR1].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)| intros r0 []].
+ exact TB1.
+ split; [exact STEP1|]. split; [exact EE1|].
apply (PMKB.ec_keepA RSEGS L ar (PM.parser_own s1 ++ LBX) FF 0 0 [] M1 Mf EKf PMKB.wapp_nil FRB _ v c (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))) in EC1;
[exact (proj1 (proj2 (proj2 EC1)))| intros i _ r0 []].
- exact AHf.
- pose proof (PMB.ly_cost L C LY) as (Hk8 & Hb3 & Hbo).
destruct (pot_parser_nonnegA (PMSPA.HV L ar) M1 op _ s1 PA1 TB1) as (N1 & N2);
[unfold PMSPA.HV, LibIfaceAJ.heap_view; cbn; rewrite Hk8; clear; lia| unfold PMSPA.HV, LibIfaceAJ.heap_view; cbn; rewrite Hbo; clear; lia|].
unfold PMSPA.credit_keep, PMSPA.cr0, PMSPA.scA in *. cbn [fst snd] in *. rewrite Hb3 in *. clear - CK1 N1 N2. lia.
- exact MRTf.
- exact INCL1.
- exact INCA1.
- exact AMf.
- exact HHf.
Qed.
End WithHeap.
End PMBLPX.
