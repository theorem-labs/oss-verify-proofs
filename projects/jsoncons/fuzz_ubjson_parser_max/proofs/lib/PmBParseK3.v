(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBReset1 PmBParseD PmBParseK PmBParseK2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseK3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "4Model"; "5bvmap"; "0M"; "0M1"]; ["0M1'"; "0M2"; "0M2'"; "0R"; "0R1"; "0R2"; "6credit"; "6regs_preserved"; "7fframe"; "7model_rt"; "7ri_inv"; "7vml_of"; "9in_rng"; "9ra_ok"; "9range"; "8SCFG"]; [":aframe"; ":apctx"; ":lmem"; ";AADDR_B"; ";ADDR_B"; "<PST"; "<inv"; "<parser_own"; "<pst"; "<pstate"; "<pstate_at"; "<srcst"; "<strm"; "<vstr"; "=W_run"; "=cfg"]; ["=ec_at"; "=o_ec"; "=run_post"; "=run_spec_r"; ">FPState"; ">getr"; "?TSet"; "@srealizes"; "Amem_grows"; "Bamodel_ok"; "Cloaded_segments"; "0SCFG_P"; "DIn"; "Eadd"; "Ele"; "Elt"]; ["Emul"; "Eof_nat"; "Epow"; "Esub"; "0a"; "0ar"; "0args"; "0cat"; "0cr"; "0cr1"; "0cr2"; "0dn1"; "0dp1"; "0e"; "0e1"; "0e2"]; ["0fb"; "0fl"; "0fx1"; "0fx2"; "0h"; "0mo1"; "0model"; "0model1"; "0model1'"; "0model2"; "0model2'"; "0n"; "0off"; "0pc"; "0pre"; "0prog"]; ["0r"; "0r0"; "0rr"; "0s"; "0s1"; "0s2"; "0sm"; "0sm1"; "0sm2"; "0sp"; "0src1"; "FZ_to_bv"; "Fbv"; "0str"; "0tb1"; "0tg1"]; ["0top"; "0top'"; "0vb1"; "0vk1"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPK3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma step_top : ltac2:(TCodec.tc2 tcn__PmBParseK3 "W7&R6&My5'SLyR0%211%5241'9y8%611%311p061'L'7';'A%2211%411&Q8%611&Q6'QH'QM'QL'4'QK'QI%>11&QAvR;vFvREvDrQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%FEEDCBA@?>=<;:987654321&Q@rKrJrIrH%5BJIHGFEDCBA@?;74321&QBrQ=rGrFrE(QErDrCrBrAr@r?r>r=&3r<(5r;(8%11QB%43QC31%73QD61%A9@?>=<;:91r9r8r7%JJQEQDQCIQBQAQ@Q?Q>Q=Q<Q;Q9Q7Q6Q5Q4Q3LHGF4321&Q:&QG%=3QL>:%@3QMA1%J9KIHGFEDC1%411%C3R:1QH%R=2R;R<(:+1%24R?R?Q?1&R=&RC+Y0%22QK1+Q0%5221%94RERF71%M3;1R3&Q;r6%211%F8R:@4Q?IQ>H1&R9%12QAJ&Q9%12QIM&R8r:%22R01'<&R>zr1%3221&R?&RB+2+R0%3221%5271%;271&?&R@&RA&6%12S8R2%311%52Q11%Q62R81%Q721QLr2%E221%Q:23I%C231%I231%>11'=&SKr3%22T<1%R<11%S512%63T921p081p0H1pU:T71%Q42Q3Q7%Q12Q4Q8%QJ2RAR?%Q721QG&QJ&R:%L2T3S0%N11%Q02QL1%R12S51%645RM1S1rQGrQFrQErQDrQCrQBrQArQ@rQ?%S23TAS<RO%S53TBS@1%S?9SNSMSLSISHSGSFSB1%SEJT@T?T><;:987654SDT<T;T:T9T8S;S:T1T01S>S=S<p0>1p0F1p0I1p0K1p0M1p0R31p0R71p0R:1p0R=1p0S51p0T11p0T81pVHU<1pVJU=1pVBUA1pR2UC1pUDU;1pUNU81pW@U:1pX4U81pX2U91pVNU91pX8UF1pX6UG1pX0UH1pWNUB1pWFU@1pUJUK1pUHUL1pV<UM1p4UL1pQDUK1pV@V31pR0V51pVDV51pR4V71pQFV01pV4V51pQ6V61pULUN1pW>V01pWLV21pW8V41pU@V;1pV2V<1pW2V=1pWDV>1pUBV:1p2V>1pQBV=1pQ8V>1pQ@VA1pV>VG1pQNVI1pR8VO1pQ<W61").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre top top' sm1 e1 cr1 M1' model1' off n.
intros CTX G LM HH1' AM1' MRT1' MG1 FR1 Hoff Hn Hon PT'.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1). change (PMSPA.pm_scr 10) with 32768 in *.
set (s1 := PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [top])) in *.
set (FF' := (F, 1, sp - 288 + 32) :: FF) in *.
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & WF1 & FSAPP1 & FSCEIL1 & _).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). cbn [s1 PM.p_b PM.p_k PM.p_stk] in PVEC.
pose proof PVEC as (_ & _ & _ & Hk & Hlen & Hal & _).
rewrite length_app in Hlen. cbn [length] in Hlen. rewrite Nat2Z.inj_add in Hlen. cbn [Z.of_nat Pos.of_succ_nat] in Hlen.
assert (VIN : In (vb1, 32 * 2 ^ vk1) LB1) by (unfold LB1; apply in_or_app; left; unfold s1, PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (WB1 _ VIN) as ((B0 & BI0 & B16 & _ & B4 & BAPP) & _ & _ & _ & _ & BFA & _). cbn [fst snd] in B0, BI0, B16, B4, BAPP, BFA.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
pose proof (PM.pow2_pos vk1 ltac:(lia)) as P2K.
assert (TB : vb1 <= T /\ T + 32 <= vb1 + 32 * 2 ^ vk1) by (unfold T; clear - Hlen; lia).
assert (EKp : L5SAR.ek L ar LB1 FF' 0 0 [(T + off, n)] M1 M1').
{ apply (L5SAR.ek_piece L ar LB1 FF' 0 0 [(T + off, n)] M1 M1' (fun a => T + off <= a < T + off + n) FR1).
intros a Ha _ O X. apply (O (T + off, n)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X]. }
assert (WSp : PMKB.wapp [(T + off, n)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct BAPP as (_ & [X|X] & _); [left| right]; clear - X TB Hon Hoff; lia| apply PMKB.wapp_nil]. }
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
assert (AOF : forall a k0, fb + 32 <= a -> a + k0 <= fb + 1016 -> PMSPA.aobjA FF' a k0).
{ intros a k0 X1 X2. exists (fb, 4, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - X1 X2; lia. }
pose proof (BFA (fb, 4, rs) (in_or_app FF' LK1 (fb, 4, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 4) with 1024 in Z2.
assert (OUTF : forall a k0, fb + 32 <= a -> a + k0 <= fb + 1016 -> forall i, a <= i < a + k0 -> L5.outside [(T + off, n)] i).
{ intros a k0 X1 X2 i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - X1 X2 Hi Z2 TB Hoff Hon. lia. }
assert (OUTB : forall q m, In (q, m) LB1 -> q <> vb1 -> forall i, q <= i < q + m -> L5.outside [(T + off, n)] i).
{ intros q m Hq NE i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
destruct (PMBSK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q m vb1 (32 * 2 ^ vk1) HH1 Hq VIN NE) as [X|X]; clear - X Hi TB Hoff Hon; lia. }
assert (ND1 : NoDup (map fst LB1)) by exact (PMBSK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH1).
assert (QIN : In (PM.sr_qc src1, PM.CHUNK) LB1) by (unfold LB1; apply in_or_app; left; unfold s1, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (QNE : PM.sr_qc src1 <> vb1).
{ intros E. unfold LB1, s1, PM.parser_own, PM.src_own, PM.vec_own in ND1. cbn in ND1. rewrite E in ND1. inversion ND1 as [|x l NI _]. apply NI. apply PMBSK.elem_of_InA. left. reflexivity. }
assert (OP : PMSPA.o_p PMB.AD fb = fb + 464) by reflexivity.
split; [|split; [| split; [| split; [exact STEP1| split; [exact EE1| exact CK1]]]]].
- apply (PMBLPK.binv_pieceB L ar C HI HIok R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 _ _ M1 model1 LK1 cr1 Aw1 M1' model1' (fun a => T + off <= a < T + off + n) G BI HH1' AM1' MRT1' MG1 FR1).
intros a X. exists vb1, (32 * 2 ^ vk1). split; [unfold s1, PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity| clear - X TB Hoff Hon; lia].
- pose proof (WF1 _ (or_intror Hfb)) as (FB1 & FB2 & _). cbn [ff_addr ff_class fst snd] in FB1, FB2. change (ff_bytes 4) with 1024 in *.
pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH1) as FSI.
unfold app_mem, FS_BYTES in FSAPP1, FB2.
pose proof PA1 as (_ & PDEF1 & _ & _ & _ & _ & _ & _ & _ & PSRC1 & _ & _ & _ & PTB1 & _). cbn [s1 PM.p_src PM.p_tb] in PSRC1, PTB1.
destruct PSRC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DCH1 & _).
pose proof PVEC as (_ & _ & _ & _ & _ & _ & DB1 & _).
assert (ISX : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall i, q1 <= i < q1 + c1 -> L5.outside [(T + off, n)] i).
{ intros c1 n1 q1 E. assert (SIN : In (q1, c1) LBX) by (apply INCS; rewrite E; left; reflexivity).
apply (OUTB q1 c1 (in_or_app _ _ _ (or_intror SIN))). intros X. subst q1.
apply (PMBSK.fst_neq_appA (PM.parser_own s1) LBX vb1 (32 * 2 ^ vk1) vb1 c1 ND1); [unfold s1, PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity| exact SIN| reflexivity]. }
unfold PMSPA.run_pre. split; [| split; [| split; [| split; [| split; [| split]]]]].
+ apply (PMBLPK2.parser_top_updA M1 M1' _ _ s1 pre top top' PA1 eq_refl); cbn [s1 PM.p_src PM.p_b PM.p_k PM.p_tb].
* rewrite OP. clear - FB1 FSI; lia.
* rewrite OP. clear - FB2 FSAPP1; lia.
* apply (PMKB.agA_obj L ar LB1 FF' 0 0 _ M1 M1' EKp WSp FRB1 (PMSPA.o_p PMB.AD fb) 384 (AOF (PMSPA.o_p PMB.AD fb) 384 ltac:(rewrite OP; clear; lia) ltac:(rewrite OP; clear; lia))).
apply (OUTF (PMSPA.o_p PMB.AD fb) 384); rewrite OP; clear; lia.
* apply (L5.defined_grows M1 M1' _ _ MG1 DCH1).
* apply (PMBSK.agsh_blk L ar LB1 FF' 0 0 _ M1 M1' _ 16384 EKp WSp QIN); [destruct (BRB1 _ QIN) as (X1 & X2); cbn [fst snd] in X1, X2; clear - X1; lia| destruct (BRB1 _ QIN) as (X1 & X2); cbn [fst snd] in X1, X2; unfold PM.CHUNK in X2; clear - X2; lia].
* clear - B0. lia.
* clear - B4 SLO SHI SPT. lia.
* intros i Hi. rewrite FR1; [reflexivity| clear - Hi TB B0 B4 SLO SHI SPT; lia| clear - Hi TB Hoff; unfold T in *; lia].
* intros i Hi. rewrite FR1; [reflexivity| clear - Hi TB B0 B4 SLO SHI SPT; lia| clear - Hi TB Hon; unfold T in *; lia].
* apply (PMBSK.agsh_blk L ar LB1 FF' 0 0 _ M1 M1' vb1 (32 * 2 ^ vk1) EKp WSp VIN); clear - B0 B4 SLO SHI SPT; lia.
* apply (L5.defined_grows M1 M1' _ _ MG1). apply (L5.defined_sub M1 vb1 (32 * 2 ^ vk1)); [exact DB1| clear - TB; lia| clear - TB; lia].
* exact PT'.
* intros c0 n0 q0 E. assert (TIN : In (q0, c0) LB1) by (unfold LB1; apply in_or_app; left; unfold s1, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; rewrite E; cbn; right; right; left; reflexivity).
apply (PMKB.agA_blk L ar LB1 FF' 0 0 _ M1 M1' EKp WSp BRB1 q0 c0 TIN). apply (OUTB q0 c0 TIN). intros X. subst q0.
unfold LB1, s1, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own in ND1. rewrite E in ND1. cbn in ND1.
inversion ND1 as [|x l _ ND2]. inversion ND2 as [|x2 l2 NI _]. apply NI. apply PMBSK.elem_of_InA. left. reflexivity.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB1 FF' 0 0 _ M1 M1' EKp WSp FRB1 BRB1 _ str sm1 (AOF (PMSPA.o_is PMB.AD fb) 272 ltac:(unfold PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; clear; lia) ltac:(unfold PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; clear; lia)));
[unfold LB1; apply incl_appr; exact INCS| apply (OUTF _ 272); unfold PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; clear; lia| exact ISX| exact IA1].
+ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar LB1 FF' 0 0 _ M1 M1' EKp WSp FRB1 _ (AOF (PMSPA.o_v PMB.AD fb) 8 ltac:(unfold PMSPA.o_v; cbn [pa_off_v PMB.AD ADDR_B]; clear; lia) ltac:(unfold PMSPA.o_v; cbn [pa_off_v PMB.AD ADDR_B]; clear; lia)));
[apply (OUTF _ 8); unfold PMSPA.o_v; cbn [pa_off_v PMB.AD ADDR_B]; clear; lia| exact VIS1].
+ apply (PMKB.u64_keepA RSEGS L ar LB1 FF' 0 0 _ M1 M1' EKp WSp FRB1 (PMSPA.o_p PMB.AD fb + 384) _ (AOF (PMSPA.o_p PMB.AD fb + 384) 8 ltac:(rewrite OP; clear; lia) ltac:(rewrite OP; clear; lia)));
[apply (OUTF (PMSPA.o_p PMB.AD fb + 384) 8); rewrite OP; clear; lia| exact VREF1].
+ apply (PMBSK.base_keep L ar C LY LB1 FF' 0 0 _ M1 M1' EKp); [| exact BASE1].
intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI0. clear - Ha BI0 TB Hoff Hon. lia.
+ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar LB1 FF' 0 0 _ M1 M1' EKp e1 PMB.addrs_wf_A); [| exact ERR1].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)|]. intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI0. clear - DI BI0 TB Hoff Hon. lia.
+ exact TB1.
- apply (PMBLPD.lspill_agree M1 M1' sp F _ _ _ ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) LS1).
intros a Ha. apply FR1; [clear - Ha SLO SHI SPT; lia| clear - Ha TB B4 SLO Hoff Hon; unfold T in *; lia].
Qed.
Lemma wrun_where : ltac2:(TCodec.tc2 tcn__PmBParseK3 "Q5'A'>&Q>'<&R<r1&QN&QDr3%3221%63851&Q<r2%2281%;241qW4=1%?2>1'@&R>&R=+Q0%22=1%421:&R?+oH%62A1%32>1%H251+V]lV0%;21A+VbSaD%82C1%M231%@261p0B1pU:Q31pV2Q41").
Proof. intros fb a.
intros (r0 & Hin & Hr). unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_is, PMSPA.o_p in Hin.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMB.AD ADDR_B app] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Lemma alp_call_run : ltac2:(TCodec.tc2 tcn__PmBParseK3 "W5&R6&My5'SLyR0%211%5241'9y8%611%311p061'L'7';'A%2211%411&Q8%611&Q6'QH'QM'QL'4!p051p0<1p0F1p064p071p0:1p0;1p0K1'R4&R3vR;&R:&QD&QCvFvREvDr?r>r=r<%<;;:987654321&QArQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrF%BENJIHA@?>=<;:987654321&Q@rErDrCrB%5BQ0ONGFEDCBA@?;74321&QBrQ7r;r:r9r8r7r6r5%9JQ:Q9Q88Q1Q0ONMLKJHFEDCBQ47654321'<&R>z%221?+9%42A1%6231'=&R5&SK&RAu1%211%42RN1%62QF1%62RNB%93RN21&Q=%11FrAu2%;11%=2S71%?241&RC+Y0%22QI1%B2S:1%E3S:51u3%D11%F2S@1%H2Q<1rQ<%J213%L3SA31u4%K11%M2SG1%O2QD1rQ=%Q1213%Q33SH31%QN3QIR;RC&QFr@%211&R0&R1%12RNRC%35S0R11Q@RC&Q7%12RAQJ&R2rQBrQ?r4r3rQA%6?S9S8S7RKR2R15RDQM4RC3RB21rQMrQLrQKrQJrQIrQHrQGrQFrQErQCrQ@rQ>%RBJSCSBSA<;:9876543>2A1Q0R?R>R=R<R;R:@?'R7&Q?%11SJ&QO%16SKSCSBS4RERDrQO%64SM421p081p0F1p0N1pUFTB1pV0T?1pWBTA1pW<TD1p6TI1pQHTH1pVFU01pR6U21pR<U81pV8T=1%A6T;SBSASFS@S?%E4T<C1Ip031p0Q>1p0QC1p0QG1p0QI1p0R11p0R91p0RD1p0RG1p0S21p0S:1p0SE1p0SL1p0T@1pW6UA1pUDU=1pUNU:1pW@U<1pW:U?1p4UD1pQDUC1pV@UK1pR0UM1pR:V31pV6U81pW0U:1pU>U@1pV:UN1pVLUO1pVDV31pR4V51pQFUN1pV4V31pQ6V41pULUL1pW>UN1pWLV01pW8V21pU@V91pV2V:1pW2V;1pWDV<1pUBV81p2V<1pQBV;1pQ8V<1pQ@V?1pV>VE1pQNVG1pR8VM1pQ<W41").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 pc h args prog fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 rr.
intros CALLEE CTX G LM Hh G1 RA G2 G3 G4 ARG1 INV1 EC1 KX.
pose proof (PMBLPK.alp_callpre L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 h CTX G LM Hh)
as (ASTKc & SZc & FRc & FSc & FOKc).
pose proof CTX as CTX0.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
pose proof LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & _).
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
unfold PMSPA.run_spec_r in CALLEE.
apply (CALLEE fx1 R1 M1 model1 K LBX ((F, 1, sp - 288 + 32) :: FF) LK1 Aw1 cr1 (sp - 288) rr fb cat s1 str sm1 e1 HH1 AM1 K0).
- split; [exact G1|]. split; [exact RA|]. split; [exact G2|]. split; [exact (eq_trans G3 Rgp)|]. split; [exact (eq_trans G4 Rtp)|].
split; [exact ASTKc| exact SZc].
- exact FRc.
- exact FSc.
- exact FOKc.
- replace (sp - 288) with (sp + (-9) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32.
- exact ARG1.
- exact RP1.
- exact INCS.
- exact INV1.
- exact EC1.
- destruct STEP1 as (_ & _ & _ & _ & SU). clear - SU UNR. lia.
- exact (PMBPAR.credit_le_keepA _ _ _ _ CRED CK1).
- intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2 HP2 CK2 MRT2 INCL2 INCA2 AM2 HH2.
apply (KX fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2).
destruct POST2 as (RP2' & STEP2 & EE2 & _).
apply (PMBLPK.alp_liftW L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1
M2' model2' LK2' Aw2 s2 sm2 e2 cr2 [] (PMSPA.pm_scr h) (PMSPA.W_run PMB.AD fb) CTX0 G LM ltac:(unfold PMSPA.pm_scr; clear - Hh; lia) HP2);
[| intros a _ O; exact O| exact RP2'| exact STEP2| exact EE2| exact CK2| exact MRT2| exact INCL2| exact INCA2| exact AM2| exact HH2].
intros rr0 a Hin Hr. destruct (wrun_where fb a (ex_intro _ rr0 (conj Hin Hr))) as [X|X].
+ split; [clear - X F1 F2 FSCEIL SLO; lia|]. pose proof (Z.div_le_mono 6893568 F 8 ltac:(lia) ltac:(clear - GFR; lia)) as D8. change (6893568 / 8) with 861696 in D8.
unfold SB. unfold FS_BYTES in GFS2. change (ff_bytes 1) with 128 in GFS2. destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; clear - X Y F1 F2 D8 GFS2 GFR; lia.
+ split; [clear - X GFCEIL SLO GFR; lia|]. pose proof (Z.div_le_mono 6893568 F 8 ltac:(lia) ltac:(clear - GFR; lia)) as D8. change (6893568 / 8) with 861696 in D8.
unfold SB. clear - X D8; lia.
Qed.
End WithHeap.
End PMBLPK3.
