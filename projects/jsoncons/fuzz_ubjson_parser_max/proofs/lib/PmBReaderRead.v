(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx
PmSpecsA PmSpecsAX PmSpecsAb PmSpecsBX PmModelFactsA PmStepAB0 PmBSrcKit PmBReaderReadP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBReaderRead () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMBX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0BX"; "1app"; "1list"; "1option"; "1prod"; "2eq"; "3map"; "4Z"; "0FF"; "0HI"; "0L"; "0LB"; "0LK"; "0LK2"; "0M"; "0M'"]; ["5asan_layout"; "5asan_run"; "5ff_addr"; "5fframe"; "6range"; "7inv"; "7p_src"; "7p_tb"; "7p_tg"; "7parser_own"; "7pst"; "7srcst"; "7tb_ok"; "8ffroomA"; "8pst_reset"; "9parse_spec"]; ["9reset_spec"; ":reader_read_spec"; ";ek"; "0SCFG_P"; "<incl"; "=le"; "0W"; "0ar"; "0h"; "0h'"; "0s"; "0scr"; "0sp"; ">NoDup"; "?bv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMBRR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma own_reset : ltac2:(TCodec.tc2 tcn__PmBReaderRead "?'J'5'2'4'7%2211%411&I&Nr1%211%411%513%<3721pRF>1").
Proof. intros s. destruct s as [m d dp src tb tg b k stk]. unfold PM.parser_own, PMSPA.pst_reset. cbn. destruct tb; reflexivity. Qed.
Lemma tb_ok_reset : ltac2:(TCodec.tc2 tcn__PmBReaderRead "@'J&L&Gr1%211&H%113%6231&Nr2%211%911%712%<221p071pRF?1").
Proof. intros s. destruct s as [m d dp src tb tg b k stk]. cbn. destruct tb; intros H; exact H. Qed.
Lemma inv_reset : ltac2:(TCodec.tc2 tcn__PmBReaderRead "?'J&L&Gr1%211&H%113%6231&E&Nr2%211%411p061pRF>1").
Proof. intros s.
intros TB. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|apply tb_ok_reset; exact TB].
unfold PM.stack_shape. cbn [PMSPA.pst_reset PM.p_stk length nth]. split; [lia|]. split; [unfold PM.MAX_DEPTH; lia|]. split; [left; reflexivity|].
split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PM.pstate_ok, PM.ps_root. cbn. split; [lia|]. right. right. split; [left; reflexivity| split; reflexivity].
Qed.
Lemma src_reset : ltac2:(TCodec.tc2 tcn__PmBReaderRead ";'J'5'K&F&Nr1%211%411%513%83721pRF:1").
Proof. intros s. destruct s; reflexivity. Qed.
Lemma ek_drop : ltac2:(TCodec.tc2 tcn__PmBReaderRead "Q>'@'A'2'4'7%2211%411&C%611&D%811'Q>yR0%211'3y8%511%311p051&Q2r:r9&1r8r7%33D21r6r5r4r3r2r1%=9<;7654321r;%?91>;:87654p031pQ0B1pNC1pR>L1pRHQ31pRJQ41pBQ11pHQ41p2Q51pR@Q;1pFQ=1").
Proof. intros L ar BX LB FF sp scr W M M'. induction BX as [|b BX IH]; intros E; [exact E| apply IH; exact (L5SAR.ek_tl L ar _ b FF sp scr W M M' E)]. Qed.
Lemma ffroomA_sub : ltac2:(TCodec.tc2 tcn__PmBReaderRead "Q0'7'2&C%211&Mr5r3r2%43321&Q4%13834'Q=&6&B&1%13=:9%44>@31%62A1&Q5r7r8%3221%B323Ap021p071p0?1p0B1pLH1pJI1pBJ1pRDN1pRBO1").
Proof. intros h h' FF LK LK2.
intros FR INC ND Hh k Hk. specialize (FR k Hk). rewrite L5SAR.ff_count_app in FR. rewrite L5SAR.ff_count_app.
pose proof (L5SAR.ff_count_incl k LK2 LK INC (L5SAR.nodup_of_map_app_r FF LK2 ND)) as C2. lia.
Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Theorem reader_read_ok : ltac2:(TCodec.tc2 tcn__PmBReaderRead "<&Q0vQ3v:vQ7v9%544321&O%146543&Q1%148765p031p061").
Proof.
intros RST PARSE. unfold PMBX.reader_read_spec, PMSBX.reader_read_spec.
intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 A10 A11 RPRE INCS LEN EC ACC384 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 11) with 34816 in *. change (34816 / 8) with 4352 in STKSH.
pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
set (LB := PM.parser_own s ++ LBX) in *.
set (op := PMSPA.o_p PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *. set (ois := PMSPA.o_is PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *.
pose proof FOK as ((rs & Hfb) & Fal).
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n Xa1 Xa2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Xa1 Xa2; lia. }
assert (Eoec : oec = fb + 992) by reflexivity. assert (Eop : op = fb + 464) by reflexivity.
assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VISs & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (PMBSK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 34816 32 HH ASTK ltac:(lia)) as (SL32 & SH32 & V3).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs18.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (V0' : L5.img_clear MV 1232896 1269760) by (intros i Hi; apply V0; lia).
cfeed P (PMBRRP.brrA_conc fx R MV (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [assumption | unfold PMBRRP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A11' & A18 & C32 & C24 & C16 & C8).
unfold PMSPA.cfg. cbn [pa_reader_read PMB.AD ADDR_B].
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xa8738 R1 0xace2c M1v (fun a => sp - 32 <= a < sp - 32 + 32) K HH AM MS1 MG1 FRZ1).
{ intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (EK01 : L5SAR.ek L ar LB FF sp 34816 [] M M1).
{ apply (PMKB.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 34816 [] (sp - 32) (sp - 32 + 32) HH SPT); [lia|lia|lia|].
intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
assert (ASTK1 : L5CA.astk ar M1 sp 34816) by (apply (L5SAR.astk_grows ar M M1 sp 34816 ASTK MGM1)).
assert (SV1 : forall k v, 1 <= k <= 4 -> L5.u64_at RSEGS M1v (sp - 8 * k) v -> L5.u64_at RSEGS M1 (sp - 8 * k) v).
{ intros k v Hk X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 (sp - 8 * k) v (VISs (sp - 8 * k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; clear - Eop; lia).
assert (PA1 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M1 op ois s).
{ apply (PMKB.parser_keepA RSEGS PMB.AD L ar LB FF sp 34816 [] M M1 EK01 PMKB.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl. }
unfold PMB.reset_spec, PMSPA.reset_spec in RST. cbn [pa_reset PMB.AD ADDR_B] in RST.
apply (RST fx1 R1 M1 model1 K LBX FF LK Aw cr (sp - 32) 0xa8764 fb s HH1 AM1 K0).
{ split; [rewrite L5K.rl1; exact A1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact A2|].
split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
split; [apply (L5SAR.astk_sub ar M1 M1 sp 34816 32 14336 ASTK1 (fun _ X => X)); [lia|lia|lia|]; replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact A16|].
apply (PMKB.stksh_keepA L ar LB FF sp 34816 [] M M1 EK01 PMKB.wapp_nil (sp - 32 - 14336) 1792); [lia|lia|lia| | lia|].
- apply PMKB.mod16_8'. replace (sp - 32 - 14336) with (sp + (-898) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
- apply (PMKB.shadow_zero_sub M (sp - 34816) 4352); [| | lia| lia| lia| exact STKSH].
+ apply PMKB.mod16_8'. replace (sp - 34816) with (sp + (-2176) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
+ apply PMKB.mod16_8'. replace (sp - 32 - 14336) with (sp + (-898) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
{ intros k Hk. specialize (FRM k Hk). lia. }
{ intros f Hf. specialize (FRS f Hf). lia. }
{ exact FOK. }
{ rewrite L5K.rl10. rewrite (KS1 10%nat) by inl. exact A10. }
{ exact PA1. }
{ exact LEN. }
intros fx2 R2 M2 model2 LK2 Aw2 RP2 PA2 HP2 MRT2 INCLK2 INCA2 AM2 HH2.
change (PMSPA.pm_scr 1) with 14336 in HP2. unfold PMSPA.o_tb, PMSPA.o_vec in HP2. fold op in HP2.
set (W4 := [(op + 8, 8); (op + 336, 24); (op + 360, 24)]) in *.
assert (WC4 : forall rr a, In rr W4 -> L5.in_rng rr a -> op + 8 <= a < op + 384).
{ intros rr a Hin Hr. unfold W4 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hr; lia. }
assert (EK12 : L5SAR.ek L ar LBX FF sp 34816 W4 M1 M2).
{ apply (L5SAR.ek_callee L ar LBX [] FF [] sp 34816 (sp - 32) 14336 W4 W4 M1 M2 HP2); [lia|lia|]. intros a _ O. exact O. }
assert (DK12 : L5SAR.dk L ar LBX FF sp 34816 M1 M2) by (apply (L5SAR.dk_callee L ar LBX [] FF [] sp 34816 (sp - 32) 14336 W4 M1 M2 HP2); lia).
assert (EK01x : L5SAR.ek L ar LBX FF sp 34816 W4 M M1).
{ apply (L5SAR.ek_W L ar LBX FF sp 34816 W4 [] M M1); [| intros a _ r0 []]. exact (ek_drop L ar (PM.parser_own s) LBX FF sp 34816 [] M M1 EK01). }
assert (EK02 : L5SAR.ek L ar LBX FF sp 34816 W4 M M2) by exact (L5SAR.ek_trans L ar LBX FF sp 34816 W4 M M1 M2 EK01x EK12).
assert (WAPP4 : PMKB.wapp W4).
{ unfold W4. pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
repeat apply PMKB.wapp_cons; [..| apply PMKB.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [Y|Y]; clear - Y F1 F2 Eop; lia. }
pose proof FRB as FRBx.
assert (BRBx : forall b, In b LBX -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB; unfold LB; apply in_or_app; right; exact Hb).
assert (OUT4 : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= op + 8 \/ op + 384 <= a) -> forall i, a <= i < a + n -> L5.outside W4 i).
{ intros a n X1 X2 X3 i Hi rr Hin Hr. pose proof (WC4 rr i Hin Hr) as Y. clear - X3 Hi Y. lia. }
assert (ASTK2 : L5CA.astk ar M2 sp 34816) by (apply (PMKB.astk_after_ahpres L ar LBX FF M1 M2 sp 34816 (sp - 32) 14336 W4 ASTK1 HP2); lia).
assert (IA2 : PM.iss_at RSEGS PMB.AD PMSPA.accA M2 ois str sm).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LBX FF sp 34816 W4 M M2 EK02 WAPP4 FRBx BRBx _ _ _
(AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [exact INCS| apply OUT4; clear - Eois Eop; lia| | exact IA].
intros c0 n0 p0 E0. unfold PMKB.blk_out. intros i Hi rr Hin Hr. pose proof (WC4 rr i Hin Hr) as Y.
destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ p0 c0 op 384 HH (in_or_app _ _ _ (or_intror (INCS _ ltac:(rewrite E0; cbn; left; reflexivity)))) AOP) as [Z|Z];
clear - Hi Y Z; lia. }
assert (VIS2 : PMSPA.visitor_at RSEGS PMB.AD M2 ov).
{ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar LBX FF sp 34816 W4 M M2 EK02 WAPP4 FRBx _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS].
apply OUT4; clear - Eov Eop; lia. }
assert (VREF2 : L5.u64_at RSEGS M2 (op + 384) ov).
{ apply (PMKB.u64_keepA RSEGS L ar LBX FF sp 34816 W4 M M2 EK02 WAPP4 FRBx (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
apply OUT4; clear - Eop; lia. }
assert (EC2 : PMSPA.ec_at RSEGS M2 oec 0 cat).
{ apply (PMKB.ec_keepA RSEGS L ar LBX FF sp 34816 W4 M M2 EK02 WAPP4 FRBx _ 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC].
apply OUT4; clear - Eoec Eop; lia. }
assert (FB0 : 6893568 <= fb) by (clear - FSI F1; lia).
assert (BASE2 : PMSTA.base_okA RSEGS PMB.AD M2).
{ apply (PMBSK.base_keep L ar C LY LBX FF sp 34816 W4 M M2 EK02); [| exact BASE].
intros a Ha rr Hin Hr. pose proof (WC4 rr a Hin Hr) as Y. clear - Ha Y FB0 Eop; lia. }
assert (ERR2 : PMSTA.err_okA RSEGS PMB.AD PMB.AAD M2 e).
{ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar LBX FF sp 34816 W4 M M2 EK02 e PMB.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)|]. intros rr Hin Hr. pose proof (WC4 rr a Hin Hr) as Y. clear - DI Y FB0 Eop; lia. }
assert (FRAME12 : forall a, sp - 32 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha. destruct HP2 as (P2 & _ & _). apply P2. split; [lia|]. split.
- unfold aclient, aclient_g. right; left. split; [lia| intros X; lia].
- intros rr Hin Hr. pose proof (WC4 rr a Hin Hr) as Y. clear - Ha Y F2 FSCEIL SLO Eop; lia. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
assert (SV2 : forall k v, 1 <= k <= 4 -> L5.u64_at RSEGS M1v (sp - 8 * k) v -> L5.u64_at RSEGS MV2 (sp - 8 * k) v).
{ intros k v Hk X. apply (proj2 (L5A.u64_at_vis H2 M2 (sp - 8 * k) v (VIS2s (sp - 8 * k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRAME12; lia| lia| lia| exact (SV1 k v Hk X)]. }
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK2 cr Aw2 M2 model2 sp 34816 32 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 op 392 sp 34816 HH2 (PMKB.aobj_of_aobjA FF op 392 (AOF op 392 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)) ltac:(clear - Eop Fal; lia)) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
change (392 / 8) with 49 in OSHV. unfold SB in OSHV.
assert (VR2v : L5.u64_at RSEGS MV2 (op + 384) ov).
{ apply (proj2 (L5A.u64_at_vis H2 M2 (op + 384) ov ltac:(eapply L5A.avis_sub; [exact OVIS|lia|lia]) ltac:(lia) ltac:(lia))). exact VREF2. }
assert (Z384 : L5KA.zeros_at MV2 ((op / 8) + 2147450928) 1).
{ assert (ACC2 : PMSPA.accA M2 (op + 384) 8).
{ apply (PMKB.acc_keepA L ar LBX FF sp 34816 W4 M M2 EK02 WAPP4 FRBx (op + 384) 8 (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact ACC384].
apply OUT4; clear - Eop; lia. }
assert (SX : HeapIfaceA.S (op + 391) = op / 8 + 2147450928).
{ unfold HeapIfaceA.S, HeapIfaceA.SB. rewrite <- O5 at 1. replace (op / 8 * 8 + 391) with (7 + (op / 8 + 48) * 8) by lia. rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
assert (M7 : (op + 391) mod 8 = 7).
{ rewrite <- O5 at 1. replace (op / 8 * 8 + 391) with (7 + (op / 8 + 48) * 8) by lia. rewrite Z_mod_plus_full. reflexivity. }
apply (proj2 (L5A.zeros_at_vis H2 M2 (op / 8 + 2147450928) 1 ltac:(eapply L5A.avis_sub; [exact OSHV| lia| lia]))).
intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
destruct (ACC2 (op + 391) ltac:(lia)) as [B|(v & B & Bv1 & Bv2)]; rewrite SX in B; [exact B|]. exfalso. clear - M7 Bv1 Bv2. lia. }
pose proof (PMBRRP.brrB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => bv_unsigned (getr R (reg 18)) | 37%nat => r
| 38%nat => bv_unsigned (getr R (reg 9)) | 39%nat => bv_unsigned (getr R (reg 8)) | 40%nat => op | 41%nat => oec | 43%nat => ov | _ => 0 end)) as P.
cbn beta iota in P.
assert (R22 : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact A2).
assert (R28 : getr R2 (reg 8) = Z_to_bv 64 oec) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; rewrite A8; exact A11).
assert (R29 : getr R2 (reg 9) = Z_to_bv 64 op) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; rewrite A9; exact A10).
assert (R218 : getr R2 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl; exact A18).
rewrite Rra, L5.unsigned_lit in C8 by lia.
assert (D8 : L5.u64_at RSEGS MV2 (sp - 8) r) by (replace (sp - 8) with (sp - 8 * 1) by lia; apply SV2; [lia| exact C8]).
assert (D16 : L5.u64_at RSEGS MV2 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (replace (sp - 16) with (sp - 8 * 2) by lia; apply SV2; [lia| exact C16]).
assert (D24 : L5.u64_at RSEGS MV2 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (replace (sp - 24) with (sp - 8 * 3) by lia; apply SV2; [lia| exact C24]).
assert (D32 : L5.u64_at RSEGS MV2 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (replace (sp - 32) with (sp - 8 * 4) by lia; apply SV2; [lia| exact C32]).
pose proof VIS as (VU & _). fold ov in VU.
L5SAR.feed P ltac:(first [assumption | unfold PMBRRP.aligned; lia | lia]).
destruct P as (fx3 & R3 & M3v & MG3 & FRW3 & _ & MS3 & KS3 & B1 & B2 & B8 & B9 & B10 & B11 & B12 & B18).
assert (E3 : M3v = MV2) by (apply functional_extensionality; exact FRW3). subst M3v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xa8764 R3 0xad088 MV2 K HH2 AM2 MS3 MG3 (fun a Ha => eq_refl)).
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
assert (CH : forall k, In k PMBRRP.KS_brrA -> In k PMBRRP.KS_brrB -> In k L5SAR.cs_all -> getr R3 (reg k) = getr R (reg k)).
{ intros k K1 K2 K3. rewrite (KS3 k K2). rewrite (L5SAR.cs_of_preserved R1 R2 k RP2 K3). apply KS1. exact K1. }
unfold PMB.parse_spec, PMSPA.parse_spec in PARSE. cbn [pa_parse PMB.AD ADDR_B] in PARSE. rewrite <- (own_reset s) in HH3.
apply (PARSE fx3 R3 M2 model3 K LBX FF LK2 Aw2 cr sp r fb cat (PMSPA.pst_reset s) str sm e HH3 AM3 K0).
- split; [rewrite L5K.rl1; exact B1|]. split; [exact RAok|]. split; [rewrite L5K.rl2; exact B2|].
split; [rewrite L5K.rl3; rewrite (CH 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (CH 4%nat) by inl; exact Rtp|].
change (PMSPA.pm_scr 10) with 32768. change (32768 / 8) with 4096.
split; [pose proof (L5SAR.astk_sub ar M2 M2 sp 34816 0 32768 ASTK2 (fun _ X => X) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (sp - 0) with sp by lia; exact A16)) as X;
replace (sp - 0) with sp in X by lia; exact X|].
replace (sp - 32768) with (sp - 0 - 32768) by lia.
apply (PMKB.stksh_keepA L ar LBX FF sp 34816 W4 M M2 EK02 WAPP4 (sp - 0 - 32768) 4096); [lia|lia|lia| | lia|].
+ apply PMKB.mod16_8'. replace (sp - 0 - 32768) with (sp + (-2048) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
+ apply (PMKB.shadow_zero_sub M (sp - 34816) 4352); [| | lia| lia| lia| exact STKSH].
* apply PMKB.mod16_8'. replace (sp - 34816) with (sp + (-2176) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
* apply PMKB.mod16_8'. replace (sp - 0 - 32768) with (sp + (-2048) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
- pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
exact (ffroomA_sub 11 10 FF LK LK2 FRM INCLK2 NDF3 ltac:(lia)).
- exact FRS.
- exact FOK.
- exact SP32.
- split; [rewrite L5K.rl10; exact B10|]. split; [rewrite L5K.rl11; exact B11| rewrite L5K.rl12; exact B12].
- split; [exact PA2|]. split; [exact IA2|]. split; [exact VIS2|]. split; [exact VREF2|]. split; [exact BASE2|]. split; [exact ERR2|]. apply tb_ok_reset. exact TBOK.
- exact INCS.
- apply inv_reset. exact TBOK.
- exact EC2.
- rewrite src_reset. exact UNR.
- exact CRED.
- intros fx4 R4 M4 model4 LK4 Aw4 s' sm' e' cr' RP4 PPOST HP4 CK4 MRT4 INCLK4 INCA4 AM4 HH4.
change (PMSPA.pm_scr 10) with 32768 in HP4.
apply (KONT fx4 R4 M4 model4 LK4 Aw4 s' sm' e' cr'); [| exact PPOST| | exact CK4| | | | exact AM4| exact HH4].
+ apply (L5SAR.regs_preserved_trans R R3 R4); [|exact RP4]. apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
destruct Hk as [<-|Hk]; [rewrite B2, Rsp; reflexivity|].
repeat (destruct Hk as [<-|Hk];
[ first [ (rewrite B8; apply Z_to_bv_bv_unsigned) | (rewrite B9; apply Z_to_bv_bv_unsigned) | (rewrite B18; apply Z_to_bv_bv_unsigned)
| (apply CH; [inl| inl| unfold L5SAR.cs_all; cbn; tauto]) ] |]).
destruct Hk.
+ set (WR4 := PMSPA.W_run PMB.AD fb) in *.
assert (SUB : forall a, L5.outside WR4 a -> L5.outside W4 a).
{ intros a O rr Hin. apply O. unfold WR4, PMSPA.W_run, PMSPA.W_srcf, PMSPA.o_tb, PMSPA.o_vec. fold op. cbn [app]. unfold W4 in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; [left; reflexivity| do 4 right; left; reflexivity| do 5 right; left; reflexivity]. }
assert (EK24 : L5SAR.ek L ar LBX FF sp 34816 WR4 M2 M4).
{ apply (L5SAR.ek_callee L ar LBX [] FF [] sp 34816 sp 32768 WR4 WR4 M2 M4 HP4); [lia|lia|]. intros a _ O. exact O. }
apply (L5SAR.ahpres_of L ar LBX FF sp 34816 WR4 M M4).
* apply (L5SAR.ek_trans L ar LBX FF sp 34816 WR4 M M2 M4); [apply (L5SAR.ek_W L ar LBX FF sp 34816 WR4 W4 M M2 EK02 SUB)| exact EK24].
* pose proof (PMKB.astk_after_ahpres L ar LBX FF M2 M4 sp 34816 sp 32768 WR4 ASTK2 HP4 ltac:(lia) ltac:(lia) ltac:(lia) TOP) as (_ & _ & _ & _ & D4 & _). exact D4.
* apply (L5SAR.dk_trans L ar LBX FF sp 34816 M M1 M4); [apply L5SAR.dk_grows; exact MGM1|].
apply (L5SAR.dk_trans L ar LBX FF sp 34816 M1 M2 M4); [exact DK12|].
apply (L5SAR.dk_callee L ar LBX [] FF [] sp 34816 sp 32768 WR4 M2 M4 HP4); lia.
+ eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
+ intros x Hx. apply INCLK2. apply INCLK4. exact Hx.
+ intros x Hx. apply INCA4. apply INCA2. exact Hx.
Qed.
End WithHeap.
End SCFG_1.
End PMBRR.
